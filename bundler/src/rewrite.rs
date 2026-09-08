use proc_macro2::Ident;
use proc_macro2::Punct;
use proc_macro2::Spacing;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use proc_macro2::TokenTree;
use std::collections::BTreeSet;
use syn::Item;
use syn::PathArguments;
use syn::PathSegment;
use syn::UseGlob;
use syn::UseTree;
use syn::visit_mut::VisitMut;

/// クレート `self_name` 自身のコード中に現れる、内部依存クレートへの参照を
/// バンドル後のフラットな `mod` 構造（すべて crate root の兄弟）に合わせて付け替える。
///
/// - `crate::foo` (自己参照) -> `crate::self_name::foo`
/// - `dep::foo` (`known` に含まれる他クレートへの参照) -> `crate::dep::foo`
/// - `macro_rules!` 本体中の `$crate::foo` -> `$crate::self_name::foo`
pub fn rewrite_items(items: &mut [Item], self_name: &str, known: &BTreeSet<String>) {
    let mut rewriter = Rewriter { self_name, known };
    for item in items {
        rewriter.visit_item_mut(item);
    }
}

struct Rewriter<'a> {
    self_name: &'a str,
    known: &'a BTreeSet<String>,
}

impl VisitMut for Rewriter<'_> {
    fn visit_path_mut(&mut self, path: &mut syn::Path) {
        rewrite_path_head(path, self.self_name, self.known);
        syn::visit_mut::visit_path_mut(self, path);
    }

    fn visit_item_use_mut(&mut self, item_use: &mut syn::ItemUse) {
        let tree = std::mem::replace(
            &mut item_use.tree,
            UseTree::Glob(UseGlob {
                star_token: syn::token::Star::default(),
            }),
        );
        item_use.tree = rewrite_use_tree(tree, self.self_name, self.known);
        syn::visit_mut::visit_item_use_mut(self, item_use);
    }

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        mac.tokens = rewrite_dollar_crate_tokens(mac.tokens.clone(), self.self_name);
        syn::visit_mut::visit_macro_mut(self, mac);
    }
}

fn rewrite_path_head(path: &mut syn::Path, self_name: &str, known: &BTreeSet<String>) {
    let Some(first) = path.segments.first() else {
        return;
    };
    let ident = first.ident.to_string();
    if ident == "crate" {
        insert_segment(path, 1, self_name);
    } else if known.contains(&ident) {
        insert_segment(path, 0, "crate");
    }
}

fn insert_segment(path: &mut syn::Path, index: usize, name: &str) {
    path.segments.insert(
        index,
        PathSegment {
            ident: Ident::new(name, Span::call_site()),
            arguments: PathArguments::None,
        },
    );
}

fn rewrite_use_tree(tree: UseTree, self_name: &str, known: &BTreeSet<String>) -> UseTree {
    let UseTree::Path(path) = &tree else {
        return tree;
    };
    let ident = path.ident.to_string();
    if ident == "crate" {
        let UseTree::Path(mut path) = tree else { unreachable!() };
        let inner = std::mem::replace(
            &mut *path.tree,
            UseTree::Glob(UseGlob {
                star_token: syn::token::Star::default(),
            }),
        );
        *path.tree = UseTree::Path(syn::UsePath {
            ident: Ident::new(self_name, Span::call_site()),
            colon2_token: path.colon2_token,
            tree: Box::new(inner),
        });
        UseTree::Path(path)
    } else if known.contains(&ident) {
        UseTree::Path(syn::UsePath {
            ident: Ident::new("crate", Span::call_site()),
            colon2_token: syn::token::PathSep::default(),
            tree: Box::new(tree),
        })
    } else {
        tree
    }
}

/// `macro_rules!` 本体は `syn` が構文木化しない不透明なトークン列のため、
/// `$crate::foo` のパターンをトークンレベルで検出して付け替える。
fn rewrite_dollar_crate_tokens(tokens: TokenStream, self_name: &str) -> TokenStream {
    let mut result = Vec::new();
    let mut iter = tokens.into_iter().peekable();
    while let Some(tt) = iter.next() {
        let TokenTree::Punct(dollar) = &tt else {
            result.push(recurse_into_groups(tt, self_name));
            continue;
        };
        if dollar.as_char() != '$' {
            result.push(tt);
            continue;
        }
        result.push(tt);
        let Some(TokenTree::Ident(ident)) = iter.peek() else {
            continue;
        };
        if ident != "crate" {
            continue;
        }
        result.push(iter.next().unwrap());
        let Some(colon1) = take_colon(&mut iter) else {
            continue;
        };
        let Some(colon2) = take_colon(&mut iter) else {
            result.push(colon1);
            continue;
        };
        result.push(colon1);
        result.push(colon2);
        // `$crate::foo!(..)` は `foo` 自身が `#[macro_export]` されている前提のマクロ呼び出しで
        // ある可能性があり、その場合 `foo` は常にクレート直下に存在するためセグメント挿入は不要
        // (むしろ挿入すると壊れる)。直後が `!` かどうかで判定する。
        let Some(TokenTree::Ident(_)) = iter.peek() else {
            continue;
        };
        let item_ident = iter.next().unwrap();
        let is_macro_call = matches!(iter.peek(), Some(TokenTree::Punct(p)) if p.as_char() == '!');
        if !is_macro_call {
            result.push(TokenTree::Ident(Ident::new(self_name, Span::call_site())));
            result.push(TokenTree::Punct(Punct::new(':', Spacing::Joint)));
            result.push(TokenTree::Punct(Punct::new(':', Spacing::Alone)));
        }
        result.push(item_ident);
    }
    result.into_iter().collect()
}

fn take_colon(
    iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
) -> Option<TokenTree> {
    match iter.peek() {
        Some(TokenTree::Punct(p)) if p.as_char() == ':' => iter.next(),
        _ => None,
    }
}

fn recurse_into_groups(tt: TokenTree, self_name: &str) -> TokenTree {
    let TokenTree::Group(group) = tt else {
        return tt;
    };
    let mut new_group = proc_macro2::Group::new(
        group.delimiter(),
        rewrite_dollar_crate_tokens(group.stream(), self_name),
    );
    new_group.set_span(group.span());
    TokenTree::Group(new_group)
}
