use crate::inline;
use crate::metadata::Workspace;
use crate::rewrite;
use crate::strip;
use crate::strip::StripOptions;
use anyhow::Result;
use anyhow::bail;
use std::collections::BTreeSet;
use syn::Ident;
use syn::Item;

pub struct Options {
    pub strip_tests: bool,
    pub strip_docs: bool,
}

/// 指定された全クレート＋その全内部依存をdedupし、それぞれを `mod <name> { .. }`
/// として1つの `syn::File` にまとめ、`prettyplease` で整形したソースを返す。
pub fn bundle(ws: &Workspace, requested: &[String], opts: &Options) -> Result<String> {
    for name in requested {
        if !ws.crates.contains_key(name) {
            let mut available: Vec<&str> = ws.crates.keys().map(String::as_str).collect();
            available.sort_unstable();
            bail!(
                "クレート `{name}` は libs/ 配下に見つかりません。\n利用可能なクレート:\n{}",
                available.join(", ")
            );
        }
    }

    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    for name in requested {
        collect_transitive(ws, name, &mut seen, &mut order);
    }

    let mut items = Vec::new();
    for name in &order {
        let info = &ws.crates[name];
        let mut crate_items = inline::load_crate_items(&info.lib_rs)?;
        crate_items = strip::strip_items(
            crate_items,
            &StripOptions {
                strip_tests: opts.strip_tests,
                strip_docs: opts.strip_docs,
            },
        );
        rewrite::rewrite_items(&mut crate_items, name, &seen);
        items.push(wrap_mod(name, crate_items));
    }

    let file = syn::File {
        shebang: None,
        attrs: Vec::new(),
        items,
    };
    let pretty = prettyplease::unparse(&file);
    Ok(insert_fold_markers(&pretty, &order))
}

fn collect_transitive(
    ws: &Workspace,
    name: &str,
    seen: &mut BTreeSet<String>,
    order: &mut Vec<String>,
) {
    if !seen.insert(name.to_owned()) {
        return;
    }
    order.push(name.to_owned());
    if let Some(info) = ws.crates.get(name) {
        for dep in &info.deps {
            collect_transitive(ws, dep, seen, order);
        }
    }
}

fn wrap_mod(name: &str, items: Vec<Item>) -> Item {
    Item::Mod(syn::ItemMod {
        attrs: vec![syn::parse_quote!(#[allow(unused_imports, dead_code)])],
        vis: syn::Visibility::Inherited,
        unsafety: None,
        mod_token: syn::token::Mod::default(),
        ident: Ident::new(name, proc_macro2::Span::call_site()),
        content: Some((syn::token::Brace::default(), items)),
        semi: None,
    })
}

fn insert_fold_markers(source: &str, crate_names: &[String]) -> String {
    use std::fmt::Write as _;

    let mut result = String::with_capacity(source.len());
    let mut depth = None::<(usize, String)>;
    // `mod <name> {` の直前に付く `#[allow(..)]` 等の属性行を、fold の外に出さず
    // 内側に含めるため、いったんバッファに溜めてから fold開始マーカーの後に流し込む。
    let mut pending_attrs = Vec::new();
    for line in source.lines() {
        if depth.is_none() {
            if line.starts_with("#[") {
                pending_attrs.push(line);
                continue;
            }
            for name in crate_names {
                if line.starts_with(&format!("mod {name} {{")) {
                    let _ = writeln!(result, "// {name} {{{{{{");
                    depth = Some((0, name.clone()));
                    break;
                }
            }
            for attr_line in pending_attrs.drain(..) {
                result.push_str(attr_line);
                result.push('\n');
            }
        }
        result.push_str(line);
        result.push('\n');
        if let Some((count, name)) = &mut depth {
            *count += line.matches('{').count();
            *count -= line.matches('}').count();
            if *count == 0 {
                let _ = writeln!(result, "// {name} }}}}}}");
                depth = None;
            }
        }
    }
    result
}
