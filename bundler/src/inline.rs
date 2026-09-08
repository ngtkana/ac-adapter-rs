use anyhow::Context;
use anyhow::Result;
use std::fs;
use std::path::Path;
use syn::Item;

/// `lib.rs` を起点に、`mod foo;` 宣言を再帰的に `src/foo.rs` の中身で埋め込んだ `Item` 列を返す。
///
/// `foo/mod.rs` 形式のサブディレクトリは非対応（ac-adapter-rs の `libs/*` に存在しないため）。
pub fn load_crate_items(lib_rs: &Path) -> Result<Vec<Item>> {
    let dir = lib_rs
        .parent()
        .expect("lib.rs always has a parent directory");
    let items = parse_file(lib_rs)?;
    inline_items(items, dir)
}

fn parse_file(path: &Path) -> Result<Vec<Item>> {
    let source =
        fs::read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;
    let file = syn::parse_file(&source)
        .with_context(|| format!("failed to parse {} as Rust source", path.display()))?;
    Ok(file.items)
}

fn inline_items(items: Vec<Item>, dir: &Path) -> Result<Vec<Item>> {
    items
        .into_iter()
        .map(|item| inline_item(item, dir))
        .collect()
}

fn inline_item(item: Item, dir: &Path) -> Result<Item> {
    let Item::Mod(mut item_mod) = item else {
        return Ok(item);
    };
    if item_mod.content.is_some() {
        return Ok(Item::Mod(item_mod));
    }
    let sub_path = dir.join(format!("{}.rs", item_mod.ident));
    let sub_items = parse_file(&sub_path)?;
    let sub_items = inline_items(sub_items, dir)?;
    item_mod.content = Some((syn::token::Brace::default(), sub_items));
    item_mod.semi = None;
    Ok(Item::Mod(item_mod))
}
