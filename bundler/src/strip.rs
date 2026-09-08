use syn::Attribute;
use syn::Item;

pub struct StripOptions {
    pub strip_tests: bool,
    pub strip_docs: bool,
}

pub fn strip_items(items: Vec<Item>, opts: &StripOptions) -> Vec<Item> {
    items
        .into_iter()
        .filter(|item| !(opts.strip_tests && has_cfg_test(item)))
        .map(|item| strip_item(item, opts))
        .collect()
}

fn strip_item(mut item: Item, opts: &StripOptions) -> Item {
    if let Item::Mod(m) = &mut item
        && let Some((brace, content)) = m.content.take()
    {
        m.content = Some((brace, strip_items(content, opts)));
    }
    if opts.strip_docs
        && let Some(attrs) = item_attrs_mut(&mut item)
    {
        attrs.retain(|attr| !attr.path().is_ident("doc"));
    }
    item
}

fn has_cfg_test(item: &Item) -> bool {
    item_attrs(item).into_iter().flatten().any(is_cfg_test)
}

fn is_cfg_test(attr: &Attribute) -> bool {
    if !attr.path().is_ident("cfg") {
        return false;
    }
    attr.parse_args::<syn::Path>()
        .is_ok_and(|path| path.is_ident("test"))
}

fn item_attrs(item: &Item) -> Option<&Vec<Attribute>> {
    Some(match item {
        Item::Const(i) => &i.attrs,
        Item::Enum(i) => &i.attrs,
        Item::ExternCrate(i) => &i.attrs,
        Item::Fn(i) => &i.attrs,
        Item::ForeignMod(i) => &i.attrs,
        Item::Impl(i) => &i.attrs,
        Item::Macro(i) => &i.attrs,
        Item::Mod(i) => &i.attrs,
        Item::Static(i) => &i.attrs,
        Item::Struct(i) => &i.attrs,
        Item::Trait(i) => &i.attrs,
        Item::TraitAlias(i) => &i.attrs,
        Item::Type(i) => &i.attrs,
        Item::Union(i) => &i.attrs,
        Item::Use(i) => &i.attrs,
        _ => return None,
    })
}

fn item_attrs_mut(item: &mut Item) -> Option<&mut Vec<Attribute>> {
    Some(match item {
        Item::Const(i) => &mut i.attrs,
        Item::Enum(i) => &mut i.attrs,
        Item::ExternCrate(i) => &mut i.attrs,
        Item::Fn(i) => &mut i.attrs,
        Item::ForeignMod(i) => &mut i.attrs,
        Item::Impl(i) => &mut i.attrs,
        Item::Macro(i) => &mut i.attrs,
        Item::Mod(i) => &mut i.attrs,
        Item::Static(i) => &mut i.attrs,
        Item::Struct(i) => &mut i.attrs,
        Item::Trait(i) => &mut i.attrs,
        Item::TraitAlias(i) => &mut i.attrs,
        Item::Type(i) => &mut i.attrs,
        Item::Union(i) => &mut i.attrs,
        Item::Use(i) => &mut i.attrs,
        _ => return None,
    })
}
