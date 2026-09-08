use cargo_metadata::DependencyKind;
use cargo_metadata::MetadataCommand;
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, serde::Serialize)]
struct CrateMetadata {
    dependencies: Vec<String>,
    tags: Vec<String>,
    description: Option<String>,
    /// crate root doc comment の要約行より後（本文）を HTML にレンダリングしたもの。
    full: Option<String>,
}

fn main() {
    let metadata = MetadataCommand::new().no_deps().exec().unwrap();
    let project_root = metadata.workspace_root.clone();

    let crate_metadatas: HashMap<String, CrateMetadata> = metadata
        .packages
        .iter()
        .filter(|package| package.manifest_path.starts_with(project_root.join("libs")))
        .map(|package| {
            let dependencies = package
                .dependencies
                .iter()
                .filter(|dep| dep.kind == DependencyKind::Normal && dep.path.is_some())
                .map(|dep| dep.name.clone())
                .collect();
            let tags = package.keywords.clone();
            let lib_rs_path: PathBuf = package
                .manifest_path
                .parent()
                .unwrap()
                .join("src")
                .join("lib.rs")
                .into();
            let (description, full) = fs::read_to_string(&lib_rs_path)
                .map(|content| parse_crate_docs(&content))
                .unwrap_or((None, None));

            (package.name.clone(), CrateMetadata {
                dependencies,
                tags,
                description,
                full,
            })
        })
        .collect();

    let json = serde_json::to_string(&crate_metadatas).unwrap();
    let docs_dir = PathBuf::from(&project_root).join("docs");
    fs::create_dir_all(&docs_dir).unwrap();
    fs::write(docs_dir.join("dependencies.js"), format!("dependencies = {json}")).unwrap();
}

/// crate ルートの `//!` doc comment を、要約行（1行目）と本文（2行目以降を HTML レンダリングしたもの）に分ける。
fn parse_crate_docs(lib_rs_content: &str) -> (Option<String>, Option<String>) {
    let lines: Vec<&str> = lib_rs_content
        .lines()
        .take_while(|line| line.starts_with("//!"))
        .map(|line| {
            let rest = &line["//!".len()..];
            rest.strip_prefix(' ').unwrap_or(rest)
        })
        .collect();

    let mut idx = 0;
    while idx < lines.len() && lines[idx].trim().is_empty() {
        idx += 1;
    }
    if idx >= lines.len() {
        return (None, None);
    }
    let description = lines[idx].trim().to_owned();
    idx += 1;
    while idx < lines.len() && lines[idx].trim().is_empty() {
        idx += 1;
    }
    if idx >= lines.len() {
        return (Some(description), None);
    }

    let markdown = lines[idx..].join("\n");
    let mut html = String::new();
    pulldown_cmark::html::push_html(&mut html, pulldown_cmark::Parser::new(&markdown));
    (Some(description), Some(html))
}
