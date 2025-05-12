use itertools::Itertools;
use once_cell::sync::OnceCell;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::path::PathBuf;

static PROJECT_ROOT: OnceCell<PathBuf> = OnceCell::new();
static CRATE_METADATAS: OnceCell<HashMap<String, CrateMetadata>> = OnceCell::new();

#[derive(Clone, Debug, PartialEq, serde::Serialize)]
struct CrateMetadata {
    dependencies: Vec<String>,
    tags: Vec<String>,
    description: Option<String>,
}

#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
struct MetadataFile {
    tags: Option<TagsSection>,
    description: Option<DescriptionSection>,
}

#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
struct TagsSection {
    list: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, serde::Deserialize)]
struct DescriptionSection {
    short: String,
}

// TODO: use crates.js etc. in target/doc/{crates.js,source-files.js} to bundle files
// TODO: or use `.packages | map({ "name": .name, "dependencies": .dependencies })` of `cargo
// metadata
fn main() {
    PROJECT_ROOT.set(find_project_root_path()).unwrap();
    CRATE_METADATAS
        .set(
            PROJECT_ROOT
                .get()
                .unwrap()
                .join(Path::new("libs"))
                .read_dir()
                .unwrap()
                .filter_map(Result::ok)
                .filter_map(|crate_entry| {
                    let crate_path = crate_entry.path();
                    let cargo_toml_path = crate_path.join("Cargo.toml");
                    let metadata_path = crate_path.join("metadata.toml");

                    if cargo_toml_path.exists() {
                        let crate_name = crate_path
                            .file_name()
                            .unwrap()
                            .to_string_lossy()
                            .into_owned();
                        let dependencies = parse_local_dependencies_from_cargo_toml(
                            &fs::read_to_string(&cargo_toml_path).unwrap(),
                        );

                        // メタデータファイルからタグと説明を読み取る
                        let (tags, description) = if metadata_path.exists() {
                            let metadata_content =
                                fs::read_to_string(&metadata_path).unwrap_or_default();
                            let metadata: MetadataFile = toml::from_str(&metadata_content)
                                .unwrap_or(MetadataFile {
                                    tags: None,
                                    description: None,
                                });

                            let tags = metadata.tags.map_or(Vec::new(), |t| t.list);
                            let description = metadata.description.map(|d| d.short);

                            (tags, description)
                        } else {
                            (Vec::new(), None)
                        };

                        Some((
                            crate_name,
                            CrateMetadata {
                                dependencies,
                                tags,
                                description,
                            },
                        ))
                    } else {
                        None
                    }
                })
                .collect(),
        )
        .unwrap();

    let json = serde_json::to_string(CRATE_METADATAS.get().unwrap()).unwrap();
    fs::create_dir_all(PROJECT_ROOT.get().unwrap().join("docs")).unwrap();
    fs::write(
        PROJECT_ROOT
            .get()
            .unwrap()
            .join("docs")
            .join("dependencies.js"),
        format!("dependencies = {json}"),
    )
    .unwrap();
}

fn find_project_root_path() -> PathBuf {
    std::env::current_dir()
        .unwrap()
        .ancestors()
        .find(|&ancestor| {
            ancestor.read_dir().unwrap().any(|entry| {
                entry.unwrap().path().as_path().file_name() == Some(OsStr::new("Cargo.lock"))
            })
        })
        .unwrap()
        .to_path_buf()
}

fn parse_local_dependencies_from_cargo_toml(file_content: &str) -> Vec<String> {
    match toml::from_str::<toml::Value>(file_content).unwrap() {
        toml::Value::Table(table) => match table.get("dependencies") {
            None => Vec::new(),
            Some(toml::Value::Table(table)) => table
                .iter()
                .filter_map(|(key, value)| -> Option<String> {
                    (match value {
                        toml::Value::Table(table) => table.get("path").map(|value| match value {
                            toml::Value::String(path) => path,
                            _ => unreachable!(),
                        }),
                        toml::Value::String(path) => Some(path),
                        _ => unreachable!(),
                    })
                    .and_then(|path| path.starts_with("../").then(|| key.clone()))
                })
                .collect_vec(),
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}
