use itertools::Itertools;
use once_cell::sync::OnceCell;
use std::{
    collections::HashMap,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
};

static PROJECT_ROOT: OnceCell<PathBuf> = OnceCell::new();
static CRATE_METADATAS: OnceCell<HashMap<String, CrateMetadata>> = OnceCell::new();

#[derive(Clone, Debug, PartialEq, serde::Serialize)]
struct CrateMetadata {
    dependencies: Vec<String>,
    tags: Vec<String>,
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
                .join(Path::new("crates"))
                .read_dir()
                .unwrap()
                .filter_map(Result::ok)
                .filter_map(|crate_entry| {
                    crate_entry
                        .path()
                        .read_dir()
                        .unwrap()
                        .filter_map(Result::ok)
                        .find(|crate_entry| {
                            crate_entry.path().as_path().file_name()
                                == Some(OsStr::new("Cargo.toml"))
                        })
                        .map(|cargo_toml_entry| {
                            (
                                crate_entry
                                    .path()
                                    .file_name()
                                    .unwrap()
                                    .to_string_lossy()
                                    .into_owned(),
                                CrateMetadata {
                                    dependencies: parse_local_dependencies_from_cargo_toml(
                                        &fs::read_to_string(cargo_toml_entry.path()).unwrap(),
                                    ),
                                    tags: Vec::new(),
                                },
                            )
                        })
                })
                .collect(),
        )
        .unwrap();

    let json = serde_json::to_string(CRATE_METADATAS.get().unwrap()).unwrap();
    fs::create_dir_all(PROJECT_ROOT.get().unwrap().join("target").join("doc")).unwrap();
    fs::write(
        PROJECT_ROOT
            .get()
            .unwrap()
            .join("target")
            .join("doc")
            .join("dependencies.js"),
        format!("dependencies = {}", json),
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
