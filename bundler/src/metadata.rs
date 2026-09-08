use anyhow::Context;
use anyhow::Result;
use anyhow::bail;
use std::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;

pub struct CrateInfo {
    pub lib_rs: PathBuf,
    pub deps: Vec<String>,
}

pub struct Workspace {
    pub crates: BTreeMap<String, CrateInfo>,
}

impl Workspace {
    pub fn resolve() -> Result<Self> {
        let root = find_root()?;
        let metadata = cargo_metadata::MetadataCommand::new()
            .manifest_path(root.join("Cargo.toml"))
            .no_deps()
            .exec()
            .context("failed to run `cargo metadata`")?;

        let libs_dir = root.join("libs");
        let mut crates = BTreeMap::new();
        for package in &metadata.packages {
            let manifest_dir = package
                .manifest_path
                .parent()
                .expect("manifest path always has a parent directory")
                .as_std_path();
            if manifest_dir.parent() != Some(libs_dir.as_path()) {
                continue;
            }
            let deps = package
                .dependencies
                .iter()
                .filter(|dep| {
                    dep.kind == cargo_metadata::DependencyKind::Normal && dep.path.is_some()
                })
                .map(|dep| dep.name.clone())
                .collect();
            crates.insert(
                package.name.clone(),
                CrateInfo {
                    lib_rs: manifest_dir.join("src").join("lib.rs"),
                    deps,
                },
            );
        }
        Ok(Self { crates })
    }
}

fn find_root() -> Result<PathBuf> {
    if let Ok(dir) = std::env::var("AC_ADAPTER_RS_ROOT") {
        let path = PathBuf::from(dir);
        if is_workspace_root(&path) {
            return Ok(path);
        }
        bail!(
            "AC_ADAPTER_RS_ROOT ({}) は ac-adapter-rs リポジトリのルートに見えません。",
            path.display()
        );
    }
    if let Ok(cwd) = std::env::current_dir() {
        for ancestor in cwd.ancestors() {
            if is_workspace_root(ancestor) {
                return Ok(ancestor.to_path_buf());
            }
        }
    }
    bail!(
        "ac-adapter-rs リポジトリが見つかりません。\n\n\
         以下を ~/.zshrc または ~/.bashrc に追記してください:\n\n\
         \x20\x20\x20\x20export AC_ADAPTER_RS_ROOT=\"/path/to/ac-adapter-rs\"  # このリポジトリのルート\n\n\
         追記後、シェルを再起動するか `source ~/.zshrc` を実行してください。"
    );
}

fn is_workspace_root(path: &Path) -> bool {
    path.join("Cargo.toml").is_file() && path.join("libs").is_dir()
}
