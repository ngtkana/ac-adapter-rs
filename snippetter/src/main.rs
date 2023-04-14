use itertools::Itertools;
use once_cell::sync::OnceCell;
use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

static PROJECT_ROOT: OnceCell<PathBuf> = OnceCell::new();
static CRATE_NAMES: OnceCell<Vec<String>> = OnceCell::new();

fn main() {
    PROJECT_ROOT
        .set(
            std::env::current_dir()
                .unwrap()
                .ancestors()
                .find(|&ancestor| {
                    ancestor.read_dir().unwrap().any(|entry| {
                        entry.unwrap().path().as_path().file_name()
                            == Some(OsStr::new("Cargo.lock"))
                    })
                })
                .unwrap()
                .to_path_buf(),
        )
        .unwrap();
    dbg!(PROJECT_ROOT.get());
    CRATE_NAMES
        .set(
            PROJECT_ROOT
                .get()
                .unwrap()
                .join(Path::new("crates"))
                .read_dir()
                .unwrap()
                .filter_map(Result::ok)
                .filter_map(|crate_entry| {
                    (crate_entry
                        .path()
                        .read_dir()
                        .unwrap()
                        .filter_map(Result::ok)
                        .find(|crate_entry| {
                            crate_entry.path().as_path().file_name()
                                == Some(OsStr::new("Cargo.toml"))
                        })
                        .is_some())
                    .then(|| {
                        crate_entry
                            .path()
                            .file_name()
                            .unwrap()
                            .to_string_lossy()
                            .into_owned()
                    })
                })
                .collect_vec(),
        )
        .unwrap();
    dbg!(CRATE_NAMES.get());
}
