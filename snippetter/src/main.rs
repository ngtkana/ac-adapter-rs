use once_cell::sync::OnceCell;
use std::{ffi::OsStr, path::PathBuf};

static PROJECT_ROOT: OnceCell<PathBuf> = OnceCell::new();

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
    dbg!(&PROJECT_ROOT);
}
