mod bundle;
mod inline;
mod metadata;
mod rewrite;
mod strip;

use anyhow::Result;
use anyhow::bail;
use metadata::Workspace;

fn main() -> Result<()> {
    let mut crate_names = Vec::new();
    let mut strip_docs = true;
    let mut strip_tests = true;
    let mut list_crates = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--keep-docs" => strip_docs = false,
            "--keep-tests" => strip_tests = false,
            // シェル補完スクリプト（completions/）から利用する内部フラグ
            "--list-crates" => list_crates = true,
            _ if arg.starts_with('-') => bail!("unknown option: {arg}"),
            _ => crate_names.push(arg),
        }
    }

    if list_crates {
        let ws = Workspace::resolve()?;
        for name in ws.crates.keys() {
            println!("{name}");
        }
        return Ok(());
    }

    if crate_names.is_empty() {
        bail!("usage: libbundle <CRATE_NAME>... [--keep-docs] [--keep-tests]");
    }

    let ws = Workspace::resolve()?;
    let output = bundle::bundle(
        &ws,
        &crate_names,
        &bundle::Options {
            strip_tests,
            strip_docs,
        },
    )?;
    print!("{output}");
    Ok(())
}
