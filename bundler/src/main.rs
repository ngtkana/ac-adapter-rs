mod bundle;
mod inline;
mod metadata;
mod rewrite;
mod strip;

use anyhow::Context;
use anyhow::Result;
use anyhow::bail;
use metadata::Workspace;
use std::collections::BTreeSet;

fn main() -> Result<()> {
    let mut crate_names = Vec::new();
    let mut strip_docs = true;
    let mut strip_tests = true;
    let mut list_crates = false;
    let mut skip_from = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--keep-docs" => strip_docs = false,
            "--keep-tests" => strip_tests = false,
            // シェル補完スクリプト（completions/）から利用する内部フラグ
            "--list-crates" => list_crates = true,
            "--skip-from" => {
                skip_from = Some(args.next().context("--skip-from requires a file path")?);
            }
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
        bail!("usage: libbundle <CRATE_NAME>... [--keep-docs] [--keep-tests] [--skip-from <file>]");
    }

    let exclude = match &skip_from {
        Some(path) => already_bundled_crate_names(path)?,
        None => BTreeSet::new(),
    };

    let ws = Workspace::resolve()?;
    let output = bundle::bundle(
        &ws,
        &crate_names,
        &exclude,
        &bundle::Options {
            strip_tests,
            strip_docs,
        },
    )?;
    if output.trim().is_empty() {
        eprintln!(
            "指定されたクレートはすべて --skip-from のファイルに既にバンドル済みのため、出力はありません。"
        );
    }
    print!("{output}");
    Ok(())
}

/// `--skip-from` で指定されたファイルから、既にバンドル済みのクレート名を
/// fold マーカー（`// <name> {{{`）を手がかりに収集する。
fn already_bundled_crate_names(path: &str) -> Result<BTreeSet<String>> {
    let content =
        std::fs::read_to_string(path).with_context(|| format!("failed to read {path}"))?;
    Ok(content
        .lines()
        .filter_map(|line| line.strip_prefix("// ")?.strip_suffix(" {{{"))
        .map(str::to_owned)
        .collect())
}
