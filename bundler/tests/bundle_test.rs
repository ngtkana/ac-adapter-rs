use std::fmt::Write as _;
use std::process::Command;

fn libbundle(args: &[&str]) -> String {
    let bin = env!("CARGO_BIN_EXE_libbundle");
    let output = Command::new(bin)
        .args(args)
        .output()
        .expect("failed to run libbundle");
    assert!(
        output.status.success(),
        "libbundle failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("libbundle output is not valid UTF-8")
}

fn rustc_compile_lib(source: &str) {
    let dir = tempdir();
    let src_path = dir.join("bundle.rs");
    std::fs::write(&src_path, source).unwrap();
    let out_path = dir.join("bundle.rlib");
    let output = Command::new("rustc")
        .args(["--edition", "2024", "--crate-type", "lib", "-o"])
        .arg(&out_path)
        .arg(&src_path)
        .output()
        .expect("failed to run rustc");
    assert!(
        output.status.success(),
        "rustc failed to compile bundle:\n{}\n---\n{}",
        String::from_utf8_lossy(&output.stderr),
        source
    );
}

fn rustc_compile_and_run_bin(source: &str) -> String {
    let dir = tempdir();
    let src_path = dir.join("bundle.rs");
    std::fs::write(&src_path, source).unwrap();
    let out_path = dir.join("bundle_bin");
    let output = Command::new("rustc")
        .args(["--edition", "2024", "-o"])
        .arg(&out_path)
        .arg(&src_path)
        .output()
        .expect("failed to run rustc");
    assert!(
        output.status.success(),
        "rustc failed to compile bundle:\n{}\n---\n{}",
        String::from_utf8_lossy(&output.stderr),
        source
    );
    let run = Command::new(&out_path)
        .output()
        .expect("failed to run compiled binary");
    assert!(run.status.success(), "binary exited with failure");
    String::from_utf8(run.stdout).unwrap()
}

fn tempdir() -> std::path::PathBuf {
    let mut dir = std::env::temp_dir();
    let unique = format!(
        "bundler-test-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    );
    dir.push(unique);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

#[test]
fn jagged_vec_is_callable_bare_after_bundling() {
    let mut source = libbundle(&["jagged_vec"]);
    writeln!(
        source,
        "\nfn main() {{ let v = jagged_vec![0, 3]; assert_eq!(v, vec![0, 0, 0]); println!(\"ok\"); }}"
    )
    .unwrap();
    let stdout = rustc_compile_and_run_bin(&source);
    assert_eq!(stdout.trim(), "ok");
}

#[test]
fn diamond_dependency_is_deduplicated() {
    let source = libbundle(&["fp_fps"]);
    assert_eq!(source.matches("mod fp {").count(), 1);
    assert!(source.contains("mod fp_fft {"));
    assert!(source.contains("mod fp_fps {"));
    rustc_compile_lib(&source);
}

#[test]
fn multi_file_crate_self_reference_is_rewritten() {
    let source = libbundle(&["bit_vec"]);
    assert!(source.contains("crate::bit_vec::"));
    rustc_compile_lib(&source);
}

#[test]
fn dollar_crate_in_macro_export_is_rewritten_correctly() {
    let source = libbundle(&["io_reader"]);
    // 非マクロ項目へのセルフ参照はセグメントが挿入される
    assert!(source.contains("$crate::io_reader::stdin_source"));
    // マクロ呼び出し（他の #[macro_export] マクロ）はセグメントを挿入しない
    assert!(source.contains("$crate::input!"));
    rustc_compile_lib(&source);
}

#[test]
fn multiple_crates_share_deduplicated_dependencies() {
    let source = libbundle(&["fp_fps", "dinic"]);
    assert_eq!(source.matches("mod fp {").count(), 1);
    for name in ["fp_fps", "fp_fft", "dinic"] {
        assert!(source.contains(&format!("mod {name} {{")));
    }
    rustc_compile_lib(&source);
}

#[test]
fn skip_from_excludes_already_bundled_crate() {
    let existing = libbundle(&["fp"]);
    let dir = tempdir();
    let existing_path = dir.join("existing.rs");
    std::fs::write(&existing_path, &existing).unwrap();

    let new_source = libbundle(&["fp_fps", "--skip-from", existing_path.to_str().unwrap()]);
    assert!(!new_source.contains("mod fp {"));
    assert!(new_source.contains("mod fp_fps {"));
    assert!(new_source.contains("mod fp_fft {"));
    // 除外されたクレートへの参照は書き換え済みのまま残るので、
    // 既存の展開結果と結合すれば単体でコンパイルできるはず
    let combined = format!("{existing}\n{new_source}");
    rustc_compile_lib(&combined);
}

#[test]
fn list_crates_includes_known_crate_names() {
    let output = libbundle(&["--list-crates"]);
    let names: Vec<&str> = output.lines().collect();
    assert!(names.contains(&"jagged_vec"));
    assert!(names.contains(&"fp"));
    assert_eq!(names, {
        let mut sorted = names.clone();
        sorted.sort_unstable();
        sorted
    });
}

#[test]
fn unknown_crate_name_is_reported() {
    let bin = env!("CARGO_BIN_EXE_libbundle");
    let output = Command::new(bin)
        .arg("this_crate_does_not_exist")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("this_crate_does_not_exist"));
}
