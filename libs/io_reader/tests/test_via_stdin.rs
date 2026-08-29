use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn test_stdin_input() {
    // テスト対象のバイナリを起動
    let mut child = Command::new("cargo")
        .args(["run", "--example", "test_io_reader_input"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn binary");

    // stdin に入力を書き込む
    {
        let stdin = child.stdin.as_mut().expect("failed to get stdin");
        stdin.write_all(b"10\n20\n").expect("failed to write");
    }

    // 実行完了を待つ
    let output = child.wait_with_output().expect("failed to wait");

    // 結果を検証
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout, "a=10, b=20\n");
}

#[test]
fn test_stdin_multiple_input() {
    // テスト対象のバイナリを起動
    let mut child = Command::new("cargo")
        .args(["run", "--example", "test_io_reader_multiple_input"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn binary");

    // stdin に入力を書き込む
    {
        let stdin = child.stdin.as_mut().expect("failed to get stdin");
        stdin.write_all(b"10\n20\n").expect("failed to write");
    }

    // 実行完了を待つ
    let output = child.wait_with_output().expect("failed to wait");

    // 結果を検証
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(stdout, "a=10, b=20\n");
}
