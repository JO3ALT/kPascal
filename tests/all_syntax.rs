use std::process::{Command, Stdio};

fn run_compiler(src: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_kpascal"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn kpascal");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("stdin not available");
        stdin
            .write_all(src.as_bytes())
            .expect("failed to write source to stdin");
    }

    let out = child.wait_with_output().expect("failed to wait on child");
    assert!(
        out.status.success(),
        "compiler failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("stdout is not valid utf-8")
}

#[test]
fn compiles_all_syntax_fixture() {
    let src = include_str!("fixtures/all_syntax.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("IF"));
    assert!(forth.contains("THEN"));
    assert!(forth.contains("BEGIN"));
    assert!(forth.contains("WHILE"));
    assert!(forth.contains("REPEAT"));
    assert!(forth.contains("UNTIL"));
    assert!(forth.matches(": R_").count() >= 2);
    assert!(forth.contains("R@ -1 = IF"));

    assert!(forth.contains("PVAR!"));
    assert!(forth.contains("PVAR@"));
    assert!(forth.contains("PFIELD!"));
    assert!(forth.contains("PFIELD@"));
    assert!(forth.contains("PWRITE-I32"));
    assert!(forth.contains("PWRITE-CHAR"));
    assert!(forth.contains("PWRITE-BOOL"));
    assert!(forth.contains("PWRITELN"));
}

#[test]
fn compiles_read_all_types_fixture() {
    let src = include_str!("fixtures/read_all_types.pas");
    let forth = run_compiler(src);

    assert!(forth.contains("PREAD-I32"));
    assert!(forth.contains("PREAD-BOOL"));
    assert!(forth.contains("PREAD-CHAR"));
    assert!(forth.contains("PWRITE-I32"));
    assert!(forth.contains("PWRITE-BOOL"));
    assert!(forth.contains("PWRITE-CHAR"));
}
