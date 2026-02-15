use std::fs;
use std::process::{Command, Stdio};

fn compile_pascal(src: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_kpascal"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn kpascal");

    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .expect("stdin not available")
            .write_all(src.as_bytes())
            .expect("failed to feed Pascal source");
    }

    let out = child.wait_with_output().expect("failed to wait for kpascal");
    assert!(
        out.status.success(),
        "kpascal failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("kpascal stdout is not UTF-8")
}

fn run_kforth_with_bootstrap(forth_src: &str, runtime_input: &str) -> String {
    let bootstrap = fs::read_to_string("../kforth/bootstrap.fth")
        .expect("failed to read ../kforth/bootstrap.fth");
    let payload = format!("{bootstrap}\n{forth_src}\n{runtime_input}\nBYE\n");

    let mut child = Command::new("../kforth/build/kforth")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ../kforth/build/kforth");

    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .expect("stdin not available")
            .write_all(payload.as_bytes())
            .expect("failed to feed kforth input");
    }

    let out = child.wait_with_output().expect("failed to wait for kforth");
    assert!(
        out.status.success(),
        "kforth failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn normalize_kforth_output(raw: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for original in raw.lines() {
        let mut s = original.trim().to_string();
        while s == "ok" || s.starts_with("ok ") {
            if s == "ok" {
                s.clear();
                break;
            }
            s = s[3..].trim().to_string();
        }
        if !s.is_empty() {
            lines.push(s);
        }
    }
    lines
}

#[test]
fn e2e_all_syntax_runs_on_kforth() {
    let src = include_str!("fixtures/all_syntax.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out).join("\n");
    assert!(got.contains("N"));
    assert!(got.contains("A"));
    assert!(got.contains("-19"));
    assert!(got.contains("20"));
    assert!(got.contains("TRUE"));
    assert!(got.contains("Z"));
}

#[test]
fn e2e_read_all_types_runs_on_kforth() {
    let src = include_str!("fixtures/read_all_types.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "12 1 X 34 0 Y");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "12".to_string(),
        "TRUE".to_string(),
        "X".to_string(),
        "34".to_string(),
        "FALSE".to_string(),
        "Y".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_read_write_array_runs_on_kforth() {
    let src = include_str!("fixtures/read_write_arr.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "7 8 9");
    let got = normalize_kforth_output(&out);
    let expected = vec!["7".to_string(), "8".to_string(), "9".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_aggregate_and_3d_runs_on_kforth() {
    let src = include_str!("fixtures/aggregate_and_3d.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["10".to_string(), "20".to_string(), "77".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_string_assignment_to_char_array_runs_on_kforth() {
    let src = include_str!("fixtures/string_assign_char_array.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "ABC".to_string(),
        "TRUE".to_string(),
        "XYZLO".to_string(),
        "TRUE".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_readstr_writestr_runs_on_kforth() {
    let src = include_str!("fixtures/read_write_str.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "H e l l o");
    let got = normalize_kforth_output(&out);
    let expected = vec!["Hello".to_string(), "XYZ".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_builtins_and_hex_runs_on_kforth() {
    let src = include_str!("fixtures/builtins_and_hex.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "255\n42");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "81".to_string(),
        "B".to_string(),
        "5".to_string(),
        "0".to_string(),
        "4".to_string(),
        "000000FF".to_string(),
        "42".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_include_directive_runs_on_kforth() {
    let src = include_str!("fixtures/include_program.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["42".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_all_features_runs_on_kforth() {
    let src = include_str!("fixtures/all_features.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "255\n1 X\n7 8 9\nH e l l o");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "BEGIN".to_string(),
        "42".to_string(),
        "65".to_string(),
        "B".to_string(),
        "5".to_string(),
        "TRUE".to_string(),
        "Z".to_string(),
        "10".to_string(),
        "1".to_string(),
        "2".to_string(),
        "3".to_string(),
        "4".to_string(),
        "77".to_string(),
        "4".to_string(),
        "0".to_string(),
        "3".to_string(),
        "ABC".to_string(),
        "TRUE".to_string(),
        "***".to_string(),
        "###".to_string(),
        "4".to_string(),
        "FOUR".to_string(),
        "14".to_string(),
        "9".to_string(),
        "20000".to_string(),
        "20000".to_string(),
        "10000".to_string(),
        "7".to_string(),
        "83".to_string(),
        "45".to_string(),
        "6928".to_string(),
        "9998".to_string(),
        "000000FF".to_string(),
        "TRUE".to_string(),
        "X".to_string(),
        "7".to_string(),
        "8".to_string(),
        "9".to_string(),
        "Hello".to_string(),
        "END".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}
