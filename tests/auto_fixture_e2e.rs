use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn kforth_binary_path() -> Option<&'static str> {
    if fs::metadata("../kforth/build/kforth").is_ok() {
        Some("../kforth/build/kforth")
    } else if fs::metadata("../kforth/kforth").is_ok() {
        Some("../kforth/kforth")
    } else {
        None
    }
}

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

    let out = child
        .wait_with_output()
        .expect("failed to wait for kpascal");
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
    let bin = kforth_binary_path().expect("missing kforth binary");

    let mut child = Command::new(bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn kforth");
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

fn fixture_cases() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for entry in fs::read_dir("tests/fixtures").expect("read_dir tests/fixtures failed") {
        let entry = entry.expect("fixture dir entry failed");
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("out") {
            continue;
        }
        if path
            .file_name()
            .and_then(|s| s.to_str())
            .is_some_and(|name| {
                name.starts_with("list_")
                    || name.starts_with("use_math")
                    || name == "use_string_utils.out"
            })
        {
            continue;
        }
        out.push(path);
    }
    out.sort();
    out
}

fn stemmed_path(path: &Path, ext: &str) -> PathBuf {
    path.with_extension(ext)
}

#[test]
fn auto_fixtures_with_in_out_run_on_kforth() {
    if fs::metadata("../kforth/bootstrap.fth").is_err() || kforth_binary_path().is_none() {
        eprintln!("skipping auto fixture e2e: missing kforth/bootstrap");
        return;
    }

    let cases = fixture_cases();
    assert!(
        !cases.is_empty(),
        "no *.out fixtures found in tests/fixtures"
    );

    for out_path in cases {
        let pas_path = stemmed_path(&out_path, "pas");
        let in_path = stemmed_path(&out_path, "in");
        let label = pas_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("<unknown>");

        let src = fs::read_to_string(&pas_path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", pas_path.display()));
        let runtime_input = fs::read_to_string(&in_path).unwrap_or_default();
        let expected = fs::read_to_string(&out_path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", out_path.display()));

        let forth = compile_pascal(&src);
        let raw = run_kforth_with_bootstrap(&forth, &runtime_input);
        let got = normalize_kforth_output(&raw).join("\n");
        let expected_norm = expected
            .lines()
            .map(|s| s.trim_end())
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>()
            .join("\n");

        assert_eq!(got, expected_norm, "auto fixture failed: {label}");
    }
}
