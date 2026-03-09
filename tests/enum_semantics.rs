use std::process::{Command, Stdio};

fn run_ok(src: &str) -> String {
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
            .expect("failed to write source");
    }
    let out = child.wait_with_output().expect("failed to wait");
    assert!(
        out.status.success(),
        "compiler failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn run_fail(src: &str) -> String {
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
            .expect("failed to write source");
    }
    let out = child.wait_with_output().expect("failed to wait");
    assert!(!out.status.success(), "compiler unexpectedly succeeded");
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn enum_is_nominally_distinct_from_integer() {
    let stderr = run_fail(
        r#"
program p;
type color = (red, green);
var c: color;
begin
  c := 1
end.
"#,
    );
    assert!(stderr.contains("type mismatch in assignment"));
}

#[test]
fn different_enums_are_not_assignable() {
    let stderr = run_fail(
        r#"
program p;
type
  color = (red, green);
  shape = (circle, square);
var
  c: color;
  s: shape;
begin
  c := red;
  s := circle;
  c := s
end.
"#,
    );
    assert!(stderr.contains("type mismatch in assignment"));
}

#[test]
fn enum_case_requires_exhaustive_or_else() {
    let stderr = run_fail(
        r#"
program p;
type
  color = (red, green, blue);
var
  c: color;
begin
  c := red;
  case c of
    red: WriteLn(1);
    green: WriteLn(2)
  end
end.
"#,
    );
    assert!(stderr.contains("enum case must be exhaustive or include else"));
}

#[test]
fn enum_case_accepts_exhaustive_arms_without_else() {
    let forth = run_ok(
        r#"
program p;
type
  color = (red, green, blue);
var
  c: color;
begin
  c := red;
  case c of
    red: WriteLn(1);
    green: WriteLn(2);
    blue: WriteLn(3)
  end
end.
"#,
    );
    assert!(forth.contains("__CASE_MATCH"));
}
