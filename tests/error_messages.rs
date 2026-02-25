use std::process::{Command, Stdio};

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
fn parse_error_shows_source_line_and_caret() {
    let stderr = run_fail(
        r#"
program p;
begin
  WriteLn(1
end.
"#,
    );
    assert!(stderr.contains("parse error at line"));
    assert!(stderr.contains("end."));
    assert!(stderr.contains("^"));
}

#[test]
fn semantic_error_shows_source_line_and_caret() {
    let stderr = run_fail(
        r#"
program p;
begin
  WriteLn(unknown_name)
end.
"#,
    );
    assert!(stderr.contains("unknown identifier: unknown_name"));
    assert!(stderr.contains("WriteLn(unknown_name)"));
    assert!(stderr.contains("^"));
}

#[test]
fn builtin_type_error_shows_expected_and_actual() {
    let stderr = run_fail(
        r#"
program p;
begin
  WriteLn(Float(TRUE))
end.
"#,
    );
    assert!(stderr.contains("Float argument #1"));
    assert!(stderr.contains("expected integer"));
    assert!(stderr.contains("got boolean"));
    assert!(stderr.contains("Float(TRUE)"));
    assert!(stderr.contains("^"));
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
fn record_copy_update_rejects_duplicate_field() {
    let stderr = run_fail(
        r#"
program p;
type
  pair = record
    x: integer;
    y: integer;
  end;
var
  p1: pair;
  p2: pair;
begin
  p1 := pair(x := 1; y := 2);
  p2 := p1 with (x := 10; x := 20)
end.
"#,
    );
    assert!(stderr.contains("duplicate record update field"));
}

#[test]
fn new_rejects_non_pointer() {
    let stderr = run_fail(
        r#"
program p;
var
  x: integer;
begin
  New(x)
end.
"#,
    );
    assert!(stderr.contains("New argument must be pointer"));
}

#[test]
fn map_rejects_wrong_callback_signature() {
    let stderr = run_fail(
        r#"
program p;
type
  plist = ^list_node;
  list_node = record
    next: plist;
    value: integer;
  end;
var
  xs: plist;
  ys: plist;

function bad(v: integer): boolean;
begin
  bad := TRUE
end;

begin
  xs := nil;
  ys := Map(xs, bad)
end.
"#,
    );
    assert!(stderr.contains("Map callback must have signature procedure(var src: T; var dst: T)"));
}

#[test]
fn cast_rejects_size_mismatch() {
    let stderr = run_fail(
        r#"
program p;
type
  pnode = ^node;
  node = record
    next: pnode;
    value: integer;
  end;
var
  p1: pnode;
begin
  p1 := cast(pnode, cast(array[2] of integer, p1))
end.
"#,
    );
    assert!(stderr.contains("cast size mismatch"));
}

#[test]
fn cast_rejects_non_pointer_integer_casts() {
    let stderr = run_fail(
        r#"
program p;
var
  x: integer;
begin
  x := cast(integer, TRUE)
end.
"#,
    );
    assert!(stderr.contains("unsafe cast is only supported for pointer/integer"));
}
