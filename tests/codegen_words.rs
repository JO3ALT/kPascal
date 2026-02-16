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

fn run_compiler_fail(src: &str) -> String {
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
    assert!(!out.status.success(), "compiler should fail but succeeded");
    String::from_utf8(out.stderr).expect("stderr is not valid utf-8")
}

#[test]
fn generates_wrappers_for_var_store_and_int_write() {
    let src = r#"
program p;
var
  x: integer;
begin
  x := 7;
  WriteLn(x)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("7 x PVAR!"));
    assert!(forth.contains("x PVAR@ PWRITE-I32"));
    assert!(forth.contains("PWRITELN"));
    assert!(!forth.contains(" x @"));
    assert!(!forth.contains(" x !"));
}

#[test]
fn generates_wrappers_for_record_field_access() {
    let src = r#"
program p;
type
  point = record
    x: integer;
    y: integer;
  end;
var
  p: point;
begin
  p.y := 20;
  WriteLn(p.y)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("20 p 4 PFIELD!"));
    assert!(forth.contains("p 4 PFIELD@ PWRITE-I32"));
}

#[test]
fn generates_wrappers_for_bool_and_char_write() {
    let src = r#"
program p;
begin
  WriteLn(1 < 2);
  WriteLn('A')
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("1 2 < PWRITE-BOOL"));
    assert!(forth.contains("65 PWRITE-CHAR"));
}

#[test]
fn supports_true_false_literals_in_expr() {
    let src = r#"
program p;
var
  b: boolean;
begin
  b := true;
  WriteLn(b);
  WriteLn(false)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("1 b PVAR!"));
    assert!(forth.contains("0 PWRITE-BOOL"));
}

#[test]
fn generates_typed_read_wrappers_for_vars() {
    let src = r#"
program p;
var
  i: integer;
  b: boolean;
  c: char;
begin
  Read(i, b, c)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("PREAD-I32 i PVAR!"));
    assert!(forth.contains("PREAD-BOOL b PVAR!"));
    assert!(forth.contains("PREAD-CHAR c PVAR!"));
}

#[test]
fn generates_typed_read_wrappers_for_record_fields() {
    let src = r#"
program p;
type
  rec = record
    i: integer;
    b: boolean;
    c: char;
  end;
var
  r: rec;
begin
  Read(r.i, r.b, r.c)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("PREAD-I32 r PVAR!"));
    assert!(forth.contains("PREAD-BOOL r 4 PFIELD!"));
    assert!(forth.contains("PREAD-CHAR r 8 PFIELD!"));
}

#[test]
fn writes_const_char_and_bool_with_typed_words() {
    let src = r#"
program p;
const
  c4 = 'Z';
  c5 = 1 < 2;
begin
  WriteLn(c4);
  WriteLn(c5)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("90 PWRITE-CHAR"));
    assert!(forth.contains("1 PWRITE-BOOL"));
}

#[test]
fn generates_complete_arithmetic_stack_sequence() {
    let src = r#"
program p;
var
  i: integer;
begin
  i := 2 * 2 + 3;
  WriteLn(i)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("2 2 * 3 + i PVAR!"));
    assert!(!forth.contains("2 2 * + i PVAR!"));
}

#[test]
fn supports_div_and_mod_operators() {
    let src = r#"
program p;
var
  i: integer;
begin
  i := 7 div 3 mod 2;
  WriteLn(i)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("7 3 / 2 MOD i PVAR!"));
}

#[test]
fn generates_simple_assignment_without_stack_underflow_pattern() {
    let src = r#"
program p;
var
  i: integer;
begin
  i := 4;
  WriteLn(i)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("4 i PVAR!"));
}

#[test]
fn supports_for_and_multi_write_with_string() {
    let src = r#"
program p;
var
  i: integer;
begin
  for i := 1 to 3 do
    Write('*');
  for i := 3 downto 1 do
    Write('*');
  WriteLn(' ', 'ABC', i)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("BEGIN"));
    assert!(forth.contains("WHILE"));
    assert!(forth.contains("REPEAT"));
    assert!(forth.contains("i PVAR@ 1 + i PVAR!"));
    assert!(forth.contains("i PVAR@ 1 - i PVAR!"));
    assert!(forth.contains("65 PWRITE-CHAR"));
    assert!(forth.contains("66 PWRITE-CHAR"));
    assert!(forth.contains("67 PWRITE-CHAR"));
}

#[test]
fn supports_case_procedure_function_and_by_ref() {
    let src = r#"
program p;
var
  x: integer;

procedure IncRef(var a: integer);
begin
  a := a + 1
end;

function Twice(v: integer): integer;
begin
  Twice := v * 2
end;

begin
  x := 2;
  IncRef(x);
  case x of
    3: WriteLn('OK');
    4: WriteLn('NG')
  else
    WriteLn('EL')
  end;
  WriteLn(Twice(x))
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.matches(": R_").count() >= 2);
    assert!(forth.contains(" x R_"));
    assert!(forth.contains("R@ 3 = IF"));
    assert!(forth.contains("R_"));
    assert!(forth.contains("PWRITE-I32"));
}

#[test]
fn supports_nested_routines_and_local_decl_blocks() {
    let src = r#"
program p;
var
  x: integer;

procedure Outer(var a: integer);
const
  k = 2;
type
  localint = integer;
var
  y: localint;

  procedure Inner(var z: integer);
  begin
    z := z + k
  end;
begin
  y := a;
  Inner(y);
  a := y
end;

begin
  x := 1;
  Outer(x);
  WriteLn(x)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.matches(": R_").count() >= 2);
    assert!(forth.contains("2"));
    assert!(forth.contains("R_"));
}

#[test]
fn rejects_non_boolean_if_condition() {
    let src = r#"
program p;
var
  i: integer;
begin
  i := 1;
  if i then
    WriteLn(i)
end.
"#;

    let err = run_compiler_fail(src);
    assert!(err.contains("if condition"));
}

#[test]
fn rejects_duplicate_case_labels() {
    let src = r#"
program p;
var
  x: integer;
begin
  x := 1;
  case x of
    1: WriteLn('A');
    1: WriteLn('B')
  end
end.
"#;

    let err = run_compiler_fail(src);
    assert!(err.contains("duplicate case label"));
}

#[test]
fn supports_array_type_and_index_access() {
    let src = r#"
program p;
type
  arr = array[4] of integer;
var
  a: arr;
  i: integer;
begin
  i := 2;
  a[i] := 7;
  WriteLn(a[i])
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("2 i PVAR!"));
    assert!(forth.contains("7 a i PVAR@ 4 * + PVAR!"));
    assert!(forth.contains("a i PVAR@ 4 * + PVAR@ PWRITE-I32"));
}

#[test]
fn rejects_non_integer_array_index() {
    let src = r#"
program p;
type
  arr = array[2] of integer;
var
  a: arr;
  b: boolean;
begin
  b := 1 < 2;
  a[b] := 1
end.
"#;
    let err = run_compiler_fail(src);
    assert!(err.contains("array index"));
}

#[test]
fn emits_safe_string_output_for_quotes() {
    let src = r#"
program p;
begin
  WriteLn('A"Z')
end.
"#;
    let forth = run_compiler(src);
    assert!(!forth.contains("S\" A\"Z\" PWRITE-STR"));
    assert!(forth.contains("65 PWRITE-CHAR"));
    assert!(forth.contains("34 PWRITE-CHAR"));
    assert!(forth.contains("90 PWRITE-CHAR"));
}

#[test]
fn includes_line_and_column_for_semantic_errors() {
    let src = r#"
program p;
begin
  WriteLn(x)
end.
"#;
    let err = run_compiler_fail(src);
    assert!(err.contains("line"));
    assert!(err.contains("column"));
}

#[test]
fn supports_readarr_writearr_for_integer_array() {
    let src = r#"
program p;
type
  arr = array[4] of integer;
var
  a: arr;
begin
  ReadArr(a, 3);
  WriteArr(a, 3)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("0 >R"));
    assert!(forth.contains("R@ 3 < WHILE"));
    assert!(forth.contains("PREAD-I32"));
    assert!(forth.contains("PWRITE-I32"));
}

#[test]
fn rejects_readarr_non_array_argument() {
    let src = r#"
program p;
var
  x: integer;
begin
  ReadArr(x, 1)
end.
"#;
    let err = run_compiler_fail(src);
    assert!(err.contains("ReadArr first argument must be array"));
}

#[test]
fn supports_record_and_array_aggregate_assignment() {
    let src = r#"
program p;
type
  rec = record
    x: integer;
    y: integer;
  end;
  arr = array[3] of integer;
var
  a: rec;
  b: rec;
  u: arr;
  v: arr;
begin
  a.x := 10; a.y := 20;
  b := a;
  u[0] := 1; u[1] := 2; u[2] := 3;
  v := u;
  WriteLn(b.x);
  WriteLn(b.y);
  WriteLn(v[0]);
  WriteLn(v[1]);
  WriteLn(v[2])
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("a PVAR@ b PVAR!"));
    assert!(forth.contains("a 4 PFIELD@ b 4 PFIELD!"));
    assert!(forth.contains("u PVAR@ v PVAR!"));
    assert!(forth.contains("u 4 PFIELD@ v 4 PFIELD!"));
    assert!(forth.contains("u 8 PFIELD@ v 8 PFIELD!"));
}

#[test]
fn supports_three_dimensional_array_indexing() {
    let src = r#"
program p;
type
  cube = array[2,3,4] of integer;
var
  c: cube;
begin
  c[1,2,3] := 99;
  WriteLn(c[1,2,3])
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("99"));
    assert!(forth.contains("* +"));
    assert!(forth.contains("PWRITE-I32"));
}

#[test]
fn supports_string_literal_assignment_to_char_array() {
    let src = r#"
program p;
type
  s6 = array[6] of char;
var
  s: s6;
begin
  s := 'ABC';
  WriteLn(s[0], s[1], s[2]);
  WriteLn(s[3] = #0);
  s := 'XYZLONG';
  WriteLn(s[0], s[1], s[2], s[3], s[4]);
  WriteLn(s[5] = #0)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("65 s PVAR!"));
    assert!(forth.contains("66 s 4 PFIELD!"));
    assert!(forth.contains("67 s 8 PFIELD!"));
    assert!(forth.contains("0 s 20 PFIELD!"));
}

#[test]
fn supports_readstr_writestr_for_char_array() {
    let src = r#"
program p;
type
  s8 = array[8] of char;
var
  s: s8;
begin
  ReadStr(s, 5);
  WriteStr(s);
  WriteLn
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("PREAD-CHAR"));
    assert!(forth.contains("__WSTR_STOP"));
    assert!(forth.contains("PWRITE-CHAR"));
}

#[test]
fn reports_detailed_argument_type_mismatch() {
    let src = r#"
program p;
procedure F(var a: integer);
begin
end;
begin
  F(1 < 2)
end.
"#;
    let err = run_compiler_fail(src);
    assert!(err.contains("argument #1"));
    assert!(err.contains("var parameter"));
    assert!(err.contains("line"));
    assert!(err.contains("column"));
}

#[test]
fn supports_ord_chr_length_high_low_and_hex_literal() {
    let src = r#"
program p;
type
  a5 = array[5] of char;
var
  s: a5;
  i: integer;
begin
  s := 'AB';
  i := Ord('A') + $10;
  WriteLn(i);
  WriteLn(Chr(66));
  WriteLn(Length(s));
  WriteLn(Low(s));
  WriteLn(High(s))
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("65 16 + i PVAR!"));
    assert!(forth.contains("66 PWRITE-CHAR"));
    assert!(forth.contains("5 PWRITE-I32"));
    assert!(forth.contains("0 PWRITE-I32"));
    assert!(forth.contains("4 PWRITE-I32"));
}

#[test]
fn supports_writehex_and_readln_builtins() {
    let src = r#"
program p;
var
  a: integer;
  b: integer;
begin
  Read(a);
  ReadLn;
  Read(b);
  WriteHex(a);
  WriteLn;
  WriteLn(b)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("PREADLN"));
    assert!(forth.contains("PWRITE-HEX"));
}

#[test]
fn uses_loop_copy_for_large_aggregate_assignment() {
    let src = r#"
program p;
type
  big = array[40] of integer;
var
  a: big;
  b: big;
begin
  b := a
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("__CP_SRC"));
    assert!(forth.contains("__CP_DST"));
    assert!(forth.contains("__CP_I PVAR@ __CP_N PVAR@ < WHILE"));
}

#[test]
fn supports_turbo_pascal_include_directive_and_paren_comment() {
    let src = include_str!("fixtures/include_program.pas");
    let forth = run_compiler(src);
    assert!(forth.contains("42 CONSTANT K"));
    assert!(forth.contains("CREATE x 0 ,"));
    assert!(forth.contains("x PVAR@ PWRITE-I32"));
}

#[test]
fn compiles_math_pas_include() {
    let src = include_str!("fixtures/use_math.pas");
    let forth = run_compiler(src);
    assert!(forth.contains("ROUTINE program::sqrt"));
    assert!(forth.contains("ROUTINE program::sin"));
    assert!(forth.contains("PWRITE-I32"));
}
