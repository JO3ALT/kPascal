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
fn supports_named_function_return_types_and_by_ref_procedures() {
    let src = r#"
program p;
type
  small = integer;
  point = record
    x: integer;
    y: integer;
  end;
var
  n: small;
  pt: point;

procedure Bump(var p: point);
begin
  p.x := p.x + 1;
  p.y := p.y + 2
end;

function Next(v: small): small;
begin
  Next := v + 5
end;

begin
  n := 7;
  pt.x := 10;
  pt.y := 20;
  Bump(pt);
  WriteLn(Next(n));
  WriteLn(pt.x);
  WriteLn(pt.y)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("pt R_"));
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
fn rejects_read_on_aggregate_argument() {
    let src = r#"
program p;
type
  arr = array[4] of integer;
var
  x: arr;
begin
  Read(x)
end.
"#;
    let err = run_compiler_fail(src);
    assert!(err.contains("Read on aggregate type is not supported"));
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
fn supports_writeln_for_char_array() {
    let src = r#"
program p;
type
  s8 = array[8] of char;
var
  s: s8;
begin
  s := 'Hello';
  WriteLn(s)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("__WSTR_STOP"));
    assert!(forth.contains("PWRITE-CHAR"));
}

#[test]
fn supports_read_char_array_with_max_length() {
    let src = r#"
program p;
type
  s8 = array[8] of char;
var
  s: s8;
begin
  Read(s, 5);
  WriteLn(s)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("PREAD-CHAR"));
    assert!(forth.contains("__WSTR_STOP"));
    assert!(forth.contains("R@ 5 <"));
}

#[test]
fn rejects_read_char_array_without_max_length() {
    let src = r#"
program p;
type
  s8 = array[8] of char;
var
  s: s8;
begin
  Read(s)
end.
"#;
    let err = run_compiler_fail(src);
    assert!(err.contains("Read on array of char requires max length"));
}

#[test]
fn supports_c_style_string_builtins() {
    let src = r#"
program p;
type
  s16 = array[16] of char;
var
  a: s16;
  b: s16;
  c: s16;
begin
  a := 'Hello';
  b := 'World';
  Copy(a, c);
  Concat(a, b, c);
  Delete(c, 6, 5);
  Insert(b, a, 6);
  WriteLn(Pos(b, a));
  WriteLn(UpCase('q'))
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("__STRCPY"));
    assert!(forth.contains("__STRPOS"));
    assert!(forth.contains("__STRDELETE"));
    assert!(forth.contains("__STRINSERT"));
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
fn supports_inttohex_and_readln_builtins() {
    let src = r#"
program p;
type
  s9 = array[9] of char;
var
  s: s9;
  a: integer;
  b: integer;
begin
  Read(a);
  ReadLn;
  Read(b);
  IntToHex(a, s, 8, true);
  WriteLn(s);
  WriteLn(b)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("PREADLN"));
    assert!(forth.contains("__I32_TO_HEX_STR"));
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

#[test]
fn supports_standard_pascal_real_subrange_enum_set_and_in_ops() {
    let src = r#"
program p;
type
  color = (red, green, blue);
  colors = set of color;
  idx = 1..3;
  real_arr = array[1..3] of real;
var
  c: color;
  s: colors;
  i: idx;
  a: real_arr;
begin
  i := 2;
  c := green;
  s := [red, green];
  a[i] := 1.5 / 0.5;
  WriteLn(a[i]);
  WriteLn((c in s) and ((red in s) or (blue in s)));
  WriteLn(Ord(c))
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("1069547520 1056964608 FDIV"));
    assert!(forth.contains("PWRITE-F32"));
    assert!(forth.contains("i PVAR@ 1 - 4 * +"));
    assert!(forth.contains("AND"));
    assert!(forth.contains("OR"));
    assert!(forth.contains("LSHIFT"));
}

#[test]
fn supports_multiple_const_type_var_sections_and_pointer_new_dispose() {
    let src = r#"
program p;
const
  one = 1;
type
  node = record
    value: integer;
  end;
var
  p: ^node;
const
  two = 2;
var
  x: integer;
begin
  new(p);
  p^.value := one + two;
  x := p^.value;
  dispose(p);
  WriteLn(x);
  WriteLn(p = nil)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("HERE __NEWP PVAR!"));
    assert!(forth.contains("ALLOT"));
    assert!(forth.contains("__NEWP PVAR@ p PVAR!"));
    assert!(forth.contains("0 p PVAR!"));
    assert!(forth.contains("p PVAR@ 0 + PVAR!"));
    assert!(forth.contains("p PVAR@ 0 + PVAR@"));
}

#[test]
fn supports_addr_and_setaddr_for_pointer_aliasing() {
    let src = r#"
program p;
type
  cellp = ^integer;
var
  p: cellp;
  q: cellp;
  addr: integer;
begin
  new(p);
  p^ := 123;
  addr := Addr(p^);
  SetAddr(q, addr);
  q^ := 456;
  WriteLn(p^)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("p PVAR@"));
    assert!(forth.contains("addr PVAR!"));
    assert!(forth.contains("addr PVAR@ q PVAR!"));
    assert!(forth.contains("456 q PVAR@ PVAR!"));
    assert!(forth.contains("p PVAR@ PVAR@"));
}

#[test]
fn supports_with_variant_record_case_ranges_set_ops_and_3d_arrays() {
    let src = r#"
program p;
type
  color = (red, green, blue, yellow);
  colors = set of color;
  point = record
    x: integer;
    y: integer;
  end;
  node = record
    case tag: integer of
      0: (i: integer;);
      1: (j: integer; k: integer;);
  end;
  cube = array[1..2, 1..2, 1..2] of integer;
var
  pnt: point;
  n: node;
  c: cube;
  s1: colors;
  s2: colors;
begin
  pnt.x := 10;
  pnt.y := 20;
  with pnt do
  begin
    x := x + 1;
    y := y + 2
  end;
  c[1, 2, 2] := pnt.x + pnt.y;
  n.tag := 1;
  n.j := c[1, 2, 2];
  s1 := [red, blue];
  s2 := [blue, yellow];
  WriteLn(true xor false);
  WriteLn((s1 - s2) = [red]);
  WriteLn([blue] <= s1);
  case n.j of
    30, 31..33: WriteLn(n.j);
  else
    WriteLn(0)
  end
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("10 pnt PVAR!"));
    assert!(forth.contains("20 pnt 4 PFIELD!"));
    assert!(forth.contains("pnt PVAR@ 1 + pnt PVAR!"));
    assert!(forth.contains("pnt 4 PFIELD@ 2 + pnt 4 PFIELD!"));
    assert!(forth.contains("XOR PWRITE-BOOL"));
    assert!(forth.contains("-1 XOR"));
    assert!(forth.contains("R@ 30 ="));
    assert!(forth.contains("R@ 31 >= R@ 33 <= AND"));
}

#[test]
fn supports_four_dimensional_arrays() {
    let src = r#"
program p;
type
  hyper = array[1..2, 1..2, 1..2, 1..2] of integer;
var
  h: hyper;
begin
  h[2, 1, 2, 1] := 77;
  WriteLn(h[2, 1, 2, 1])
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("77"));
    assert!(forth.contains("PWRITE-I32"));
}

#[test]
fn supports_nested_variant_records() {
    let src = r#"
program p;
type
  nested = record
    case tag: integer of
      0: (i: integer;);
      1: (
        case sub: integer of
          0: (c: char;);
          1: (j: integer;);
      );
  end;
var
  n: nested;
begin
  n.tag := 1;
  n.sub := 1;
  n.j := 42;
  WriteLn(n.j)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("42"));
    assert!(forth.contains("PWRITE-I32"));
}

#[test]
fn emits_variant_tag_runtime_checks() {
    let src = r#"
program p;
type
  node = record
    case tag: integer of
      0: (i: integer;);
      1: (j: integer;);
  end;
var
  n: node;
begin
  n.tag := 0;
  WriteLn(n.j)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("__VARIANT_MISMATCH"));
    assert!(forth.contains("__VAR_TAG"));
}

#[test]
fn emits_subrange_runtime_checks() {
    let src = r#"
program p;
type
  small = 1..10;
var
  x: small;

procedure SetIt(v: small);
begin
  x := v
end;

begin
  x := 3;
  SetIt(4);
  WriteLn(x)
end.
"#;
    let forth = run_compiler(src);
    assert!(forth.contains("__SUBRANGE_MISMATCH"));
    assert!(forth.contains("DUP 1 >= OVER 10 <="));
}

#[test]
fn supports_conformant_array_parameters() {
    let src = r#"
program p;
type
  arr = array[3..5] of integer;

procedure Sum(var a: array[l..u: integer] of integer);
var
  i: integer;
  s: integer;
begin
  s := 0;
  for i := l to u do
    s := s + a[i];
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(Length(a));
  WriteLn(s)
end;

var
  data: arr;
begin
  data[3] := 10;
  data[4] := 20;
  data[5] := 30;
  Sum(data)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("PVAR@ - 4 *"));
    assert!(forth.contains("1 +"));
    assert!(forth.contains("R_"));
}

#[test]
fn supports_multidimensional_conformant_array_parameters() {
    let src = r#"
program p;
type
  matrix = array[1..2, 3..4] of integer;

procedure Sum2(var a: array[i1..j1: integer; i2..j2: integer] of integer);
begin
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(Length(a));
  WriteLn(a[i1, i2] + a[j1, j2])
end;

var
  m: matrix;
begin
  m[1,3] := 10;
  m[2,4] := 20;
  Sum2(m)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("S_"));
    assert!(forth.contains("PVAR@ -"));
    assert!(forth.contains("* +"));
}

#[test]
fn supports_set_literal_ranges_and_numeric_builtins() {
    let src = r#"
program p;
type
  idx = (i1, i2, i3, i4, i5, i6, i7, i8);
  idxs = set of idx;
var
  s: idxs;
begin
  s := [i1, i3..i5, i8];
  WriteLn(i4 in s);
  WriteLn(i2 in s);
  WriteLn(Abs(-7));
  WriteLn(Sqr(3));
  WriteLn(Round(2.6));
  WriteLn(Trunc(2.6));
  WriteLn(Succ(4));
  WriteLn(Pred(4));
  WriteLn(Odd(5))
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("LSHIFT"));
    assert!(forth.contains("FROUND-I32"));
    assert!(forth.contains("F>S"));
    assert!(forth.contains("1 +"));
    assert!(forth.contains("1 -"));
}

#[test]
fn supports_writing_char_arrays_directly() {
    let src = r#"
program p;
type
  s6 = array[6] of char;
var
  s: s6;
begin
  s := 'Hello';
  WriteLn(s)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("__WSTR_STOP"));
    assert!(forth.contains("PWRITE-CHAR"));
}

#[test]
fn supports_hex_string_to_integer_conversion() {
    let src = r#"
program p;
type
  s9 = array[9] of char;
var
  s: s9;
begin
  s := 'FF';
  WriteLn(HexToInt('1A'));
  WriteLn(HexToInt(s));
  IntToHex(HexToInt(s), s, 8, true);
  WriteLn(s)
end.
"#;

    let forth = run_compiler(src);
    assert!(forth.contains("__HEX_TO_I32"));
    assert!(forth.contains("__HEX_PTR PVAR!"));
    assert!(forth.contains("__I32_TO_HEX_STR"));
    assert!(forth.contains("__I2H_VAL PVAR!"));
}
