use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);

fn runtime_c_path() -> PathBuf {
    Path::new("../kFORTHc/runtime/runtime.c").to_path_buf()
}

fn llc_bin() -> Option<&'static str> {
    for candidate in ["llc", "llc-14"] {
        if Command::new(candidate)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .ok()
            .is_some_and(|s| s.success())
        {
            return Some(candidate);
        }
    }
    None
}

fn has_native_backend() -> bool {
    Command::new("kforthc")
        .arg("--help")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .ok()
        .is_some()
        && llc_bin().is_some()
        && Command::new("clang")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .ok()
            .is_some_and(|s| s.success())
        && runtime_c_path().exists()
}

macro_rules! require_native_backend {
    () => {
        if !has_native_backend() {
            eprintln!(
                "skipping native e2e: missing kforthc/llc/clang or ../kFORTHc/runtime/runtime.c"
            );
            return;
        }
    };
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

fn fresh_work_dir(test_name: &str) -> PathBuf {
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("kpascal-{test_name}-{}-{id}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("failed to create temporary directory");
    dir
}

fn run_native_with_kforthc(test_name: &str, forth_src: &str, runtime_input: &str) -> String {
    let work_dir = fresh_work_dir(test_name);
    let forth_path = work_dir.join("program.fth");
    let ll_path = work_dir.join("program.ll");
    let obj_path = work_dir.join("program.o");
    let bin_path = work_dir.join("program.out");
    std::fs::write(&forth_path, forth_src).expect("failed to write Forth source");

    let out = Command::new("kforthc")
        .arg(&forth_path)
        .arg(&ll_path)
        .output()
        .expect("failed to spawn kforthc");
    assert!(
        out.status.success(),
        "kforthc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let llc = llc_bin().expect("llc not found");
    let out = Command::new(llc)
        .arg("-filetype=obj")
        .arg(&ll_path)
        .arg("-o")
        .arg(&obj_path)
        .output()
        .expect("failed to spawn llc");
    assert!(
        out.status.success(),
        "llc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new("clang")
        .arg("-no-pie")
        .arg(&obj_path)
        .arg(runtime_c_path())
        .arg("-o")
        .arg(&bin_path)
        .arg("-lm")
        .output()
        .expect("failed to spawn clang");
    assert!(
        out.status.success(),
        "clang failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let mut child = Command::new(&bin_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to run native binary");

    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .expect("stdin not available")
            .write_all(runtime_input.as_bytes())
            .expect("failed to feed runtime input");
    }

    let out = child
        .wait_with_output()
        .expect("failed to wait for native binary");
    assert!(
        out.status.success(),
        "native binary failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("native stdout is not UTF-8")
}

fn normalize_native_output(raw: &str) -> Vec<String> {
    raw.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

#[test]
fn e2e_all_syntax_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/all_syntax.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("all_syntax", &forth, "");
    let got = normalize_native_output(&out).join("\n");
    assert!(got.contains("N"));
    assert!(got.contains("A"));
    assert!(got.contains("-19"));
    assert!(got.contains("20"));
    assert!(got.contains("TRUE"));
    assert!(got.contains("Z"));
}

#[test]
fn e2e_read_all_types_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/read_all_types.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("read_all_types", &forth, "12 1 X 34 0 Y");
    let got = normalize_native_output(&out);
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
fn e2e_aggregate_and_3d_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/aggregate_and_3d.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("aggregate_and_3d", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["10".to_string(), "20".to_string(), "77".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_string_assignment_to_char_array_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/string_assign_char_array.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("string_assign_char_array", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "ABC".to_string(),
        "TRUE".to_string(),
        "XYZLO".to_string(),
        "TRUE".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_read_char_array_with_max_length_runs_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("read_char_array", &forth, "H e l l o");
    let got = normalize_native_output(&out);
    let expected = vec!["Hello".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_c_style_string_builtins_run_on_kforthc_native() {
    require_native_backend!();
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
  WriteLn(c);
  Concat(a, b, c);
  WriteLn(c);
  Delete(c, 6, 5);
  WriteLn(c);
  Insert(b, a, 6);
  WriteLn(a);
  WriteLn(Pos(b, a));
  WriteLn(UpCase('q'))
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("c_style_string_builtins", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "Hello".to_string(),
        "HelloWorld".to_string(),
        "Hello".to_string(),
        "HelloWorld".to_string(),
        "6".to_string(),
        "Q".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_string_copy_builtin_differs_from_fixed_array_assignment() {
    require_native_backend!();
    let src = r#"
program p;
type
  s6 = array[6] of char;
var
  src: s6;
  dst_assign: s6;
  dst_copy: s6;
begin
  src[0] := 'A';
  src[1] := 'B';
  src[2] := #0;
  src[3] := 'X';
  src[4] := 'Y';
  src[5] := #0;

  dst_assign := src;
  Copy(src, dst_copy);

  WriteLn(dst_assign[3] = 'X');
  WriteLn(dst_assign[4] = 'Y');
  WriteLn(dst_copy[3] = #0);
  WriteLn(dst_copy[4] = #0);
  WriteLn(dst_assign);
  WriteLn(dst_copy)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("string_copy_vs_fixed_assign", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "TRUE".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
        "AB".to_string(),
        "AB".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_builtins_and_hex_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/builtins_and_hex.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("builtins_and_hex", &forth, "255\n42");
    let got = normalize_native_output(&out);
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
fn e2e_include_directive_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/include_program.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("include_program", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["42".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_div_mod_runs_on_kforthc_native() {
    require_native_backend!();
    let src = r#"
program p;
begin
  WriteLn(7 div 3);
  WriteLn(7 mod 3);
  WriteLn(20 div 6);
  WriteLn(20 mod 6)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("div_mod", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "2".to_string(),
        "1".to_string(),
        "3".to_string(),
        "2".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_true_false_literals_run_on_kforthc_native() {
    require_native_backend!();
    let src = r#"
program p;
begin
  WriteLn(true);
  WriteLn(false)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("true_false", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["TRUE".to_string(), "FALSE".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_branching_recursion_fib_runs_on_kforthc_native() {
    require_native_backend!();
    let src = r#"
program p;
function Fib(n: integer): integer;
begin
  if n <= 1 then
    Fib := n
  else
    Fib := Fib(n - 1) + Fib(n - 2)
end;
begin
  WriteLn(Fib(6))
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("fib", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["8".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_named_function_return_and_by_ref_procedure_run_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("named_return_and_by_ref", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["12".to_string(), "11".to_string(), "22".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_all_features_runs_on_kforthc_native() {
    require_native_backend!();
    let src = include_str!("fixtures/all_features.pas");
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("all_features", &forth, "255\n1 X\n7 8 9\nH e l l o");
    let got = normalize_native_output(&out);
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
    assert_eq!(got.len(), expected.len(), "unexpected runtime line count");
    for (idx, (actual, want)) in got.iter().zip(expected.iter()).enumerate() {
        if (23..31).contains(&idx) {
            assert!(
                actual.parse::<i32>().is_ok(),
                "math segment line {} should be integer output, got {actual}",
                idx + 1
            );
            continue;
        }
        assert_eq!(
            actual,
            want,
            "unexpected runtime output at line {}",
            idx + 1
        );
    }
}

#[test]
fn e2e_standard_pascal_real_subrange_enum_set_runs_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("std_pascal_features", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["3.0000".to_string(), "TRUE".to_string(), "1".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_pointer_new_dispose_and_repeated_sections_run_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("pointer_sections", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["3".to_string(), "TRUE".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_addr_and_setaddr_alias_heap_memory_on_kforthc_native() {
    require_native_backend!();
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
  WriteLn(p^);
  dispose(p);
  WriteLn(p = nil)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("addr_setaddr_heap_alias", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["456".to_string(), "TRUE".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_with_variant_record_case_ranges_set_ops_and_3d_arrays_run_on_kforthc_native() {
    require_native_backend!();
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
  WriteLn(s1 >= [blue]);
  WriteLn(s1 < (s1 + s2));
  WriteLn((s1 + s2) > s1);
  case n.j of
    30, 31..33: WriteLn(n.j);
  else
    WriteLn(0)
  end;
  WriteLn(pnt.x);
  WriteLn(pnt.y)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("std_pascal_more", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "TRUE".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
        "33".to_string(),
        "11".to_string(),
        "22".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_nested_variant_records_run_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("nested_variant_records", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["42".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_subrange_assignments_run_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("subrange_assignments", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["4".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_four_dimensional_arrays_and_conformant_params_run_on_kforthc_native() {
    require_native_backend!();
    let src = r#"
program p;
type
  hyper = array[1..2, 1..2, 1..2, 1..2] of integer;
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
  h: hyper;
  data: arr;
begin
  h[2, 1, 2, 1] := 77;
  WriteLn(h[2, 1, 2, 1]);
  data[3] := 10;
  data[4] := 20;
  data[5] := 30;
  Sum(data)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("arrays_complete", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "77".to_string(),
        "3".to_string(),
        "5".to_string(),
        "3".to_string(),
        "60".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_multidimensional_conformant_array_params_run_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("arrays_conformant_2d", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "1".to_string(),
        "2".to_string(),
        "2".to_string(),
        "30".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_set_literal_ranges_numeric_builtins_and_char_arrays_run_on_kforthc_native() {
    require_native_backend!();
    let src = r#"
program p;
type
  idx = (i1, i2, i3, i4, i5, i6, i7, i8);
  idxs = set of idx;
  s6 = array[6] of char;
var
  s: idxs;
  txt: s6;
begin
  s := [i1, i3..i5, i8];
  txt := 'Hello';
  WriteLn(i4 in s);
  WriteLn(i2 in s);
  WriteLn(Abs(-7));
  WriteLn(Sqr(3));
  WriteLn(Round(2.6));
  WriteLn(Trunc(2.6));
  WriteLn(Succ(4));
  WriteLn(Pred(4));
  WriteLn(Odd(5));
  WriteLn(txt)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("pascal_remaining", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec![
        "TRUE".to_string(),
        "FALSE".to_string(),
        "7".to_string(),
        "9".to_string(),
        "3".to_string(),
        "2".to_string(),
        "5".to_string(),
        "3".to_string(),
        "TRUE".to_string(),
        "Hello".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_hex_string_to_integer_conversion_runs_on_kforthc_native() {
    require_native_backend!();
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
    let forth = compile_pascal(src);
    let out = run_native_with_kforthc("hex_to_int", &forth, "");
    let got = normalize_native_output(&out);
    let expected = vec!["26".to_string(), "255".to_string(), "000000FF".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}
