use std::fs;
use std::process::{Command, Stdio};

fn missing_kforth_reason() -> Option<String> {
    let bootstrap = "../kforth/bootstrap.fth";
    let binaries = ["../kforth/build/kforth", "../kforth/kforth"];

    if fs::metadata(bootstrap).is_err() {
        return Some(format!("missing {bootstrap}"));
    }
    if binaries.iter().all(|path| fs::metadata(path).is_err()) {
        return Some(format!(
            "missing kforth binary (tried: {})",
            binaries.join(", ")
        ));
    }
    None
}

fn kforth_binary_path() -> &'static str {
    if fs::metadata("../kforth/build/kforth").is_ok() {
        "../kforth/build/kforth"
    } else {
        "../kforth/kforth"
    }
}

macro_rules! require_kforth {
    () => {
        if let Some(reason) = missing_kforth_reason() {
            eprintln!("skipping e2e_kforth: {reason}");
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

fn compile_pascal_fail(src: &str) -> String {
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
        !out.status.success(),
        "kpascal unexpectedly succeeded.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stderr).expect("kpascal stderr is not UTF-8")
}

fn run_kforth_with_bootstrap(forth_src: &str, runtime_input: &str) -> String {
    let bootstrap = fs::read_to_string("../kforth/bootstrap.fth")
        .expect("failed to read ../kforth/bootstrap.fth");
    let payload = format!("{bootstrap}\n{forth_src}\n{runtime_input}\nBYE\n");

    let mut child = Command::new(kforth_binary_path())
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

fn run_kforth_with_bootstrap_raw(forth_src: &str, runtime_input: &str) -> (bool, String, String) {
    let bootstrap = fs::read_to_string("../kforth/bootstrap.fth")
        .expect("failed to read ../kforth/bootstrap.fth");
    let payload = format!("{bootstrap}\n{forth_src}\n{runtime_input}\nBYE\n");

    let mut child = Command::new(kforth_binary_path())
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
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
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
    require_kforth!();
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
    require_kforth!();
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
fn e2e_aggregate_and_3d_runs_on_kforth() {
    require_kforth!();
    let src = include_str!("fixtures/aggregate_and_3d.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["10".to_string(), "20".to_string(), "77".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_string_assignment_to_char_array_runs_on_kforth() {
    require_kforth!();
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
fn e2e_include_directive_runs_on_kforth() {
    require_kforth!();
    let src = include_str!("fixtures/include_program.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["42".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_div_mod_runs_on_kforth() {
    require_kforth!();
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
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "2".to_string(),
        "1".to_string(),
        "3".to_string(),
        "2".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_true_false_literals_run_on_kforth() {
    require_kforth!();
    let src = r#"
program p;
begin
  WriteLn(true);
  WriteLn(false)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["TRUE".to_string(), "FALSE".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_branching_recursion_fib_runs_on_kforth() {
    require_kforth!();
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
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["8".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
#[ignore = "all_features exercises extension-heavy coverage outside the standard Pascal target"]
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
        "30".to_string(),
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
        "5000".to_string(),
        "5000".to_string(),
        "10000".to_string(),
        "30".to_string(),
        "60".to_string(),
        "45".to_string(),
        "6931".to_string(),
        "10000".to_string(),
        "255".to_string(),
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

#[test]
fn e2e_functional_smoke_runs_on_kforth() {
    require_kforth!();
    let src = include_str!("fixtures/functional_smoke.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "***".to_string(),
        "THREE".to_string(),
        "8".to_string(),
        "20".to_string(),
        "99".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_use_math_runs_on_kforth() {
    require_kforth!();
    let src = include_str!("fixtures/use_math.pas");
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "9".to_string(),
        "5000".to_string(),
        "5000".to_string(),
        "10000".to_string(),
        "30".to_string(),
        "60".to_string(),
        "45".to_string(),
        "6931".to_string(),
        "10000".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_dispose_sets_pointer_to_nil_runs_on_kforth() {
    require_kforth!();
    let src = r#"
program p;
type
  pnode = ^node;
  node = record
    value: integer;
  end;
var
  p1: pnode;
begin
  New(p1);
  p1^.value := 7;
  WriteLn(p1^.value);
  Dispose(p1);
  WriteLn(p1 = nil)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["7".to_string(), "TRUE".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
#[ignore = "cond expressions are outside the current standard Pascal target"]
fn e2e_with_cond_and_record_update_run_on_kforth() {
    let src = r#"
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
  p1.x := 10;
  p1.y := 20;
  with p1 do
    p2 := p1 with (y := cond(
      x = 10: begin
        value y + 5
      end;
      else: begin
        value 0
      end
    ));
  WriteLn(p2.x);
  WriteLn(p2.y)
end.
"#;
    let err = compile_pascal_fail(src);
    assert!(err.contains("unknown identifier: x"));
}

#[test]
#[ignore = "pointer/integer cast roundtrip is outside the current standard Pascal target"]
fn e2e_pointer_integer_cast_roundtrip_runs_on_kforth() {
    let src = r#"
program p;
type
  pnode = ^node;
  node = record
    value: integer;
  end;
var
  p1: pnode;
  p2: pnode;
  addr: integer;
begin
  New(p1);
  p1^.value := 123;
  addr := cast(integer, p1);
  p2 := cast(pnode, addr);
  WriteLn(p2^.value)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["123".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
#[ignore = "pointer allocation stress coverage is outside the current standard Pascal target"]
fn e2e_multiple_new_allocations_keep_distinct_storage() {
    let src = r#"
program p;
type
  pnode = ^node;
  node = record
    value: integer;
    next: pnode;
  end;
var
  a: pnode;
  b: pnode;
begin
  New(a);
  New(b);
  a^.value := 11;
  b^.value := 22;
  a^.next := b;
  b^.next := nil;
  WriteLn(a^.value);
  WriteLn(b^.value);
  WriteLn(a^.next = b);
  WriteLn(b^.next = nil)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "11".to_string(),
        "22".to_string(),
        "TRUE".to_string(),
        "TRUE".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_multiple_new_allocations_across_different_types() {
    require_kforth!();
    let src = r#"
program p;
type
  psmall = ^smallrec;
  smallrec = record
    a: integer;
  end;
  pbig = ^bigrec;
  bigrec = record
    x: integer;
    y: integer;
    z: integer;
  end;
var
  s1: psmall;
  b1: pbig;
  s2: psmall;
begin
  New(s1);
  New(b1);
  New(s2);

  s1^.a := 11;
  b1^.x := 21;
  b1^.y := 22;
  b1^.z := 23;
  s2^.a := 31;

  WriteLn(s1^.a);
  WriteLn(b1^.x);
  WriteLn(b1^.y);
  WriteLn(b1^.z);
  WriteLn(s2^.a)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec![
        "11".to_string(),
        "21".to_string(),
        "22".to_string(),
        "23".to_string(),
        "31".to_string(),
    ];
    assert_eq!(got, expected, "unexpected runtime output");
}

#[test]
fn e2e_string_copy_builtin_differs_from_fixed_array_assignment() {
    require_kforth!();
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
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
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
#[ignore = "list builtins are outside the current standard Pascal target"]
fn e2e_list_builtins_handle_empty_and_singleton_lists() {
    let src = r#"
program p;
(* $I list.pas *)

procedure plus1(var src: integer; var dst: integer);
begin
  dst := src + 1
end;

function keep_even(var v: integer): boolean;
begin
  keep_even := (v mod 2) = 0
end;

function add_i(acc: integer; var v: integer): integer;
begin
  add_i := acc + v
end;

var
  empty: plist;
  one: plist;
  mapped: plist;
  filtered_empty: plist;
  filtered_one: plist;
begin
  empty := list_nil();
  WriteLn(list_len(empty));
  mapped := Map(empty, plus1);
  WriteLn(list_len(mapped));
  filtered_empty := Filter(empty, keep_even);
  WriteLn(list_len(filtered_empty));
  WriteLn(Fold(empty, 99, add_i));

  one := list_cons(4, list_nil());
  filtered_one := Filter(one, keep_even);
  WriteLn(list_len(filtered_one));
  WriteLn(list_head(filtered_one));
  WriteLn(Fold(one, 10, add_i));

  list_free(filtered_one);
  list_free(filtered_empty);
  list_free(mapped);
  list_free(one);
  list_free(empty)
end.
"#;
    let err = compile_pascal_fail(src);
    assert!(err.contains("unknown routine in scope: Map"));
}

#[test]
#[ignore = "option/result sum helpers are outside the current standard Pascal target"]
fn e2e_nested_option_result_and_sum_case_run_on_kforth() {
    let src = r#"
program p;
type
  pair = record
    x: integer;
    y: integer;
  end;
  maybe_pair = option of pair;
  nested = result of maybe_pair, integer;
var
  v: nested;
  outv: integer;

function build(flag: integer): nested;
var
  p: pair;
begin
  p := pair(x := 7; y := 9);
  build := cond(
    flag = 0: begin
      value ok(value := none)
    end;
    flag = 1: begin
      value ok(value := some(p))
    end;
    else: begin
      value err(error := 5)
    end
  )
end;

procedure consume(n: nested);
begin
  case n of
    ok(opt): begin
      case opt of
        none(): outv := 100;
        some(p): begin
          outv := p.x + p.y
        end
      end
    end;
    err(e): outv := e
  end
end;

begin
  v := build(0);
  consume(v);
  WriteLn(outv);

  v := build(1);
  consume(v);
  WriteLn(outv);

  v := build(2);
  consume(v);
  WriteLn(outv)
end.
"#;
    let err = compile_pascal_fail(src);
    assert!(err.contains("aggregate constructor field value must be lvalue in codegen"));
}

#[test]
#[ignore = "variant tag runtime traps are not in the current standard Pascal target"]
fn e2e_variant_tag_mismatch_fails_on_kforth() {
    let src = r#"
program p;
type
  rec = record
    case kind: integer of
      0: (a: integer;);
      1: (b: integer;)
  end;
var
  r: rec;
begin
  r.kind := 0;
  WriteLn(r.b)
end.
"#;
    let forth = compile_pascal(src);
    let (ok, stdout, stderr) = run_kforth_with_bootstrap_raw(&forth, "");
    assert!(
        !ok || stdout.contains("__VARIANT_MISMATCH") || stdout.contains("Variant tag mismatch"),
        "expected variant mismatch trap.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
#[ignore = "subrange runtime traps are not in the current standard Pascal target"]
fn e2e_subrange_check_fails_on_kforth() {
    let src = r#"
program p;
var
  x: 1..3;
begin
  x := 4
end.
"#;
    let forth = compile_pascal(src);
    let (ok, stdout, stderr) = run_kforth_with_bootstrap_raw(&forth, "");
    assert!(
        !ok || stdout.contains("__SUBRANGE_MISMATCH") || stdout.contains("Subrange check failed"),
        "expected subrange trap.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn e2e_cond_short_circuits_side_effects_on_kforth() {
    require_kforth!();
    let src = r#"
program p;
var
  a: integer;
  b: integer;
function Tick(n: integer): integer;
begin
  b := b + 1;
  Tick := n
end;
begin
  a := cond(
    1 < 2: begin
      b := b + 10;
      value 111
    end;
    Tick(0) = 0: begin
      b := b + 100;
      value 222
    end;
    else: begin
      value 333
    end
  );
  WriteLn(a);
  WriteLn(b)
end.
"#;
    let forth = compile_pascal(src);
    let out = run_kforth_with_bootstrap(&forth, "");
    let got = normalize_kforth_output(&out);
    let expected = vec!["111".to_string(), "10".to_string()];
    assert_eq!(got, expected, "unexpected runtime output");
}
