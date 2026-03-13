use std::fs;
use std::path::Path;
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

fn preprocess_pascal_file(src_path: &str) -> String {
    let prekpasc = Path::new("../prekpascal/target/debug/prekpascal");
    assert!(
        prekpasc.exists(),
        "missing prekpascal binary at {}",
        prekpasc.display()
    );
    let src = fs::read_to_string(src_path).expect("failed to read Pascal source for preprocessing");
    let mut child = Command::new(prekpasc)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn prekpascal");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("stdin not available");
        stdin
            .write_all(src.as_bytes())
            .expect("failed to write source to prekpascal stdin");
    }

    let out = child
        .wait_with_output()
        .expect("failed to wait on prekpascal");
    assert!(
        out.status.success(),
        "prekpascal failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("prekpascal output is not valid utf-8")
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

#[test]
fn compiles_string_utils_fixture() {
    let src = include_str!("fixtures/use_string_utils.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("PWRITELN"));
}

#[test]
fn compiles_selfhost_kpsc_skeleton() {
    let src = include_str!("../selfhost/kpsc.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("R_PROGR"));
}

#[test]
fn compiles_selfhost_kpsc_main() {
    let src = include_str!("../selfhost/kpsc_main.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ReadSourceFromStdin"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_preprocessed_selfhost_kpsc_main() {
    let src = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let forth = run_compiler(&src);

    assert!(!src.contains("$I"));
    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ReadSourceFromStdin"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_seed_hello_single() {
    let src = include_str!("../selfhost/kpsc_seed_hello_single.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("CREATE __CASE_MATCH 0 ,"));
    assert!(forth.contains("PWRITE-CHAR"));
}

#[test]
fn compiles_selfhost_kpsc_string() {
    let src = include_str!("../selfhost/kpsc_string.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_routines() {
    let src = include_str!("../selfhost/kpsc_routines.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("CREATE __CALL_RET 0 ,"));
    assert!(forth.contains("ParseProcedureDecl"));
    assert!(forth.contains("ParseFunctionDecl"));
}

#[test]
fn compiles_selfhost_kpsc_string_edit() {
    let src = include_str!("../selfhost/kpsc_string_edit.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
    assert!(forth.contains("__STRINSERT"));
}

#[test]
fn compiles_selfhost_kpsc_hex() {
    let src = include_str!("../selfhost/kpsc_hex.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
    assert!(forth.contains("__I32_TO_HEX_STR"));
    assert!(forth.contains("__HEX_TO_I32"));
}

#[test]
fn compiles_selfhost_kpsc_real() {
    let src = include_str!("../selfhost/kpsc_real.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_case() {
    let src = include_str!("../selfhost/kpsc_case.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
    assert!(forth.contains("__CASE_MATCH"));
}

#[test]
fn compiles_selfhost_kpsc_scalar() {
    let src = include_str!("../selfhost/kpsc_scalar.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_array2d() {
    let src = include_str!("../selfhost/kpsc_array2d.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_array4d() {
    let src = include_str!("../selfhost/kpsc_array4d.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_variant() {
    let src = include_str!("../selfhost/kpsc_variant.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_pointer() {
    let src = include_str!("../selfhost/kpsc_pointer.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_addr() {
    let src = include_str!("../selfhost/kpsc_addr.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_enumset() {
    let src = include_str!("../selfhost/kpsc_enumset.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_conf1d() {
    let src = include_str!("../selfhost/kpsc_conf1d.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_conf2d() {
    let src = include_str!("../selfhost/kpsc_conf2d.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}

#[test]
fn compiles_selfhost_kpsc_setops() {
    let src = include_str!("../selfhost/kpsc_setops.pas");
    let forth = run_compiler(src);

    assert!(forth.contains(": MAIN"));
    assert!(forth.contains("ParseProgram"));
}
