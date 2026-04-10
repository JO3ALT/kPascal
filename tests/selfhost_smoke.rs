use std::fmt::Write as _;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::ErrorKind;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::{Mutex, MutexGuard, OnceLock};

fn kforthc_bin() -> Option<&'static str> {
    for path in [
        "../kforthc/target/release/kforthc",
        "../kFORTHc/target/release/kforthc",
        "/home/kamitani/bin/kforthc",
    ] {
        if Path::new(path).exists() {
            return Some(path);
        }
    }
    if Command::new("kforthc")
        .arg("--help")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .ok()
        .is_some_and(|s| s.success() || s.code().is_some())
    {
        Some("kforthc")
    } else {
        None
    }
}

fn runtime_c_path() -> Option<&'static str> {
    for path in [
        "../kforthc/runtime/runtime.c",
        "../kFORTHc/runtime/runtime.c",
    ] {
        if Path::new(path).exists() {
            return Some(path);
        }
    }
    None
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

fn selfhost_serial_guard() -> MutexGuard<'static, ()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn has_selfhost_native_backend() -> bool {
    kforthc_bin().is_some()
        && llc_bin().is_some()
        && runtime_c_path().is_some()
        && Command::new("clang")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .ok()
            .is_some_and(|s| s.success())
}

fn prekpascal_bin() -> &'static str {
    "scripts/preprocess_selfhost.sh"
}

fn preprocess_pascal_file(src_path: &str) -> String {
    let child = Command::new("bash")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .arg(prekpascal_bin())
        .arg(src_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn selfhost preprocessor");

    let out = child
        .wait_with_output()
        .expect("failed to wait for selfhost preprocessor");
    assert!(
        out.status.success(),
        "selfhost preprocessor failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("prekpascal stdout is not utf-8")
}

fn run_compiler(src: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_kpascal"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
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
    String::from_utf8(out.stdout).expect("stdout is not utf-8")
}

fn run_native_forth(test_name: &str, forth_src: &str) -> String {
    let work_dir = std::env::temp_dir().join(format!(
        "kpascal-selfhost-{test_name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&work_dir);
    fs::create_dir_all(&work_dir).expect("failed to create temp dir");

    let forth_path = work_dir.join("program.fth");
    let ll_path = work_dir.join("program.ll");
    let obj_path = work_dir.join("program.o");
    let bin_path = work_dir.join("program.out");
    fs::write(&forth_path, forth_src).expect("failed to write forth source");

    let out = Command::new(kforthc_bin().expect("missing kforthc"))
        .arg(&forth_path)
        .arg(&ll_path)
        .output()
        .expect("failed to run kforthc");
    assert!(
        out.status.success(),
        "kforthc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new(llc_bin().expect("missing llc"))
        .arg("-filetype=obj")
        .arg(&ll_path)
        .arg("-o")
        .arg(&obj_path)
        .output()
        .expect("failed to run llc");
    assert!(
        out.status.success(),
        "llc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new("clang")
        .arg("-no-pie")
        .arg(&obj_path)
        .arg(runtime_c_path().expect("missing runtime.c"))
        .arg("-o")
        .arg(&bin_path)
        .arg("-lm")
        .output()
        .expect("failed to run clang");
    assert!(
        out.status.success(),
        "clang failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new(&bin_path)
        .output()
        .expect("failed to run native binary");
    assert!(
        out.status.success(),
        "native run failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("stdout is not utf-8")
}

fn run_native_forth_with_input(test_name: &str, forth_src: &str, stdin_src: &str) -> String {
    let work_dir = std::env::temp_dir().join(format!(
        "kpascal-selfhost-{test_name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&work_dir);
    fs::create_dir_all(&work_dir).expect("failed to create temp dir");

    let forth_path = work_dir.join("program.fth");
    let ll_path = work_dir.join("program.ll");
    let obj_path = work_dir.join("program.o");
    let bin_path = work_dir.join("program.out");
    fs::write(&forth_path, forth_src).expect("failed to write forth source");

    let out = Command::new(kforthc_bin().expect("missing kforthc"))
        .arg(&forth_path)
        .arg(&ll_path)
        .output()
        .expect("failed to run kforthc");
    assert!(
        out.status.success(),
        "kforthc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new(llc_bin().expect("missing llc"))
        .arg("-filetype=obj")
        .arg(&ll_path)
        .arg("-o")
        .arg(&obj_path)
        .output()
        .expect("failed to run llc");
    assert!(
        out.status.success(),
        "llc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new("clang")
        .arg("-no-pie")
        .arg(&obj_path)
        .arg(runtime_c_path().expect("missing runtime.c"))
        .arg("-o")
        .arg(&bin_path)
        .arg("-lm")
        .output()
        .expect("failed to run clang");
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
            .write_all(stdin_src.as_bytes())
            .expect("failed to feed stdin");
    }
    let out = child
        .wait_with_output()
        .expect("failed to wait for native binary");
    assert!(
        out.status.success(),
        "native run failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("stdout is not utf-8")
}

fn build_native_forth_binary(
    test_name: &str,
    forth_src: &str,
) -> (std::path::PathBuf, std::path::PathBuf) {
    let work_dir = std::env::temp_dir().join(format!(
        "kpascal-selfhost-{test_name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&work_dir);
    fs::create_dir_all(&work_dir).expect("failed to create temp dir");

    let forth_path = work_dir.join("program.fth");
    let ll_path = work_dir.join("program.ll");
    let obj_path = work_dir.join("program.o");
    let bin_path = work_dir.join("program.out");
    fs::write(&forth_path, forth_src).expect("failed to write forth source");

    let out = Command::new(kforthc_bin().expect("missing kforthc"))
        .arg(&forth_path)
        .arg(&ll_path)
        .output()
        .expect("failed to run kforthc");
    assert!(
        out.status.success(),
        "kforthc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new(llc_bin().expect("missing llc"))
        .arg("-filetype=obj")
        .arg(&ll_path)
        .arg("-o")
        .arg(&obj_path)
        .output()
        .expect("failed to run llc");
    assert!(
        out.status.success(),
        "llc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new("clang")
        .arg("-no-pie")
        .arg(&obj_path)
        .arg(runtime_c_path().expect("missing runtime.c"))
        .arg("-o")
        .arg(&bin_path)
        .arg("-lm")
        .output()
        .expect("failed to run clang");
    assert!(
        out.status.success(),
        "clang failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    (work_dir, bin_path)
}

fn run_native_binary_with_input(bin_path: &Path, stdin_src: &str) -> String {
    let mut child = Command::new(bin_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to run native binary");
    {
        use std::io::Write;
        if let Some(stdin) = child.stdin.as_mut() {
            if let Err(err) = stdin.write_all(stdin_src.as_bytes()) {
                assert!(
                    err.kind() == ErrorKind::BrokenPipe,
                    "failed to feed stdin: {err}"
                );
            }
        } else {
            panic!("stdin not available");
        }
    }
    let out = child
        .wait_with_output()
        .expect("failed to wait for native binary");
    assert!(
        out.status.success(),
        "native run failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("stdout is not utf-8")
}

fn encode_ascii_program(src: &str) -> String {
    let mut encoded = String::new();
    let _ = write!(&mut encoded, "{}", src.chars().count());
    for ch in src.chars() {
        let _ = write!(&mut encoded, " {}", ch as u32);
    }
    encoded
}

fn classify_seed_program_kind(src: &str) -> i32 {
    let lower = src.to_ascii_lowercase();
    if let Some(program_pos) = lower.find("program") {
        let after_program = &lower[program_pos + "program".len()..];
        let trimmed = after_program.trim_start();
        let mut name = String::new();
        for ch in trimmed.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                name.push(ch);
            } else {
                break;
            }
        }
        if name == "p" {
            0
        } else if let Some(num) = name.strip_prefix("sample") {
            num.parse::<i32>().unwrap_or(0)
        } else {
            0
        }
    } else {
        0
    }
}

fn encode_seed_ascii_program(src: &str) -> String {
    let mut encoded = String::new();
    let kind = classify_seed_program_kind(src);
    let _ = write!(&mut encoded, "{} {}", src.chars().count(), kind);
    for ch in src.chars() {
        let _ = write!(&mut encoded, " {}", ch as u32);
    }
    encoded
}

fn run_selfhost_main_for_input(test_name: &str, src: &str) -> String {
    let selfhost_src = include_str!("../selfhost/kpsc_main.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let encoded = encode_ascii_program(src);
    run_native_forth_with_input(test_name, &selfhost_forth, &encoded)
}

fn run_preprocessed_selfhost_main_for_input(test_name: &str, src: &str) -> String {
    let selfhost_src = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let selfhost_forth = run_compiler(&selfhost_src);
    let encoded = encode_ascii_program(src);
    run_native_forth_with_input(test_name, &selfhost_forth, &encoded)
}

fn cached_preprocessed_selfhost_main_native_bin() -> std::path::PathBuf {
    let selfhost_src = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let compiler_bin = env!("CARGO_BIN_EXE_kpascal");
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    selfhost_src.hash(&mut hasher);
    fs::read(compiler_bin)
        .expect("failed to read current kpascal binary")
        .hash(&mut hasher);
    let key = hasher.finish();

    let cache_dir = std::env::temp_dir().join("kpascal-selfhost-binary-cache");
    fs::create_dir_all(&cache_dir).expect("failed to create selfhost binary cache dir");

    let forth_path = cache_dir.join(format!("selfhost-main-{key:016x}.fth"));
    let ll_path = cache_dir.join(format!("selfhost-main-{key:016x}.ll"));
    let obj_path = cache_dir.join(format!("selfhost-main-{key:016x}.o"));
    let bin_path = cache_dir.join(format!("selfhost-main-{key:016x}.out"));

    if bin_path.exists() {
        return bin_path;
    }

    fs::write(&forth_path, run_compiler(&selfhost_src))
        .expect("failed to write cached selfhost forth");

    let out = Command::new(kforthc_bin().expect("missing kforthc"))
        .arg(&forth_path)
        .arg(&ll_path)
        .output()
        .expect("failed to run kforthc for cached selfhost");
    assert!(
        out.status.success(),
        "kforthc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new(llc_bin().expect("missing llc"))
        .arg("-filetype=obj")
        .arg(&ll_path)
        .arg("-o")
        .arg(&obj_path)
        .output()
        .expect("failed to run llc for cached selfhost");
    assert!(
        out.status.success(),
        "llc failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let out = Command::new("clang")
        .arg("-no-pie")
        .arg(&obj_path)
        .arg(runtime_c_path().expect("missing runtime.c"))
        .arg("-o")
        .arg(&bin_path)
        .arg("-lm")
        .output()
        .expect("failed to run clang for cached selfhost");
    assert!(
        out.status.success(),
        "clang failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    bin_path
}

fn cached_preprocessed_selfhost_main_stage1_output(test_name: &str, src: &str) -> String {
    let bin_path = cached_preprocessed_selfhost_main_native_bin();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    src.hash(&mut hasher);
    fs::read(&bin_path)
        .expect("failed to read cached selfhost native binary")
        .hash(&mut hasher);
    let key = hasher.finish();
    let cache_dir = std::env::temp_dir().join("kpascal-selfhost-stage1-cache");
    fs::create_dir_all(&cache_dir).expect("failed to create stage1 cache dir");
    let cache_path = cache_dir.join(format!("{test_name}-{key:016x}.fth"));
    if cache_path.exists() {
        return fs::read_to_string(&cache_path).expect("failed to read cached stage1 output");
    }

    let encoded = encode_ascii_program(src);
    let out = run_native_binary_with_input(&bin_path, &encoded);
    fs::write(&cache_path, &out).expect("failed to write cached stage1 output");
    out
}

#[test]
fn selfhost_kpsc_main_emitted_forth_exposes_stage1_surface_markers() {
    let selfhost_src = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let selfhost_forth = run_compiler(&selfhost_src);

    for marker in [
        "program::ReadSourceFromStdin",
        "program::ReadToken",
        "program::WriteToken",
        "program::ExpectKind",
        "program::ExpectAssignSymbol",
        "program::ExpectSymbolChar",
        "program::ParseProgram",
        "program::EmitProgram",
    ] {
        assert!(
            selfhost_forth.contains(marker),
            "missing stage1 marker `{marker}`"
        );
    }
}

#[test]
fn selfhost_kpsc_emits_and_runs_hello_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let emitted_forth = run_native_forth("stage1", &selfhost_forth);
    let normalized = emitted_forth
        .lines()
        .map(str::trim_end)
        .filter(|s| !s.is_empty())
        .filter(|s| *s != "CREATE __CASE_MATCH 0 ,")
        .collect::<Vec<_>>()
        .join("\n");

    let expected = [
        ": MAIN",
        "  72 PWRITE-CHAR",
        "  69 PWRITE-CHAR",
        "  76 PWRITE-CHAR",
        "  76 PWRITE-CHAR",
        "  79 PWRITE-CHAR",
        "  PWRITELN",
        ";",
        "MAIN",
    ]
    .join("\n");
    assert_eq!(normalized, expected, "unexpected selfhost compiler output");

    let hello = run_native_forth("stage2", &emitted_forth);
    assert_eq!(hello.trim_end(), "HELLO");
}

#[test]
fn selfhost_kpsc_main_reads_encoded_stdin_and_emits_hello_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let emitted_forth = run_selfhost_main_for_input(
        "main-hello-stage1",
        "program p; begin WriteLn('HELLO') end.",
    );
    let hello = run_native_forth("main-stage2", &emitted_forth);
    assert_eq!(hello.trim_end(), "HELLO");
}

#[test]
fn selfhost_kpsc_main_captures_simple_writeln_literals_without_sample_name_dispatch() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main literal-capture smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let emitted_forth = run_selfhost_main_for_input(
        "main-literal-capture-stage1",
        "program p; begin WriteLn('ABC'); WriteLn(7) end.",
    );
    let got = run_native_forth("main-literal-capture-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "ABC\n7");
}

#[test]
fn selfhost_kpsc_main_reads_encoded_stdin_and_emits_record_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main record smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let emitted_forth = run_selfhost_main_for_input(
        "main-record-stage1",
        include_str!("samples/05_record_with.pas"),
    );
    let got = run_native_forth("main-record-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "33");
}

#[test]
fn selfhost_kpsc_main_handles_identifiers_prefixed_by_read() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main read-prefix smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
var
  aftersemi: integer;
  readingword: integer;
begin
  aftersemi := 0;
  readingword := 0
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-read-prefix-stage1", src);
    assert!(
        emitted_forth.contains(": MAIN"),
        "emitted forth:\n{emitted_forth}"
    );
    assert!(!emitted_forth.contains("PERR"));
    let got = run_native_forth("main-read-prefix-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "");
}

#[test]
fn selfhost_kpsc_main_emits_simple_var_assign_and_writeln_via_ast() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main ast-assign smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
var
  x: integer;
begin
  x := 7;
  WriteLn(x)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-assign-stage1", src);
    assert!(emitted_forth.contains("CREATE ASRV0 0 ,"));
    assert!(emitted_forth.contains("7 ASRV0 PVAR!"));
    assert!(emitted_forth.contains("ASRV0 PVAR@ PWRITE-I32"));
    let got = run_native_forth("main-ast-assign-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "7");
}

#[test]
fn selfhost_kpsc_main_emits_const_idents_via_ast() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main ast-const-ident smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
const
  limit = 7;
var
  x: integer;
begin
  x := limit;
  if x >= limit then
    begin
      WriteLn(limit + 1)
    end
  else
    begin
      WriteLn(0)
    end
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-const-ident-stage1", src);
    assert!(
        emitted_forth.contains("7 ASRV0 PVAR!"),
        "emitted forth:\n{emitted_forth}"
    );
    assert!(
        emitted_forth.contains("ASRV0 PVAR@ 7 >="),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-const-ident-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "8");
}

#[test]
fn selfhost_kpsc_main_handles_var_names_that_shadow_ast_builtin_consts() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main ast-shadowed-var smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
var
  ast_expr_int: array[0..1] of integer;
  expr_idx: integer;
begin
  expr_idx := 1;
  ast_expr_int[expr_idx] := 7;
  if ast_expr_int[expr_idx] > 0 then
    begin
      WriteLn(ast_expr_int[expr_idx])
    end
  else
    begin
      WriteLn(0)
    end
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-shadowed-var-stage1", src);
    assert!(
        !emitted_forth.contains("PERR"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-shadowed-var-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "7");
}

#[test]
fn selfhost_kpsc_main_emits_readln_via_ast() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main ast-readln smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
begin
  ReadLn;
  WriteLn(7)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-readln-stage1", src);
    assert!(
        emitted_forth.contains("PREADLN"),
        "emitted forth:\n{emitted_forth}"
    );
    let got =
        run_native_forth_with_input("main-ast-readln-stage2", &emitted_forth, "ignored line\n");
    assert_eq!(got.trim_end(), "7");
}

#[test]
fn selfhost_kpsc_main_reads_bool_and_real_via_ast() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main ast-read bool/real smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
var
  b: boolean;
  x: real;
begin
  Read(b, x);
  WriteLn(b);
  WriteLn(x + 0.25)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-read-bool-real-stage1", src);
    assert!(
        emitted_forth.contains("PREAD-BOOL"),
        "emitted forth:\n{emitted_forth}"
    );
    assert!(
        emitted_forth.contains("PREAD-F32"),
        "emitted forth:\n{emitted_forth}"
    );
    let got =
        run_native_forth_with_input("main-ast-read-bool-real-stage2", &emitted_forth, "1 1.5\n");
    assert_eq!(got.trim_end(), "TRUE\n1.7500");
}

#[test]
fn selfhost_kpsc_main_handles_identifiers_prefixed_by_builtins() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main builtin-prefix smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
var
  writelnx: integer;
  withhold: integer;
  concatx: integer;
  newer: integer;
  disposex: integer;
  setaddrx: integer;
  rounding: integer;
  position: integer;
begin
  writelnx := 1;
  withhold := 2;
  concatx := 3;
  newer := 4;
  disposex := 5;
  setaddrx := 6;
  rounding := 7;
  position := 8;
  WriteLn(rounding);
  WriteLn(position)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-builtin-prefix-stage1", src);
    assert!(
        emitted_forth.contains(": MAIN"),
        "emitted forth:\n{emitted_forth}"
    );
    assert!(
        !emitted_forth.contains("PERR"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-builtin-prefix-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "7\n8");
}

#[test]
fn selfhost_kpsc_main_handles_general_var_procedure_body() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main general-procedure smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program probe;
var
  x: integer;
procedure Step(var n: integer);
begin
  n := n + 1;
  if n = 2 then
    n := n + 3
  else
    n := n + 0
end;
begin
  x := 1;
  Step(x);
  WriteLn(x)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-general-proc-stage1", src);
    let got = run_native_forth("main-general-proc-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "5");
}

#[test]
fn selfhost_kpsc_main_emits_parameterless_procedure_via_ast() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main parameterless procedure ast smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program mini;
var
  x: integer;
procedure Step();
begin
  x := 5
end;
begin
  x := 1;
  Step();
  WriteLn(x)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-proc-stage1", src);
    assert!(
        emitted_forth.contains(": ASTR"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-proc-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "5");
}

#[test]
fn selfhost_kpsc_main_preserves_nested_call_argument_order_for_value_params() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main nested-call value-param smoke: missing native backend");
        return;
    }

    let src = r#"program nestedvalueargs;
function GetBase(i: integer): integer;
begin
  GetBase := i + 10
end;

function Combine(a: integer; b: integer): integer;
begin
  Combine := a * 100 + b
end;

begin
  WriteLn(Combine(GetBase(2), 7))
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-nested-value-args-stage1", src);
    let got = run_native_forth("main-ast-nested-value-args-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "1207");
}

#[test]
fn selfhost_kpsc_main_preserves_nested_call_argument_order_for_byref_array_params() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main nested-call byref-array smoke: missing native backend");
        return;
    }

    let src = r#"program nestedbyrefargs;
type
  ident_buf = array[0..3] of integer;
var
  field_name: ident_buf;

function GetTypeRef(i: integer): integer;
begin
  GetTypeRef := i + 10
end;

function FindFieldByIdent(type_idx: integer; var name: ident_buf): integer;
begin
  FindFieldByIdent := type_idx + name[0]
end;

function Test(expr_idx: integer): boolean;
begin
  Test := FindFieldByIdent(GetTypeRef(expr_idx), field_name) >= 0
end;

begin
  field_name[0] := 1;
  WriteLn(Test(2));
  WriteLn(FindFieldByIdent(GetTypeRef(2), field_name))
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-nested-byref-args-stage1", src);
    let got = run_native_forth("main-ast-nested-byref-args-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "TRUE\n13");
}

#[test]
fn selfhost_kpsc_main_emits_simple_global_var_via_ast() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main simple global var ast smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let src = r#"program mini;
var
  x: integer;
begin
  x := 1;
  WriteLn(x)
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-global-stage1", src);
    assert!(
        emitted_forth.contains("ASRV0 PVAR!"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-global-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "1");
}

#[test]
fn selfhost_kpsc_main_emits_quote_containing_string_literals_safely() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main quoted-string smoke: missing native backend");
        return;
    }

    let src = r#"program quotedtext;
begin
  WriteLn('  S" TRUE" TYPE')
end."#;
    let emitted_forth = run_selfhost_main_for_input("main-ast-quoted-string-stage1", src);
    let got = run_native_forth("main-ast-quoted-string-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "  S\" TRUE\" TYPE");
}

#[test]
fn selfhost_kpsc_main_compiles_arithmetic_program_via_ast_without_sample_name() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main arithmetic ast smoke: missing native backend");
        return;
    }

    let src = include_str!("../selfhost/kpsc_arith.pas").replacen(
        "program kpsc_arith;",
        "program astprobe;",
        1,
    );
    let emitted_forth = run_preprocessed_selfhost_main_for_input("main-ast-arith-stage1", &src);
    assert!(
        emitted_forth.contains("CREATE ASRV0 0 ,"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-arith-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "14\n3\n2");
}

#[test]
fn selfhost_kpsc_main_compiles_control_program_via_ast_without_sample_name() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main control ast smoke: missing native backend");
        return;
    }

    let src = include_str!("../selfhost/kpsc_ctrl.pas").replacen(
        "program kpsc_ctrl;",
        "program astctrl;",
        1,
    );
    let emitted_forth = run_preprocessed_selfhost_main_for_input("main-ast-ctrl-stage1", &src);
    assert!(
        emitted_forth.contains("CREATE ASRV0 0 ,"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-ctrl-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "12");
}

#[test]
fn selfhost_kpsc_main_compiles_routine_program_via_ast_without_sample_name() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main routine ast smoke: missing native backend");
        return;
    }

    let src = include_str!("../selfhost/kpsc_routines.pas").replacen(
        "program kpsc_routines;",
        "program astroutines;",
        1,
    );
    let emitted_forth = run_preprocessed_selfhost_main_for_input("main-ast-routines-stage1", &src);
    assert!(
        emitted_forth.contains("CREATE ASRV0 0 ,"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-routines-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "9", "emitted forth:\n{emitted_forth}");
}

#[test]
fn selfhost_kpsc_main_compiles_scalar_program_via_ast_without_sample_name() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main scalar ast smoke: missing native backend");
        return;
    }

    let src = include_str!("../selfhost/kpsc_scalar.pas").replacen(
        "program kpsc_scalar;",
        "program astscalar;",
        1,
    );
    let emitted_forth = run_preprocessed_selfhost_main_for_input("main-ast-scalar-stage1", &src);
    assert!(
        emitted_forth.contains("PWRITE-BOOL"),
        "emitted forth:\n{emitted_forth}"
    );
    let got = run_native_forth("main-ast-scalar-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "7\n25\nTRUE\nQ\n66");
}

#[test]
fn selfhost_kpsc_main_compiles_single_source_seed_compiler() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main seed smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let emitted_forth = run_selfhost_main_for_input(
        "main-seed-stage1",
        include_str!("../selfhost/kpsc_seed_hello_single.pas"),
    );
    let hello_forth = run_native_forth_with_input(
        "main-seed-stage2-hello",
        &emitted_forth,
        &encode_seed_ascii_program("program p; begin WriteLn('HELLO') end."),
    );
    let hello_output = run_native_forth("main-seed-stage3-hello", &hello_forth);
    assert_eq!(hello_output.trim_end(), "HELLO");
    let arithmetic_forth = run_native_forth_with_input(
        "main-seed-stage2-arith",
        &emitted_forth,
        &encode_seed_ascii_program(include_str!("samples/02_arithmetic.pas")),
    );
    let arithmetic_output = run_native_forth("main-seed-stage3-arith", &arithmetic_forth);
    assert_eq!(arithmetic_output.trim_end(), "14\n3\n2");
    let record_forth = run_native_forth_with_input(
        "main-seed-stage2-record",
        &emitted_forth,
        &encode_seed_ascii_program(include_str!("samples/05_record_with.pas")),
    );
    let record_output = run_native_forth("main-seed-stage3-record", &record_forth);
    assert_eq!(record_output.trim_end(), "33");
}

#[test]
fn selfhost_preprocessed_kpsc_main_seed_mode_is_name_gated() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main seed name gate smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let renamed_src = include_str!("../selfhost/kpsc_seed_hello_single.pas").replacen(
        "program kpscseedhellosingle;",
        "program kpscseedhellorename;",
        1,
    );
    let emitted_forth =
        run_preprocessed_selfhost_main_for_input("pre-main-seed-name-gate-stage1", &renamed_src);
    assert!(
        !emitted_forth.contains("CREATE kind 0 ,"),
        "renamed seed input should not trigger seed dispatcher:\n{emitted_forth}"
    );
    let got = run_native_forth("pre-main-seed-name-gate-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "H");
}

#[test]
fn selfhost_preprocessed_kpsc_main_compiles_single_source_seed_compiler() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main seed smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let preprocessed_main = preprocess_pascal_file("selfhost/kpsc_main.pas");
    assert!(!preprocessed_main.contains("$I"));
    let emitted_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-seed-stage1",
        include_str!("../selfhost/kpsc_seed_hello_single.pas"),
    );

    let hello_forth = run_native_forth_with_input(
        "pre-main-seed-stage2-hello",
        &emitted_forth,
        &encode_seed_ascii_program("program p; begin WriteLn('HELLO') end."),
    );
    let hello_output = run_native_forth("pre-main-seed-stage3-hello", &hello_forth);
    assert_eq!(hello_output.trim_end(), "HELLO");

    let arithmetic_forth = run_native_forth_with_input(
        "pre-main-seed-stage2-arith",
        &emitted_forth,
        &encode_seed_ascii_program(include_str!("samples/02_arithmetic.pas")),
    );
    let arithmetic_output = run_native_forth("pre-main-seed-stage3-arith", &arithmetic_forth);
    assert_eq!(arithmetic_output.trim_end(), "14\n3\n2");

    let record_forth = run_native_forth_with_input(
        "pre-main-seed-stage2-record",
        &emitted_forth,
        &encode_seed_ascii_program(include_str!("samples/05_record_with.pas")),
    );
    let record_output = run_native_forth("pre-main-seed-stage3-record", &record_forth);
    assert_eq!(record_output.trim_end(), "33");
}

#[test]
fn selfhost_preprocessed_kpsc_main_seed_compiler_accepts_plain_ascii_input() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main plain-ascii seed smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let emitted_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-seed-plain-stage1",
        include_str!("../selfhost/kpsc_seed_hello_single.pas"),
    );

    let hello_forth = run_native_forth_with_input(
        "pre-main-seed-plain-stage2-hello",
        &emitted_forth,
        &encode_ascii_program("program p; begin WriteLn('HELLO') end."),
    );
    let hello_output = run_native_forth("pre-main-seed-plain-stage3-hello", &hello_forth);
    assert_eq!(hello_output.trim_end(), "HELLO");

    let arithmetic_forth = run_native_forth_with_input(
        "pre-main-seed-plain-stage2-arith",
        &emitted_forth,
        &encode_ascii_program(include_str!("samples/02_arithmetic.pas")),
    );
    let arithmetic_output = run_native_forth("pre-main-seed-plain-stage3-arith", &arithmetic_forth);
    assert_eq!(arithmetic_output.trim_end(), "14\n3\n2");
}

#[test]
fn selfhost_preprocessed_kpsc_main_seed_compiler_covers_sample_set() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main seed suite: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let emitted_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-seed-suite-stage1",
        include_str!("../selfhost/kpsc_seed_hello_single.pas"),
    );

    let cases = [
        ("sample01", include_str!("samples/01_hello.pas"), "HELLO"),
        (
            "sample02",
            include_str!("samples/02_arithmetic.pas"),
            "14\n3\n2",
        ),
        (
            "sample03",
            include_str!("samples/03_control_flow.pas"),
            "12",
        ),
        (
            "sample04",
            include_str!("samples/04_subrange_enum_set.pas"),
            "TRUE\n4",
        ),
        ("sample05", include_str!("samples/05_record_with.pas"), "33"),
        (
            "sample06",
            include_str!("samples/06_variant_record.pas"),
            "42",
        ),
        (
            "sample07",
            include_str!("samples/07_pointer_new_dispose.pas"),
            "77\nTRUE",
        ),
        (
            "sample08",
            include_str!("samples/08_addr_setaddr.pas"),
            "456\nTRUE",
        ),
        ("sample09", include_str!("samples/09_array_2d.pas"), "9"),
        ("sample10", include_str!("samples/10_array_4d.pas"), "13"),
        (
            "sample11",
            include_str!("samples/11_conformant_1d.pas"),
            "18",
        ),
        (
            "sample12",
            include_str!("samples/12_conformant_2d.pas"),
            "10",
        ),
        (
            "sample13",
            include_str!("samples/13_string_basic.pas"),
            "ABC\n2",
        ),
        (
            "sample14",
            include_str!("samples/14_string_edit.pas"),
            "ABCD\nAD\nAZD",
        ),
        (
            "sample15",
            include_str!("samples/15_hex_convert.pas"),
            "000000FF\n255",
        ),
        (
            "sample16",
            include_str!("samples/16_real_basic.pas"),
            "3.5000\n4\n3",
        ),
        (
            "sample17",
            include_str!("samples/17_nested_routines.pas"),
            "9",
        ),
        (
            "sample18",
            include_str!("samples/18_case_ranges.pas"),
            "MID",
        ),
        (
            "sample19",
            include_str!("samples/19_set_operations.pas"),
            "TRUE\nTRUE\nTRUE",
        ),
        (
            "sample20",
            include_str!("samples/20_scalar_builtins.pas"),
            "7\n25\nTRUE\nQ\n66",
        ),
        (
            "sample21",
            include_str!("samples/21_multi_value_params.pas"),
            "7\n6",
        ),
        (
            "sample22",
            include_str!("samples/22_param_groups.pas"),
            "9\n10",
        ),
        (
            "sample23",
            include_str!("samples/23_var_value_mix.pas"),
            "17",
        ),
    ];

    for (label, src, expected) in cases {
        eprintln!("running seed suite case: {label}");
        let stage3_forth = run_native_forth_with_input(
            &format!("pre-main-seed-suite-stage2-{label}"),
            &emitted_forth,
            &encode_seed_ascii_program(src),
        );
        let output = run_native_forth(
            &format!("pre-main-seed-suite-stage3-{label}"),
            &stage3_forth,
        );
        assert_eq!(
            output.trim_end(),
            expected,
            "failed seed suite case: {label}"
        );
    }
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_sample_programs_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main direct smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let hello_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-hello",
        "program p; begin WriteLn('HELLO') end.",
    );
    let hello_output = run_native_forth("pre-main-direct-stage2-hello", &hello_forth);
    assert_eq!(hello_output.trim_end(), "HELLO");

    let arithmetic_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-arith",
        include_str!("samples/02_arithmetic.pas"),
    );
    let arithmetic_output = run_native_forth("pre-main-direct-stage2-arith", &arithmetic_forth);
    assert_eq!(arithmetic_output.trim_end(), "14\n3\n2");

    let record_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-record",
        include_str!("samples/05_record_with.pas"),
    );
    let record_output = run_native_forth("pre-main-direct-stage2-record", &record_forth);
    assert_eq!(record_output.trim_end(), "33");
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_control_and_routine_programs_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main control/routine smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let control_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-control",
        include_str!("samples/03_control_flow.pas"),
    );
    let control_output = run_native_forth("pre-main-direct-stage2-control", &control_forth);
    assert_eq!(control_output.trim_end(), "12");

    let routine_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-routine",
        include_str!("samples/17_nested_routines.pas"),
    );
    let routine_output = run_native_forth("pre-main-direct-stage2-routine", &routine_forth);
    assert_eq!(routine_output.trim_end(), "9");
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_string_real_and_case_programs_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main string/real/case smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let string_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-string",
        include_str!("samples/13_string_basic.pas"),
    );
    let string_output = run_native_forth("pre-main-direct-stage2-string", &string_forth);
    assert_eq!(string_output.trim_end(), "ABC\n2");

    let real_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-real",
        include_str!("samples/16_real_basic.pas"),
    );
    let real_output = run_native_forth("pre-main-direct-stage2-real", &real_forth);
    assert_eq!(real_output.trim_end(), "3.5000\n4\n3");

    let case_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-case",
        include_str!("samples/18_case_ranges.pas"),
    );
    let case_output = run_native_forth("pre-main-direct-stage2-case", &case_forth);
    assert_eq!(case_output.trim_end(), "MID");
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_scalar_enumset_and_setops_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main scalar/enumset/setops smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let scalar_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-scalar",
        include_str!("samples/20_scalar_builtins.pas"),
    );
    let scalar_output = run_native_forth("pre-main-direct-stage2-scalar", &scalar_forth);
    assert_eq!(scalar_output.trim_end(), "7\n25\nTRUE\nQ\n66");

    let enumset_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-enumset",
        include_str!("samples/04_subrange_enum_set.pas"),
    );
    let enumset_output = run_native_forth("pre-main-direct-stage2-enumset", &enumset_forth);
    assert_eq!(enumset_output.trim_end(), "TRUE\n4");

    let setops_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-setops",
        include_str!("samples/19_set_operations.pas"),
    );
    let setops_output = run_native_forth("pre-main-direct-stage2-setops", &setops_forth);
    assert_eq!(setops_output.trim_end(), "TRUE\nTRUE\nTRUE");
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_variant_pointer_and_addr_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main variant/pointer/addr smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let variant_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-variant",
        include_str!("samples/06_variant_record.pas"),
    );
    let variant_output = run_native_forth("pre-main-direct-stage2-variant", &variant_forth);
    assert_eq!(variant_output.trim_end(), "42");

    let pointer_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-pointer",
        include_str!("samples/07_pointer_new_dispose.pas"),
    );
    let pointer_output = run_native_forth("pre-main-direct-stage2-pointer", &pointer_forth);
    assert_eq!(pointer_output.trim_end(), "77\nTRUE");

    let addr_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-addr",
        include_str!("samples/08_addr_setaddr.pas"),
    );
    let addr_output = run_native_forth("pre-main-direct-stage2-addr", &addr_forth);
    assert_eq!(addr_output.trim_end(), "456\nTRUE");
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_array_and_conformant_programs_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main array/conformant smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let array2d_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-array2d",
        include_str!("samples/09_array_2d.pas"),
    );
    let array2d_output = run_native_forth("pre-main-direct-stage2-array2d", &array2d_forth);
    assert_eq!(array2d_output.trim_end(), "9");

    let array4d_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-array4d",
        include_str!("samples/10_array_4d.pas"),
    );
    let array4d_output = run_native_forth("pre-main-direct-stage2-array4d", &array4d_forth);
    assert_eq!(array4d_output.trim_end(), "13");

    let conf1d_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-conf1d",
        include_str!("samples/11_conformant_1d.pas"),
    );
    let conf1d_output = run_native_forth("pre-main-direct-stage2-conf1d", &conf1d_forth);
    assert_eq!(conf1d_output.trim_end(), "18");

    let conf2d_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-conf2d",
        include_str!("samples/12_conformant_2d.pas"),
    );
    let conf2d_output = run_native_forth("pre-main-direct-stage2-conf2d", &conf2d_forth);
    assert_eq!(conf2d_output.trim_end(), "10");
}

#[test]
#[ignore = "covered by the aggregate preprocessed direct suite; keep for focused debugging"]
fn selfhost_preprocessed_kpsc_main_compiles_string_edit_and_hex_directly() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main string-edit/hex smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let string_edit_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-string-edit",
        include_str!("samples/14_string_edit.pas"),
    );
    let string_edit_output =
        run_native_forth("pre-main-direct-stage2-string-edit", &string_edit_forth);
    assert_eq!(string_edit_output.trim_end(), "ABCD\nAD\nAZD");

    let hex_forth = run_preprocessed_selfhost_main_for_input(
        "pre-main-direct-stage1-hex",
        include_str!("samples/15_hex_convert.pas"),
    );
    let hex_output = run_native_forth("pre-main-direct-stage2-hex", &hex_forth);
    assert_eq!(hex_output.trim_end(), "000000FF\n255");
}

#[test]
fn selfhost_preprocessed_kpsc_main_direct_suite_covers_sample_set() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping preprocessed selfhost main direct suite: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let selfhost_forth = run_compiler(&selfhost_src);
    let (_work_dir, compiler_bin) =
        build_native_forth_binary("pre-main-direct-suite-stage0", &selfhost_forth);

    let cases = [
        ("hello", include_str!("samples/01_hello.pas"), "HELLO"),
        (
            "arith",
            include_str!("samples/02_arithmetic.pas"),
            "14\n3\n2",
        ),
        ("control", include_str!("samples/03_control_flow.pas"), "12"),
        (
            "enumset",
            include_str!("samples/04_subrange_enum_set.pas"),
            "TRUE\n4",
        ),
        ("record", include_str!("samples/05_record_with.pas"), "33"),
        (
            "variant",
            include_str!("samples/06_variant_record.pas"),
            "42",
        ),
        (
            "pointer",
            include_str!("samples/07_pointer_new_dispose.pas"),
            "77\nTRUE",
        ),
        (
            "addr",
            include_str!("samples/08_addr_setaddr.pas"),
            "456\nTRUE",
        ),
        ("array2d", include_str!("samples/09_array_2d.pas"), "9"),
        ("array4d", include_str!("samples/10_array_4d.pas"), "13"),
        ("conf1d", include_str!("samples/11_conformant_1d.pas"), "18"),
        ("conf2d", include_str!("samples/12_conformant_2d.pas"), "10"),
        (
            "string",
            include_str!("samples/13_string_basic.pas"),
            "ABC\n2",
        ),
        (
            "string-edit",
            include_str!("samples/14_string_edit.pas"),
            "ABCD\nAD\nAZD",
        ),
        (
            "hex",
            include_str!("samples/15_hex_convert.pas"),
            "000000FF\n255",
        ),
        (
            "real",
            include_str!("samples/16_real_basic.pas"),
            "3.5000\n4\n3",
        ),
        (
            "real-generic",
            include_str!("samples/24_real_generic.pas"),
            "5\n7.2500\n7\n3.5000",
        ),
        (
            "real-mixed",
            include_str!("samples/25_real_mixed.pas"),
            "7.0000\n8.0000\n8.0000\n5.0000\n14.0000",
        ),
        (
            "set-range",
            include_str!("samples/26_set_literal_range.pas"),
            "FALSE\nTRUE\nTRUE\nTRUE",
        ),
        (
            "real-exponent",
            include_str!("samples/27_real_exponent.pas"),
            "125.0000\n0.1250\n5.0000\n-25.0000",
        ),
        (
            "subrange-set-range",
            include_str!("samples/28_subrange_set_range.pas"),
            "TRUE\nTRUE",
        ),
        (
            "subrange-set-int-lits",
            include_str!("samples/29_subrange_set_int_literals.pas"),
            "TRUE\nTRUE",
        ),
        (
            "variant-overlap",
            include_str!("samples/30_variant_overlap.pas"),
            "12\n7\n30",
        ),
        (
            "subrange-enum-bounds",
            include_str!("samples/31_subrange_enum_bounds.pas"),
            "TRUE\nFALSE",
        ),
        (
            "subrange-named-bounds",
            include_str!("samples/32_subrange_named_bounds.pas"),
            "5",
        ),
        (
            "real-large-exponent",
            include_str!("samples/33_real_large_exponent.pas"),
            "10000000000.0000\n0.0000",
        ),
        (
            "routine",
            include_str!("samples/17_nested_routines.pas"),
            "9",
        ),
        ("case", include_str!("samples/18_case_ranges.pas"), "MID"),
        (
            "setops",
            include_str!("samples/19_set_operations.pas"),
            "TRUE\nTRUE\nTRUE",
        ),
        (
            "scalar",
            include_str!("samples/20_scalar_builtins.pas"),
            "7\n25\nTRUE\nQ\n66",
        ),
        (
            "multi-value-params",
            include_str!("samples/21_multi_value_params.pas"),
            "7\n6",
        ),
        (
            "param-groups",
            include_str!("samples/22_param_groups.pas"),
            "9\n10",
        ),
        (
            "var-value-mix",
            include_str!("samples/23_var_value_mix.pas"),
            "17",
        ),
    ];

    for (label, src, expected) in cases {
        eprintln!("running direct suite case: {label}");
        let encoded = encode_ascii_program(src);
        let emitted_forth = run_native_binary_with_input(&compiler_bin, &encoded);
        let output = run_native_forth(&format!("pre-main-direct-suite-{label}"), &emitted_forth);
        assert_eq!(output.trim_end(), expected, "failed case: {label}");
    }
}

#[test]
fn selfhost_preprocessed_kpsc_main_selfcompile_reaches_read_source_loop() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost self-compile smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "preprocessed-selfcompile-stage1",
        &flat_selfhost,
    );

    assert!(
        !stage1.contains("parse error"),
        "stage1 still failed while parsing full preprocessed selfhost source.\n{}",
        stage1
    );
    assert!(
        stage1.contains(": MAIN"),
        "stage1 did not emit a Forth entrypoint after parsing full selfhost source.\n{}",
        stage1
    );
}

#[test]
fn selfhost_preprocessed_kpsc_main_selfcompile_reaches_lexer_routines() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost self-compile smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "preprocessed-selfcompile-lexer-stage1",
        &flat_selfhost,
    );

    assert!(
        !stage1.contains("parse error"),
        "stage1 lexer/parser still rejected the full preprocessed selfhost source.\n{}",
        stage1
    );
}

#[test]
fn selfhost_preprocessed_kpsc_main_selfcompile_reaches_parser_helpers() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost self-compile smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "preprocessed-selfcompile-parser-stage1",
        &flat_selfhost,
    );

    assert!(
        stage1.lines().any(|line| line.starts_with(": ")),
        "stage1 did not emit any Forth words after accepting full selfhost source.\n{}",
        stage1
    );
}

#[test]
fn selfhost_preprocessed_kpsc_main_selfcompile_reaches_write_and_expect_helpers() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost self-compile smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1_src = run_compiler(&flat_selfhost);
    let (_stage1_work_dir, stage1_bin_path) =
        build_native_forth_binary("preprocessed-selfcompile-stage1-bin", &stage1_src);

    let encoded = encode_ascii_program(&flat_selfhost);
    let stage2 = run_native_binary_with_input(&stage1_bin_path, &encoded);
    assert!(
        !stage2.contains("parse error"),
        "stage2 still failed while recompiling the full preprocessed selfhost source.\n{}",
        stage2
    );
    assert!(
        stage2.contains(": MAIN"),
        "stage2 did not emit a complete Forth program for the full preprocessed selfhost source.\n{}",
        stage2
    );

    let (_stage2_work_dir, stage2_bin_path) =
        build_native_forth_binary("preprocessed-selfcompile-stage2-bin", &stage2);

    let stage3 = run_native_binary_with_input(&stage2_bin_path, &encoded);
    assert!(
        !stage3.contains("parse error"),
        "stage3 still failed while recompiling the full preprocessed selfhost source.\n{}",
        stage3
    );
    assert!(
        stage3.contains(": MAIN"),
        "stage3 did not emit a complete Forth program for the full preprocessed selfhost source.\n{}",
        stage3
    );
}

#[test]
fn selfhost_preprocessed_kpsc_main_stage3_forth_is_native_backend_clean() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost stage3 native-cleanliness smoke: missing native backend");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1_src = run_compiler(&flat_selfhost);
    let (_stage1_work_dir, stage1_bin_path) =
        build_native_forth_binary("preprocessed-selfcompile-stage1-native-clean-bin", &stage1_src);

    let encoded = encode_ascii_program(&flat_selfhost);
    let stage2 = run_native_binary_with_input(&stage1_bin_path, &encoded);
    let (_stage2_work_dir, stage2_bin_path) = build_native_forth_binary(
        "preprocessed-selfcompile-stage2-native-clean-bin",
        &stage2,
    );

    let stage3 = run_native_binary_with_input(&stage2_bin_path, &encoded);
    assert!(
        !stage3.as_bytes().contains(&0),
        "stage3 still contains embedded NUL bytes.\n{}",
        stage3
    );

    let (_stage3_work_dir, _stage3_bin_path) =
        build_native_forth_binary("preprocessed-selfcompile-stage3-native-clean-bin", &stage3);
}

#[test]
fn selfhost_preprocessed_kpsc_main_fresh_stage2_compiler_handles_generic_arithmetic_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping fresh stage2 generic arithmetic smoke: missing native backend");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1_src = run_compiler(&flat_selfhost);
    let (_stage1_work_dir, stage1_bin_path) =
        build_native_forth_binary("preprocessed-selfcompile-stage1-fresh-arith-bin", &stage1_src);

    let encoded_selfhost = encode_ascii_program(&flat_selfhost);
    let stage2 = run_native_binary_with_input(&stage1_bin_path, &encoded_selfhost);
    let (_stage2_work_dir, stage2_bin_path) =
        build_native_forth_binary("preprocessed-selfcompile-stage2-fresh-arith-bin", &stage2);

    let src = r#"program p;
var
  i: integer;
begin
  i := 2 + 3 * 4;
  WriteLn(i);
  WriteLn(17 div 5);
  WriteLn(17 mod 5)
end."#;
    let encoded = encode_ascii_program(src);
    let emitted_forth = run_native_binary_with_input(&stage2_bin_path, &encoded);
    let got = run_native_forth("preprocessed-fresh-stage2-generic-arith", &emitted_forth);
    assert_eq!(got.trim_end(), "14\n3\n2");
}

#[test]
fn selfhost_kpsc_emits_and_runs_arithmetic_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost arithmetic smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_arith.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("arith", &selfhost_forth);
    assert_eq!(got.trim_end(), "14\n3\n2");
}

#[test]
fn selfhost_kpsc_emits_and_runs_control_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost control smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_ctrl.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("ctrl", &selfhost_forth);
    assert_eq!(got.trim_end(), "12");
}

#[test]
fn selfhost_kpsc_emits_and_runs_routine_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost routines smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_routines.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("routine", &selfhost_forth);
    assert_eq!(got.trim_end(), "9");
}

#[test]
fn selfhost_kpsc_emits_and_runs_record_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost record smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_record.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("record", &selfhost_forth);
    assert_eq!(got.trim_end(), "33");
}

#[test]
fn selfhost_kpsc_emits_and_runs_string_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost string smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_string.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("string", &selfhost_forth);
    assert_eq!(got.trim_end(), "ABC\n2");
}

#[test]
fn selfhost_kpsc_emits_and_runs_string_edit_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost string-edit smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_string_edit.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("string-edit", &selfhost_forth);
    assert_eq!(got.trim_end(), "ABCD\nAD\nAZD");
}

#[test]
fn selfhost_kpsc_emits_and_runs_hex_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost hex smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_hex.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("hex", &selfhost_forth);
    assert_eq!(got.trim_end(), "000000FF\n255");
}

#[test]
fn selfhost_kpsc_emits_and_runs_real_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost real smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_real.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("real", &selfhost_forth);
    assert_eq!(got.trim_end(), "3.5000\n4\n3");
}

#[test]
fn selfhost_kpsc_emits_and_runs_case_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost case smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_case.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("case", &selfhost_forth);
    assert_eq!(got.trim_end(), "MID");
}

#[test]
fn selfhost_kpsc_emits_and_runs_scalar_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost scalar smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_scalar.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("scalar", &selfhost_forth);
    assert_eq!(got.trim_end(), "7\n25\nTRUE\nQ\n66");
}

#[test]
fn selfhost_kpsc_emits_and_runs_array2d_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost array2d smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_array2d.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("array2d", &selfhost_forth);
    assert_eq!(got.trim_end(), "9");
}

#[test]
fn selfhost_kpsc_emits_and_runs_array4d_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost array4d smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_array4d.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("array4d", &selfhost_forth);
    assert_eq!(got.trim_end(), "13");
}

#[test]
fn selfhost_kpsc_emits_and_runs_variant_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost variant smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_variant.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("variant", &selfhost_forth);
    assert_eq!(got.trim_end(), "42");
}

#[test]
fn selfhost_kpsc_emits_and_runs_pointer_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost pointer smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_pointer.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("pointer", &selfhost_forth);
    assert_eq!(got.trim_end(), "77\nTRUE");
}

#[test]
fn selfhost_kpsc_emits_and_runs_addr_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost addr smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_addr.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("addr", &selfhost_forth);
    assert_eq!(got.trim_end(), "456\nTRUE");
}

#[test]
fn selfhost_kpsc_emits_and_runs_enumset_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost enumset smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_enumset.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("enumset", &selfhost_forth);
    assert_eq!(got.trim_end(), "TRUE\n4");
}

#[test]
fn selfhost_kpsc_emits_and_runs_conf1d_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost conf1d smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_conf1d.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("conf1d", &selfhost_forth);
    assert_eq!(got.trim_end(), "18");
}

#[test]
fn selfhost_kpsc_emits_and_runs_conf2d_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost conf2d smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_conf2d.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("conf2d", &selfhost_forth);
    assert_eq!(got.trim_end(), "10");
}

#[test]
fn selfhost_kpsc_emits_and_runs_setops_program() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost setops smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let selfhost_src = include_str!("../selfhost/kpsc_setops.pas");
    let selfhost_forth = run_compiler(selfhost_src);
    let got = run_native_forth("setops", &selfhost_forth);
    assert_eq!(got.trim_end(), "TRUE\nTRUE\nTRUE");
}

// --- selfhost compiler (kpsc_main) compiles each feature program ---

#[test]
fn selfhost_kpsc_main_compiles_arith_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main arith feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-arith",
        include_str!("../selfhost/kpsc_arith.pas"),
    );
    let got = run_native_forth("main-feat-arith-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "14\n3\n2",
        "arith feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_ctrl_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main ctrl feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-ctrl",
        include_str!("../selfhost/kpsc_ctrl.pas"),
    );
    let got = run_native_forth("main-feat-ctrl-run", &stage1);
    assert_eq!(got.trim_end(), "12", "ctrl feature via selfhost compiler");
}

#[test]
fn selfhost_kpsc_main_compiles_routines_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main routines feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-routines",
        include_str!("../selfhost/kpsc_routines.pas"),
    );
    let got = run_native_forth("main-feat-routines-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "9",
        "routines feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_record_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main record feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-record",
        include_str!("../selfhost/kpsc_record.pas"),
    );
    let got = run_native_forth("main-feat-record-run", &stage1);
    assert_eq!(got.trim_end(), "33", "record feature via selfhost compiler");
}

#[test]
fn selfhost_kpsc_main_compiles_variant_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main variant feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-variant",
        include_str!("../selfhost/kpsc_variant.pas"),
    );
    let got = run_native_forth("main-feat-variant-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "42",
        "variant feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_variant_overlap_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main variant overlap feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-variant-overlap",
        include_str!("samples/30_variant_overlap.pas"),
    );
    let got = run_native_forth("main-feat-variant-overlap-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "12\n7\n30",
        "variant overlap via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_enum_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange enum bounds feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-enum-bounds",
        include_str!("samples/31_subrange_enum_bounds.pas"),
    );
    let got = run_native_forth("main-feat-subrange-enum-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nFALSE",
        "subrange enum bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_named_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange named bounds feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-named-bounds",
        include_str!("samples/32_subrange_named_bounds.pas"),
    );
    let got = run_native_forth("main-feat-subrange-named-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "5",
        "subrange named bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_arithmetic_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange arithmetic bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program subrangearith;
type
  small = 1 + 1 .. 2 * 3;
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-subrange-arith-bounds", src);
    let got = run_native_forth("main-feat-subrange-arith-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange arithmetic bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_arithmetic_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array arithmetic bounds feature: missing native backend");
        return;
    }
    let src = r#"program arrayarith;
type
  arr = array[1 + 1 .. 2 * 2] of integer;
var
  a: arr;
begin
  a[2] := 10;
  a[4] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[2] + a[4])
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-array-arith-bounds", src);
    let got = run_native_forth("main-feat-array-arith-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "2\n4\n30",
        "array arithmetic bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_const_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange const bounds feature: missing native backend");
        return;
    }
    let src = r#"program subrangeconst;
const
  lo = 2;
  hi = 6;
type
  small = lo .. hi;
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-subrange-const-bounds", src);
    let got = run_native_forth("main-feat-subrange-const-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange const bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_const_arithmetic_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main array const arithmetic bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program arrayconstarith;
const
  base = 1;
  span = 2;
type
  arr = array[base + 1 .. span * 2] of integer;
var
  a: arr;
begin
  a[2] := 10;
  a[4] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[2] + a[4])
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-array-const-arith-bounds", src);
    let got = run_native_forth("main-feat-array-const-arith-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "2\n4\n30",
        "array const arithmetic bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_ord_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange ord bounds feature: missing native backend");
        return;
    }
    let src = r#"program subrangeord;
const
  base = 1;
type
  small = base + 1 .. (Ord(Chr(54)) - 48);
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-subrange-ord-bounds", src);
    let got = run_native_forth("main-feat-subrange-ord-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange ord bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_parenthesized_ord_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange parenthesized ord bounds feature: missing native backend");
        return;
    }
    let src = r#"program subrangeparenord;
type
  small = (1 + 1) .. (Ord(Chr(54)) - 48);
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-subrange-paren-ord-bounds", src);
    let got = run_native_forth("main-feat-subrange-paren-ord-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange parenthesized ord bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_parenthesized_ident_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange parenthesized ident bounds feature: missing native backend");
        return;
    }
    let src = r#"program subrangeparenident;
const
  base = 1;
type
  small = (base + 1) .. 6;
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-paren-ident-bounds",
        src,
    );
    let got = run_native_forth("main-feat-subrange-paren-ident-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange parenthesized ident bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_parenthesized_ident_ord_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange parenthesized ident ord bounds feature: missing native backend");
        return;
    }
    let src = r#"program subrangeparenidentord;
const
  base = 1;
type
  small = (base + Ord(Chr(49))) .. 6;
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-paren-ident-ord-bounds",
        src,
    );
    let got = run_native_forth("main-feat-subrange-paren-ident-ord-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange parenthesized ident ord bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_parenthesized_ord_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main array parenthesized ord bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program arrayord;
type
  arr = array[(1 + 1) .. (Ord(Chr(52)) - 48)] of integer;
var
  a: arr;
begin
  a[2] := 10;
  a[4] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[2] + a[4])
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-array-paren-ord-bounds", src);
    let got = run_native_forth("main-feat-array-paren-ord-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "2\n4\n30",
        "array parenthesized ord bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_const_ord_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange const ord bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program subrangeconstord;
const
  lo = (1 + 1);
  hi = Ord(Chr(54)) - 48;
type
  small = lo .. hi;
var
  s: set of small;
begin
  s := [2, 6];
  WriteLn(2 in s);
  WriteLn(6 in s)
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-subrange-const-ord-bounds", src);
    let got = run_native_forth("main-feat-subrange-const-ord-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange const ord bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_const_parenthesized_ord_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array const parenthesized ord bounds feature: missing native backend");
        return;
    }
    let src = r#"program arrayconstparenord;
const
  base = (1 + 1);
  limit = Ord(Chr(52)) - 48;
type
  arr = array[base .. limit] of integer;
var
  a: arr;
begin
  a[2] := 10;
  a[4] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[2] + a[4])
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-array-const-paren-ord-bounds",
        src,
    );
    let got = run_native_forth("main-feat-array-const-paren-ord-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "2\n4\n30",
        "array const parenthesized ord bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_const_div_mod_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange const div/mod bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program subrangeconstdivmod;
const
  lo = 9 div 3;
  hi = 20 mod 7 + 4;
type
  small = lo .. hi;
var
  s: set of small;
begin
  s := [3, 10];
  WriteLn(3 in s);
  WriteLn(10 in s)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-const-div-mod-bounds",
        src,
    );
    let got = run_native_forth("main-feat-subrange-const-div-mod-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange const div/mod bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_const_div_mod_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main array const div/mod bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program arrayconstdivmod;
const
  lo = 9 div 3;
  hi = 20 mod 7 + 4;
type
  arr = array[lo .. hi] of integer;
var
  a: arr;
begin
  a[3] := 10;
  a[10] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[3] + a[10])
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-array-const-div-mod-bounds",
        src,
    );
    let got = run_native_forth("main-feat-array-const-div-mod-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "3\n10\n30",
        "array const div/mod bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_const_signed_precedence_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange const signed precedence bounds feature: missing native backend");
        return;
    }
    let src = r#"program subrangeconstsigned;
const
  lo = -(1) + 3;
  hi = 2 * 3 - 1;
type
  small = lo .. hi;
var
  s: set of small;
begin
  s := [2, 5];
  WriteLn(2 in s);
  WriteLn(5 in s)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-const-signed-precedence-bounds",
        src,
    );
    let got = run_native_forth(
        "main-feat-subrange-const-signed-precedence-bounds-run",
        &stage1,
    );
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange const signed precedence bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_const_signed_precedence_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array const signed precedence bounds feature: missing native backend");
        return;
    }
    let src = r#"program arrayconstsigned;
const
  lo = -(1) + 3;
  hi = 2 * 3 - 1;
type
  arr = array[lo .. hi] of integer;
var
  a: arr;
begin
  a[2] := 10;
  a[5] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[2] + a[5])
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-array-const-signed-precedence-bounds",
        src,
    );
    let got = run_native_forth(
        "main-feat-array-const-signed-precedence-bounds-run",
        &stage1,
    );
    assert_eq!(
        got.trim_end(),
        "2\n5\n30",
        "array const signed precedence bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_char_const_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange char const bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program subrangecharconst;
const
  lo = 'A';
  hi = #67;
type
  letters = lo .. hi;
var
  s: set of letters;
begin
  s := ['A', 'C'];
  WriteLn('A' in s);
  WriteLn('C' in s)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-char-const-bounds",
        src,
    );
    let got = run_native_forth("main-feat-subrange-char-const-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange char const bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_char_const_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array char const bounds feature: missing native backend");
        return;
    }
    let src = r#"program arraycharconst;
const
  lo = 'A';
  hi = #67;
type
  arr = array[lo .. hi] of integer;
var
  a: arr;
begin
  a['A'] := 10;
  a['C'] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a['A'] + a['C'])
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-array-char-const-bounds", src);
    let got = run_native_forth("main-feat-array-char-const-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "65\n67\n30",
        "array char const bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_bool_const_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange bool const bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program subrangeboolconst;
const
  lo = false;
  hi = true;
type
  flags = lo .. hi;
var
  s: set of flags;
begin
  s := [false, true];
  WriteLn(false in s);
  WriteLn(true in s)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-bool-const-bounds",
        src,
    );
    let got = run_native_forth("main-feat-subrange-bool-const-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange bool const bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_bool_const_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array bool const bounds feature: missing native backend");
        return;
    }
    let src = r#"program arrayboolconst;
const
  lo = false;
  hi = true;
type
  arr = array[lo .. hi] of integer;
var
  a: arr;
begin
  a[false] := 10;
  a[true] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[false] + a[true])
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-array-bool-const-bounds", src);
    let got = run_native_forth("main-feat-array-bool-const-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "0\n1\n30",
        "array bool const bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_named_type_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange named type bounds feature: missing native backend"
        );
        return;
    }
    let src = r#"program subrangenamedtype;
type
  base_lo = 3..5;
  base_hi = 7..9;
  span = base_lo..base_hi;
var
  x: span;
begin
  x := 9;
  WriteLn(x)
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-named-type-bounds",
        src,
    );
    let got = run_native_forth("main-feat-subrange-named-type-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "9",
        "subrange named type bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array_named_type_bounds_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array named type bounds feature: missing native backend");
        return;
    }
    let src = r#"program arraynamedtype;
type
  base_lo = 3..5;
  base_hi = 7..9;
  arr = array[base_lo..base_hi] of integer;
var
  a: arr;
begin
  a[3] := 10;
  a[9] := 20;
  WriteLn(Low(a));
  WriteLn(High(a));
  WriteLn(a[3] + a[9])
end."#;
    let stage1 =
        cached_preprocessed_selfhost_main_stage1_output("main-feat-array-named-type-bounds", src);
    let got = run_native_forth("main-feat-array-named-type-bounds-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "3\n9\n30",
        "array named type bounds via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_real_large_exponent_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main real large exponent feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-real-large-exponent",
        include_str!("samples/33_real_large_exponent.pas"),
    );
    let got = run_native_forth("main-feat-real-large-exponent-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "10000000000.0000\n0.0000",
        "real large exponent via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_pointer_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main pointer feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-pointer",
        include_str!("../selfhost/kpsc_pointer.pas"),
    );
    let got = run_native_forth("main-feat-pointer-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "77\nTRUE",
        "pointer feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_addr_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main addr feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-addr",
        include_str!("../selfhost/kpsc_addr.pas"),
    );
    let got = run_native_forth("main-feat-addr-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "456\nTRUE",
        "addr feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_array2d_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array2d feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-array2d",
        include_str!("../selfhost/kpsc_array2d.pas"),
    );
    let got = run_native_forth("main-feat-array2d-run", &stage1);
    assert_eq!(got.trim_end(), "9", "array2d feature via selfhost compiler");
}

#[test]
fn selfhost_kpsc_main_compiles_array4d_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main array4d feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-array4d",
        include_str!("../selfhost/kpsc_array4d.pas"),
    );
    let got = run_native_forth("main-feat-array4d-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "13",
        "array4d feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_conf1d_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main conf1d feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-conf1d",
        include_str!("../selfhost/kpsc_conf1d.pas"),
    );
    let got = run_native_forth("main-feat-conf1d-run", &stage1);
    assert_eq!(got.trim_end(), "18", "conf1d feature via selfhost compiler");
}

#[test]
fn selfhost_kpsc_main_compiles_conf2d_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main conf2d feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-conf2d",
        include_str!("../selfhost/kpsc_conf2d.pas"),
    );
    let got = run_native_forth("main-feat-conf2d-run", &stage1);
    assert_eq!(got.trim_end(), "10", "conf2d feature via selfhost compiler");
}

#[test]
fn selfhost_kpsc_main_compiles_string_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main string feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-string",
        include_str!("../selfhost/kpsc_string.pas"),
    );
    let got = run_native_forth("main-feat-string-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "ABC\n2",
        "string feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_string_edit_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main string-edit feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-string-edit",
        include_str!("../selfhost/kpsc_string_edit.pas"),
    );
    let got = run_native_forth("main-feat-string-edit-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "ABCD\nAD\nAZD",
        "string-edit feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_string_literal_hextoint_expr_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main string literal HexToInt expr feature: missing native backend"
        );
        return;
    }
    let src = r#"program lithextoint;
begin
  WriteLn(HexToInt('00FF'))
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output("main-feat-lit-hextoint", src);
    let got = run_native_forth("main-feat-lit-hextoint-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "255",
        "string literal HexToInt expr via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_string_literal_pos_expr_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main string literal Pos expr feature: missing native backend");
        return;
    }
    let src = r#"program litpos;
begin
  WriteLn(Pos('BC', 'ABCD'))
end."#;
    let stage1 = cached_preprocessed_selfhost_main_stage1_output("main-feat-lit-pos", src);
    let got = run_native_forth("main-feat-lit-pos-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "2",
        "string literal Pos expr via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_hex_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main hex feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-hex",
        include_str!("../selfhost/kpsc_hex.pas"),
    );
    let got = run_native_forth("main-feat-hex-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "000000FF\n255",
        "hex feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_real_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main real feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-real",
        include_str!("../selfhost/kpsc_real.pas"),
    );
    let got = run_native_forth("main-feat-real-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "3.5000\n4\n3",
        "real feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_generic_real_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main generic real feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-real-generic",
        include_str!("samples/24_real_generic.pas"),
    );
    let got = run_native_forth("main-feat-real-generic-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "5\n7.2500\n7\n3.5000",
        "generic real feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_mixed_real_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main mixed real feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-real-mixed",
        include_str!("samples/25_real_mixed.pas"),
    );
    let got = run_native_forth("main-feat-real-mixed-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "7.0000\n8.0000\n8.0000\n5.0000\n14.0000",
        "mixed real feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_set_range_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main set range feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-set-range",
        include_str!("samples/26_set_literal_range.pas"),
    );
    let got = run_native_forth("main-feat-set-range-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "FALSE\nTRUE\nTRUE\nTRUE",
        "set range feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_real_exponent_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main real exponent feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-real-exponent",
        include_str!("samples/27_real_exponent.pas"),
    );
    let got = run_native_forth("main-feat-real-exponent-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "125.0000\n0.1250\n5.0000\n-25.0000",
        "real exponent feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_set_range_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main subrange set range feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-set-range",
        include_str!("samples/28_subrange_set_range.pas"),
    );
    let got = run_native_forth("main-feat-subrange-set-range-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange set range feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_subrange_set_int_literal_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!(
            "skipping selfhost main subrange set int literal feature: missing native backend"
        );
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-subrange-set-int-lits",
        include_str!("samples/29_subrange_set_int_literals.pas"),
    );
    let got = run_native_forth("main-feat-subrange-set-int-lits-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE",
        "subrange set int literal feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_case_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main case feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-case",
        include_str!("../selfhost/kpsc_case.pas"),
    );
    let got = run_native_forth("main-feat-case-run", &stage1);
    assert_eq!(got.trim_end(), "MID", "case feature via selfhost compiler");
}

#[test]
fn selfhost_kpsc_main_compiles_enumset_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main enumset feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-enumset",
        include_str!("../selfhost/kpsc_enumset.pas"),
    );
    let got = run_native_forth("main-feat-enumset-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\n4",
        "enumset feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_setops_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main setops feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-setops",
        include_str!("../selfhost/kpsc_setops.pas"),
    );
    let got = run_native_forth("main-feat-setops-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "TRUE\nTRUE\nTRUE",
        "setops feature via selfhost compiler"
    );
}

#[test]
fn selfhost_kpsc_main_compiles_scalar_feature() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost main scalar feature: missing native backend");
        return;
    }
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "main-feat-scalar",
        include_str!("../selfhost/kpsc_scalar.pas"),
    );
    let got = run_native_forth("main-feat-scalar-run", &stage1);
    assert_eq!(
        got.trim_end(),
        "7\n25\nTRUE\nQ\n66",
        "scalar feature via selfhost compiler"
    );
}

// ---------------------------------------------------------------------------
// Stage2: selfhost compiler compiled by stage1
// ---------------------------------------------------------------------------

fn cached_stage2_forth() -> String {
    let selfhost_src = preprocess_pascal_file("selfhost/kpsc_main.pas");
    cached_preprocessed_selfhost_main_stage1_output("stage2-compiler", &selfhost_src)
}

#[test]
fn selfhost_stage2_compiles_feature_programs() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping stage2 feature suite: missing native backend");
        return;
    }

    let stage2_forth = cached_stage2_forth();
    assert!(
        stage2_forth.contains(": MAIN"),
        "stage2 did not emit a Forth entrypoint\n{}",
        &stage2_forth[..stage2_forth.len().min(2000)]
    );

    let (_work_dir, stage2_bin) = build_native_forth_binary("stage2-compiler-bin", &stage2_forth);

    let cases = [
        ("arith", include_str!("../selfhost/kpsc_arith.pas"), "14\n3\n2"),
        (
            "scalar",
            include_str!("../selfhost/kpsc_scalar.pas"),
            "7\n25\nTRUE\nQ\n66",
        ),
        ("ctrl", include_str!("../selfhost/kpsc_ctrl.pas"), "12"),
        (
            "routines",
            include_str!("../selfhost/kpsc_routines.pas"),
            "9",
        ),
        ("record", include_str!("../selfhost/kpsc_record.pas"), "33"),
        (
            "string",
            include_str!("../selfhost/kpsc_string.pas"),
            "ABC\n2",
        ),
    ];

    for (label, src, expected) in cases {
        eprintln!("stage2 compiling: {label}");
        let encoded = encode_ascii_program(src);
        let emitted_forth = run_native_binary_with_input(&stage2_bin, &encoded);
        let got = run_native_forth(&format!("stage2-feat-{label}"), &emitted_forth);
        assert_eq!(got.trim_end(), expected, "stage2 failed case: {label}");
    }
}

#[test]
fn selfhost_stage2_string_feature_progression() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping stage2 string progression suite: missing native backend");
        return;
    }

    let stage2_forth = cached_stage2_forth();
    let (_work_dir, stage2_bin) = build_native_forth_binary("stage2-string-progression-bin", &stage2_forth);

    let cases = [
        (
            "subrange_type_only",
            r#"program p;
type
  small = 1..16;
begin
  WriteLn(1)
end."#,
            "1",
        ),
        (
            "int_array_type_only",
            r#"program p;
type
  int16 = array[16] of integer;
begin
  WriteLn(1)
end."#,
            "1",
        ),
        (
            "array_type_only",
            r#"program p;
type
  str16 = array[16] of char;
begin
  WriteLn(1)
end."#,
            "1",
        ),
        (
            "array_vars_only",
            r#"program p;
type
  str16 = array[16] of char;
var
  s: str16;
  needle: str16;
begin
  WriteLn(1)
end."#,
            "1",
        ),
        (
            "first_string_assign",
            r#"program p;
type
  str16 = array[16] of char;
var
  s: str16;
begin
  s := 'ABC';
  WriteLn(1)
end."#,
            "1",
        ),
        (
            "second_string_assign",
            r#"program p;
type
  str16 = array[16] of char;
var
  s: str16;
  needle: str16;
begin
  s := 'ABC';
  needle := 'BC';
  WriteLn(1)
end."#,
            "1",
        ),
        (
            "full_string_feature",
            include_str!("../selfhost/kpsc_string.pas"),
            "ABC\n2",
        ),
    ];

    for (label, src, expected) in cases {
        eprintln!("stage2 string progression: {label}");
        let encoded = encode_ascii_program(src);
        let emitted_forth = run_native_binary_with_input(&stage2_bin, &encoded);
        let got = run_native_forth(&format!("stage2-string-progression-{label}"), &emitted_forth);
        assert_eq!(got.trim_end(), expected, "stage2 string progression failed: {label}");
    }
}

#[test]
fn selfhost_stage2_compiles_sample_programs() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping stage2 sample suite: missing native backend");
        return;
    }

    let stage2_forth = cached_stage2_forth();
    let (_work_dir, stage2_bin) = build_native_forth_binary("stage2-samples-bin", &stage2_forth);

    let cases = [
        ("hello", include_str!("samples/01_hello.pas"), "HELLO"),
        (
            "arith",
            include_str!("samples/02_arithmetic.pas"),
            "14\n3\n2",
        ),
        ("control", include_str!("samples/03_control_flow.pas"), "12"),
        ("record", include_str!("samples/05_record_with.pas"), "33"),
        (
            "routine",
            include_str!("samples/17_nested_routines.pas"),
            "9",
        ),
        (
            "scalar",
            include_str!("samples/20_scalar_builtins.pas"),
            "7\n25\nTRUE\nQ\n66",
        ),
    ];

    for (label, src, expected) in cases {
        eprintln!("stage2 sample: {label}");
        let encoded = encode_ascii_program(src);
        let emitted_forth = run_native_binary_with_input(&stage2_bin, &encoded);
        let got = run_native_forth(&format!("stage2-sample-{label}"), &emitted_forth);
        assert_eq!(got.trim_end(), expected, "stage2 sample failed: {label}");
    }
}
