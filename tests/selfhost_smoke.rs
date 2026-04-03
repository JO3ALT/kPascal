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

fn parse_i32_output_lines(output: &str) -> Vec<i32> {
    output
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            line.trim()
                .parse::<i32>()
                .unwrap_or_else(|err| panic!("expected integer output line `{line}`: {err}"))
        })
        .collect()
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
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    selfhost_src.hash(&mut hasher);
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
    bin_path.hash(&mut hasher);
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
    assert!(emitted_forth.contains("0 aftersemi PVAR!"));
    assert!(emitted_forth.contains("0 readingword PVAR!"));
    assert!(!emitted_forth.contains("PERR"));
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
    assert!(emitted_forth.contains("1 writelnx PVAR!"));
    assert!(emitted_forth.contains("2 withhold PVAR!"));
    assert!(emitted_forth.contains("3 concatx PVAR!"));
    assert!(emitted_forth.contains("4 newer PVAR!"));
    assert!(emitted_forth.contains("5 disposex PVAR!"));
    assert!(emitted_forth.contains("6 setaddrx PVAR!"));
    assert!(emitted_forth.contains("7 rounding PVAR!"));
    assert!(emitted_forth.contains("8 position PVAR!"));
    assert!(emitted_forth.contains("rounding PVAR@ PWRITE-I32"));
    assert!(emitted_forth.contains("position PVAR@ PWRITE-I32"));
    assert!(!emitted_forth.contains("PERR"));
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
#[ignore = "focused self-compile progress check"]
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
#[ignore = "focused self-compile progress check"]
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
#[ignore = "focused self-compile progress check"]
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
#[ignore = "focused self-compile progress check"]
fn selfhost_preprocessed_kpsc_main_selfcompile_reaches_write_and_expect_helpers() {
    let _guard = selfhost_serial_guard();
    if !has_selfhost_native_backend() {
        eprintln!("skipping selfhost self-compile smoke: missing ../kFORTHc/target/release/kforthc, llc, clang, or runtime.c");
        return;
    }

    let flat_selfhost = preprocess_pascal_file("selfhost/kpsc_main.pas");
    let stage1 = cached_preprocessed_selfhost_main_stage1_output(
        "preprocessed-selfcompile-write-expect-stage1",
        &flat_selfhost,
    );

    let stage1_output = run_native_forth("preprocessed-selfcompile-stage1-output", &stage1);
    let got = parse_i32_output_lines(&stage1_output);
    let expected = vec![
        6587, 7, 15, 2, 0, 27, 0, 26, -1, 4, -1, 16, -1, -1, 0, 116, 0, 27, 1, 256, -1, -1, -1, 2,
        -1, -1, 0, 116, 0, 0, 0, 0, 0, -1, 6, 1, 105, 0, 0, 3, 0, 0, 0, -1, 8, 0, 16, 0, -1, 8, 0,
        46, 0, -1, 8, 0, 48, 0, -1, 8, 0, 63, 0, -1, 8, 0, 160, 0, -1, 8, 0, 334, 0, -1,
    ];
    assert_eq!(
        got, expected,
        "stage1 no longer matches the current self-compile diagnostic snapshot.\n{}",
        stage1
    );
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
    let emitted_forth = run_native_forth("arith-stage1", &selfhost_forth);
    let got = run_native_forth("arith-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("ctrl-stage1", &selfhost_forth);
    let got = run_native_forth("ctrl-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("routine-stage1", &selfhost_forth);
    let got = run_native_forth("routine-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("record-stage1", &selfhost_forth);
    let got = run_native_forth("record-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("string-stage1", &selfhost_forth);
    let got = run_native_forth("string-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("string-edit-stage1", &selfhost_forth);
    let got = run_native_forth("string-edit-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("hex-stage1", &selfhost_forth);
    let got = run_native_forth("hex-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("real-stage1", &selfhost_forth);
    let got = run_native_forth("real-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("case-stage1", &selfhost_forth);
    let got = run_native_forth("case-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("scalar-stage1", &selfhost_forth);
    let got = run_native_forth("scalar-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("array2d-stage1", &selfhost_forth);
    let got = run_native_forth("array2d-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("array4d-stage1", &selfhost_forth);
    let got = run_native_forth("array4d-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("variant-stage1", &selfhost_forth);
    let got = run_native_forth("variant-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("pointer-stage1", &selfhost_forth);
    let got = run_native_forth("pointer-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("addr-stage1", &selfhost_forth);
    let got = run_native_forth("addr-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("enumset-stage1", &selfhost_forth);
    let got = run_native_forth("enumset-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("conf1d-stage1", &selfhost_forth);
    let got = run_native_forth("conf1d-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("conf2d-stage1", &selfhost_forth);
    let got = run_native_forth("conf2d-stage2", &emitted_forth);
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
    let emitted_forth = run_native_forth("setops-stage1", &selfhost_forth);
    let got = run_native_forth("setops-stage2", &emitted_forth);
    assert_eq!(got.trim_end(), "TRUE\nTRUE\nTRUE");
}
