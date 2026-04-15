use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);

fn samples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/samples")
}

fn runtime_c_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kFORTHc/runtime/runtime.c")
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

fn compile_pascal(src: &str) -> String {
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
    String::from_utf8(out.stdout).expect("kpascal stdout is not UTF-8")
}

fn fresh_work_dir(test_name: &str) -> PathBuf {
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "kpascal-sample-{test_name}-{}-{id}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("failed to create temporary directory");
    dir
}

fn run_native_with_kforthc(test_name: &str, forth_src: &str) -> String {
    let work_dir = fresh_work_dir(test_name);
    let forth_path = work_dir.join("program.fth");
    let ll_path = work_dir.join("program.ll");
    let obj_path = work_dir.join("program.o");
    let bin_path = work_dir.join("program.out");
    fs::write(&forth_path, forth_src).expect("failed to write Forth source");

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

    let out = Command::new(&bin_path)
        .output()
        .expect("failed to run native binary");
    assert!(
        out.status.success(),
        "native binary failed.\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("native stdout is not UTF-8")
}

fn normalized_output(raw: &str) -> String {
    let mut out = raw
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    while out.ends_with('\n') {
        out.pop();
    }
    out
}

fn sample_names() -> Vec<String> {
    let mut names = fs::read_dir(samples_dir())
        .expect("failed to read samples directory")
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            let stem = path.file_stem()?.to_str()?;
            if path.extension()?.to_str()? == "pas"
                && stem
                    .split_once('_')
                    .and_then(|(num, _)| num.parse::<u32>().ok())
                    .is_some_and(|n| n <= 23)
            {
                Some(stem.to_string())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    names.sort();
    names
}

#[test]
fn compiles_all_sample_programs() {
    let names = sample_names();
    assert!(names.len() >= 20, "expected at least 20 samples");
    for name in names {
        let src_path = samples_dir().join(format!("{name}.pas"));
        let src = fs::read_to_string(&src_path).expect("failed to read sample source");
        let forth = compile_pascal(&src);
        assert!(
            forth.contains(": MAIN"),
            "sample {} did not generate MAIN",
            src_path.display()
        );
    }
}

#[test]
fn sample_programs_match_expected_native_output() {
    if !has_native_backend() {
        eprintln!(
            "skipping sample native e2e: missing kforthc/llc/clang or ../kFORTHc/runtime/runtime.c"
        );
        return;
    }
    let names = sample_names();
    assert!(names.len() >= 20, "expected at least 20 samples");
    for name in names {
        let src = fs::read_to_string(samples_dir().join(format!("{name}.pas")))
            .expect("failed to read sample source");
        let expected = fs::read_to_string(samples_dir().join(format!("{name}.out")))
            .expect("failed to read sample output");
        let forth = compile_pascal(&src);
        let got = run_native_with_kforthc(&name, &forth);
        assert_eq!(
            normalized_output(&got),
            normalized_output(&expected),
            "unexpected runtime output for sample {name}"
        );
    }
}
