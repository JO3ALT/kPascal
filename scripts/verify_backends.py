#!/usr/bin/env python3
import math
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
KFORTHC = ROOT.parent / "kFORTHc" / "target" / "debug" / "kforthc"
KFORTH_BUILD = ROOT.parent / "kforth" / "build" / "kforth"
KFORTH_FALLBACK = ROOT.parent / "kforth" / "kforth"
BOOTSTRAP = ROOT.parent / "kforth" / "bootstrap.fth"
KPASCAL = ROOT / "target" / "debug" / "kpascal"
FIXTURES = ROOT / "tests" / "fixtures"
TMP = Path("/tmp/kpascal_backend_verify")


def run(cmd, *, input_bytes=None, cwd=None, timeout=None):
    return subprocess.run(
        cmd,
        input=input_bytes,
        cwd=cwd,
        timeout=timeout,
        capture_output=True,
        check=False,
    )


def kforth_bin() -> Path:
    return KFORTH_BUILD if KFORTH_BUILD.exists() else KFORTH_FALLBACK


def llc_bin() -> str:
    for c in ("llc", "llc-14"):
        p = subprocess.run(["bash", "-lc", f"command -v {c}"], capture_output=True, text=True)
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()
    raise RuntimeError("llc not found")


def normalize_kforth_output(raw: bytes) -> str:
    lines = []
    for line in raw.decode("utf-8", errors="replace").splitlines():
        if line.startswith("ok"):
            line = line[2:].lstrip()
        if line:
            lines.append(line)
    return "\n".join(lines) + ("\n" if lines else "")


def python_oracle_ok(fixture_name: str, native_out: str, kforth_out: str) -> tuple[bool, str]:
    native_lines = native_out.strip("\n").splitlines()
    kforth_lines = kforth_out.strip("\n").splitlines()

    if fixture_name == "use_math_float_trig_pow.pas":
        # Only float trig terms differ by FPU/approx; compare against Python to 1e-3.
        if len(native_lines) != 7:
            return False, "unexpected line count"
        expected = [
            1024.0,
            0.25,
            1.0,
            0.0,
            1.0,
            math.sin(1.0),
            math.cos(1.0),
        ]
        for i, (got, exp) in enumerate(zip(native_lines, expected), 1):
            try:
                gv = float(got)
            except ValueError:
                return False, f"line {i} not float: {got!r}"
            if abs(gv - exp) > 1e-3:
                return False, f"line {i} diff too large: got={gv} exp={exp}"
        return True, "python float oracle (tol=1e-3)"

    def rint(x: float) -> int:
        return int(x + 0.5) if x >= 0 else int(x - 0.5)

    if fixture_name == "use_math.pas":
        expected = [
            "9",
            str(rint(math.sin(math.radians(30)) * 10000.0)),
            str(rint(math.cos(math.radians(60)) * 10000.0)),
            str(rint(math.tan(math.radians(45)) * 10000.0)),
            str(rint(math.degrees(math.asin(0.5)))),
            str(rint(math.degrees(math.acos(0.5)))),
            str(rint(math.degrees(math.atan(1.0)))),
            str(rint(math.log(2.0) * 10000.0)),
            str(rint(math.log10(10.0) * 10000.0)),
        ]
        if native_lines == expected:
            return True, "python fixed-math oracle"
        return False, "native output does not match python fixed-math oracle"

    if fixture_name == "all_features.pas":
        # Validate only the fixed-math segment against Python. Everything else must match kforth.
        if len(native_lines) != len(kforth_lines):
            return False, "line count mismatch"
        for i, (a, b) in enumerate(zip(native_lines, kforth_lines), 1):
            if i in (25, 26, 27, 28, 29, 30, 31, 32):
                continue
            if a != b:
                return False, f"line {i} mismatch outside math segment"
        expected_segment = [
            str(rint(math.sin(math.radians(30)) * 10000.0)),   # line 25
            str(rint(math.cos(math.radians(60)) * 10000.0)),   # line 26
            str(rint(math.tan(math.radians(45)) * 10000.0)),   # line 27
            str(rint(math.degrees(math.asin(0.5)))),           # line 28
            str(rint(math.degrees(math.acos(0.5)))),           # line 29
            str(rint(math.degrees(math.atan(1.0)))),           # line 30
            str(rint(math.log(2.0) * 10000.0)),                # line 31
            str(rint(math.log10(10.0) * 10000.0)),             # line 32
        ]
        actual_segment = native_lines[24:32]
        if actual_segment == expected_segment:
            return True, "python fixed-math segment oracle"
        return False, "math segment does not match python oracle"

    return False, "no python oracle for fixture"


def compile_native(fth_path: Path, out_base: Path, llc: str) -> tuple[bool, str]:
    r = run([str(KFORTHC), str(fth_path), str(out_base.with_suffix(".ll"))])
    if r.returncode != 0:
        return False, r.stderr.decode() or r.stdout.decode()
    r = run([llc, "-filetype=obj", str(out_base.with_suffix(".ll")), "-o", str(out_base.with_suffix(".o"))])
    if r.returncode != 0:
        return False, r.stderr.decode() or r.stdout.decode()
    r = run(
        [
            "clang",
            "-no-pie",
            str(out_base.with_suffix(".o")),
            str(ROOT.parent / "kFORTHc" / "runtime" / "runtime.c"),
            "-o",
            str(out_base.with_suffix(".native")),
            "-lm",
        ]
    )
    if r.returncode != 0:
        return False, r.stderr.decode() or r.stdout.decode()
    return True, ""


def main() -> int:
    TMP.mkdir(parents=True, exist_ok=True)
    if not KPASCAL.exists():
        print("error: build kpascal first (target/debug/kpascal not found)", file=sys.stderr)
        return 2
    if not KFORTHC.exists():
        print("error: build kFORTHc first", file=sys.stderr)
        return 2
    llc = llc_bin()
    kforth = kforth_bin()

    fixtures = sorted(FIXTURES.glob("*.pas"))
    pass_n = fail_n = 0
    for f in fixtures:
        base = f.stem
        work = TMP / base
        work.mkdir(parents=True, exist_ok=True)
        in_path = f.with_suffix(".in")
        out_path = f.with_suffix(".out")

        cp = run([str(KPASCAL)], input_bytes=f.read_bytes())
        if cp.returncode != 0:
            print(f"FAIL compile {f}")
            sys.stdout.write(cp.stderr.decode(errors="replace"))
            fail_n += 1
            continue
        fth = work / f"{base}.fth"
        fth.write_bytes(cp.stdout)

        ok, msg = compile_native(fth, work / base, llc)
        if not ok:
            print(f"FAIL native compile {f}")
            print(msg.strip())
            fail_n += 1
            continue

        native_bin = work / f"{base}.native"
        in_bytes = in_path.read_bytes() if in_path.exists() else None
        nr = run([str(native_bin)], input_bytes=in_bytes, timeout=30)
        if nr.returncode != 0:
            print(f"FAIL native run {f} rc={nr.returncode}")
            fail_n += 1
            continue
        native_out = nr.stdout.decode("utf-8", errors="replace")

        kforth_input = BOOTSTRAP.read_bytes() + b"\n" + fth.read_bytes() + b"\n"
        if in_bytes:
            kforth_input += in_bytes + (b"" if in_bytes.endswith(b"\n") else b"\n")
        kforth_input += b"BYE\n"
        kr = run([str(kforth)], input_bytes=kforth_input, timeout=30)
        if kr.returncode != 0:
            print(f"FAIL kforth run {f} rc={kr.returncode}")
            fail_n += 1
            continue
        kforth_out = normalize_kforth_output(kr.stdout)

        if native_out == kforth_out:
            status = "PASS exact"
            pass_n += 1
        else:
            oracle_ok, reason = python_oracle_ok(f.name, native_out, kforth_out)
            if oracle_ok:
                status = f"PASS oracle ({reason})"
                pass_n += 1
            else:
                status = f"FAIL ({reason})"
                fail_n += 1

        exp_note = ""
        if out_path.exists():
            exp = out_path.read_text()
            if native_out == exp:
                exp_note = " expected=.out"
            else:
                ok_oracle, _ = python_oracle_ok(f.name, native_out, exp)
                if ok_oracle:
                    exp_note = " expected=.out differs (oracle-accepted)"
                else:
                    exp_note = " expected=.out differs"
        print(f"{status}: {f.name}{exp_note}")

    print(f"Summary: PASS={pass_n} FAIL={fail_n}")
    return 0 if fail_n == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
