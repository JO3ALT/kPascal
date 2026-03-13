#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LLC_BIN="$(command -v llc || command -v llc-14)"
if [[ -z "${LLC_BIN:-}" ]]; then
  echo "llc not found" >&2
  exit 1
fi

OUT_DIR="${1:-/tmp/kpascal-selfhost-stage1}"
mkdir -p "$OUT_DIR"

FLAT_SRC="$OUT_DIR/flat_kpsc_main.pas"
SELFHOST_FORTH="$OUT_DIR/selfhost_main.fth"
STAGE1_LL="$OUT_DIR/stage1.ll"
STAGE1_OBJ="$OUT_DIR/stage1.o"
STAGE1_BIN="$OUT_DIR/stage1.out"
STAGE1_OUT="$OUT_DIR/stage1_generated.fth"

../prekpascal/target/debug/prekpascal < selfhost/kpsc_main.pas > "$FLAT_SRC"
./target/debug/kpascal < "$FLAT_SRC" > "$SELFHOST_FORTH"
../kFORTHc/target/release/kforthc "$SELFHOST_FORTH" "$STAGE1_LL" >/dev/null
"$LLC_BIN" -filetype=obj "$STAGE1_LL" -o "$STAGE1_OBJ"
clang -no-pie "$STAGE1_OBJ" ../kFORTHc/runtime/runtime.c -o "$STAGE1_BIN" -lm

python3 - "$FLAT_SRC" "$STAGE1_BIN" "$STAGE1_OUT" <<'PY'
import pathlib
import subprocess
import sys

flat_src = pathlib.Path(sys.argv[1]).read_text()
stage1_bin = sys.argv[2]
stage1_out = pathlib.Path(sys.argv[3])
encoded = " ".join([str(len(flat_src))] + [str(ord(ch)) for ch in flat_src])
out = subprocess.check_output([stage1_bin], input=encoded.encode())
stage1_out.write_bytes(out)
print(stage1_out)
PY
