#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LLC_BIN="${LLC_BIN:-}"
if [[ -z "$LLC_BIN" ]]; then
  LLC_BIN="$(command -v llc || command -v llc-14 || true)"
fi
if [[ -z "$LLC_BIN" ]]; then
  echo "llc not found" >&2
  exit 1
fi

if [[ -x ../kforthc/target/release/kforthc ]]; then
  KFORTHC_BIN="../kforthc/target/release/kforthc"
elif [[ -x ../kFORTHc/target/release/kforthc ]]; then
  KFORTHC_BIN="../kFORTHc/target/release/kforthc"
elif command -v kforthc >/dev/null 2>&1; then
  KFORTHC_BIN="kforthc"
else
  echo "kforthc not found" >&2
  exit 1
fi

if [[ -f ../kforthc/runtime/runtime.c ]]; then
  RUNTIME_C="../kforthc/runtime/runtime.c"
elif [[ -f ../kFORTHc/runtime/runtime.c ]]; then
  RUNTIME_C="../kFORTHc/runtime/runtime.c"
else
  echo "runtime.c not found" >&2
  exit 1
fi

OUT_DIR="${1:-/tmp/kpascal-selfhost-stage3}"
mkdir -p "$OUT_DIR"

FLAT_SRC="$OUT_DIR/flat_kpsc_main.pas"
STAGE1_FORTH="$OUT_DIR/stage1.fth"
STAGE1_LL="$OUT_DIR/stage1.ll"
STAGE1_OBJ="$OUT_DIR/stage1.o"
STAGE1_BIN="$OUT_DIR/stage1.out"
STAGE2_FORTH="$OUT_DIR/stage2.fth"
STAGE2_LL="$OUT_DIR/stage2.ll"
STAGE2_OBJ="$OUT_DIR/stage2.o"
STAGE2_BIN="$OUT_DIR/stage2.out"
STAGE3_FORTH="$OUT_DIR/stage3.fth"
STAGE3_LL="$OUT_DIR/stage3.ll"
STAGE3_OBJ="$OUT_DIR/stage3.o"
STAGE3_BIN="$OUT_DIR/stage3.out"
STAGE2_SEED_FORTH="$OUT_DIR/seed_from_stage2.fth"
STAGE3_SEED_FORTH="$OUT_DIR/seed_from_stage3.fth"

compile_forth() {
  local forth_src="$1"
  local ll_path="$2"
  local obj_path="$3"
  local bin_path="$4"

  "$KFORTHC_BIN" "$forth_src" "$ll_path" >/dev/null
  "$LLC_BIN" -filetype=obj "$ll_path" -o "$obj_path"
  clang -no-pie "$obj_path" "$RUNTIME_C" -o "$bin_path" -lm
}

encode_ascii() {
  local src_file="$1"
  python3 - "$src_file" <<'PY'
from pathlib import Path
import sys

src = Path(sys.argv[1]).read_text()
print(str(len(src)) + ''.join(f' {ord(ch)}' for ch in src), end='')
PY
}

bash scripts/preprocess_selfhost.sh selfhost/kpsc_main.pas > "$FLAT_SRC"
cargo run --quiet < "$FLAT_SRC" > "$STAGE1_FORTH"
compile_forth "$STAGE1_FORTH" "$STAGE1_LL" "$STAGE1_OBJ" "$STAGE1_BIN"

encode_ascii "$FLAT_SRC" > "$OUT_DIR/kpsc_main.enc"
"$STAGE1_BIN" < "$OUT_DIR/kpsc_main.enc" > "$STAGE2_FORTH"
compile_forth "$STAGE2_FORTH" "$STAGE2_LL" "$STAGE2_OBJ" "$STAGE2_BIN"

"$STAGE2_BIN" < "$OUT_DIR/kpsc_main.enc" > "$STAGE3_FORTH"
compile_forth "$STAGE3_FORTH" "$STAGE3_LL" "$STAGE3_OBJ" "$STAGE3_BIN"

encode_ascii selfhost/kpsc_seed_hello_single.pas > "$OUT_DIR/seed.enc"
"$STAGE2_BIN" < "$OUT_DIR/seed.enc" > "$STAGE2_SEED_FORTH"
"$STAGE3_BIN" < "$OUT_DIR/seed.enc" > "$STAGE3_SEED_FORTH"

python3 - "$STAGE2_FORTH" "$STAGE3_FORTH" "$STAGE2_SEED_FORTH" "$STAGE3_SEED_FORTH" <<'PY'
from pathlib import Path
import hashlib
import sys

for label, path in [
    ("stage2", sys.argv[1]),
    ("stage3", sys.argv[2]),
    ("seed-from-stage2", sys.argv[3]),
    ("seed-from-stage3", sys.argv[4]),
]:
    data = Path(path).read_bytes()
    print(f"{label} sha256: {hashlib.sha256(data).hexdigest()}")
PY

cat <<EOF
flat source: $FLAT_SRC
stage1 binary: $STAGE1_BIN
stage2 forth: $STAGE2_FORTH
stage2 binary: $STAGE2_BIN
stage3 forth: $STAGE3_FORTH
stage3 binary: $STAGE3_BIN
stage2 seed output: $STAGE2_SEED_FORTH
stage3 seed output: $STAGE3_SEED_FORTH
EOF
