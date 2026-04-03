#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

tmp_dir="$(mktemp -d /tmp/kpascal-pre-selfhost-all-XXXXXX)"
trap 'rm -rf "$tmp_dir"' EXIT

preprocess_bin="scripts/preprocess_selfhost.sh"
kforthc_bin="../kFORTHc/target/release/kforthc"
runtime_c="../kFORTHc/runtime/runtime.c"
llc_bin="${LLC_BIN:-llc-14}"

compile_forth() {
  local forth_src="$1"
  local ll_path="$2"
  local obj_path="$3"
  local bin_path="$4"
  "$kforthc_bin" "$forth_src" "$ll_path" >/dev/null
  "$llc_bin" -filetype=obj "$ll_path" -o "$obj_path"
  clang -no-pie "$obj_path" "$runtime_c" -o "$bin_path" -lm >/dev/null 2>&1
}

encode_ascii() {
  local src_file="$1"
  python3 - "$src_file" <<'PY'
from pathlib import Path
import sys
src = Path(sys.argv[1]).read_text()
print(str(len(src)) + ''.join(f' {ord(c)}' for c in src), end='')
PY
}

if [[ ! -x "$preprocess_bin" ]]; then
  printf 'missing selfhost preprocessor: %s\n' "$preprocess_bin" >&2
  exit 1
fi

if [[ ! -x "$kforthc_bin" ]]; then
  printf 'missing kforthc binary: %s\n' "$kforthc_bin" >&2
  exit 1
fi

"$preprocess_bin" selfhost/kpsc_main.pas > "$tmp_dir/kpsc_main_flat.pas"
cargo run --quiet < "$tmp_dir/kpsc_main_flat.pas" > "$tmp_dir/kpsc_main.fth"
compile_forth \
  "$tmp_dir/kpsc_main.fth" \
  "$tmp_dir/kpsc_main.ll" \
  "$tmp_dir/kpsc_main.o" \
  "$tmp_dir/kpsc_main.out"

status=0
for sample_path in tests/samples/*.pas; do
  sample_name="$(basename "$sample_path" .pas)"
  encode_ascii "$sample_path" > "$tmp_dir/$sample_name.enc"

  if ! "$tmp_dir/kpsc_main.out" < "$tmp_dir/$sample_name.enc" > "$tmp_dir/$sample_name.fth"; then
    printf 'stage1 failed: %s\n' "$sample_name"
    status=1
    continue
  fi

  if ! compile_forth \
    "$tmp_dir/$sample_name.fth" \
    "$tmp_dir/$sample_name.ll" \
    "$tmp_dir/$sample_name.o" \
    "$tmp_dir/$sample_name.out"; then
    printf 'backend failed: %s\n' "$sample_name"
    status=1
    continue
  fi

  if ! "$tmp_dir/$sample_name.out" > "$tmp_dir/$sample_name.actual"; then
    printf 'runtime failed: %s\n' "$sample_name"
    status=1
    continue
  fi

  if ! diff -u "tests/samples/$sample_name.out" "$tmp_dir/$sample_name.actual" > "$tmp_dir/$sample_name.diff"; then
    printf 'mismatch: %s\n' "$sample_name"
    cat "$tmp_dir/$sample_name.diff"
    status=1
    continue
  fi

  printf 'ok: %s\n' "$sample_name"
done

exit "$status"
