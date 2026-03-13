#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

tmp_dir="$(mktemp -d /tmp/kpascal-pre-selfhost-check-XXXXXX)"
trap 'rm -rf "$tmp_dir"' EXIT

prekpascal_bin="../prekpascal/target/debug/prekpascal"
kforthc_bin="../kFORTHc/target/release/kforthc"
runtime_c="../kFORTHc/runtime/runtime.c"
llc_bin="${LLC_BIN:-llc-14}"

compile_forth() {
  local forth_src="$1"
  local ll_path="$2"
  local obj_path="$3"
  local bin_path="$4"
  "$kforthc_bin" "$forth_src" "$ll_path"
  "$llc_bin" -filetype=obj "$ll_path" -o "$obj_path"
  clang -no-pie "$obj_path" "$runtime_c" -o "$bin_path" -lm
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

encode_seed_ascii() {
  local src_file="$1"
  python3 - "$src_file" <<'PY'
from pathlib import Path
import sys
src = Path(sys.argv[1]).read_text()
lower = src.lower()
after = lower.split(';', 1)[1].lstrip() if ';' in lower else lower.lstrip()
if after.startswith('var'):
    kind = 1
elif after.startswith('type'):
    kind = 2
else:
    kind = 0
print(f"{len(src)} {kind}" + ''.join(f' {ord(c)}' for c in src), end='')
PY
}

run_stage3() {
  local label="$1"
  local src_file="$2"
  local expected="$3"

  encode_seed_ascii "$src_file" > "$tmp_dir/$label.enc"
  "$tmp_dir/seed.out" < "$tmp_dir/$label.enc" > "$tmp_dir/$label.fth"
  compile_forth \
    "$tmp_dir/$label.fth" \
    "$tmp_dir/$label.ll" \
    "$tmp_dir/$label.o" \
    "$tmp_dir/$label.out"
  local got
  got="$("$tmp_dir/$label.out")"
  printf '%s:\n%s\n\n' "$label" "$got"
  if [[ "$got" != "$expected" ]]; then
    printf 'unexpected output for %s\nexpected:\n%s\ngot:\n%s\n' "$label" "$expected" "$got" >&2
    exit 1
  fi
}

if [[ ! -x "$prekpascal_bin" ]]; then
  printf 'missing prekpascal binary: %s\n' "$prekpascal_bin" >&2
  exit 1
fi

if [[ ! -x "$kforthc_bin" ]]; then
  printf 'missing kforthc binary: %s\n' "$kforthc_bin" >&2
  exit 1
fi

"$prekpascal_bin" < selfhost/kpsc_main.pas > "$tmp_dir/kpsc_main_flat.pas"
cargo run --quiet < "$tmp_dir/kpsc_main_flat.pas" > "$tmp_dir/kpsc_main.fth"
compile_forth \
  "$tmp_dir/kpsc_main.fth" \
  "$tmp_dir/kpsc_main.ll" \
  "$tmp_dir/kpsc_main.o" \
  "$tmp_dir/kpsc_main.out"

encode_ascii selfhost/kpsc_seed_hello_single.pas > "$tmp_dir/seed.enc"
"$tmp_dir/kpsc_main.out" < "$tmp_dir/seed.enc" > "$tmp_dir/seed.fth"
compile_forth \
  "$tmp_dir/seed.fth" \
  "$tmp_dir/seed.ll" \
  "$tmp_dir/seed.o" \
  "$tmp_dir/seed.out"

printf "stage1 ok: preprocessed kpsc_main -> seed compiler\n\n"

printf "%s" "program p; begin WriteLn('HELLO') end." > "$tmp_dir/hello.pas"
run_stage3 "hello" "$tmp_dir/hello.pas" "HELLO"
run_stage3 "arithmetic" "tests/samples/02_arithmetic.pas" $'14\n3\n2'
run_stage3 "record" "tests/samples/05_record_with.pas" "33"

printf "all stages ok\n"
