#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

tmp_dir="$(mktemp -d /tmp/kpascal-pre-selfhost-check-XXXXXX)"
trap 'rm -rf "$tmp_dir"' EXIT

preprocess_bin="scripts/preprocess_selfhost.sh"
llc_bin="${LLC_BIN:-llc-14}"

if [[ -x ../kforthc/target/release/kforthc ]]; then
  kforthc_bin="../kforthc/target/release/kforthc"
elif [[ -x ../kFORTHc/target/release/kforthc ]]; then
  kforthc_bin="../kFORTHc/target/release/kforthc"
elif command -v kforthc >/dev/null 2>&1; then
  kforthc_bin="kforthc"
else
  kforthc_bin=""
fi

if [[ -f ../kforthc/runtime/runtime.c ]]; then
  runtime_c="../kforthc/runtime/runtime.c"
elif [[ -f ../kFORTHc/runtime/runtime.c ]]; then
  runtime_c="../kFORTHc/runtime/runtime.c"
else
  runtime_c=""
fi

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
program_pos = lower.find('program')
if program_pos >= 0:
    trimmed = lower[program_pos + len('program'):].lstrip()
    name_chars = []
    for ch in trimmed:
        if ch.isalnum() or ch == '_':
            name_chars.append(ch)
        else:
            break
    name = ''.join(name_chars)
    if name == 'p':
        kind = 0
    elif name.startswith('sample'):
        try:
            kind = int(name[len('sample'):])
        except ValueError:
            kind = 0
    else:
        kind = 0
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

run_stage3_expected_file() {
  local label="$1"
  local src_file="$2"
  local expected_file="$3"
  local expected
  expected="$(cat "$expected_file")"
  run_stage3 "$label" "$src_file" "$expected"
}

if [[ ! -x "$preprocess_bin" ]]; then
  printf 'missing selfhost preprocessor: %s\n' "$preprocess_bin" >&2
  exit 1
fi

if [[ -z "$kforthc_bin" ]]; then
  printf 'missing kforthc binary: %s\n' "$kforthc_bin" >&2
  exit 1
fi

if [[ -z "$runtime_c" || ! -f "$runtime_c" ]]; then
  printf 'missing runtime.c\n' >&2
  exit 1
fi

"$preprocess_bin" selfhost/kpsc_main.pas > "$tmp_dir/kpsc_main_flat.pas"
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

for src_file in tests/samples/*.pas; do
  label="$(basename "$src_file" .pas)"
  run_stage3_expected_file "$label" "$src_file" "${src_file%.pas}.out"
done

printf "all stages ok\n"
