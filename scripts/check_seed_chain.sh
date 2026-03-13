#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

tmp_dir="$(mktemp -d /tmp/kpascal-seed-check-XXXXXX)"
trap 'rm -rf "$tmp_dir"' EXIT

encode() {
  local src_file="$1"
  python3 - "$src_file" <<'PY'
from pathlib import Path
import sys
src = Path(sys.argv[1]).read_text()
print(str(len(src)) + ''.join(f' {ord(c)}' for c in src), end='')
PY
}

printf '%s' "$(cat selfhost/kpsc_main.pas)" | cargo run --quiet > "$tmp_dir/kpsc_main.fth"
../kFORTHc/target/release/kforthc "$tmp_dir/kpsc_main.fth" "$tmp_dir/kpsc_main.ll"
llc-14 -filetype=obj "$tmp_dir/kpsc_main.ll" -o "$tmp_dir/kpsc_main.o"
clang -no-pie "$tmp_dir/kpsc_main.o" ../kFORTHc/runtime/runtime.c -o "$tmp_dir/kpsc_main.out" -lm

encode selfhost/kpsc_seed_hello_single.pas > "$tmp_dir/seed.enc"
"$tmp_dir/kpsc_main.out" < "$tmp_dir/seed.enc" > "$tmp_dir/seed_stage1.fth"
../kFORTHc/target/release/kforthc "$tmp_dir/seed_stage1.fth" "$tmp_dir/seed_stage1.ll"
llc-14 -filetype=obj "$tmp_dir/seed_stage1.ll" -o "$tmp_dir/seed_stage1.o"
clang -no-pie "$tmp_dir/seed_stage1.o" ../kFORTHc/runtime/runtime.c -o "$tmp_dir/seed_stage1.out" -lm

printf "HELLO:\n"
printf '%s' "program p; begin WriteLn('HELLO') end." > "$tmp_dir/hello.pas"
encode "$tmp_dir/hello.pas" > "$tmp_dir/hello.enc"
"$tmp_dir/seed_stage1.out" < "$tmp_dir/hello.enc" > "$tmp_dir/hello.fth"
"$tmp_dir/hello.fth" >/dev/null 2>&1 || true
sed -n '1,12p' "$tmp_dir/hello.fth"

printf "\nARITH:\n"
encode tests/samples/02_arithmetic.pas > "$tmp_dir/arith.enc"
"$tmp_dir/seed_stage1.out" < "$tmp_dir/arith.enc" > "$tmp_dir/arith.fth"
sed -n '1,16p' "$tmp_dir/arith.fth"

printf "\nRECORD:\n"
encode tests/samples/05_record_with.pas > "$tmp_dir/record.enc"
"$tmp_dir/seed_stage1.out" < "$tmp_dir/record.enc" > "$tmp_dir/record.fth"
sed -n '1,16p' "$tmp_dir/record.fth"
