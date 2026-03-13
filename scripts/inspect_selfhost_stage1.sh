#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

OUT_DIR="${1:-/tmp/kpascal-selfhost-stage1-inspect}"
mkdir -p "$OUT_DIR"

bash scripts/dump_selfhost_stage1.sh "$OUT_DIR" >/dev/null

python3 - <<'PY' "$OUT_DIR/stage1_generated.fth"
from pathlib import Path
import sys

text = Path(sys.argv[1]).read_text(errors="replace")
markers = [
    ": ReadString",
    ": ReadNumber",
    ": ReadSymbol",
    ": NextToken",
    ": WriteToken",
    ": ExpectKind",
    ": ExpectAssignSymbol",
    ": ExpectSymbolChar",
    ": ParseProgram",
]

for marker in markers:
    print(f"{marker}: {'yes' if marker in text else 'no'}")

needle = "PERR"
idx = text.find(needle)
if idx < 0:
    print("\nno PERR found")
    print(text[-3000:])
else:
    start = max(0, idx - 1600)
    end = min(len(text), idx + 600)
    print("\n--- around first parse error ---\n")
    print(text[start:end])
PY
