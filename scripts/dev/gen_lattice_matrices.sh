#!/usr/bin/env bash
# Regenerate the committed Lean lattice-basis fixture that validate_latticegen.py
# structurally checks. Emits the bench-convention basis for each family at the
# sampled dimensions. Run from the repo root; requires `lake` (pure generators,
# no FFI). Commit the result.
set -euo pipefail
out=scripts/dev/lattice-matrices.jsonl
: > "$out"
lake env lean --run scripts/dev/emit_latticegen_family.lean ajtai 6 8 10 12 16 20 | grep '^{"family"' >> "$out"
lake env lean --run scripts/dev/emit_latticegen_family.lean q-ary 16 24 32       | grep '^{"family"' >> "$out"
lake env lean --run scripts/dev/emit_latticegen_family.lean ntru 8 12 16         | grep '^{"family"' >> "$out"
lake env lean --run scripts/dev/emit_latticegen_family.lean knapsack 16 24 32    | grep '^{"family"' >> "$out"
echo "wrote $(wc -l < "$out") matrices -> $out"
