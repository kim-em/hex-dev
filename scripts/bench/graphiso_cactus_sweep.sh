#!/usr/bin/env bash
# Regenerate the hex-graph-iso cactus sweep data and figures.
#
# Runs the compiled sweep and pairs drivers, stores the data under
# reports/bench-results/ keyed by the current commit and host, and
# re-renders the figures (re-timing the tactic leg). Run from the repo
# root after any change to hex-graph-iso implementation source, and
# commit the data and figures together with that change;
# scripts/bench/check_graphiso_sweep_freshness.py is the required
# check that keeps the figures honest.
set -euo pipefail

label="${1:-}"
root=$(git rev-parse --show-toplevel)
cd "$root"
# The fingerprint reads the index, but the sweep measures the working
# tree; stage the relevant paths first so an uncommitted change cannot
# record under its predecessor's key (they are about to be committed
# together with the data in any case).
# The pathspec must stay identical to RELEVANT in
# scripts/bench/check_graphiso_sweep_freshness.py; SPEC and README are
# excluded because documentation cannot affect measured performance.
git add -- HexGraphIso/ HexGraph/ bench/HexGraphIso/Cactus.lean \
  scripts/plots/hexgraphiso-cactus.py ':!HexGraphIso/SPEC' \
  ':!HexGraphIso/README.md'
fp=$(git ls-files -s -- HexGraphIso/ HexGraph/ bench/HexGraphIso/Cactus.lean \
  scripts/plots/hexgraphiso-cactus.py ':!HexGraphIso/SPEC' \
  ':!HexGraphIso/README.md' | sha256sum | cut -c1-12)
host=$(hostname -s)

lake build hexgraphiso_cactus
sweep="reports/bench-results/hexgraphiso-cactus-$fp-$host.jsonl"
pairs="reports/bench-results/hexgraphiso-pairs-$fp-$host.jsonl"
.lake/build/bin/hexgraphiso_cactus > "$sweep"
.lake/build/bin/hexgraphiso_cactus pairs > "$pairs"
python3 scripts/plots/hexgraphiso-cactus.py \
  --sweep "$sweep" --pairs "$pairs" --retime
cp reports/figures/hexgraphiso-tactic-times.json \
  "reports/bench-results/hexgraphiso-tactic-$fp-$host.json"
cat > "reports/bench-results/hexgraphiso-cactus-$fp-$host.meta.json" <<META
{
 "fingerprint": "$fp",
 "host": "$host",
 "date": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
 "describe": "$(git rev-parse --short=12 HEAD)",
 "label": "$label"
}
META
echo "recorded $sweep, $pairs, tactic times, meta, and reports/figures/hexgraphiso-*.svg"
