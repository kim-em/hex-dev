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

root=$(git rev-parse --show-toplevel)
cd "$root"
sha=$(git rev-parse --short=8 HEAD)
host=$(hostname -s)

lake build hexgraphiso_cactus
sweep="reports/bench-results/hexgraphiso-cactus-$sha-$host.jsonl"
pairs="reports/bench-results/hexgraphiso-pairs-$sha-$host.jsonl"
.lake/build/bin/hexgraphiso_cactus > "$sweep"
.lake/build/bin/hexgraphiso_cactus pairs > "$pairs"
python3 scripts/plots/hexgraphiso-cactus.py \
  --sweep "$sweep" --pairs "$pairs" --retime
echo "recorded $sweep, $pairs, and reports/figures/hexgraphiso-*.svg"
