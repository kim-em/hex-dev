# Automatic native ECPP fallback

The allocation in `allocation-v1.json` was fixed before this feasibility run.
It uses seed 0 for every subject, 1024 candidates, 4096 charged factor-work
units and 1000000 scalar additions, with the other stated finite caps over
`public512Budget`. `driver-v1.patch` applies the allocation to the existing
Mathlib-free `hexecpp_native` driver; build with `lake build hexecpp_native`,
then pass `SUBJECT 0 automatic`. The frozen corpus is
`../native512/corpus-v1.json`; its digest and the source revision are retained.

`native512-feasibility-v1.json` retains every completed sample in corpus order
on one automatically leased CPU of the shared host. Successful records contain
all compact rows and terminal certificate data, checks, counters, timings and
random state. The large expanded constructor rendering is addressed by SHA-256;
its original raw sample remains retained in `/tmp/hex-auto512-probe.json` on the
measurement host. No completed sample was discarded or rerun.

The allocation succeeds on four of eight tuning subjects and two of eight
holdout subjects. The held-out gains are ordinary-0 and ordinary-3, both beyond
full Pocklington construction with its registered ECM retry in the existing
native512 corpus comparison. Fixed seed 0 is different from that earlier
experiment's per-case seeds; coverage is not inferred from that experiment.
Holdout native search ranges from 67 ms to 2.51 s on this host. The two successful
holdout searches take 1.54 s and 1.65 s and use genuine elliptic rows. These are
computational feasibility observations, not accepted whole-tactic performance
claims, a completeness guarantee, or evidence for default Lean resource limits.

Implementation acceptance still requires the complete Pocklington/ECM/ECPP
portfolio, exact suggestions, finite-option kernel proofs, fresh replay without
production, and retained adjacent comparisons including unsuccessful cases.
The explicit native512 proof-cost evidence remains relevant: its fresh-module
kernel proof median is 23.436 s against a 5.346 s import/numeral baseline on the
recorded host. Reducing search allocation does not remove kernel replay cost.
