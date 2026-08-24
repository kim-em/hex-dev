# Accomplished

- Added a Mathlib-free logical comparison over one arithmetic DAG using only
  supported `Search` APIs. FIFO, static-rank, and adaptive policies repeatedly
  choose an authenticated offer, commit a real fact update through
  `Search.invokeWithin`, and install a complete serial/version-aware offer set
  through `Search.Session.refreshWithin`.
- Made adaptive ordering genuinely depend on live predecessor versions. The
  static-rank name now states that its age residue is fixed rather than learned.
- Removed formula-derived duplicate and selected-position counters. The canary
  retains only callback-instrumented comparisons, accepted history length,
  selected-order hashes, and the final fact/version checksum.
- Separated timing from policy comparison. Six `setup_fixed_benchmark`
  registrations measure the shared authenticated program/branch/session setup,
  choose/invoke/complete-refresh, report snapshot walk, and timed result-hash
  path. Runtime counts come from a module-level `IO.Ref`; every rung throws on
  failure and pins the exact full-report hash through `expectedHash`.
- Measured fixed offer counts 1,024, 2,048, 4,096, 8,192, 16,384, and 32,768
  with five repeats and a five-second per-call cap. Medians were 7.829, 12.038,
  42.102, 155.655, 599.540, and 2,343 ms; ranges were 3.902--8.131,
  11.968--12.080, 41.606--48.953, 154.152--162.673, 593.278--616.574, and
  2,303--2,460 ms. Adjacent median ratios were 1.538, 3.497, 3.697, 3.852,
  and 3.908; the empirical log-log least-squares slope was 1.712. These fixed
  observations carry no framework complexity verdict. The earlier parametric
  5x spawn-floor setup was below the normal 10x policy and has been removed.
- At the canonical 128-node logical input, every policy accepts 126 updates and
  zero live offers, and ends with semantic checksum 8,880,463,590,880,745,567.
  FIFO/static-rank/adaptive respectively record 0/7,875/7,875 comparisons and
  order hashes 13,333,310,190,265,569,661 /
  9,721,628,123,875,171,393 / 558,125,824,506,216,197.
- Kept the existing single CI job and canonical 128-node direct canary. The
  canonical input is a plain definition; there is no mutable benchmark input.
- Fixed full-report hashes at 1,024 / 2,048 / 4,096 / 8,192 / 16,384 / 32,768
  offers are `0xbbd09a2695e38e01` / `0x6e4e62b8e475bb32` /
  `0xcd7bca91050befed` / `0x5a04b99431d279fc` /
  `0xffdc8b53fcda1fd5` / `0x284aed8dace21e10`.

# Current frontier

- The logical-count leg compares policy behavior. The timing leg measures only
  shared authenticated end-to-end infrastructure and provides no comparative
  policy-performance signal or default selection.
- Mixed typed-event and split/tree workloads are out of scope for this focused
  experiment. Direct Mathlib-free `Runtime.State.stepWithin` and `Search.Result`
  runtime/split/settle APIs exist; only the `Controller.Executable` route used
  by the separate fact adapter remains Mathlib-dependent.

# Next step

- Run the complete repository gates, amend and push the single benchmark commit,
  then obtain the requested independent review before opening a pull request.
- Extend the logical matrix only when a later experiment specifically scopes
  typed-runtime or result-tree policy questions.

# Blockers

- No blocker remains for the scoped arithmetic-DAG logical comparison or the
  shared authenticated timing registration.
- The Mathlib-dependent executable route prevents this computational target
  from measuring that adapter, but it does not block the existing direct
  Mathlib-free runtime and result APIs.
