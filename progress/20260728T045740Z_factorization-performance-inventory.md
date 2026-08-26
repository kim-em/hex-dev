# Polynomial-factorization performance inventory

## Accomplished

- Inventoried the committed performance reports and raw result artifacts for
  finite-field Berlekamp factorization, integer Berlekamp–Zassenhaus
  factorization, Hensel lifting, square-free decomposition, and
  kernel/certificate replay.
- Identified the durable cross-system sweep, the current classical-BZ study,
  and the explicit retraction on the older Isabelle comparator ladders as the
  key provenance boundary for any summary.
- Collected the main recorded runtime, scaling, solve-count, optimization, and
  profile findings without modifying benchmark or library code.

## Current frontier

- The July cross-system sweep is the broadest committed end-to-end dataset:
  391 inputs, eight system configurations, a 10-second cutoff, and a successful
  differential factor-degree cross-check.
- The current corpus has 392 rows, while the broad sweep remains pinned to the
  prior 391-row corpus and predates later factor-path work.
- The kernel-versus-certificate record is only a four-input validation sample,
  not a full crossover/frontier campaign.

## Next step

- If fresh headline claims are needed, remeasure only the changed hex systems
  on dedicated hardware against the current 392-row corpus, regenerate the
  merged charts, and run the documented full kernel/certificate frontier
  campaign.

## Blockers

- The committed broad sweep is historical for the current factor path, and the
  latest hybrid seam measurement was a high-load local single-shot rather than
  a scheduled-hardware comparator run.
