# Primality and integer-factorization SPEC review

## Accomplished

- Reworked `SPEC/Libraries/hex-primality.md` to repair the
  multiplicative-order and Pocklington contracts, tie searched
  certificates to their requested subjects, expose one reusable checked
  Brent-rho primitive, account for the sieve mask bound and batched
  replay architecture, and make randomized search failures resumable.
- Reworked `SPEC/Libraries/hex-int-factor.md` around indexed checked
  factorizations, raw serializable order certificates, explicit partial
  results, local divisor/Carmichael semantics, checked cyclotomic
  candidates, shared rho, and implementable stage-1-only p-1/ECM scope.
- Reconciled the design with the landed HexConway Tier 2 proofs, current
  Lean/Mathlib pins, current PARI certificate API, UInt64-only Montgomery
  context, and the repository's randomness convention.
- Obtained and independently checked a fresh Claude/Opus review. Its
  substantive findings were incorporated, including proof-infrastructure
  milestones, bounded versus total primality APIs, failure-state
  preservation, checker cost corrections, and stale source citations.
- `git diff --check`, relative-link and code-fence checks,
  `scripts/check_dag.py`, and `scripts/check_phase4.py` pass. No Lean
  source changed, so there is no Lean build delta.

## Current frontier

The two source-less future-library SPECs are internally consistent and
ready for publication from the clean
`spec-primality-factor-review-fixes` branch. Upstream changes since the
branch point do not touch either SPEC.

## Next step

Rebase onto current `origin/main`, open the documentation PR, verify its
actual Actions job state and logs, and merge it.

## Blockers

None.
