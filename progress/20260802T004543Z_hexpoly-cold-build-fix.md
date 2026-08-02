# Accomplished

- Reproduced a cold, source-only `HexPoly.Euclid` failure through the Mathlib-free SOS staging package on Lean 4.33.0-rc1.
- Identified the missing classical decidability at the `NatPrime n` case split and added the local `classical` declaration.
- Verified `lake build HexPoly.Euclid` and the monorepo `lake build` after the fix.
- Added an exact old-blob/new-blob proof-only runtime exemption so this erased proof change does not falsely invalidate factorization timings; any later edit to the file expires the exemption automatically.

# Current frontier

- The fix and narrowly verified benchmark-freshness exemption are under review in `fix/hexpoly-natprime-decidable`.
- SOS still pins the immutable `hex-poly` rc1 tag, so its clean source build cannot consume this fix yet.

# Next step

- Merge the fix, publish `hex-poly` through the release-sync workflow, tag the new mirror revision, and update the Mathlib-free SOS staging tag.

# Blockers

- None.
