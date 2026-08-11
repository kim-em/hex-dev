# Rewrite stale open issues

**Accomplished**

- Rewrote GitHub issue #8664 as the current HexMatrix task for a measured,
  periodic-reduction `ZMod64` Strassen base kernel.
- Removed #8664's disproved Berlekamp-nullspace consumer premise and its unsafe
  one-final-reduction shape; added the generic-dimension overflow constraint,
  measurement gate, `StrassenConfig.Valid` proof target, and explicit scope.
- Rewrote GitHub issue #8569 around the current certificate tactic stack.
- Replaced the retired `irreducible_cert` / `Hex.factor` framing with
  `factor_poly`, `irreducibility`, their bang fallbacks, and
  `Hex.ZPoly.factorize`; added baseline repair, coverage/decline measurement,
  honest timing separation, and Linear-vs-Incremental replay deliverables.
- Verified both issues remain open with their original labels and no assignees.

**Current frontier**

- #8664 and #8569 are now current, premise-checked directives suitable for
  backlog prioritization.

**Next step**

- Recompute the reduced claimable backlog if requested, treating #8853 as
  tracking-only and #8369/#8370 as parked.

**Blockers**

- None.
