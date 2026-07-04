# Delete the legacy bounded combinator surface (factorWithBound) — issue #8578

## Accomplished

Part 1 of the BZ factor-path cleanup. Deleted the entire legacy bounded
combinator surface; production `factor = factorHybrid` is untouched.

- `HexBerlekampZassenhaus/Basic.lean`: deleted 37 declarations
  (`factorWithBound`, `factorWithBound?`, `factorSlowWithBound`,
  `factorWithBoundUsesExhaustiveBranch` and all `factorWithBound_*` /
  `factorWithBound?_*` lemmas) plus the one `factorWithBound` product
  `#guard`. Cleaned four survivor docstrings that cross-referenced deleted
  names (repointed to the surviving `factor_*` hybrid analogues). Rewrote the
  `def factor` docstring to describe the hybrid dispatch (classical tier under
  a level-aware subset budget, CLD lattice tier on decline, `factorSlowTrial`
  totality backstop) per the SPEC *Hybrid dispatch* section.
- `HexBerlekampZassenhausMathlib/Basic.lean`: deleted 9 lemmas whose
  statements/hypotheses mention `factorWithBound` (the `_entries_irreducible`
  / `_entry_zpolyIrreducible_*` / `_exhaustive_branch_entry_core_*` families,
  including their default-precision `factor_*` specialisations). Cleaned one
  survivor bundle docstring. This removed one pre-existing `sorry`.
- `HexBerlekampZassenhausMathlib/IntReductionMod.lean`: deleted 15 lemmas
  (the per-branch irreducibility substrate that fed the old capstone:
  small-mod-singleton / constant / quadratic / slow-quadratic / exhaustive
  branch irreducibility lemmas, the `exhaustiveCoreFactorsWithBound_expansion_*`
  and `reassemblyExpansionComplete_exhaustive_*` supports). Cleaned four
  survivor docstrings.
- `conformance/HexBerlekampZassenhaus/Conformance.lean`: deleted the three
  `factorWithBound (…) 4` product `#guard`s (each duplicated an adjacent
  `factor` guard) and updated the coverage docstring.
- `DEV.md`: updated the public-entry note (dropped the deleted `factorWithBound`).

Deletions were driven by a name/comment-aware parser plus a consumer-closure
check: verified every code reference to a deleted name lives inside another
deleted decl (zero external code consumers), so `factor_headline`,
`factor_irreducible_of_nonUnit`, the `factorHybrid*`/`factorLattice*`/
`factorClassical*` families, and the kernel-cert path are untouched.

## Current frontier

Whole-graph `lake build` green (4088 jobs). `HexConformance` +
`hexbz_bench` + `hexbz_emit_fixtures` build green (449 jobs); the BZ
conformance `#guard`s pass, `hexbz_emit_fixtures` emits 312 fixtures, and
`bz_trace_gate.py` reports 52 traces / 0 failures. Required-scope grep for
`factorWithBound` / `factorSlowWithBound` / `factorWithBoundUsesExhaustiveBranch`
is empty across `*.lean`, `bench/`, `conformance/`, `scripts/`, `DEV.md`,
and the SPEC. No new `sorry`/`axiom` (one `sorry` removed).

## Next step

Continue the cleanup sequence: retire `factorFast`, then prune the
exhaustive-core proofs, then retire `factorSlowModular`, then the renames and
hybrid collapse. The one remaining out-of-scope stale mention is
`status/hex-berlekamp-zassenhaus.scaffolding-reviewed` (a historical
phase-review snapshot, left as history).

## Blockers

None.
