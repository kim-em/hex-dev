# HexLLL / HexLLLMathlib pre-release review

## Accomplished

Reviewed both libraries for public release (no code changes). Verified
health directly rather than trusting the two exploration subagents I
dispatched — both agents hallucinated a large "missing docstrings"
finding (stale monolith line numbers, claimed headline theorems were
undocumented when they are not).

Verified facts:
- 0 `sorry`, 0 `axiom`, 0 `native_decide` in either library.
- `lake build HexLLL HexLLLMathlib` green; no warnings touch these two
  libraries (the `@[expose] has no effect` / unused-tactic warnings are
  in HexMatrix / HexGramSchmidt / HexBareissMathlib).
- No `set_option`/`maxHeartbeats` hacks, no `#eval`/`#check`/`dbg_trace`
  debug code, no TODO/FIXME, no commented-out code.
- Docstring coverage is actually excellent. Every `@[expose]` def in
  HexLLL is documented except `Provider.bump`, `Provider.intNat?`,
  `Provider.slice` (internal helpers) and the two `ProviderProbe.main`
  executables. Every headline theorem in HexLLLMathlib has a detailed
  docstring.

## Current frontier

Applied items 1-4 on branch `hexlll-release-polish` (build green, 2581
jobs; bench green):
1. Privatized six file-local Mathlib-layer lemmas
   (`gramMatrix_takeRows_eq_principalSubmatrix`,
   `independent_of_upperTriangular_pos_diag`, `swapStep_valid` in Reducer;
   `rowCombination_mem_prefixSubmodule`, `prefixRowCombination_memLattice`,
   `norm_sq_intRowToEuclidean` in Bridge). The Provider helpers could NOT
   be privatized — the module system forbids a public exposed def
   (`recordOutcome`, `validateFlat`, `tryReduce`) from referencing a
   private one. Better fix found (Kim's catch): `intNat?` and `slice` were
   reinventing core `Int.toNat?` and `Array.extract`; deleted both and
   used the stdlib versions. `bump` is domain-specific; kept + documented.
2. README quickstart now leads with `#check @lll.firstShortVector` / `@lll`
   and names the guarantee theorem; the proof-free `#eval` stays as the
   labeled run-on-data path (a verified `#eval` is impossible — `independent`
   has no Mathlib-free Decidable instance).
3. Renamed `reduced_first_row_norm_sq_le_of_mem_latticeSubmodule`
   → `reduced_first_row_norm_sq_le`.
4. Removed banned word "smoke" from the report and two bench comments.

Left alone per Kim: `@[inline]` consistency (needs care).

## Next step

Open the polish PR. Adversarial second review (Codex) requested.

## Blockers

None.
