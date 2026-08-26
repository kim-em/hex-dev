# HexGF2 module migration — decide-certificate blocker fully resolved

## Accomplished

- Replaced `xorWords` with the in-place fold form (`xorWordsAux` over
  `List.range` + `setIfInBounds`) that reduces under elaborator `decide`,
  unlike the previous `Array.ofFn` definition. Re-proved the spec lemmas
  `xorWordsFold_size`, `xorWordsFold_getElem?`, `xorWords_get?_getD`,
  `xorWords_size`, `xorWords_getD`, `xorWords_self`. `HexGF2.Basic` green.
- Traced the remaining `decide` failures past `xorWords` to two more
  module-exposure stalls and fixed both:
  - `degree?` called `Array.back?`, whose core body is not exposed to a
    downstream module's `decide` (while `getElem?`/`size` are). Inlined it
    as `p.words[p.words.size - 1]?` (verified reducing). Kept the helper
    lemma statements on `back?` and bridged with `Array.back?_eq_getElem?`.
  - `GF2Poly.instDecidableEq` compared `p.words q.words` via `Array.decEq`,
    which stalls under `decide`; switched to comparing `.toList` (List.decEq
    reduces). (This change was already present on the branch.)
- `HexGF2/Smoke.lean`: the `#guard` field-arithmetic checks are meta defs;
  added `public meta import HexGF2.Field` / `HexGF2.Euclid` so the
  instances and `ofUInt64Monic` are accessible at elaboration time.
- Net result: the 7 `decide` irreducibility-certificate proofs in
  `HexGF2/CommonIrreducibility.lean` (AES, GF16, GF65k, GHASH, plus the
  pow-chain quotient witnesses) now reduce. `lake build HexGF2` is green.
  No `sorry`, no `axiom`, `native_decide` still unused.

## Current frontier

- All Hex libraries compile under `lake build`. The only full-build failure
  is a Verso doc-output check, `HexManual/Chapters/HexRowReduce.lean:181`:
  the migrated `Repr (Hex.Matrix R n m)` `#m[...]` instance
  (`HexMatrix/Notation.lean`) is not reaching the legacy manual chapter's
  `#eval` scope, so the kernel-basis example renders the raw nested-Vector
  structure instead of `#m[-2, 1, 0; -3, 0, 1]`. Pre-existing on this
  branch (the file is unmodified vs HEAD), and unrelated to GF2.

## Next step

- Decide whether HexGF2Mathlib / HexGFq / HexGFqMathlib (still legacy) get
  migrated on this branch or a follow-up.
- Separately: fix the HexMatrix `#m[...]` `Repr` exposure so the manual
  renders matrices in notation again (likely an `@[expose]` / public-import
  reachability fix in `HexMatrix/Notation.lean` or the umbrella).
- Benchmark the in-place `xorWords` against the old `Array.ofFn` form to
  confirm the intended speedup.

## Blockers

- None for GF2. The HexManual matrix-`Repr` regression is a separate
  HexMatrix/HexManual exposure task, not a GF2 blocker.
