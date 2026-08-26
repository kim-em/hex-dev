# Matrix encapsulation — the "beautiful minimal" design (v4.32)

Branch `matrix-encapsulation-v432` (pushed). Supersedes the earlier
pairconv-everything approach (which was unnecessary churn).

## The design (decided with Kim mid-session)

`Hex.Matrix` becomes an opaque one-field `structure` wrapping the row data.
Two kinds of `GetElem`:

- **Entry access `M[(i, j)]`** (`Nat×Nat`, `Fin×Fin`): *computable*, O(1),
  flat-representation-ready. This is what compiled code must use for entries.
- **Row access `M[i]` / `M[i][j]`**: routed through a **`noncomputable`
  instance** that delegates to `getRow`. Proofs may use `M[i]` / `M[i][j]`
  freely (Props don't compile), but any *compiled* definition that touches
  `M[i]` fails to compile — the intended guard against materializing a whole
  row (O(m)) to read one entry under a future flat `Vector R (n*m)` layout.
- `getRow` stays **computable** (rows, author opts into the cost).

Key simp lemmas in `HexMatrix/Basic.lean`:
`getElem_eq_getRow` (`M[i] → getRow`), `getElem_pair_eq_nested`
(`M[(i,j)] → M[i][j]`), `getRow_ofRows`, `rows_*` reduction lemmas.
`HexMatrix/Vector/Modify.lean` adds linear `Matrix.modify/swap/mapRows`.

## Why this is near-minimal vs `main`

Because proofs keep `M[i][j]` and only *compiled defs* must change, restoring
each file from `main` and rebuilding flags **only**:
1. computable-def entry reads `M[i][j]`/`M[i]` → `M[(i,j)]` / `getRow` (the
   noncomputable guard pinpoints these);
2. `Vector`-method-on-`Matrix` (`M.set`→`setRow`, `M.map`→`mapRows`,
   `M.swap`→`Matrix.swap`, construction → `ofRows`/`ofFn`);
3. a few proof spots that `unfold` a now-pair def — add
   `simp only [getElem_pair_eq_nested]` (or `getRow, Fin.getElem_fin`) to
   re-normalize to the nested `M[i][j]` form the entry lemmas are stated in.

Plucker dropped from 69 errors (old approach) to **3** def-read fixes.

## Status

Green on v4.32: **HexMatrix, HexRowReduce, HexDeterminant** (all committed).

`HexBareiss`: def-reads done; `findPivotAux` correspondence proofs fixed
(pattern: `simp only [findPivotAux, hlt, dif_pos, getRow, Fin.getElem_fin] at h;
rw [if_pos/if_neg (by simpa [getRow, Fin.getElem_fin] using <Fin-hyp>)] at h`).
~13 errors remain, all the same flavour: `stepMatrix` / `pivotLoop` /
`matrixToRows` correspondence proofs where a hypothesis in nested/Nat form
(`M[start][col.val]`) must line up with a goal normalized to
`M.rows[start][↑col]` — add `getRow, Fin.getElem_fin` to the closing simp, or
use the explicit `if_pos/if_neg (by simpa …)` pattern. The `simpa [getRow,
Fin.getElem_fin] using hNat` bridge is the reliable closer.

## Next

1. Finish HexBareiss (~13, mechanical — same normalization).
2. Restore-from-main + minimal-fix: `HexMatrixMathlib` (matrixEquiv via entry
   API — see plan "Hard spots"), `HexRowReduceMathlib`, `HexDeterminantMathlib`,
   `HexBareissMathlib`.
3. `HexGramSchmidt(+Mathlib)`, `HexLLL(+Mathlib)`,
   `HexBerlekamp(Zassenhaus)(+Mathlib)`.
4. `bench/` + `conformance/`; full-graph green; update PR #8442; SPECs
   (`HexMatrix/SPEC` opaque boundary + the noncomputable-row-guard rationale).

Reference branch `matrix-encapsulation` (old baseline, fully green) remains the
oracle for hard proof bodies.
