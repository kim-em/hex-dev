# Phase 4/5/6 checkpoint 52

Scope: checkpoint for merged work after summarize issue #6024, covering the
current HexMatrix / HexMatrixMathlib Plucker assembly, HexPolyFp SquareFree
provider, HexPolyZMathlib Boyd/Mahler, HexLLL, HexGFq / HexGFqField, and BZ
frontiers.

## Landed work

### HexMatrix and HexMatrixMathlib Plucker assembly

The determinant front moved from one-row bridge substrate to a usable ordered
four-row `nDet` Plucker kernel.

- #6048 assembled the two-row adjugate replacement determinant identity in the
  Mathlib bridge layer.
- #6065 added ordered `nMatrix` row-transport helpers.
- #6070 exposed ordered cofactor-row pairings for the bridge path.
- #6081 exposed the ordered Plucker determinant row replacements.
- #6087 added the ordered q-row `nMatrix` transport.
- #6097 transported ordered p1-row replacements to `nDet` minors.
- #6108 finished the ordered q-row determinant transports to `nDet` minors.
- #6110 added the ordered double-row replacement transport and the signed
  p1-side Plucker wrapper.
- #6120 assembled `det_plucker_three_term_nDet_of_ordered_four`, the raw ordered
  four-row `nDet` Plucker kernel in `HexMatrixMathlib`.

The Mathlib-free HexMatrix side also gained more reusable two-column substrate:

- #6046 added the base two-column determinant substrate.
- #6071 proved the signed ordered-pair expansion for `twoColDet`.
- #6118 proved the cofactor-row two-row Plucker kernel.

Open PR #6122 is now the short determinant wrapper that should close #6112:
rewrite two-row and one-row `setRow` determinants through
`det_setRow_eq_cofactorRowPairing`, then apply the #6118 kernel. The downstream
Mathlib-free ordered `nDet` consumers remain blocked behind that wrapper and the
subsequent row-replacement transport chain.

### HexPolyFp SquareFree normalized provider

The SquareFree front found and isolated a real shape mismatch in the
derivative-active provider chain.

- #6033 reviewed the HexPolyFp Phase 6 API surface and kept follow-up work
  narrow.
- #6058 added the square-free decomposition multiplicity wrapper.
- #6062 hid quotient finite-field internals while preserving the public field
  surface.
- #6089 proved the derivative-active nonzero payload.
- #6116 added the normalized derivative-active payload provider.

The important correction is that the raw provider shape is false: derivative
active states may carry non-1 constant gcd or residual values even though their
normalized payload is reachable. The live continuation has been split into
#6124, which must establish the local raw tail reachability invariant or
normalize the private residual path, and #6125, which then mechanically refactors
the five provider consumers to use the normalized closed provider.

### HexPolyZMathlib Boyd and Mahler replacement

The Schur/Boyd route was narrowed after the counterexample to the old
unconditional derivative-bound chain.

- #6047 added the counterexample guard for the false degree-two Schur
  one-exterior count.
- #6117 clarified the Boyd boundary-comparison replacement theorem and its
  required derivative-bound hypothesis.

The old global complex theorem
`p.derivative.mahlerMeasure <= p.natDegree * p.mahlerMeasure` must stay out of
the tree. Issue #6121 is claimed to find a valid source theorem or direct
integer-side replacement for #5266. Until that lands, #5266 and the BHKS Lemma
5.1 coefficient-bound chain remain blocked.

### HexLLL performance

The exact-integer Gram path received a focused implementation tightening rather
than a broad redesign.

- #6039 trimmed HexLLL Gram array setup.
- #6053 threaded scaled-coefficient row-size invariants.
- #6072 switched scaled coefficient updates to a row-mutating path.

The harsh-cubic front is still a performance frontier, not a proof-interface
front. Further dispatch should be driven by fresh benchmark evidence and should
stay scoped to the exact-integer Gram construction hot path.

### HexGFq and HexGFqField Phase 6 polish

The finite-field API polish continued reducing exposed internals while keeping
the public operation surface stable.

- #6034 audited the HexGFqField Phase 6 API.
- #6061 repaired GFq field prime-modulus evidence.
- #6063 hid HexGFqField inverse xgcd internals.
- #6082 tightened `HexGFqField.Basic` import layering.
- #6083 added GFq field operation docstrings.
- #6102 exposed the canonical Frobenius wrapper on Conway-backed `GFq`.
- #6109 audited the GF2q equivalence surface.

This area is mostly in polish mode. New work should continue as small review or
API-hiding issues rather than broad implementation tasks.

### BZ dispatch and determinant substrate cleanup

The BZ executable front continued removing stale fallback behavior and cleaning
proof dispatch paths.

- #6038 cleaned the BZ fast-dispatch product proofs after the prime-data gate
  landed.
- #6084 reviewed the BHKS D1 frontier and left the main D1 chain blocked behind
  the Mahler/Boyd and coefficient-bound prerequisites.

The headline directives #2564, #2567, and #2637 remain dependency-blocked. They
should not be claimed until their prerequisite chains are actually unblocked.

## Current frontier

Open PRs:

- #6122, `HexMatrix: wrap cofactor Plucker as two-row setRow determinant
  identity`.
- #2656, draft SPEC PR for real roots and Sturm.

Ready or claimed work:

- #6121 is claimed for the valid HexPolyZMathlib derivative Mahler source
  theorem needed by #5266.
- #6124 is ready for the HexPolyFp derivative-active raw tail reachability
  invariant.
- #6125 is blocked on #6124 and should be the mechanical provider-consumer
  refactor afterward.

Blocked fronts:

- #5266 is blocked on #6121; BHKS Lemma 5.1 and D1 remain blocked downstream of
  #5266/#5223/#5224 and the older HO directive chain.
- HexMatrix Mathlib-free Plucker consumers #6105, #6101, #6094, #6044, #6030,
  and #6031 remain blocked behind the row-replacement transport chain starting
  at #6104/#6112.
- Gram-Schmidt consumers #5805 and #5655 remain blocked behind the Mathlib-free
  Plucker basis-case chain.
- BZ rewrite and executable irreducibility issues remain blocked behind
  #2564/#2567 and their substrate chains.

## Recommended next actions

1. Let #6122 land before dispatching #6104 or downstream Mathlib-free ordered
   `nDet` consumer issues.
2. Prioritize #6124 over #6125; the provider refactor is mechanical only after
   the raw tail invariant or private normalization route exists.
3. Treat #6121 as the gate for the Robinson/Boyd integer transport chain. If it
   narrows the theorem, replan #5266 around the narrowed hypotheses rather than
   reviving the invalid unconditional statement.
4. Keep HexGFq / HexGFqField work in small Phase 6 polish slices unless a
   specific downstream consumer exposes a real public-API gap.
5. Keep BZ and BHKS directive issues blocked until their explicit dependencies
   close; fresh workers should take the narrow prerequisite issues instead.
