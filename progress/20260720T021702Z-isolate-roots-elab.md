# Stage 3d: the `isolate_roots` term elaborator

## Accomplished

- `HexRealRootsMathlib/IsolateRootsElab.lean`: the production `isolate_roots`
  term elaborator over the landed `ofCert` replay API. Syntax exactly as the
  SPEC/prototype validated:
  `syntax (name := isolateRoots) "isolate_roots" (atomic("(" "width" ":=") term ")")? term : term`.
  - Input dispatch: closed `Hex.ZPoly` via the `evalExpr` DTO shim;
    `Polynomial ℤ/ℚ/ℝ` via a recursive interpreter (`X`, `C`, `OfNat`/numerals,
    `Nat.cast`/`Int.cast`, `+ − * ^`(Nat), `neg`; named defs unfolded one delta
    step under a fuel guard; integer-coefficient enforcement — for `ℚ` leaves,
    evaluate to `Rat` and reject non-integers). Closedness checked with
    `synthesizeSyntheticMVarsNoPostponing` first, for both polynomial and width.
  - Width: evaluated as `ℚ` via the `evalExpr` path; `k = max 0 ⌈log₂ x⁻¹⌉` in
    Int arithmetic; refinement through the cached-chain `refineToWithChain`
    (#8838); pathological cap at `2^-4096` with the dedicated diagnostic.
  - Emission: `ofCert` with reified polynomial + Sturm chain + interval dyadics
    as literals, every hypothesis `by decide` against the reified chain
    (fat-API/thin-meta); `congrRoots (by aeval_iff_bridge)` for `Polynomial`
    inputs; `IsolatedRealRoots.constant` for nonzero constants.
  - Non-squarefree: isolate `squareFreeCore` (computed in-process, reified as a
    literal) and transport with a new sound divisibility bridge
    `aevalIff_radical` (see below), *not* `aevalIff_squareFreeCore (by decide)`.
  - Full error taxonomy, each with a user-grade message.
- `HexRealRootsMathlib/IsolateRootsElabTests.lean`: end-to-end demos (ZPoly and
  `Polynomial ℝ`, three widths, ZPoly width, Wilkinson-6 over `ℤ`, a `ℚ` case,
  non-squarefree `(X-1)^2*(X-3)`, nonzero constant), obtain/have/grind
  consumption, and `#guard_msgs` coverage of every distinct diagnostic.
- Both modules wired into the `HexRealRootsMathlib` umbrella. Full `lake build`
  green (9421 jobs).

## Current frontier

Branch `isolate-roots/elab` pushed; no PR opened yet (per instructions, no merge).

## Key finding: deliverable 5's core transport is infeasible as specified

`aevalIff_squareFreeCore (by decide)` cannot compose with a reified *literal*
square-free core: identifying the literal `coreLit` with `squareFreeCore f`
needs a kernel proof, but `rfl` fails (not defeq) and `decide` gets stuck
(`squareFreeCore`'s rational helpers are unexposed — the SPEC's own "outside the
kernel-reducible replay closure" choice). Implemented the sound alternative
`aevalIff_radical`: from reified cofactors `a`, `b`, a scalar `t`, exponent `k`
with `orig = core * a` and `t·core^(k+1) = a*b` (two `ring` identities on
literals, no `squareFreeCore` reduction), the real roots of `orig` and `core`
coincide. The cofactors are computed at elaboration time by exact
integer-polynomial division.

## Next step

Open the PR when ready. Possible follow-up: a smarter Polynomial→user bridge so
a *top-level opaque named `Polynomial` def* is accepted (currently the interpreter
unfolds defs for the value, but the ℝ-bridge needs the surface polynomial
structurally expandable).

## Blockers

None.
