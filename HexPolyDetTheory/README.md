# Certified determinants

Import `HexPolyDetTheory` to enable the general symbolic determinant evaluator.
The public `det` syntax and numeric certificate backend belong to
`HexBareissTheory`; this companion attaches a symbolic handler. Symbolic
literals are evaluated with Mathlib's division-free Bird recurrence, with
cached and checked scalar equalities. The evaluator works over commutative
rings, including rings of positive characteristic. It never calls Mathlib's
`norm_det` or `eval_det` as a fallback.

```lean
import HexPolyDetTheory

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by det

example {R : Type} [CommRing R] (x : R) : True := by
  det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) R) with d hd
  -- d is the computed determinant; hd : Matrix.det … = d
  trivial

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1; 1, x] = (det% !![x, 1; 1, x]).value :=
  (det% !![x, 1; 1, x]).proof
```

`det% A` returns `HexMatrixTheory.Certified Matrix.det A` without a proposed
answer. `simp only [Hex.normPolyDet]` rewrites supported occurrences on demand.
`Hex.norm_det` remains the numeric-only certificate simproc. Both tactic forms
accept `(maxHeartbeats := …)` and `(maxRelationWork := …)`; the numeric `det`
form also retains `-packing`. The symbolic limits default to 2,000,000 public
heartbeat units and 1,000,000 distinct relation sum tails. The caller's
smaller heartbeat allowance still applies. A zero local limit declines.

The result is a readable arithmetic expression, sometimes with compact
symbolic quotients. A supplied equality is proved separately from the
computed result; failure to establish a symbolic equality is a decline. The
`HexMatrix.certificate` trace reports resource limits, comparisons and
recoverable declines. The opt-in simproc leaves a declined occurrence intact.

The retained `Sound` and `Residue` modules prove the plain native polynomial
witness and check APIs, including modular checker soundness. They are not
imported by the symbolic tactic module.
