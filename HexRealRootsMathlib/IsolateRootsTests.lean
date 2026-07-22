/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- PLAIN `public import` only: NO `import all`. The replay `decide`s below must
-- reduce in the kernel through the exposed count-check closure and the
-- `SturmChainCert` / `orderedAdjacent` certificates alone, exactly as a
-- downstream `module` consumer of the `isolate_roots` elaborator would see them.
public import HexRealRootsMathlib.IsolateRoots

public section

/-!
# Unit tests for the `IsolatedRealRoots` API

Exercises every constructor on literal data and the `isolate_roots_bridge`
tactic on all four coefficient-ring shapes, through the public API only (a plain
import, no `import all`).
-/

open Hex Polynomial HexRealRootsMathlib

namespace HexRealRootsMathlib.Tests

/-! ## The `isolate_roots_bridge` tactic (deliverable 7) -/

/-- `x⁴ − 2` over `ℝ`. -/
example : ∀ x : ℝ,
    aeval x (HexPolyZMathlib.toPolynomial (DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1])) = 0 ↔
      aeval x (X ^ 4 - 2 : Polynomial ℝ) = 0 := by
  isolate_roots_bridge

/-- `x⁴ − 2` over `ℤ`. -/
example : ∀ x : ℝ,
    aeval x (HexPolyZMathlib.toPolynomial (DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1])) = 0 ↔
      aeval x (X ^ 4 - 2 : Polynomial ℤ) = 0 := by
  isolate_roots_bridge

/-- `x⁴ − 2` over `ℚ`. -/
example : ∀ x : ℝ,
    aeval x (HexPolyZMathlib.toPolynomial (DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1])) = 0 ↔
      aeval x (X ^ 4 - 2 : Polynomial ℚ) = 0 := by
  isolate_roots_bridge

/-- A negative leading coefficient: `1 − x²` over `ℝ`. -/
example : ∀ x : ℝ,
    aeval x (HexPolyZMathlib.toPolynomial (DensePoly.ofCoeffs #[(1 : Int), 0, -1])) = 0 ↔
      aeval x (-(X ^ 2) + 1 : Polynomial ℝ) = 0 := by
  isolate_roots_bridge

/-! ## `IsolatedRealRoots.of` on `x⁴ − 2` (deliverable 8) -/

/-- `x⁴ − 2`, reified: `-2 + x⁴`. -/
def x4m2 : ZPoly := DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1]

/-- Squarefree certificate for `x⁴ − 2`, by `decide` on its Sturm chain. -/
theorem sqfree_x4m2 : ZPoly.SquareFreeRat x4m2 :=
  squareFreeRat_of_hasSquarefreeSturmChain _ (by decide)

/-- The complete run of `x⁴ − 2`: the two isolate? intervals `(-4, 0]`, `(0, 4]`. -/
def run_x4m2 : RealRootIsolations x4m2 where
  isolations :=
    #[⟨⟨Dyadic.ofInt (-4), Dyadic.ofInt 0, by decide⟩, by decide⟩,
      ⟨⟨Dyadic.ofInt 0, Dyadic.ofInt 4, by decide⟩, by decide⟩]
  ordered := by decide
  complete := by decide

/-- `x⁴ − 2` isolated via `IsolatedRealRoots.of`. -/
noncomputable def iso_x4m2_of :
    IsolatedRealRoots (HexPolyZMathlib.toPolynomial x4m2) run_x4m2.isolations.size :=
  IsolatedRealRoots.of x4m2 (ne_zero_of_size_ne_zero (by decide)) sqfree_x4m2 run_x4m2

/-! ## The replay constructor `IsolatedRealRoots.ofCert` on `x⁴ − 2` -/

/-- The reified Sturm chain of `x⁴ − 2`: `[x⁴ − 2, x³, 1]`. -/
def chain_x4m2 : Array ZPoly :=
  #[DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1],
    DensePoly.ofCoeffs #[(0 : Int), 0, 0, 1],
    DensePoly.ofCoeffs #[(1 : Int)]]

/-- `x⁴ − 2` isolated via the replay constructor: every field a `decide` on the
reified chain. -/
noncomputable def iso_x4m2_replay :
    IsolatedRealRoots (HexPolyZMathlib.toPolynomial x4m2) 2 :=
  IsolatedRealRoots.ofCert (chain := chain_x4m2)
    (iso := ⟨#[⟨⟨Dyadic.ofInt (-4), Dyadic.ofInt 0, by decide⟩,
                RealRootIsolation.count_one_of_cert (chain := chain_x4m2) (by decide) _ (by decide)⟩,
              ⟨⟨Dyadic.ofInt 0, Dyadic.ofInt 4, by decide⟩,
                RealRootIsolation.count_one_of_cert (chain := chain_x4m2) (by decide) _ (by decide)⟩],
        rfl⟩)
    (hsize := by decide) (hsf := by decide) (hcert := by decide)
    (hordered := by decide) (hcomplete := by decide)

/-! ## Replay + `congrRoots` on `(x − 1)²(x − 3)` -/

/-- `(x − 1)²(x − 3) = x³ − 5x² + 7x − 3`, reified. -/
def q : ZPoly := DensePoly.ofCoeffs #[(-3 : Int), 7, -5, 1]

/-- The reified squarefree core `(x − 1)(x − 3) = x² − 4x + 3`. -/
def qcore : ZPoly := DensePoly.ofCoeffs #[(3 : Int), -4, 1]

/-- The Sturm chain of the squarefree core: `[x² − 4x + 3, x − 2, 1]`. -/
def chain_qcore : Array ZPoly :=
  #[DensePoly.ofCoeffs #[(3 : Int), -4, 1],
    DensePoly.ofCoeffs #[(-2 : Int), 1],
    DensePoly.ofCoeffs #[(1 : Int)]]

/-- The squarefree core isolated via replay: roots in `(0, 2]` and `(2, 4]`. -/
noncomputable def iso_qcore_replay :
    IsolatedRealRoots (HexPolyZMathlib.toPolynomial qcore) 2 :=
  IsolatedRealRoots.ofCert (chain := chain_qcore)
    (iso := ⟨#[⟨⟨Dyadic.ofInt 0, Dyadic.ofInt 2, by decide⟩,
                RealRootIsolation.count_one_of_cert (chain := chain_qcore) (by decide) _ (by decide)⟩,
              ⟨⟨Dyadic.ofInt 2, Dyadic.ofInt 4, by decide⟩,
                RealRootIsolation.count_one_of_cert (chain := chain_qcore) (by decide) _ (by decide)⟩],
        rfl⟩)
    (hsize := by decide) (hsf := by decide) (hcert := by decide)
    (hordered := by decide) (hcomplete := by decide)

/-- `(x − 1)²(x − 3)` and its squarefree core share the same real roots. Proven
here by explicit factoring; in the elaborator this bridge is
`aevalIff_squareFreeCore` (see `transport_via_squareFreeCore` below), whose
`squareFreeCore q = qcore` step is a meta-level equality since `squareFreeCore`
is intentionally outside the kernel-reducible replay closure. -/
theorem qcore_same_roots (x : ℝ) :
    aeval x (HexPolyZMathlib.toPolynomial qcore) = 0 ↔
      aeval x (HexPolyZMathlib.toPolynomial q) = 0 := by
  unfold qcore q
  rw [aeval_toPolynomial_ofCoeffs, aeval_toPolynomial_ofCoeffs]
  simp [Finset.sum_range_succ, Hex.DensePoly.coeff_ofCoeffs]
  constructor
  · intro h; nlinarith [h]
  · intro h
    have hfac : (x ^ 2 - 4 * x + 3) * (x - 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · nlinarith [h1]
    · have hx : x = 1 := by linarith
      subst hx; norm_num

/-- `(x − 1)²(x − 3)` isolated: replay on the squarefree core, transported onto
`q` by `congrRoots`. -/
noncomputable def iso_q :
    IsolatedRealRoots (HexPolyZMathlib.toPolynomial q) 2 :=
  IsolatedRealRoots.congrRoots qcore_same_roots iso_qcore_replay

/-- The production transport for a non-squarefree input: `congrRoots` along
`aevalIff_squareFreeCore` carries an isolation of the squarefree core onto the
original polynomial. Exercises the exact `congrRoots (aevalIff_squareFreeCore …)`
composition the elaborator emits. -/
noncomputable def transport_via_squareFreeCore
    (H : IsolatedRealRoots (HexPolyZMathlib.toPolynomial (Hex.ZPoly.squareFreeCore q)) 2) :
    IsolatedRealRoots (HexPolyZMathlib.toPolynomial q) 2 :=
  IsolatedRealRoots.congrRoots
    (fun x => aevalIff_squareFreeCore (ne_zero_of_size_ne_zero (by decide)) x) H

/-! ## `IsolatedRealRoots.constant` -/

/-- A nonzero constant has no real roots: the empty isolation. -/
def iso_const : IsolatedRealRoots (Polynomial.C (3 : ℝ)) 0 :=
  IsolatedRealRoots.constant (by simp)

end HexRealRootsMathlib.Tests

/-! Bridge robustness: literals where `simp` alone closes the goal (the
trailing `ring_nf` must not fire on zero goals). -/

example : ∀ x : ℝ,
    Polynomial.aeval x (HexPolyZMathlib.toPolynomial (Hex.DensePoly.ofCoeffs #[3, 0, 0])) = 0 ↔
    Polynomial.aeval x ((Polynomial.C 3 : Polynomial ℤ).map (Int.castRingHom ℤ)) = 0 := by
  isolate_roots_bridge

example : ∀ x : ℝ,
    Polynomial.aeval x (HexPolyZMathlib.toPolynomial (Hex.DensePoly.ofCoeffs #[0, 0, 0])) = 0 ↔
    Polynomial.aeval x ((0 : Polynomial ℤ)) = 0 := by
  isolate_roots_bridge
