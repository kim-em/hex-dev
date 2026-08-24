/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Compose
public import HexPolyFp.ModCompose
public import HexPolyFp.Quotient

public section

/-!
Modular composition is quotient evaluation.

`FpPoly.composeModMonic f b g` computes `f(b) mod g` on representatives;
`FpPoly.Quotient.eval f β` evaluates `f` at a quotient element. They are the
same operation seen from either side of the quotient map, and this file says
so.

The proof is one induction: both are Horner folds over the same coefficient
list, in the same orientation. The composition side reduces after each step,
the evaluation side works in the quotient throughout, and `reduce_add` and
`reduce_mul` are exactly what lets one step of each be matched up.

Callers want this when a fact has been *computed* on representatives — the
kind of thing `decide` can discharge — and has to be *stated* about elements
of the quotient field.
-/

namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

local instance : DensePoly.DivModLaws (ZMod64 p) :=
  ZMod64.instDivModLawsZMod64Fp p

namespace Quotient

open Internal

variable {g : FpPoly p} {hmonic : DensePoly.Monic g}
variable {hg_pos : 0 < g.degree?.getD 0}

/-- One Horner step commutes with reduction into the quotient. -/
private theorem reduce_horner_step (acc b : FpPoly p) (c : ZMod64 p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (FpPoly.modByMonic g (acc * b + DensePoly.C c) hmonic) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) +
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) b *
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) acc := by
  have hmod :
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (FpPoly.modByMonic g (acc * b + DensePoly.C c) hmonic) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (acc * b + DensePoly.C c) := by
    apply ext
    simp only [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod,
      DensePoly.mod_mod]
  rw [hmod, reduce_add, reduce_mul]
  rw [Quotient.add_comm, Quotient.mul_comm]

/-- The coefficient-list form: evaluating the embedded coefficients at
`reduce b` is the reduction of the modular Horner walk. -/
private theorem evalCoeffList_map_eq_reduce_composeModMonicList
    (b : FpPoly p) : ∀ coeffs : List (ZMod64 p),
    Internal.evalCoeffList
        (coeffs.map fun c =>
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c))
        (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) b) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (composeModMonicList b g hmonic coeffs)
  | [] => by
      show (0 : Quotient g hmonic hg_pos) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) 0
      symm
      apply ext
      rw [reduce_val, zero_val]
  | c :: cs => by
      rw [List.map_cons, Internal.evalCoeffList_cons,
        evalCoeffList_map_eq_reduce_composeModMonicList b cs]
      show reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) +
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) b *
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (composeModMonicList b g hmonic cs) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (FpPoly.modByMonic g (composeModMonicList b g hmonic cs * b + DensePoly.C c) hmonic)
      rw [reduce_horner_step]

/--
Modular composition on representatives is evaluation in the quotient.

This is the bridge a computed fact has to cross to become a statement about
field elements: `composeModMonic f b g = 0` is `decide`-able, and says exactly
that `f` vanishes at the class of `b`.
-/
theorem eval_reduce_eq_reduce_composeModMonic (f b : FpPoly p) :
    Internal.eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
        (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) b) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (composeModMonic f b g hmonic) := by
  rw [Internal.eval_eq_evalCoeffList]
  unfold Internal.evalQuotientCoeffs composeModMonic
  exact evalCoeffList_map_eq_reduce_composeModMonicList b f.toList

/-- The `composeModMonicImpl` spelling of
{name}`Hex.FpPoly.Quotient.eval_reduce_eq_reduce_composeModMonic`, for callers
whose computation ran through the compiled Horner loop. -/
theorem eval_reduce_eq_reduce_composeModMonicImpl (f b : FpPoly p) :
    Internal.eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
        (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) b) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (composeModMonicImpl f b g hmonic) := by
  rw [eval_reduce_eq_reduce_composeModMonic, composeModMonic_eq_composeModMonicImpl]

/-- Evaluating a polynomial at the quotient class of `X` returns its quotient
class.

This is the quotient evaluation map's defining property, stated for the
project-side evaluator and executable reduction used by Conway compatibility. -/
theorem Internal.eval_X_eq_reduce (f : FpPoly p) :
    Internal.eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
        (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f := by
  rw [show X (g := g) (hmonic := hmonic) (hg_pos := hg_pos) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) FpPoly.X from rfl,
    eval_reduce_eq_reduce_composeModMonic,
    composeModMonic_eq_modByMonic_compose, FpPoly.compose_X_right]
  apply ext
  simp [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

/--
A vanishing modular composition says the polynomial has the class of `b` as a
root.

The `decide`-able left-hand side and the field-level right-hand side, in one
step.
-/
theorem eval_reduce_eq_zero_of_composeModMonicImpl_eq_zero
    {f b : FpPoly p}
    (h : composeModMonicImpl f b g hmonic = 0) :
    Internal.eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
        (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) b) = 0 := by
  rw [eval_reduce_eq_reduce_composeModMonicImpl, h]
  apply ext
  rw [reduce_val, zero_val]

end Quotient

end FpPoly

end Hex
