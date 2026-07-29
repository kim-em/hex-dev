/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Eval

@[expose] public section

/-!
Structural transformations of `Hex.MvPoly`: reordering, renaming,
differentiation, homogeneous restriction, and substitution.
-/

namespace Hex.MvPoly

universe u v

variable {n k : Nat} {R : Type u} {S : Type v}
  {cmp : Mono n → Mono n → Ordering}
  {cmp₂ : Mono n → Mono n → Ordering}
  {cmp' : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp cmp₂] [Std.LawfulEqCmp cmp₂]
  [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']

/-- Rebuild a polynomial under a different monomial comparator. -/
def reorder [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : MvPoly n R cmp₂ :=
  ofTerms p.termsList

/-- Rename variables, adding exponents in fibres and combining all resulting
term collisions. -/
def rename [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → Fin k) (p : MvPoly n R cmp) : MvPoly k R cmp' :=
  p.foldTerms
    (fun acc m c => acc.addMonomial (Mono.rename f m) c)
    0

/-- Decrease the exponent at `i` by one, leaving every other exponent
unchanged. -/
def predAt (i : Fin n) (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun j => if j = i then m[j] - 1 else m[j]

attribute [local instance 1100] Lean.Grind.Semiring.natCast

/-- Formal derivative with respect to variable `i`. -/
def derivative [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc m c =>
      let e := Mono.degreeOf i m
      if e = 0 then acc
      else acc.addMonomial (predAt i m) ((e : R) * c))
    0

/-- Homogeneous component of total degree `d`. -/
def homogeneousComponent [Lean.Grind.Semiring R] [DecidableEq R]
    (d : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degree m = d)

/-- General substitution, mapping coefficients through `f` and variables
through `g`. -/
def bind [Zero R] [Lean.Grind.Semiring S] [DecidableEq S]
    (f : R → S) (g : Fin n → MvPoly k S cmp')
    (p : MvPoly n R cmp) : MvPoly k S cmp' :=
  p.foldTerms
    (fun acc m c => acc + C (f c) * Mono.prod g m)
    0

/-- Substitute polynomials for variables without changing the coefficient
type. -/
def subst [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → MvPoly k R cmp') (p : MvPoly n R cmp) : MvPoly k R cmp' :=
  bind id f p

/-- Compatibility spelling for same-coefficient substitution. -/
def bind₁ [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → MvPoly k R cmp') (p : MvPoly n R cmp) : MvPoly k R cmp' :=
  subst f p

/-- Reconstruct a polynomial by summing its ordered term iteration. -/
def sumToIter [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  ofTerms p.termsList

theorem coeff_reorder [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (reorder (cmp₂ := cmp₂) p) = coeff m p := by
  sorry

theorem coeff_rename [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → Fin k) (m : Mono k) (p : MvPoly n R cmp) :
    coeff m (rename (cmp' := cmp') f p) =
      p.termsList.foldl
        (fun acc term => if Mono.rename f term.1 = m then acc + term.2 else acc) 0 := by
  sorry

theorem coeff_derivative [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin n) (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (derivative i p) =
      ((Mono.degreeOf i m + 1 : Nat) : R) * coeff (Mono.succAt i m) p := by
  sorry

theorem coeff_homogeneousComponent [Lean.Grind.Semiring R] [DecidableEq R]
    (d : Nat) (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (homogeneousComponent d p) =
      if Mono.degree m = d then coeff m p else 0 := by
  sorry

theorem subst_eq [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → MvPoly k R cmp') (p : MvPoly n R cmp) :
    subst f p =
      p.termsList.foldl
        (fun acc term => acc + C term.2 * Mono.prod f term.1) 0 := by
  sorry

theorem partialEval_eq_subst [Lean.Grind.Semiring R] [DecidableEq R]
    (s : Fin n → Option R) (p : MvPoly n R cmp) :
    partialEval s p =
      subst (cmp' := cmp)
        (fun i => match s i with | some x => C x | none => X i) p := by
  sorry

end Hex.MvPoly
