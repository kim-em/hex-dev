import HexBerlekamp.Basic

/-!
Executable Berlekamp split-step factoring for `hex-berlekamp`.

This module adds the factoring-facing surface promised by the spec. It first
exposes the single-witness split primitive `gcd(f, h - c)`, then builds the
public Berlekamp factorization driver by computing the fixed-space kernel once
and repeatedly applying those witnesses to the current factor list.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- Result of one Berlekamp kernel-witness split search. -/
structure SplitResult (p : Nat) [ZMod64.Bounds p] where
  splitConstant : ZMod64 p
  factor : FpPoly p
  cofactor : FpPoly p

/-- Public result of executable Berlekamp factorization. -/
structure Factorization (p : Nat) [ZMod64.Bounds p] where
  input : FpPoly p
  factors : List (FpPoly p)

/-- Multiply a list of `F_p[x]` factors in stored order. -/
def factorProduct (factors : List (FpPoly p)) : FpPoly p :=
  factors.foldl (fun acc factor => acc * factor) 1

/-- Product of the factors returned by a `Factorization`. -/
def Factorization.product (result : Factorization p) : FpPoly p :=
  factorProduct result.factors

/-- The gcd candidate attached to one field constant `c`. -/
def splitFactorAt (f witness : FpPoly p) (c : ZMod64 p) : FpPoly p :=
  DensePoly.gcd f (witness - FpPoly.C c)

/-- `true` exactly when the gcd candidate is nonconstant and not all of `f`. -/
private def isNontrivialSplitFactor (f g : FpPoly p) : Bool :=
  !g.isZero && g.degree? ≠ some 0 && g ≠ f

/-- Search the constants `0, 1, ..., p - 1` for a nontrivial Berlekamp split. -/
private def kernelWitnessSplitAux (f witness : FpPoly p) : Nat → Nat → Option (SplitResult p)
  | 0, _ => none
  | fuel + 1, c =>
      let splitConstant := ZMod64.ofNat p c
      let factor := splitFactorAt f witness splitConstant
      if isNontrivialSplitFactor f factor then
        some
          { splitConstant
            factor
            cofactor := f / factor }
      else
        kernelWitnessSplitAux f witness fuel (c + 1)

/--
Search the Berlekamp split candidates `gcd(f, h - c)` over all constants
`c : F_p`, returning the first nontrivial factorization found.
-/
def kernelWitnessSplit? (f witness : FpPoly p) : Option (SplitResult p) :=
  kernelWitnessSplitAux f witness p 0

/-- Try a list of kernel witnesses against one current factor. -/
private def splitWithWitnesses? (f : FpPoly p) : List (FpPoly p) → Option (SplitResult p)
  | [] => none
  | witness :: witnesses =>
      match kernelWitnessSplit? f witness with
      | some split => some split
      | none => splitWithWitnesses? f witnesses

/-- Split the first factor in the list that admits a Berlekamp witness split. -/
private def splitFirstFactor? (witnesses : List (FpPoly p)) :
    List (FpPoly p) → Option (List (FpPoly p))
  | [] => none
  | factor :: rest =>
      match splitWithWitnesses? factor witnesses with
      | some split => some (split.factor :: split.cofactor :: rest)
      | none =>
          match splitFirstFactor? witnesses rest with
          | some rest' => some (factor :: rest')
          | none => none

/--
Repeatedly split the current factor list using the fixed-space witnesses.
The fuel bounds the executable loop; for square-free input, every successful
split increases the factor count and the natural bound is the input size.
-/
private def berlekampFactorLoop (witnesses : List (FpPoly p)) :
    Nat → List (FpPoly p) → List (FpPoly p)
  | 0, factors => factors
  | fuel + 1, factors =>
      match splitFirstFactor? witnesses factors with
      | some factors' => berlekampFactorLoop witnesses fuel factors'
      | none => factors

/--
Compute the Berlekamp factorization of a monic polynomial over `F_p` by
building the fixed-space kernel of `Q_f - I` and repeatedly splitting current
factors with the resulting kernel representatives.
-/
def berlekampFactor (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] : Factorization p :=
  let witnesses := (fixedSpaceKernel f hmonic).toList
  { input := f
    factors := berlekampFactorLoop witnesses (f.size + 1) [f] }

theorem splitFactorAt_spec (f witness : FpPoly p) (c : ZMod64 p) :
    splitFactorAt f witness c = DensePoly.gcd f (witness - FpPoly.C c) := by
  rfl

private theorem splitFactorAt_mul_div_eq
    [ZMod64.PrimeModulus p]
    (f witness : FpPoly p) (c : ZMod64 p) :
    splitFactorAt f witness c * (f / splitFactorAt f witness c) = f := by
  have hspec := DensePoly.div_mul_add_mod f (splitFactorAt f witness c)
  have hmod :
      f % splitFactorAt f witness c = 0 := by
    rw [splitFactorAt_spec]
    exact DensePoly.mod_eq_zero_of_dvd f (DensePoly.gcd f (witness - FpPoly.C c))
      (DensePoly.gcd_dvd_left f (witness - FpPoly.C c))
  rw [hmod] at hspec
  exact (DensePoly.mul_comm_poly (splitFactorAt f witness c)
      (f / splitFactorAt f witness c)).trans
    ((DensePoly.add_zero_poly
      ((f / splitFactorAt f witness c) * splitFactorAt f witness c)).symm.trans hspec)

private theorem kernelWitnessSplitAux_product_spec
    [ZMod64.PrimeModulus p]
    (f witness : FpPoly p) (fuel c : Nat) (r : SplitResult p)
    (hsplit : kernelWitnessSplitAux f witness fuel c = some r) :
    r.factor * r.cofactor = f := by
  induction fuel generalizing c with
  | zero =>
      simp [kernelWitnessSplitAux] at hsplit
  | succ fuel ih =>
      unfold kernelWitnessSplitAux at hsplit
      let splitConstant := ZMod64.ofNat p c
      let factor := splitFactorAt f witness splitConstant
      by_cases hnon : isNontrivialSplitFactor f factor
      · simp [splitConstant, factor, hnon] at hsplit
        cases hsplit
        exact splitFactorAt_mul_div_eq f witness splitConstant
      · simp [splitConstant, factor, hnon] at hsplit
        exact ih (c + 1) hsplit

private theorem isNontrivialSplitFactor_not_zero
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    !g.isZero := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h ⊢

private theorem isNontrivialSplitFactor_degree_ne_zero
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g.degree? ≠ some 0 := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h
  exact h.1

private theorem isNontrivialSplitFactor_ne_input
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g ≠ f := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h
  exact h.2

private theorem isNontrivialSplitFactor_ne_one
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g ≠ 1 := by
  intro hg
  have hnotZero := isNontrivialSplitFactor_not_zero f g h
  have hdegree := isNontrivialSplitFactor_degree_ne_zero f g h
  subst g
  by_cases hone : (1 : ZMod64 p) = 0
  · have honePoly : (1 : FpPoly p) = 0 := by
      change DensePoly.C (1 : ZMod64 p) = 0
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_C]
      rw [hone]
      by_cases hn : n = 0 <;> simp [hn] <;> rfl
    rw [honePoly] at hnotZero
    have hzeroIsZero : (0 : FpPoly p).isZero = true := rfl
    rw [hzeroIsZero] at hnotZero
    simp at hnotZero
  · have honeDegree : (1 : FpPoly p).degree? = some 0 := by
      change (DensePoly.C (1 : ZMod64 p)).degree? = some 0
      have hcoeffs := DensePoly.coeffs_C_of_ne_zero (R := ZMod64 p) hone
      simp [DensePoly.degree?, DensePoly.size, hcoeffs]
    exact hdegree honeDegree

private theorem kernelWitnessSplitAux_nontrivial
    (f witness : FpPoly p) (fuel c : Nat) (r : SplitResult p)
    (hsplit : kernelWitnessSplitAux f witness fuel c = some r) :
    !r.factor.isZero ∧ r.factor ≠ 1 ∧ r.factor ≠ f := by
  induction fuel generalizing c with
  | zero =>
      simp [kernelWitnessSplitAux] at hsplit
  | succ fuel ih =>
      unfold kernelWitnessSplitAux at hsplit
      let splitConstant := ZMod64.ofNat p c
      let factor := splitFactorAt f witness splitConstant
      by_cases hnon : isNontrivialSplitFactor f factor
      · simp [splitConstant, factor, hnon] at hsplit
        cases hsplit
        exact ⟨isNontrivialSplitFactor_not_zero f factor hnon,
          isNontrivialSplitFactor_ne_one f factor hnon,
          isNontrivialSplitFactor_ne_input f factor hnon⟩
      · simp [splitConstant, factor, hnon] at hsplit
        exact ih (c + 1) hsplit

/--
Any successful Berlekamp split records a factor and cofactor whose product is
the original polynomial.
-/
theorem kernelWitnessSplit_product_spec
    [ZMod64.PrimeModulus p]
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    r.factor * r.cofactor = f := by
  exact kernelWitnessSplitAux_product_spec f witness p 0 r hsplit

/--
Any successful Berlekamp split is nontrivial: the returned factor is neither
`0`, `1`, nor the full input polynomial.
-/
theorem kernelWitnessSplit_nontrivial
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    !r.factor.isZero ∧ r.factor ≠ 1 ∧ r.factor ≠ f := by
  exact kernelWitnessSplitAux_nontrivial f witness p 0 r hsplit

/--
The executable Berlekamp factorization preserves the input polynomial as the
product of the returned factors for square-free monic inputs.
-/
theorem prod_berlekampFactor
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (berlekampFactor f hmonic).product = f := by
  sorry

end Berlekamp

end Hex
