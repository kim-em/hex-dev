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

/-- Multiply a list of `F_p[x]` factors in stored order, starting from `1`. -/
def factorProduct (factors : List (FpPoly p)) : FpPoly p :=
  factors.foldl (fun acc factor => acc * factor) 1

/-- Product of the factors returned by a `Factorization`. -/
def Factorization.product (result : Factorization p) : FpPoly p :=
  factorProduct result.factors

/-- Empty-list base case for `factorProduct`. -/
@[simp] theorem factorProduct_nil : factorProduct ([] : List (FpPoly p)) = 1 := rfl

/-- Unfold a `Factorization`'s product to the `factorProduct` of its stored factors. -/
@[simp] theorem Factorization.product_def (result : Factorization p) :
    result.product = factorProduct result.factors :=
  rfl

/-- The gcd candidate attached to one field constant `c`. -/
def splitFactorAt (f witness : FpPoly p) (c : ZMod64 p) : FpPoly p :=
  DensePoly.gcd f (witness - FpPoly.C c)

/-- `true` exactly when the gcd candidate is nonconstant and strictly smaller
than `f` in size (i.e. strictly smaller in degree). Strict size suffices to
imply `g ≠ f`; the strict form additionally rules out non-identity unit
multiples `g = u · f`, which is what the downstream `Nodup` argument needs. -/
private def isNontrivialSplitFactor (f g : FpPoly p) : Bool :=
  !g.isZero && g.degree? ≠ some 0 && g.size < f.size

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

/-- Definitional unfolding of `splitFactorAt` to its underlying `gcd` candidate. -/
theorem splitFactorAt_spec (f witness : FpPoly p) (c : ZMod64 p) :
    splitFactorAt f witness c = DensePoly.gcd f (witness - FpPoly.C c) := rfl

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

private theorem isNontrivialSplitFactor_size_lt
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g.size < f.size := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h
  exact h.2

private theorem isNontrivialSplitFactor_ne_input
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g ≠ f := by
  intro hg
  have hsize := isNontrivialSplitFactor_size_lt f g h
  rw [hg] at hsize
  exact Nat.lt_irrefl _ hsize

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

private theorem kernelWitnessSplitAux_some_of_nontrivial_offset
    (f witness : FpPoly p) :
    ∀ (fuel start offset : Nat),
      offset < fuel →
      isNontrivialSplitFactor f
        (splitFactorAt f witness (ZMod64.ofNat p (start + offset))) = true →
      ∃ r : SplitResult p, kernelWitnessSplitAux f witness fuel start = some r := by
  intro fuel
  induction fuel with
  | zero =>
      intro start offset hoffset _
      omega
  | succ fuel ih =>
      intro start offset hoffset hnon_target
      unfold kernelWitnessSplitAux
      let splitConstant := ZMod64.ofNat p start
      let factor := splitFactorAt f witness splitConstant
      by_cases hnon : isNontrivialSplitFactor f factor
      · exact ⟨
          { splitConstant
            factor
            cofactor := f / factor },
          by simp [splitConstant, factor, hnon]⟩
      · cases offset with
        | zero =>
            have htarget :
                isNontrivialSplitFactor f factor = true := by
              simpa [splitConstant, factor] using hnon_target
            exact False.elim (hnon htarget)
        | succ offset =>
            have hoffset' : offset < fuel := by omega
            have htarget' :
                isNontrivialSplitFactor f
                  (splitFactorAt f witness (ZMod64.ofNat p (start + 1 + offset))) = true := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnon_target
            have hsome := ih (start + 1) offset hoffset' htarget'
            simpa [splitConstant, factor, hnon] using hsome

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

private theorem kernelWitnessSplitAux_size_lt
    (f witness : FpPoly p) (fuel c : Nat) (r : SplitResult p)
    (hsplit : kernelWitnessSplitAux f witness fuel c = some r) :
    r.factor.size < f.size := by
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
        exact isNontrivialSplitFactor_size_lt f factor hnon
      · simp [splitConstant, factor, hnon] at hsplit
        exact ih (c + 1) hsplit

/--
Any successful Berlekamp split returns a factor strictly smaller in size than
the input.  This is the strict-descent companion of `kernelWitnessSplit_nontrivial`
and is what drives the `Nodup` invariant on the running factor list.
-/
theorem kernelWitnessSplit_size_lt
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    r.factor.size < f.size :=
  kernelWitnessSplitAux_size_lt f witness p 0 r hsplit

/--
Executable search reflection for one field constant: if the gcd candidate
attached to `c` is nonzero, nonconstant, and strictly smaller in size than
the input, then the bounded Berlekamp witness search succeeds.
-/
theorem kernelWitnessSplit?_some_of_nontrivial_splitFactorAt
    (f witness : FpPoly p) (c : ZMod64 p)
    (hnotZero : !(splitFactorAt f witness c).isZero)
    (hdegree : (splitFactorAt f witness c).degree? ≠ some 0)
    (hsize_lt : (splitFactorAt f witness c).size < f.size) :
    ∃ r : SplitResult p, kernelWitnessSplit? f witness = some r := by
  have hc_lt : c.toNat < p := c.toNat_lt
  have hc_eq : ZMod64.ofNat p c.toNat = c := ZMod64.ofNat_toNat c
  have hnon :
      isNontrivialSplitFactor f
        (splitFactorAt f witness (ZMod64.ofNat p (0 + c.toNat))) = true := by
    unfold isNontrivialSplitFactor
    rw [Nat.zero_add, hc_eq]
    cases hz : (splitFactorAt f witness c).isZero <;> simp [hz] at hnotZero ⊢
    exact ⟨hdegree, hsize_lt⟩
  exact kernelWitnessSplitAux_some_of_nontrivial_offset f witness p 0 c.toNat hc_lt hnon

private theorem splitWithWitnesses?_product_spec
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (witnesses : List (FpPoly p))
    {r : SplitResult p}
    (h : splitWithWitnesses? f witnesses = some r) :
    r.factor * r.cofactor = f := by
  induction witnesses with
  | nil => simp [splitWithWitnesses?] at h
  | cons w ws ih =>
    rw [splitWithWitnesses?] at h
    cases hk : kernelWitnessSplit? f w with
    | some r' =>
      rw [hk] at h
      simp only [Option.some.injEq] at h
      subst h
      exact kernelWitnessSplit_product_spec f w r' hk
    | none =>
      rw [hk] at h
      exact ih h

private theorem one_mul_poly
    [ZMod64.PrimeModulus p]
    (a : FpPoly p) :
    (1 : FpPoly p) * a = a :=
  (DensePoly.mul_comm_poly (1 : FpPoly p) a).trans (DensePoly.mul_one_right_poly a)

private theorem foldl_mul_left_factor
    [ZMod64.PrimeModulus p]
    (z a : FpPoly p) (xs : List (FpPoly p)) :
    xs.foldl (fun acc factor => acc * factor) (z * a)
      = z * xs.foldl (fun acc factor => acc * factor) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hcong : List.foldl (fun acc factor : FpPoly p => acc * factor) ((z * a) * b) bs
        = List.foldl (fun acc factor => acc * factor) (z * (a * b)) bs := by
      congr 1
      exact DensePoly.mul_assoc_poly z a b
    have hih : List.foldl (fun acc factor : FpPoly p => acc * factor) (z * (a * b)) bs
        = z * List.foldl (fun acc factor => acc * factor) (a * b) bs := ih (a * b)
    show List.foldl (fun acc factor => acc * factor) (z * a * b) bs
        = z * List.foldl (fun acc factor => acc * factor) (a * b) bs
    exact hcong.trans hih

private theorem foldl_mul_eq_mul_foldl
    [ZMod64.PrimeModulus p]
    (z : FpPoly p) (xs : List (FpPoly p)) :
    xs.foldl (fun acc factor => acc * factor) z
      = z * xs.foldl (fun acc factor => acc * factor) 1 := by
  have h1 : xs.foldl (fun acc factor => acc * factor) z
      = xs.foldl (fun acc factor => acc * factor) (z * 1) := by
    congr 1
    exact (DensePoly.mul_one_right_poly z).symm
  exact h1.trans (foldl_mul_left_factor z 1 xs)

/--
Cons-expansion for `factorProduct`: pulling the head factor out of the running
product. Useful for downstream proofs that reason about `factorProduct` without
unfolding the underlying `List.foldl`.
-/
theorem factorProduct_cons
    [ZMod64.PrimeModulus p]
    (x : FpPoly p) (xs : List (FpPoly p)) :
    factorProduct (x :: xs) = x * factorProduct xs := by
  show xs.foldl (fun acc factor => acc * factor) (1 * x)
    = x * xs.foldl (fun acc factor => acc * factor) 1
  rw [one_mul_poly x]
  exact foldl_mul_eq_mul_foldl x xs

private theorem factorProduct_splitFirstFactor?_eq
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p))
    {factors factors' : List (FpPoly p)}
    (h : splitFirstFactor? witnesses factors = some factors') :
    factorProduct factors' = factorProduct factors := by
  induction factors generalizing factors' with
  | nil => simp [splitFirstFactor?] at h
  | cons fac rest ih =>
    rw [splitFirstFactor?] at h
    cases hsplit : splitWithWitnesses? fac witnesses with
    | some r =>
      rw [hsplit] at h
      simp only [Option.some.injEq] at h
      subst h
      have hp : r.factor * r.cofactor = fac :=
        splitWithWitnesses?_product_spec fac witnesses hsplit
      rw [factorProduct_cons r.factor, factorProduct_cons r.cofactor,
        factorProduct_cons fac]
      have hassoc : r.factor * (r.cofactor * factorProduct rest)
          = (r.factor * r.cofactor) * factorProduct rest :=
        (DensePoly.mul_assoc_poly r.factor r.cofactor (factorProduct rest)).symm
      rw [hassoc, hp]
    | none =>
      rw [hsplit] at h
      cases hrest : splitFirstFactor? witnesses rest with
      | some rest' =>
        rw [hrest] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [factorProduct_cons fac, factorProduct_cons fac]
        rw [ih hrest]
      | none =>
        rw [hrest] at h
        exact absurd h (by simp)

private theorem factorProduct_berlekampFactorLoop_eq
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) (fuel : Nat)
    (factors : List (FpPoly p)) :
    factorProduct (berlekampFactorLoop witnesses fuel factors)
      = factorProduct factors := by
  induction fuel generalizing factors with
  | zero => rfl
  | succ fuel ih =>
    rw [berlekampFactorLoop]
    cases hsplit : splitFirstFactor? witnesses factors with
    | some factors' =>
      rw [ih]
      exact factorProduct_splitFirstFactor?_eq witnesses hsplit
    | none => rfl

/--
The executable Berlekamp factorization preserves the input polynomial as the
product of the returned factors for square-free monic inputs.
-/
theorem prod_berlekampFactor
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (berlekampFactor f hmonic).product = f := by
  simp only [Factorization.product_def]
  rw [show (berlekampFactor f hmonic).factors
        = berlekampFactorLoop ((fixedSpaceKernel f hmonic).toList)
            (f.size + 1) [f] from rfl]
  rw [factorProduct_berlekampFactorLoop_eq, factorProduct_cons, factorProduct_nil]
  exact DensePoly.mul_one_right_poly f

/-! ### Singleton-output loop structure

Each successful `splitFirstFactor?` extends the factor list by one entry, so
`berlekampFactorLoop` is length-monotone. When `berlekampFactor` returns at
most one factor (starting from the singleton `[f]`), the very first
`splitFirstFactor?` invocation must have returned `none`, which by direct
unfolding means every fixed-space kernel witness yields
`kernelWitnessSplit? = none`. This isolates the executable / loop side of
Berlekamp completeness; the algebraic implication "no kernel-witness split
implies irreducibility" lives in a separate finite-field bridge. -/

private theorem splitFirstFactor?_length_succ_of_some
    (witnesses : List (FpPoly p)) :
    ∀ {factors factors' : List (FpPoly p)},
      splitFirstFactor? witnesses factors = some factors' →
        factors'.length = factors.length + 1 := by
  intro factors
  induction factors with
  | nil =>
      intro factors' h
      simp [splitFirstFactor?] at h
  | cons fac rest ih =>
      intro factors' h
      rw [splitFirstFactor?] at h
      cases hsplit : splitWithWitnesses? fac witnesses with
      | some _ =>
          rw [hsplit] at h
          simp only [Option.some.injEq] at h
          subst h
          simp [List.length_cons]
      | none =>
          rw [hsplit] at h
          cases hrest : splitFirstFactor? witnesses rest with
          | some rest' =>
              rw [hrest] at h
              simp only [Option.some.injEq] at h
              subst h
              have ihr := ih hrest
              simp [List.length_cons, ihr]
          | none =>
              rw [hrest] at h
              exact absurd h (by simp)

theorem berlekampFactorLoop_length_ge
    (witnesses : List (FpPoly p)) (fuel : Nat) (factors : List (FpPoly p)) :
    factors.length ≤ (berlekampFactorLoop witnesses fuel factors).length := by
  induction fuel generalizing factors with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [berlekampFactorLoop]
      cases hsplit : splitFirstFactor? witnesses factors with
      | some factors' =>
          change factors.length ≤
            (berlekampFactorLoop witnesses fuel factors').length
          have hlen := splitFirstFactor?_length_succ_of_some witnesses hsplit
          have hih := ih factors'
          omega
      | none =>
          exact Nat.le_refl _

/-- Executable Berlekamp factorization always retains at least one factor. -/
theorem berlekampFactor_factors_ne_nil
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    (berlekampFactor f hmonic).factors ≠ [] := by
  intro hnil
  have hlen :=
    berlekampFactorLoop_length_ge
      ((fixedSpaceKernel f hmonic).toList) (f.size + 1) [f]
  change
    ([f] : List (FpPoly p)).length ≤
      (berlekampFactor f hmonic).factors.length at hlen
  rw [hnil] at hlen
  simp at hlen

private theorem splitFirstFactor?_singleton_none_iff
    (witnesses : List (FpPoly p)) (f : FpPoly p) :
    splitFirstFactor? witnesses [f] = none ↔
      splitWithWitnesses? f witnesses = none := by
  constructor
  · intro h
    rw [splitFirstFactor?] at h
    cases hw : splitWithWitnesses? f witnesses with
    | some _ =>
        rw [hw] at h
        simp at h
    | none => rfl
  · intro h
    rw [splitFirstFactor?, h, splitFirstFactor?]

private theorem splitWithWitnesses?_none_iff_forall
    (f : FpPoly p) (witnesses : List (FpPoly p)) :
    splitWithWitnesses? f witnesses = none ↔
      ∀ w ∈ witnesses, kernelWitnessSplit? f w = none := by
  induction witnesses with
  | nil =>
      simp [splitWithWitnesses?]
  | cons w ws ih =>
      rw [splitWithWitnesses?]
      cases hw : kernelWitnessSplit? f w with
      | some split =>
          constructor
          · intro hcontra; simp at hcontra
          · intro hforall
            have hwnone := hforall w (by simp)
            rw [hw] at hwnone
            simp at hwnone
      | none =>
          rw [ih]
          constructor
          · intro h w' hw'
            rcases List.mem_cons.mp hw' with heq | hmem
            · exact heq ▸ hw
            · exact h w' hmem
          · intro h w' hw'
            exact h w' (List.mem_cons_of_mem _ hw')

/--
Structural lemma about `berlekampFactor` output: if its `factors` list has
length at most one, then every fixed-space kernel witness yields
`kernelWitnessSplit? = none`. This is the loop-tracing half of the parent
Berlekamp completeness theorem; the algebraic half (no kernel-witness split
forces irreducibility for square-free monic inputs) belongs to a separate
Mathlib-free finite-field bridge.
-/
theorem kernelWitnessSplit?_none_of_berlekampFactor_factors_length_le_one
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    (hsmall : (berlekampFactor f hmonic).factors.length ≤ 1) :
    ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
      kernelWitnessSplit? f w = none := by
  have hloop_eq :
      (berlekampFactor f hmonic).factors
        = berlekampFactorLoop ((fixedSpaceKernel f hmonic).toList)
            (f.size + 1) [f] := rfl
  rw [hloop_eq] at hsmall
  have hsplit :
      splitFirstFactor? ((fixedSpaceKernel f hmonic).toList) [f] = none := by
    rw [berlekampFactorLoop] at hsmall
    cases h : splitFirstFactor? ((fixedSpaceKernel f hmonic).toList) [f] with
    | none => rfl
    | some factors' =>
        simp only [h] at hsmall
        have hlen' :=
          splitFirstFactor?_length_succ_of_some
            ((fixedSpaceKernel f hmonic).toList) h
        have hmono :=
          berlekampFactorLoop_length_ge
            ((fixedSpaceKernel f hmonic).toList) f.size factors'
        simp at hlen'
        omega
  rw [splitFirstFactor?_singleton_none_iff,
      splitWithWitnesses?_none_iff_forall] at hsplit
  exact hsplit

/-! ### `Nodup` invariant on `berlekampFactor.factors`

The running factor list maintained by the executable Berlekamp loop is
`Nodup` whenever no positive-degree polynomial squares to a divisor of the
input.  That hypothesis is fed in abstractly here so that the inductive
proof lives in this file without depending on the algebraic
`squareFree`-implies-`isUnitPolynomial` chain from
`HexBerlekamp/RabinSoundness.lean`.  See
`Hex.Berlekamp.berlekampFactor_factors_nodup` in
`HexBerlekamp/RabinSoundness.lean` for the user-facing wrapper that
discharges the abstract hypothesis from `gcd f f' = 1`. -/

private theorem pos_degree_of_ne_zero_of_degree_ne_zero
    {a : FpPoly p} (ha_ne_zero : a ≠ 0)
    (ha_deg : a.degree? ≠ some 0) :
    0 < a.degree?.getD 0 := by
  have ha_size_pos : 0 < a.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply ha_ne_zero
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
  have ha_size_ne_zero : a.size ≠ 0 := Nat.pos_iff_ne_zero.mp ha_size_pos
  have hdeg : a.degree? = some (a.size - 1) := by
    unfold DensePoly.degree?
    simp [ha_size_ne_zero]
  rw [hdeg] at ha_deg
  rw [hdeg]
  have hne : a.size - 1 ≠ 0 := fun h => ha_deg (by rw [h])
  simp
  omega

private theorem isNontrivialSplitFactor_factor_pos_degree
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    0 < g.degree?.getD 0 := by
  have hnotZero := isNontrivialSplitFactor_not_zero f g h
  have hdegree := isNontrivialSplitFactor_degree_ne_zero f g h
  have hne_zero : g ≠ 0 := by
    intro hg
    rw [hg] at hnotZero
    have : (0 : FpPoly p).isZero = true := rfl
    rw [this] at hnotZero
    simp at hnotZero
  exact pos_degree_of_ne_zero_of_degree_ne_zero hne_zero hdegree

private theorem kernelWitnessSplitAux_factor_pos_degree
    (f witness : FpPoly p) (fuel c : Nat) (r : SplitResult p)
    (hsplit : kernelWitnessSplitAux f witness fuel c = some r) :
    0 < r.factor.degree?.getD 0 := by
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
        exact isNontrivialSplitFactor_factor_pos_degree f factor hnon
      · simp [splitConstant, factor, hnon] at hsplit
        exact ih (c + 1) hsplit

theorem kernelWitnessSplit_factor_pos_degree
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    0 < r.factor.degree?.getD 0 :=
  kernelWitnessSplitAux_factor_pos_degree f witness p 0 r hsplit

private theorem splitWithWitnesses?_factor_pos_degree
    (f : FpPoly p) (witnesses : List (FpPoly p))
    {r : SplitResult p}
    (h : splitWithWitnesses? f witnesses = some r) :
    0 < r.factor.degree?.getD 0 := by
  induction witnesses with
  | nil => simp [splitWithWitnesses?] at h
  | cons w ws ih =>
      rw [splitWithWitnesses?] at h
      cases hk : kernelWitnessSplit? f w with
      | some r' =>
          rw [hk] at h
          simp only [Option.some.injEq] at h
          subst h
          exact kernelWitnessSplit_factor_pos_degree f w r' hk
      | none =>
          rw [hk] at h
          exact ih h

private theorem splitWithWitnesses?_size_lt
    (f : FpPoly p) (witnesses : List (FpPoly p))
    {r : SplitResult p}
    (h : splitWithWitnesses? f witnesses = some r) :
    r.factor.size < f.size := by
  induction witnesses with
  | nil => simp [splitWithWitnesses?] at h
  | cons w ws ih =>
      rw [splitWithWitnesses?] at h
      cases hk : kernelWitnessSplit? f w with
      | some r' =>
          rw [hk] at h
          simp only [Option.some.injEq] at h
          subst h
          exact kernelWitnessSplit_size_lt f w r' hk
      | none =>
          rw [hk] at h
          exact ih h

private theorem splitWithWitnesses?_cofactor_pos_degree
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (witnesses : List (FpPoly p))
    (hf_ne : f ≠ 0)
    {r : SplitResult p}
    (h : splitWithWitnesses? f witnesses = some r) :
    0 < r.cofactor.degree?.getD 0 := by
  have hfac_pos := splitWithWitnesses?_factor_pos_degree f witnesses h
  have hsize_lt := splitWithWitnesses?_size_lt f witnesses h
  have hprod := splitWithWitnesses?_product_spec f witnesses h
  -- r.factor * r.cofactor = f, both nonzero, with strict size descent on factor.
  have hfac_ne : r.factor ≠ 0 := by
    intro hr
    rw [hr] at hfac_pos
    have : (0 : FpPoly p).degree? = none := rfl
    rw [this] at hfac_pos
    simp at hfac_pos
  have hcof_ne : r.cofactor ≠ 0 := by
    intro hr
    rw [hr] at hprod
    rw [FpPoly.mul_zero] at hprod
    exact hf_ne hprod.symm
  have hfac_dvd : r.factor ∣ f := ⟨r.cofactor, hprod.symm⟩
  have hcof_dvd : r.cofactor ∣ f := by
    refine ⟨r.factor, ?_⟩
    rw [FpPoly.mul_comm]
    exact hprod.symm
  have hsize_sum : r.factor.size + r.cofactor.size = f.size + 1 := by
    have hf_size_eq : f.size = (r.factor * r.cofactor).size := by rw [hprod]
    rw [hf_size_eq]
    rw [FpPoly.size_mul_eq_add_sub_one r.factor r.cofactor hfac_ne hcof_ne]
    have hf_size_pos : 0 < f.size := FpPoly.size_pos_of_ne_zero hf_ne
    have hfac_size_pos : 0 < r.factor.size := FpPoly.size_pos_of_ne_zero hfac_ne
    have hcof_size_pos : 0 < r.cofactor.size := FpPoly.size_pos_of_ne_zero hcof_ne
    omega
  have hcof_size_ge_2 : 2 ≤ r.cofactor.size := by omega
  apply pos_degree_of_ne_zero_of_degree_ne_zero hcof_ne
  have hcof_size_ne : r.cofactor.size ≠ 0 := by omega
  intro hdeg
  unfold DensePoly.degree? at hdeg
  simp [hcof_size_ne] at hdeg
  omega

/-- An element of a list of `FpPoly p` divides the product of the list. -/
private theorem dvd_factorProduct_of_mem
    [ZMod64.PrimeModulus p]
    (xs : List (FpPoly p)) {g : FpPoly p} (hg : g ∈ xs) :
    g ∣ factorProduct xs := by
  induction xs with
  | nil => exact absurd hg List.not_mem_nil
  | cons x rest ih =>
    rcases List.mem_cons.mp hg with hx | hx
    · subst hx
      rw [factorProduct_cons]
      exact ⟨factorProduct rest, rfl⟩
    · rcases ih hx with ⟨k, hk⟩
      refine ⟨x * k, ?_⟩
      rw [factorProduct_cons, hk]
      calc x * (g * k)
          = (x * g) * k := (DensePoly.mul_assoc_poly x g k).symm
        _ = (g * x) * k :=
            congrArg (fun y => y * k) (DensePoly.mul_comm_poly x g)
        _ = g * (x * k) := DensePoly.mul_assoc_poly g x k

/-- A polynomial that divides both `a` and `b` squares-divides `a * b`. -/
private theorem squared_dvd_of_dvd_dvd
    [ZMod64.PrimeModulus p]
    {a b g : FpPoly p} (hga : g ∣ a) (hgb : g ∣ b) :
    g * g ∣ a * b := by
  rcases hga with ⟨a', ha'⟩
  rcases hgb with ⟨b', hb'⟩
  refine ⟨a' * b', ?_⟩
  rw [ha', hb']
  calc g * a' * (g * b')
      = g * (a' * (g * b')) := DensePoly.mul_assoc_poly g a' (g * b')
    _ = g * ((a' * g) * b') :=
        congrArg (g * ·) (DensePoly.mul_assoc_poly a' g b').symm
    _ = g * ((g * a') * b') :=
        congrArg (fun x => g * (x * b')) (DensePoly.mul_comm_poly a' g)
    _ = g * (g * (a' * b')) :=
        congrArg (g * ·) (DensePoly.mul_assoc_poly g a' b')
    _ = g * g * (a' * b') := (DensePoly.mul_assoc_poly g g (a' * b')).symm

/-- `factorProduct rest` divides `factorProduct (fac :: rest)`. -/
private theorem factorProduct_tail_dvd_cons
    [ZMod64.PrimeModulus p]
    (fac : FpPoly p) (rest : List (FpPoly p)) :
    factorProduct rest ∣ factorProduct (fac :: rest) := by
  rw [factorProduct_cons]
  exact ⟨fac, DensePoly.mul_comm_poly fac (factorProduct rest)⟩

/-- Loop invariant preserved by one `splitFirstFactor?` step: when every
entry of the factor list has positive degree and no positive-degree
polynomial squares to a divisor of `factorProduct xs`, then a successful
split returns a `Nodup` list whose entries again all have positive
degree. -/
private theorem splitFirstFactor?_invariant
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p))
    {xs xs' : List (FpPoly p)}
    (h_nodup : xs.Nodup)
    (h_pos : ∀ g ∈ xs, 0 < g.degree?.getD 0)
    (h_no_squared : ∀ g : FpPoly p,
        g * g ∣ factorProduct xs → ¬ (0 < g.degree?.getD 0))
    (h_split : splitFirstFactor? witnesses xs = some xs') :
    xs'.Nodup ∧ (∀ g ∈ xs', 0 < g.degree?.getD 0) := by
  induction xs generalizing xs' with
  | nil => simp [splitFirstFactor?] at h_split
  | cons fac rest ih =>
      rw [splitFirstFactor?] at h_split
      have h_fac_pos : 0 < fac.degree?.getD 0 := h_pos fac List.mem_cons_self
      have h_fac_ne_zero : fac ≠ 0 := by
        intro hzero
        rw [hzero] at h_fac_pos
        have : (0 : FpPoly p).degree? = none := rfl
        rw [this] at h_fac_pos
        simp at h_fac_pos
      have h_fac_notmem : fac ∉ rest := (List.nodup_cons.mp h_nodup).1
      have h_rest_nodup : rest.Nodup := (List.nodup_cons.mp h_nodup).2
      have h_rest_pos : ∀ g ∈ rest, 0 < g.degree?.getD 0 :=
        fun g hg => h_pos g (List.mem_cons_of_mem fac hg)
      cases hsplit : splitWithWitnesses? fac witnesses with
      | some split =>
          rw [hsplit] at h_split
          simp only [Option.some.injEq] at h_split
          subst h_split
          have h_factor_pos := splitWithWitnesses?_factor_pos_degree fac witnesses hsplit
          have h_cofactor_pos :=
            splitWithWitnesses?_cofactor_pos_degree fac witnesses h_fac_ne_zero hsplit
          have h_prod := splitWithWitnesses?_product_spec fac witnesses hsplit
          -- factorProduct (split.factor :: split.cofactor :: rest)
          --   = split.factor * (split.cofactor * factorProduct rest)
          --   = (split.factor * split.cofactor) * factorProduct rest
          --   = fac * factorProduct rest = factorProduct (fac :: rest)
          have h_factorProduct_eq :
              factorProduct (split.factor :: split.cofactor :: rest)
                = factorProduct (fac :: rest) := by
            rw [factorProduct_cons split.factor (split.cofactor :: rest),
                factorProduct_cons split.cofactor rest,
                factorProduct_cons fac rest]
            calc split.factor * (split.cofactor * factorProduct rest)
                = (split.factor * split.cofactor) * factorProduct rest :=
                  (DensePoly.mul_assoc_poly split.factor split.cofactor _).symm
              _ = fac * factorProduct rest := by rw [h_prod]
          -- Set up the squared-divisor hypothesis on the new list's product.
          have h_no_squared_new : ∀ g : FpPoly p,
              g * g ∣ factorProduct (split.factor :: split.cofactor :: rest) →
                ¬ (0 < g.degree?.getD 0) := by
            intro g hgg
            rw [h_factorProduct_eq] at hgg
            exact h_no_squared g hgg
          -- Show Nodup of split.factor :: split.cofactor :: rest.
          have h_fac_dvd : split.factor ∣ fac := ⟨split.cofactor, h_prod.symm⟩
          have h_cof_dvd : split.cofactor ∣ fac :=
            ⟨split.factor, by rw [← h_prod]; exact FpPoly.mul_comm _ _⟩
          have h_factorProduct_xs : factorProduct (fac :: rest) = fac * factorProduct rest :=
            factorProduct_cons fac rest
          -- split.factor ≠ split.cofactor.
          have h_factor_ne_cofactor : split.factor ≠ split.cofactor := by
            intro heq
            have hgg : split.factor * split.factor ∣ factorProduct (fac :: rest) := by
              rw [h_factorProduct_xs]
              have hfac_eq : fac = split.factor * split.cofactor := h_prod.symm
              rw [hfac_eq, ← heq]
              exact ⟨factorProduct rest, rfl⟩
            exact h_no_squared split.factor hgg h_factor_pos
          -- split.factor ∉ rest.
          have h_factor_notmem : split.factor ∉ rest := by
            intro hmem
            have hfac_dvd_rest : split.factor ∣ factorProduct rest :=
              dvd_factorProduct_of_mem rest hmem
            have hgg : split.factor * split.factor ∣ factorProduct (fac :: rest) := by
              rw [h_factorProduct_xs]
              exact squared_dvd_of_dvd_dvd h_fac_dvd hfac_dvd_rest
            exact h_no_squared split.factor hgg h_factor_pos
          -- split.cofactor ∉ rest.
          have h_cofactor_notmem : split.cofactor ∉ rest := by
            intro hmem
            have hcof_dvd_rest : split.cofactor ∣ factorProduct rest :=
              dvd_factorProduct_of_mem rest hmem
            have hgg : split.cofactor * split.cofactor ∣ factorProduct (fac :: rest) := by
              rw [h_factorProduct_xs]
              exact squared_dvd_of_dvd_dvd h_cof_dvd hcof_dvd_rest
            exact h_no_squared split.cofactor hgg h_cofactor_pos
          -- Assemble Nodup.
          have h_nodup' :
              (split.factor :: split.cofactor :: rest).Nodup := by
            apply List.nodup_cons.mpr
            refine ⟨?_, ?_⟩
            · intro hmem
              rcases List.mem_cons.mp hmem with heq | hmem'
              · exact h_factor_ne_cofactor heq
              · exact h_factor_notmem hmem'
            apply List.nodup_cons.mpr
            exact ⟨h_cofactor_notmem, h_rest_nodup⟩
          refine ⟨h_nodup', ?_⟩
          intro g hg
          rcases List.mem_cons.mp hg with heq | hmem
          · subst heq; exact h_factor_pos
          rcases List.mem_cons.mp hmem with heq | hmem'
          · subst heq; exact h_cofactor_pos
          exact h_rest_pos g hmem'
      | none =>
          rw [hsplit] at h_split
          cases hrest : splitFirstFactor? witnesses rest with
          | some rest' =>
              rw [hrest] at h_split
              simp only [Option.some.injEq] at h_split
              subst h_split
              -- IH on rest with appropriate hypotheses.
              have h_no_squared_rest : ∀ g : FpPoly p,
                  g * g ∣ factorProduct rest → ¬ (0 < g.degree?.getD 0) := by
                intro g hgg
                have htrans : g * g ∣ factorProduct (fac :: rest) := by
                  rcases hgg with ⟨k, hk⟩
                  refine ⟨fac * k, ?_⟩
                  calc factorProduct (fac :: rest)
                      = fac * factorProduct rest := factorProduct_cons fac rest
                    _ = fac * (g * g * k) := by rw [hk]
                    _ = (fac * (g * g)) * k :=
                        (DensePoly.mul_assoc_poly fac (g * g) k).symm
                    _ = ((g * g) * fac) * k :=
                        congrArg (fun y => y * k) (DensePoly.mul_comm_poly fac (g * g))
                    _ = (g * g) * (fac * k) :=
                        DensePoly.mul_assoc_poly (g * g) fac k
                exact h_no_squared g htrans
              have ⟨h_rest'_nodup, h_rest'_pos⟩ :=
                ih h_rest_nodup h_rest_pos h_no_squared_rest hrest
              -- factorProduct rest' = factorProduct rest.
              have h_rest_prod_eq : factorProduct rest' = factorProduct rest :=
                factorProduct_splitFirstFactor?_eq witnesses hrest
              -- Goal: (fac :: rest').Nodup ∧ ∀ g ∈ fac :: rest', pos degree.
              -- Need fac ∉ rest'.
              have h_fac_notmem' : fac ∉ rest' := by
                intro hmem
                have hfac_dvd_rest' : fac ∣ factorProduct rest' :=
                  dvd_factorProduct_of_mem rest' hmem
                rw [h_rest_prod_eq] at hfac_dvd_rest'
                have hfac_dvd_self : fac ∣ fac := ⟨1, (DensePoly.mul_one_right_poly fac).symm⟩
                have hgg : fac * fac ∣ factorProduct (fac :: rest) := by
                  rw [factorProduct_cons]
                  exact squared_dvd_of_dvd_dvd hfac_dvd_self hfac_dvd_rest'
                exact h_no_squared fac hgg h_fac_pos
              refine ⟨?_, ?_⟩
              · exact List.nodup_cons.mpr ⟨h_fac_notmem', h_rest'_nodup⟩
              intro g hg
              rcases List.mem_cons.mp hg with heq | hmem
              · subst heq; exact h_fac_pos
              · exact h_rest'_pos g hmem
          | none =>
              rw [hrest] at h_split
              exact absurd h_split (by simp)

private theorem berlekampFactorLoop_invariant
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) (fuel : Nat) (factors : List (FpPoly p))
    (h_nodup : factors.Nodup)
    (h_pos : ∀ g ∈ factors, 0 < g.degree?.getD 0)
    (h_no_squared : ∀ g : FpPoly p,
        g * g ∣ factorProduct factors → ¬ (0 < g.degree?.getD 0)) :
    (berlekampFactorLoop witnesses fuel factors).Nodup ∧
      (∀ g ∈ berlekampFactorLoop witnesses fuel factors, 0 < g.degree?.getD 0) := by
  induction fuel generalizing factors with
  | zero => exact ⟨h_nodup, h_pos⟩
  | succ fuel ih =>
      rw [berlekampFactorLoop]
      cases hsplit : splitFirstFactor? witnesses factors with
      | some factors' =>
          have ⟨h_nodup', h_pos'⟩ :=
            splitFirstFactor?_invariant witnesses h_nodup h_pos h_no_squared hsplit
          -- factorProduct factors' = factorProduct factors (existing lemma)
          have h_prod_eq : factorProduct factors' = factorProduct factors :=
            factorProduct_splitFirstFactor?_eq witnesses hsplit
          have h_no_squared' : ∀ g : FpPoly p,
              g * g ∣ factorProduct factors' → ¬ (0 < g.degree?.getD 0) := by
            intro g hgg
            rw [h_prod_eq] at hgg
            exact h_no_squared g hgg
          exact ih factors' h_nodup' h_pos' h_no_squared'
      | none => exact ⟨h_nodup, h_pos⟩

/-- Abstract form of `berlekampFactor.factors.Nodup`: when no positive-degree
polynomial squares to a divisor of `f`, the executable Berlekamp factor list
has no duplicates.  The Mathlib-free squareness-implies-irreducibility chain
discharges this hypothesis from `gcd f f' = 1`; see
`Hex.Berlekamp.berlekampFactor_factors_nodup` in
`HexBerlekamp/RabinSoundness.lean`. -/
theorem berlekampFactor_factors_nodup_of_no_squared
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (h_no_squared : ∀ g : FpPoly p,
        g * g ∣ f → ¬ (0 < g.degree?.getD 0)) :
    (berlekampFactor f hmonic).factors.Nodup := by
  -- Case split on whether f has positive degree.
  have h_singleton_nodup : ([f] : List (FpPoly p)).Nodup :=
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  by_cases h_f_pos : 0 < f.degree?.getD 0
  · -- Positive-degree case: use the loop invariant.
    have h_init_pos : ∀ g ∈ ([f] : List (FpPoly p)), 0 < g.degree?.getD 0 := by
      intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      exact h_f_pos
    have h_init_prod : factorProduct ([f] : List (FpPoly p)) = f := by
      rw [factorProduct_cons, factorProduct_nil]
      exact DensePoly.mul_one_right_poly f
    have h_init_no_squared : ∀ g : FpPoly p,
        g * g ∣ factorProduct ([f] : List (FpPoly p)) → ¬ (0 < g.degree?.getD 0) := by
      intro g hgg
      rw [h_init_prod] at hgg
      exact h_no_squared g hgg
    exact (berlekampFactorLoop_invariant ((fixedSpaceKernel f hmonic).toList)
      (f.size + 1) [f] h_singleton_nodup h_init_pos h_init_no_squared).1
  · -- Degree 0: any returned split must have positive-degree factor of strictly
    -- smaller size, which is impossible when `f.size ≤ 1`.  The loop therefore
    -- preserves the initial singleton `[f]`, which is trivially `Nodup`.
    -- Step 1: derive `f.size ≤ 1` from the negation of pos degree.
    have h_f_size_le_one : f.size ≤ 1 := by
      rcases Nat.lt_or_ge f.size 2 with hlt | hge
      · omega
      · exfalso
        apply h_f_pos
        have hsize_ne : f.size ≠ 0 := by omega
        have hdeg_eq : f.degree? = some (f.size - 1) := by
          unfold DensePoly.degree?
          simp [hsize_ne]
        rw [hdeg_eq]
        simp
        omega
    -- Step 2: every kernel split is impossible.
    have h_no_split : ∀ w ∈ ((fixedSpaceKernel f hmonic).toList),
        kernelWitnessSplit? f w = none := by
      intro w _hw
      cases hopt : kernelWitnessSplit? f w with
      | none => rfl
      | some r =>
          exfalso
          have hsize_lt := kernelWitnessSplit_size_lt f w r hopt
          have hfac_pos := kernelWitnessSplit_factor_pos_degree f w r hopt
          -- r.factor.size ≥ 2 from pos degree.
          have hfac_size_ge_two : 2 ≤ r.factor.size := by
            rcases Nat.lt_or_ge r.factor.size 2 with hlt | hge
            · exfalso
              -- r.factor.size ≤ 1
              cases hfac_size : r.factor.size with
              | zero =>
                  have hfac_eq_zero : r.factor = 0 := by
                    apply DensePoly.ext_coeff
                    intro i
                    rw [DensePoly.coeff_zero]
                    exact DensePoly.coeff_eq_zero_of_size_le r.factor (by omega)
                  rw [hfac_eq_zero] at hfac_pos
                  have hzero : (0 : FpPoly p).degree? = none := rfl
                  rw [hzero] at hfac_pos
                  simp at hfac_pos
              | succ k =>
                  have hk : k = 0 := by omega
                  subst hk
                  have hdeg : r.factor.degree? = some 0 := by
                    unfold DensePoly.degree?
                    simp [hfac_size]
                  rw [hdeg] at hfac_pos
                  simp at hfac_pos
            · exact hge
          omega
    -- Step 3: the loop preserves [f].
    have h_loop : ∀ fuel,
        berlekampFactorLoop ((fixedSpaceKernel f hmonic).toList) fuel [f] = [f] := by
      intro fuel
      induction fuel with
      | zero => rfl
      | succ fuel _ih_fuel =>
          rw [berlekampFactorLoop]
          have h_sff_none :
              splitFirstFactor? ((fixedSpaceKernel f hmonic).toList) [f] = none := by
            rw [splitFirstFactor?_singleton_none_iff,
                splitWithWitnesses?_none_iff_forall]
            exact h_no_split
          rw [h_sff_none]
    show (berlekampFactor f hmonic).factors.Nodup
    change (berlekampFactorLoop _ (f.size + 1) [f]).Nodup
    rw [h_loop]
    exact h_singleton_nodup

/-- Under the no-squared invariant on `factorProduct`, distinct factors in a
list of `FpPoly p` are pairwise coprime: no positive-degree polynomial
divides two distinct positions.  This is a direct consequence of the
no-squared invariant and the fact that any two list entries multiply to a
factor of `factorProduct`. -/
private theorem factorProduct_pairwise_no_common_pos_divisor
    [ZMod64.PrimeModulus p]
    (factors : List (FpPoly p))
    (h_no_squared : ∀ g : FpPoly p,
        g * g ∣ factorProduct factors → ¬ (0 < g.degree?.getD 0)) :
    factors.Pairwise (fun a b =>
      ∀ d : FpPoly p, d ∣ a → d ∣ b → ¬ (0 < d.degree?.getD 0)) := by
  induction factors with
  | nil => exact List.Pairwise.nil
  | cons fac rest ih =>
      refine List.Pairwise.cons ?_ ?_
      · -- For each b ∈ rest, fac and b have no common positive-degree divisor.
        intro b hb d hd_fac hd_b
        have hb_dvd_rest : b ∣ factorProduct rest :=
          dvd_factorProduct_of_mem rest hb
        have hd_dvd_rest : d ∣ factorProduct rest := by
          rcases hd_b with ⟨k, hk⟩
          rcases hb_dvd_rest with ⟨q, hq⟩
          refine ⟨k * q, ?_⟩
          rw [hq, hk]; exact DensePoly.mul_assoc_poly d k q
        have hdd_dvd : d * d ∣ fac * factorProduct rest :=
          squared_dvd_of_dvd_dvd hd_fac hd_dvd_rest
        have hprod_eq : fac * factorProduct rest = factorProduct (fac :: rest) :=
          (factorProduct_cons fac rest).symm
        rw [hprod_eq] at hdd_dvd
        exact h_no_squared d hdd_dvd
      · -- Inductive hypothesis: rest is pairwise coprime.
        apply ih
        intro g hg_dvd
        have h_rest_dvd : factorProduct rest ∣ factorProduct (fac :: rest) :=
          factorProduct_tail_dvd_cons fac rest
        rcases hg_dvd with ⟨k, hk⟩
        rcases h_rest_dvd with ⟨q, hq⟩
        refine h_no_squared g ⟨k * q, ?_⟩
        rw [hq, hk]; exact DensePoly.mul_assoc_poly (g * g) k q

/-- The Berlekamp factor list's product equals the input polynomial.  This is
the squarefree-free core of `prod_berlekampFactor`: the proof that the
splitting loop preserves `factorProduct` does not use the squarefree
hypothesis, so the product equality holds for every monic input. -/
theorem factorProduct_berlekampFactor
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    factorProduct (berlekampFactor f hmonic).factors = f := by
  rw [show (berlekampFactor f hmonic).factors
        = berlekampFactorLoop ((fixedSpaceKernel f hmonic).toList)
            (f.size + 1) [f] from rfl]
  rw [factorProduct_berlekampFactorLoop_eq, factorProduct_cons, factorProduct_nil]
  exact DensePoly.mul_one_right_poly f

/-- Abstract pairwise-coprime form of `berlekampFactor`'s output: when no
positive-degree polynomial squares to a divisor of `f`, distinct factors in
the returned list share no positive-degree common divisor.  This strengthens
`berlekampFactor_factors_nodup_of_no_squared` from "distinct values" to "no
shared positive-degree divisor".  The Mathlib-free squareness-implies-
irreducibility chain discharges the no-squared hypothesis from
`gcd f f' = 1`; see callers that pair this with
`isUnitPolynomial_of_squareFree_of_squared_dvd`. -/
theorem berlekampFactor_factors_pairwise_coprime
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (h_no_squared : ∀ g : FpPoly p,
        g * g ∣ f → ¬ (0 < g.degree?.getD 0)) :
    (berlekampFactor f hmonic).factors.Pairwise (fun a b =>
      ∀ d : FpPoly p, d ∣ a → d ∣ b → ¬ (0 < d.degree?.getD 0)) := by
  have h_prod_eq : factorProduct (berlekampFactor f hmonic).factors = f :=
    factorProduct_berlekampFactor f hmonic
  have h_no_squared' : ∀ g : FpPoly p,
      g * g ∣ factorProduct (berlekampFactor f hmonic).factors →
        ¬ (0 < g.degree?.getD 0) := by
    intro g hgg
    rw [h_prod_eq] at hgg
    exact h_no_squared g hgg
  exact factorProduct_pairwise_no_common_pos_divisor
    (berlekampFactor f hmonic).factors h_no_squared'

/-- Positivity-only variant of the single-step `splitFirstFactor?` invariant:
positive degree of every factor is preserved by a successful split, without
requiring the squareness-free hypothesis used by the joint Nodup/positivity
invariant.  Positivity is preserved because each new factor produced by
`splitWithWitnesses?` has strictly positive degree, and remaining unchanged
entries already had positive degree by assumption. -/
private theorem splitFirstFactor?_pos_invariant
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p))
    {xs xs' : List (FpPoly p)}
    (h_pos : ∀ g ∈ xs, 0 < g.degree?.getD 0)
    (h_split : splitFirstFactor? witnesses xs = some xs') :
    ∀ g ∈ xs', 0 < g.degree?.getD 0 := by
  induction xs generalizing xs' with
  | nil => simp [splitFirstFactor?] at h_split
  | cons fac rest ih =>
      rw [splitFirstFactor?] at h_split
      have h_fac_pos : 0 < fac.degree?.getD 0 := h_pos fac List.mem_cons_self
      have h_fac_ne_zero : fac ≠ 0 := by
        intro hzero
        rw [hzero] at h_fac_pos
        have : (0 : FpPoly p).degree? = none := rfl
        rw [this] at h_fac_pos
        simp at h_fac_pos
      have h_rest_pos : ∀ g ∈ rest, 0 < g.degree?.getD 0 :=
        fun g hg => h_pos g (List.mem_cons_of_mem fac hg)
      cases hsplit : splitWithWitnesses? fac witnesses with
      | some split =>
          rw [hsplit] at h_split
          simp only [Option.some.injEq] at h_split
          subst h_split
          have h_factor_pos := splitWithWitnesses?_factor_pos_degree fac witnesses hsplit
          have h_cofactor_pos :=
            splitWithWitnesses?_cofactor_pos_degree fac witnesses h_fac_ne_zero hsplit
          intro g hg
          rcases List.mem_cons.mp hg with heq | hmem
          · subst heq; exact h_factor_pos
          rcases List.mem_cons.mp hmem with heq | hmem'
          · subst heq; exact h_cofactor_pos
          exact h_rest_pos g hmem'
      | none =>
          rw [hsplit] at h_split
          cases hrest : splitFirstFactor? witnesses rest with
          | some rest' =>
              rw [hrest] at h_split
              simp only [Option.some.injEq] at h_split
              subst h_split
              have h_rest'_pos := ih h_rest_pos hrest
              intro g hg
              rcases List.mem_cons.mp hg with heq | hmem
              · subst heq; exact h_fac_pos
              · exact h_rest'_pos g hmem
          | none =>
              rw [hrest] at h_split
              exact absurd h_split (by simp)

/-- Positivity-only variant of `berlekampFactorLoop_invariant`: positive degree
of every entry is preserved by the entire splitting loop, without requiring
the squareness-free hypothesis. -/
private theorem berlekampFactorLoop_pos_invariant
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) (fuel : Nat) (factors : List (FpPoly p))
    (h_pos : ∀ g ∈ factors, 0 < g.degree?.getD 0) :
    ∀ g ∈ berlekampFactorLoop witnesses fuel factors, 0 < g.degree?.getD 0 := by
  induction fuel generalizing factors with
  | zero => exact h_pos
  | succ fuel ih =>
      rw [berlekampFactorLoop]
      cases hsplit : splitFirstFactor? witnesses factors with
      | some factors' =>
          have h_pos' := splitFirstFactor?_pos_invariant witnesses h_pos hsplit
          exact ih factors' h_pos'
      | none => exact h_pos

/-- Abstract form of `berlekampFactor`'s output factor-degree positivity: if
the input polynomial has positive degree, then every factor in the executable
Berlekamp factor list has positive degree.  The squareness-free hypothesis
needed by `berlekampFactor_factors_nodup_of_no_squared` is not needed here:
positivity is preserved by every loop step regardless of square-freeness. -/
theorem berlekampFactor_factors_pos_degree
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hf_pos : 0 < f.degree?.getD 0) :
    ∀ g ∈ (berlekampFactor f hmonic).factors, 0 < g.degree?.getD 0 := by
  have h_init_pos : ∀ g ∈ ([f] : List (FpPoly p)), 0 < g.degree?.getD 0 := by
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact hf_pos
  change ∀ g ∈ berlekampFactorLoop ((fixedSpaceKernel f hmonic).toList)
    (f.size + 1) [f], 0 < g.degree?.getD 0
  exact berlekampFactorLoop_pos_invariant ((fixedSpaceKernel f hmonic).toList)
    (f.size + 1) [f] h_init_pos

end Berlekamp

end Hex
