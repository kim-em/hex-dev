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

end Berlekamp

end Hex
