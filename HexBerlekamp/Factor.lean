module

public import HexBerlekamp.Basic

public section

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
@[expose]
def factorProduct (factors : List (FpPoly p)) : FpPoly p :=
  factors.foldl (fun acc factor => acc * factor) 1

/-- Product of the factors returned by a `Factorization`. -/
@[expose]
def Factorization.product (result : Factorization p) : FpPoly p :=
  factorProduct result.factors

/-- Empty-list base case for `factorProduct`. -/
@[simp, grind =] theorem factorProduct_nil : factorProduct ([] : List (FpPoly p)) = 1 := rfl

/-- Unfold a `Factorization`'s product to the `factorProduct` of its stored factors. -/
@[simp, grind =] theorem Factorization.product_def (result : Factorization p) :
    result.product = factorProduct result.factors :=
  rfl

/-- The gcd candidate attached to one field constant `c`. -/
@[expose]
def splitFactorAt (f witness : FpPoly p) (c : ZMod64 p) : FpPoly p :=
  DensePoly.gcd f (witness - FpPoly.C c)

/-- `true` exactly when the gcd candidate is nonconstant and strictly smaller
than `f` in size (i.e. strictly smaller in degree). Strict size suffices to
imply `g ≠ f`; the strict form additionally rules out non-identity unit
multiples `g = u · f`, which is what the downstream `Nodup` argument needs. -/
private def isNontrivialSplitFactor (f g : FpPoly p) : Bool :=
  !g.isZero && g.degree? ≠ some 0 && g.size < f.size

/-- Search the constants `0, 1, ..., p - 1` for a nontrivial Berlekamp split. -/
@[expose]
def kernelWitnessSplitAux (f witness : FpPoly p) : Nat → Nat → Option (SplitResult p)
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

A witness `w` can only split `f` when `w mod f` is nonconstant: every
candidate `gcd(f, w - c)` reduces to `gcd(f, (w mod f) - c)`, which is `f`
or a unit (never a proper factor) once `w mod f` is a field constant.  The
leading `(witness % f).size ≤ 1` guard skips the whole `p`-wide constant
sweep in that case — the dominant cost once a factor is already irreducible,
since every kernel witness is then constant modulo it.  The guard is
value-preserving: `kernelWitnessSplitAux_none_of_mod_size_le_one` proves the
skipped sweep would have returned `none` (over a field), so this agrees with
the unguarded search at every input.
-/
@[expose]
def kernelWitnessSplit? (f witness : FpPoly p) : Option (SplitResult p) :=
  if (witness % f).size ≤ 1 then none
  else kernelWitnessSplitAux f witness p 0

/-- A successful guarded search forces the underlying sweep to succeed: the
`(witness % f).size ≤ 1` skip returns `none`, so a `some` result can only come
from the `kernelWitnessSplitAux` branch.  Lets the structural `some`-lemmas
delegate to their `kernelWitnessSplitAux` counterparts unchanged. -/
private theorem kernelWitnessSplitAux_of_some
    {f witness : FpPoly p} {r : SplitResult p}
    (hsplit : kernelWitnessSplit? f witness = some r) :
    kernelWitnessSplitAux f witness p 0 = some r := by
  unfold kernelWitnessSplit? at hsplit
  by_cases hguard : (witness % f).size ≤ 1
  · rw [if_pos hguard] at hsplit; exact absurd hsplit (by simp)
  · rw [if_neg hguard] at hsplit; exact hsplit

/-- Try a list of kernel witnesses against one current factor. -/
private def splitWithWitnesses? (f : FpPoly p) : List (FpPoly p) → Option (SplitResult p)
  | [] => none
  | witness :: witnesses =>
      match kernelWitnessSplit? f witness with
      | some split => some split
      | none => splitWithWitnesses? f witnesses

/--
Fully split a single factor into its witness-irreducible pieces.

Once `splitWithWitnesses?` reports that `f` admits no kernel-witness split,
`f` is irreducible and is emitted as a leaf — the recursion never re-tests
it. Each side of a successful split recurses independently, so an
already-irreducible factor is tested against the witnesses exactly once
(the former restart-from-front loop re-tested every irreducible factor on
every pass). The fuel bounds the recursion depth; `f.size` strictly
decreases at every split, so `f.size + 1` fuel reaches the
witness-irreducible leaves.

The output preserves the depth-first, factor-before-cofactor order of the
former loop, keeping the factor multiset *and its order* identical.
-/
@[expose]
def fullySplit (witnesses : List (FpPoly p)) :
    Nat → FpPoly p → List (FpPoly p)
  | 0, f => [f]
  | fuel + 1, f =>
      match splitWithWitnesses? f witnesses with
      | none => [f]
      | some split =>
          fullySplit witnesses fuel split.factor ++ fullySplit witnesses fuel split.cofactor

/--
Compute the Berlekamp factorization of a monic polynomial over `F_p` by
building the fixed-space kernel of `Q_f - I` and fully splitting the input
with the resulting kernel representatives.
-/
@[expose]
def berlekampFactor (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] : Factorization p :=
  let witnesses := (fixedSpaceKernel f hmonic).toList
  { input := f
    factors := fullySplit witnesses (f.size + 1) f }

/-- Definitional unfolding of `splitFactorAt` to its underlying `gcd` candidate. -/
theorem splitFactorAt_spec (f witness : FpPoly p) (c : ZMod64 p) :
    splitFactorAt f witness c = DensePoly.gcd f (witness - FpPoly.C c) := rfl

/-- `splitFactorAt_mul_div_eq`: the chosen split factor times its cofactor
`f / splitFactorAt f witness c` recovers `f`, since the factor divides `f`. -/
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

/-- `kernelWitnessSplitAux_product_spec`: the factor and cofactor of the
`SplitResult` returned by the fueled split loop multiply back to `f`. -/
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

/-- `isNontrivialSplitFactor_not_zero`: a witnessed nontrivial split factor is
nonzero. -/
private theorem isNontrivialSplitFactor_not_zero
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    !g.isZero := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h ⊢

/-- `isNontrivialSplitFactor_degree_ne_zero`: a witnessed nontrivial split
factor has nonzero degree (`degree? ≠ some 0`). -/
private theorem isNontrivialSplitFactor_degree_ne_zero
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g.degree? ≠ some 0 := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h
  exact h.1

/-- `isNontrivialSplitFactor_size_lt`: a witnessed nontrivial split factor has
strictly smaller `size` than the input `f`. -/
private theorem isNontrivialSplitFactor_size_lt
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g.size < f.size := by
  unfold isNontrivialSplitFactor at h
  cases hz : g.isZero <;> simp [hz] at h
  exact h.2

/-- `isNontrivialSplitFactor_ne_input`: a witnessed nontrivial split factor is
distinct from the input `f`, as it is strictly smaller. -/
private theorem isNontrivialSplitFactor_ne_input
    (f g : FpPoly p) (h : isNontrivialSplitFactor f g = true) :
    g ≠ f := by
  intro hg
  have hsize := isNontrivialSplitFactor_size_lt f g h
  rw [hg] at hsize
  exact Nat.lt_irrefl _ hsize

/-- `isNontrivialSplitFactor_ne_one`: a witnessed nontrivial split factor is
distinct from `1`, since it is nonzero with nonzero degree. -/
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

/-- `kernelWitnessSplitAux_nontrivial`: the factor of the `SplitResult` returned
by the fueled split loop is nonzero, not `1`, and not equal to `f`. -/
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
  exact kernelWitnessSplitAux_product_spec f witness p 0 r (kernelWitnessSplitAux_of_some hsplit)

/--
Any successful Berlekamp split is nontrivial: the returned factor is neither
`0`, `1`, nor the full input polynomial.
-/
theorem kernelWitnessSplit_nontrivial
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    !r.factor.isZero ∧ r.factor ≠ 1 ∧ r.factor ≠ f := by
  exact kernelWitnessSplitAux_nontrivial f witness p 0 r (kernelWitnessSplitAux_of_some hsplit)

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
  kernelWitnessSplitAux_size_lt f witness p 0 r (kernelWitnessSplitAux_of_some hsplit)

/-! ### Invariance of the split search under a unit scaling

The factors returned by `berlekampFactor` are raw `gcd` outputs, hence
defined only up to a unit scalar.  To feed them to the monic-divisor
completeness theorem we transport the "no kernel-witness split" fact from a
nonzero polynomial `g` to its monic associate `scale c g` (`c ≠ 0`).  The
split search compares each candidate `gcd(g, w - C k)` against `g` only
through its size and degree, both of which are preserved when `g` is replaced
by an associate, so the search returns `none` for `g` exactly when it does for
`scale c g`. -/

/-- Local divisibility transitivity for `FpPoly`, avoiding a dependency on the
later `RabinSoundness` transitivity wrapper. -/
private theorem dvd_trans_fp {a b d : FpPoly p}
    (hab : a ∣ b) (hbd : b ∣ d) : a ∣ d := by
  rcases hab with ⟨x, hx⟩
  rcases hbd with ⟨y, hy⟩
  exact ⟨x * y, by rw [hy, hx]; exact DensePoly.mul_assoc_poly a x y⟩

/-- Mutually dividing polynomials share their coefficient-array size: over a
field, associates have the same degree, hence the same size. -/
private theorem size_eq_of_dvd_dvd
    [ZMod64.PrimeModulus p] {a b : FpPoly p}
    (hab : a ∣ b) (hba : b ∣ a) :
    a.size = b.size := by
  by_cases hb : b = 0
  · subst hb
    rcases hba with ⟨d, hd⟩
    rw [FpPoly.zero_mul] at hd
    rw [hd]
  · have ha : a ≠ 0 := by
      intro ha0
      rw [ha0] at hab
      rcases hab with ⟨d, hd⟩
      rw [FpPoly.zero_mul] at hd
      exact hb hd
    exact Nat.le_antisymm
      (FpPoly.size_le_of_dvd_of_ne_zero hab hb)
      (FpPoly.size_le_of_dvd_of_ne_zero hba ha)

/-! ### The constant-witness guard is value-preserving

`kernelWitnessSplit?` skips the full `p`-wide constant sweep when
`(witness % f).size ≤ 1`, i.e. when the witness is constant modulo `f`.  The
lemmas here prove that skip loses nothing over a field: every candidate
`gcd(f, witness - c)` is then either an associate of `f` or a unit, never a
proper factor, so the skipped `kernelWitnessSplitAux` sweep would have
returned `none`. -/

/-- A polynomial whose coefficients all vanish from index `1` onward has size
at most one (it is a constant). -/
private theorem size_le_one_of_coeff_ge_one_zero (s : FpPoly p)
    (h : ∀ i, 1 ≤ i → s.coeff i = 0) : s.size ≤ 1 := by
  rcases Nat.lt_or_ge s.size 2 with hlt | hge
  · omega
  · exfalso
    have hpos : 0 < s.size := by omega
    have htop : s.coeff (s.size - 1) = 0 := h (s.size - 1) (by omega)
    exact DensePoly.coeff_last_ne_zero_of_pos_size s hpos htop

/-- Reducing `witness - c` by the multiple `(witness / f) * f` of `f` lands on
`(witness % f) - c`: the Euclidean remainder shifted by the same constant. -/
private theorem mod_sub_C_eq
    [ZMod64.PrimeModulus p] (f witness : FpPoly p) (c : ZMod64 p) :
    (witness - FpPoly.C c) - (witness / f) * f = witness % f - FpPoly.C c := by
  have hdm := DensePoly.div_mul_add_mod witness f
  apply DensePoly.ext_coeff
  intro n
  have hc := congrArg (fun x : FpPoly p => x.coeff n) hdm
  simp only [DensePoly.coeff_add_semiring, DensePoly.coeff_sub_ring] at hc ⊢
  grind

/-- Coefficient-wise cancellation: a zero difference forces equality. -/
private theorem eq_of_sub_eq_zero_fp (a b : FpPoly p) (h : a - b = 0) : a = b := by
  apply DensePoly.ext_coeff
  intro n
  have hc := congrArg (fun x : FpPoly p => x.coeff n) h
  simp only [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hc
  grind

/-- **The guard is sound.** Over a field, if `witness` is constant modulo `f`
then no constant `c` yields a nontrivial Berlekamp split: `gcd(f, witness - c)`
is an associate of `f` (when `c` matches the constant residue) or a nonzero
constant otherwise, so it never has degree strictly between `0` and `deg f`. -/
private theorem isNontrivialSplitFactor_false_of_mod_size_le_one
    [ZMod64.PrimeModulus p] (f witness : FpPoly p)
    (hconst : (witness % f).size ≤ 1) (c : ZMod64 p) :
    isNontrivialSplitFactor f (splitFactorAt f witness c) = false := by
  show isNontrivialSplitFactor f (DensePoly.gcd f (witness - FpPoly.C c)) = false
  have hg_dvd_f : DensePoly.gcd f (witness - FpPoly.C c) ∣ f :=
    DensePoly.gcd_dvd_left f (witness - FpPoly.C c)
  have hg_dvd_w : DensePoly.gcd f (witness - FpPoly.C c) ∣ (witness - FpPoly.C c) :=
    DensePoly.gcd_dvd_right f (witness - FpPoly.C c)
  have hEQ : (witness - FpPoly.C c) - (witness / f) * f = witness % f - FpPoly.C c :=
    mod_sub_C_eq f witness c
  have hg_dvd_mul : DensePoly.gcd f (witness - FpPoly.C c) ∣ (witness / f) * f :=
    DensePoly.dvd_mul_left_poly (witness / f) hg_dvd_f
  have hg_dvd_s : DensePoly.gcd f (witness - FpPoly.C c) ∣ (witness % f - FpPoly.C c) := by
    rw [← hEQ]; exact DensePoly.dvd_sub_poly hg_dvd_w hg_dvd_mul
  have hs_size : (witness % f - FpPoly.C c).size ≤ 1 := by
    apply size_le_one_of_coeff_ge_one_zero
    intro i hi
    rw [DensePoly.coeff_sub_ring]
    have h1 : (witness % f).coeff i = 0 :=
      DensePoly.coeff_eq_zero_of_size_le (witness % f) (by omega)
    have h2 : (FpPoly.C c).coeff i = 0 := by rw [FpPoly.coeff_C, if_neg (by omega)]
    rw [h1, h2]; grind
  by_cases hs0 : (witness % f - FpPoly.C c) = 0
  · -- `c` matches the constant residue: `f ∣ witness - c`, so the gcd is `~ f`.
    have heq2 : (witness - FpPoly.C c) = (witness / f) * f := by
      apply eq_of_sub_eq_zero_fp
      rw [hEQ]; exact hs0
    have hf_dvd_w : f ∣ (witness - FpPoly.C c) :=
      ⟨witness / f, by rw [heq2]; exact FpPoly.mul_comm _ _⟩
    have hf_self : f ∣ f := ⟨1, (DensePoly.mul_one_right_poly f).symm⟩
    have hf_dvd_g : f ∣ DensePoly.gcd f (witness - FpPoly.C c) :=
      DensePoly.dvd_gcd f f (witness - FpPoly.C c) hf_self hf_dvd_w
    have hsize_eq : (DensePoly.gcd f (witness - FpPoly.C c)).size = f.size :=
      size_eq_of_dvd_dvd hg_dvd_f hf_dvd_g
    unfold isNontrivialSplitFactor
    have hnlt : ¬ (DensePoly.gcd f (witness - FpPoly.C c)).size < f.size := by omega
    simp [hnlt]
  · -- otherwise the gcd divides a nonzero constant, so it is itself a constant.
    have hs_ne : (witness % f - FpPoly.C c) ≠ 0 := hs0
    rcases hg_dvd_s with ⟨e, he⟩
    have hg_ne : DensePoly.gcd f (witness - FpPoly.C c) ≠ 0 := by
      intro h; apply hs_ne; rw [he, h, FpPoly.zero_mul]
    have he_ne : e ≠ 0 := by
      intro h; apply hs_ne; rw [he, h, FpPoly.mul_zero]
    have hs_deg0 : (witness % f - FpPoly.C c).degree?.getD 0 = 0 := by
      have hs_pos : 0 < (witness % f - FpPoly.C c).size := FpPoly.size_pos_of_ne_zero hs_ne
      have hs_size1 : (witness % f - FpPoly.C c).size = 1 := by omega
      unfold DensePoly.degree?; simp [hs_size1]
    have hdeg := FpPoly.degree?_mul_eq_add_degree?
      (DensePoly.gcd f (witness - FpPoly.C c)) e hg_ne he_ne
    rw [← he] at hdeg
    have hg_deg0 : (DensePoly.gcd f (witness - FpPoly.C c)).degree?.getD 0 = 0 := by
      omega
    have hg_pos : 0 < (DensePoly.gcd f (witness - FpPoly.C c)).size :=
      FpPoly.size_pos_of_ne_zero hg_ne
    have hg_size1 : (DensePoly.gcd f (witness - FpPoly.C c)).size = 1 := by
      have hsome : (DensePoly.gcd f (witness - FpPoly.C c)).degree?
          = some ((DensePoly.gcd f (witness - FpPoly.C c)).size - 1) := by
        unfold DensePoly.degree?; simp [Nat.pos_iff_ne_zero.mp hg_pos]
      rw [hsome] at hg_deg0; simp at hg_deg0; omega
    have hg_deg_some : (DensePoly.gcd f (witness - FpPoly.C c)).degree? = some 0 := by
      unfold DensePoly.degree?; simp [hg_size1]
    unfold isNontrivialSplitFactor
    simp [hg_deg_some]

/-- The guarded constant sweep returns `none` whenever the witness is constant
modulo `f`: a direct corollary of the per-constant
`isNontrivialSplitFactor_false_of_mod_size_le_one`. -/
private theorem kernelWitnessSplitAux_none_of_mod_size_le_one
    [ZMod64.PrimeModulus p] (f witness : FpPoly p)
    (hconst : (witness % f).size ≤ 1) :
    ∀ (fuel c : Nat), kernelWitnessSplitAux f witness fuel c = none := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
      intro c
      unfold kernelWitnessSplitAux
      have hnon : isNontrivialSplitFactor f
          (splitFactorAt f witness (ZMod64.ofNat p c)) = false :=
        isNontrivialSplitFactor_false_of_mod_size_le_one f witness hconst (ZMod64.ofNat p c)
      simp only [hnon, Bool.false_eq_true, if_false]
      exact ih (c + 1)

/--
Executable search reflection for one field constant: if the gcd candidate
attached to `c` is nonzero, nonconstant, and strictly smaller in size than
the input, then the guarded Berlekamp witness search succeeds.  The guard
cannot fire here: a genuine split means `witness` is nonconstant modulo `f`.
-/
theorem kernelWitnessSplit?_some_of_nontrivial_splitFactorAt
    [ZMod64.PrimeModulus p]
    (f witness : FpPoly p) (c : ZMod64 p)
    (hnotZero : !(splitFactorAt f witness c).isZero)
    (hdegree : (splitFactorAt f witness c).degree? ≠ some 0)
    (hsize_lt : (splitFactorAt f witness c).size < f.size) :
    ∃ r : SplitResult p, kernelWitnessSplit? f witness = some r := by
  have hc_lt : c.toNat < p := c.toNat_lt
  have hc_eq : ZMod64.ofNat p c.toNat = c := ZMod64.ofNat_toNat c
  have hnontriv : isNontrivialSplitFactor f (splitFactorAt f witness c) = true := by
    unfold isNontrivialSplitFactor
    cases hz : (splitFactorAt f witness c).isZero <;> simp [hz] at hnotZero ⊢
    exact ⟨hdegree, hsize_lt⟩
  have hguard : ¬ (witness % f).size ≤ 1 := by
    intro hle
    rw [isNontrivialSplitFactor_false_of_mod_size_le_one f witness hle c] at hnontriv
    exact absurd hnontriv (by simp)
  have hnon :
      isNontrivialSplitFactor f
        (splitFactorAt f witness (ZMod64.ofNat p (0 + c.toNat))) = true := by
    rw [Nat.zero_add, hc_eq]; exact hnontriv
  unfold kernelWitnessSplit?
  rw [if_neg hguard]
  exact kernelWitnessSplitAux_some_of_nontrivial_offset f witness p 0 c.toNat hc_lt hnon

/-- `isNontrivialSplitFactor` only sees its arguments through size and degree,
so it agrees on associate candidates relative to equally sized inputs. -/
private theorem isNontrivialSplitFactor_eq_of_associate
    [ZMod64.PrimeModulus p] {f₁ f₂ d₁ d₂ : FpPoly p}
    (hf : f₁.size = f₂.size)
    (hd₁₂ : d₁ ∣ d₂) (hd₂₁ : d₂ ∣ d₁) :
    isNontrivialSplitFactor f₁ d₁ = isNontrivialSplitFactor f₂ d₂ := by
  have hsize := size_eq_of_dvd_dvd hd₁₂ hd₂₁
  have hzero : d₁.isZero = d₂.isZero := by
    rcases Nat.eq_zero_or_pos d₂.size with hz | hz
    · rw [(DensePoly.isZero_eq_true_iff d₁).mpr (hsize.trans hz),
          (DensePoly.isZero_eq_true_iff d₂).mpr hz]
    · rw [(DensePoly.isZero_eq_false_iff d₁).mpr (by rw [hsize]; exact hz),
          (DensePoly.isZero_eq_false_iff d₂).mpr hz]
  have hdeg : d₁.degree? = d₂.degree? := by
    unfold DensePoly.degree?
    rw [hsize]
  unfold isNontrivialSplitFactor
  rw [hzero, hdeg, hsize, hf]

/-- The split candidates of `g` and its unit scaling `scale c g` are associates
for every witness and constant: each divides the other. -/
private theorem splitFactorAt_dvd_dvd_scale
    [ZMod64.PrimeModulus p] {c : ZMod64 p} (hc : c ≠ 0)
    (g witness : FpPoly p) (k : ZMod64 p) :
    splitFactorAt (DensePoly.scale c g) witness k ∣ splitFactorAt g witness k ∧
      splitFactorAt g witness k ∣ splitFactorAt (DensePoly.scale c g) witness k := by
  rw [splitFactorAt_spec, splitFactorAt_spec]
  have hsg_dvd_g : DensePoly.scale c g ∣ g := FpPoly.dvd_scale_self_of_ne_zero hc g
  have hg_dvd_sg : g ∣ DensePoly.scale c g := by
    rw [← FpPoly.C_mul_eq_scale]
    exact ⟨DensePoly.C c, (DensePoly.mul_comm_poly g (DensePoly.C c)).symm⟩
  refine ⟨DensePoly.dvd_gcd _ _ _ ?_ (DensePoly.gcd_dvd_right _ _),
    DensePoly.dvd_gcd _ _ _ ?_ (DensePoly.gcd_dvd_right _ _)⟩
  · exact dvd_trans_fp (DensePoly.gcd_dvd_left _ _) hsg_dvd_g
  · exact dvd_trans_fp (DensePoly.gcd_dvd_left _ _) hg_dvd_sg

/-- A failed Berlekamp split search is preserved under a unit scaling of the
factor being split.  Drives the no-split transport in
`kernelWitnessSplit?_none_scale`. -/
private theorem kernelWitnessSplitAux_none_scale
    [ZMod64.PrimeModulus p] {c : ZMod64 p} (hc : c ≠ 0)
    (g witness : FpPoly p) :
    ∀ (fuel start : Nat),
      kernelWitnessSplitAux g witness fuel start = none →
        kernelWitnessSplitAux (DensePoly.scale c g) witness fuel start = none := by
  intro fuel
  induction fuel with
  | zero => intro start _h; rfl
  | succ fuel ih =>
      intro start h
      unfold kernelWitnessSplitAux at h ⊢
      let splitConstant := ZMod64.ofNat p start
      let factorG := splitFactorAt g witness splitConstant
      let factorSG := splitFactorAt (DensePoly.scale c g) witness splitConstant
      have hcong : isNontrivialSplitFactor (DensePoly.scale c g) factorSG
          = isNontrivialSplitFactor g factorG := by
        obtain ⟨h1, h2⟩ := splitFactorAt_dvd_dvd_scale hc g witness splitConstant
        exact isNontrivialSplitFactor_eq_of_associate
          (FpPoly.scale_size_eq_of_ne_zero hc g) h1 h2
      by_cases hnon : isNontrivialSplitFactor g factorG
      · simp [splitConstant, factorG, hnon] at h
      · have hnonSG : ¬ isNontrivialSplitFactor (DensePoly.scale c g) factorSG := by
          rw [hcong]; exact hnon
        simp only [splitConstant, factorG, hnon, Bool.false_eq_true, if_false] at h
        simp only [splitConstant, factorSG, hnonSG, Bool.false_eq_true, if_false]
        exact ih (start + 1) h

/-- Transport of a failed Berlekamp split search across a unit scaling: if no
kernel-witness split of `g` is found, none is found for `scale c g` either
(`c ≠ 0`).  Lets callers move a no-split fact from a raw factor to its monic
associate. -/
theorem kernelWitnessSplit?_none_scale
    [ZMod64.PrimeModulus p] {c : ZMod64 p} (hc : c ≠ 0)
    (g witness : FpPoly p)
    (h : kernelWitnessSplit? g witness = none) :
    kernelWitnessSplit? (DensePoly.scale c g) witness = none := by
  -- Extract `kernelWitnessSplitAux g witness p 0 = none`: either the guard
  -- fired (and the skipped sweep is `none` by soundness) or the sweep ran and
  -- returned `none` directly.
  have haux_g : kernelWitnessSplitAux g witness p 0 = none := by
    by_cases hguard : (witness % g).size ≤ 1
    · exact kernelWitnessSplitAux_none_of_mod_size_le_one g witness hguard p 0
    · have h' := h
      unfold kernelWitnessSplit? at h'
      rw [if_neg hguard] at h'
      exact h'
  have haux_sg : kernelWitnessSplitAux (DensePoly.scale c g) witness p 0 = none :=
    kernelWitnessSplitAux_none_scale hc g witness p 0 haux_g
  unfold kernelWitnessSplit?
  by_cases hguard2 : (witness % DensePoly.scale c g).size ≤ 1
  · rw [if_pos hguard2]
  · rw [if_neg hguard2]; exact haux_sg

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

/-- `factorProduct` distributes over list append. -/
private theorem factorProduct_append
    [ZMod64.PrimeModulus p]
    (xs ys : List (FpPoly p)) :
    factorProduct (xs ++ ys) = factorProduct xs * factorProduct ys := by
  induction xs with
  | nil =>
      show factorProduct ys = factorProduct ([] : List (FpPoly p)) * factorProduct ys
      rw [factorProduct_nil]
      exact (one_mul_poly (factorProduct ys)).symm
  | cons x xs ih =>
      show factorProduct (x :: (xs ++ ys)) = factorProduct (x :: xs) * factorProduct ys
      rw [factorProduct_cons, factorProduct_cons, ih]
      exact (DensePoly.mul_assoc_poly x (factorProduct xs) (factorProduct ys)).symm

/-- The product of the witness-irreducible pieces of `f` recovers `f`. -/
private theorem factorProduct_fullySplit
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) (fuel : Nat) (f : FpPoly p) :
    factorProduct (fullySplit witnesses fuel f) = f := by
  induction fuel generalizing f with
  | zero =>
      show factorProduct [f] = f
      rw [factorProduct_cons, factorProduct_nil]
      exact DensePoly.mul_one_right_poly f
  | succ fuel ih =>
      rw [fullySplit]
      cases hsplit : splitWithWitnesses? f witnesses with
      | none =>
          show factorProduct [f] = f
          rw [factorProduct_cons, factorProduct_nil]
          exact DensePoly.mul_one_right_poly f
      | some split =>
          rw [factorProduct_append, ih, ih]
          exact splitWithWitnesses?_product_spec f witnesses hsplit

/-- The Berlekamp factor list's product equals the input polynomial.  Fully
splitting preserves `factorProduct` without using square-freeness, so the
product equality holds for every monic input. -/
theorem factorProduct_berlekampFactor
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    factorProduct (berlekampFactor f hmonic).factors = f :=
  factorProduct_fullySplit ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f

/--
The executable Berlekamp factorization preserves the input polynomial as the
product of the returned factors for any monic input.
-/
theorem prod_berlekampFactor
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p] :
    (berlekampFactor f hmonic).product = f := by
  simp only [Factorization.product_def]
  exact factorProduct_berlekampFactor f hmonic

/-! ### Witness-irreducible leaf structure

`fullySplit` emits a factor as a singleton leaf exactly when it admits no
kernel-witness split, and a successful split produces two nonempty subtrees.
So the output is always nonempty, and a length-≤-1 output means the input
itself admits no split — every fixed-space kernel witness yields
`kernelWitnessSplit? = none`. This isolates the executable side of Berlekamp
completeness; the algebraic implication "no kernel-witness split implies
irreducibility" lives in a separate finite-field module. -/

/-- Fully splitting always retains at least one factor. -/
private theorem fullySplit_ne_nil
    (witnesses : List (FpPoly p)) (fuel : Nat) (f : FpPoly p) :
    fullySplit witnesses fuel f ≠ [] := by
  induction fuel generalizing f with
  | zero => show ([f] : List (FpPoly p)) ≠ []; exact List.cons_ne_nil f []
  | succ fuel ih =>
      rw [fullySplit]
      cases hsplit : splitWithWitnesses? f witnesses with
      | none => show ([f] : List (FpPoly p)) ≠ []; exact List.cons_ne_nil f []
      | some split =>
          show (fullySplit witnesses fuel split.factor
            ++ fullySplit witnesses fuel split.cofactor) ≠ []
          intro hcontra
          cases hA : fullySplit witnesses fuel split.factor with
          | nil => exact ih split.factor hA
          | cons a as => rw [hA] at hcontra; simp at hcontra

/-- When `f` admits no kernel-witness split, fully splitting it (with positive
fuel) returns the singleton `[f]`. -/
private theorem fullySplit_succ_eq_self_of_none
    (witnesses : List (FpPoly p)) (fuel : Nat) (f : FpPoly p)
    (h : splitWithWitnesses? f witnesses = none) :
    fullySplit witnesses (fuel + 1) f = [f] := by
  rw [fullySplit, h]

/-- Executable Berlekamp factorization always retains at least one factor. -/
theorem berlekampFactor_factors_ne_nil
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    (berlekampFactor f hmonic).factors ≠ [] :=
  fullySplit_ne_nil ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f

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
Mathlib-free finite-field module.
-/
theorem kernelWitnessSplit?_none_of_berlekampFactor_factors_length_le_one
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    (hsmall : (berlekampFactor f hmonic).factors.length ≤ 1) :
    ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
      kernelWitnessSplit? f w = none := by
  -- A length-≤-1 output forces `f` itself to admit no kernel-witness split:
  -- a successful split would emit two nonempty subtrees, hence length ≥ 2.
  have hsplit_none :
      splitWithWitnesses? f ((fixedSpaceKernel f hmonic).toList) = none := by
    cases hsp : splitWithWitnesses? f ((fixedSpaceKernel f hmonic).toList) with
    | none => rfl
    | some split =>
        exfalso
        have hfac_eq : (berlekampFactor f hmonic).factors
            = fullySplit ((fixedSpaceKernel f hmonic).toList) f.size split.factor
              ++ fullySplit ((fixedSpaceKernel f hmonic).toList) f.size split.cofactor := by
          show fullySplit ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f = _
          rw [fullySplit, hsp]
        rw [hfac_eq, List.length_append] at hsmall
        have h1 : 0 < (fullySplit ((fixedSpaceKernel f hmonic).toList) f.size split.factor).length :=
          List.length_pos_iff.mpr (fullySplit_ne_nil _ _ _)
        have h2 : 0 < (fullySplit ((fixedSpaceKernel f hmonic).toList) f.size split.cofactor).length :=
          List.length_pos_iff.mpr (fullySplit_ne_nil _ _ _)
        omega
  rw [splitWithWitnesses?_none_iff_forall] at hsplit_none
  exact hsplit_none

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
  kernelWitnessSplitAux_factor_pos_degree f witness p 0 r (kernelWitnessSplitAux_of_some hsplit)

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

/-- A polynomial of positive degree is nonzero. -/
private theorem ne_zero_of_pos_degree {g : FpPoly p}
    (h : 0 < g.degree?.getD 0) : g ≠ 0 := by
  intro hz
  rw [hz] at h
  have hnone : (0 : FpPoly p).degree? = none := rfl
  rw [hnone] at h
  simp at h

/-- A polynomial of positive degree has `size` at least two. -/
private theorem size_ge_two_of_pos_degree {g : FpPoly p}
    (h : 0 < g.degree?.getD 0) : 2 ≤ g.size := by
  rcases Nat.lt_or_ge g.size 2 with hlt | hge
  · exfalso
    have hsize_pos : 0 < g.size := FpPoly.size_pos_of_ne_zero (ne_zero_of_pos_degree h)
    have hsize1 : g.size = 1 := by omega
    have hdeg : g.degree? = some 0 := by
      unfold DensePoly.degree?
      simp [hsize1]
    rw [hdeg] at h
    simp at h
  · exact hge

/-- A successful `splitWithWitnesses?` cofactor is strictly smaller than the
input.  Together with `splitWithWitnesses?_size_lt` this drives the recursion
depth of `fullySplit`. -/
private theorem splitWithWitnesses?_cofactor_size_lt
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (witnesses : List (FpPoly p))
    (hf_ne : f ≠ 0)
    {r : SplitResult p}
    (h : splitWithWitnesses? f witnesses = some r) :
    r.cofactor.size < f.size := by
  have hfac_pos := splitWithWitnesses?_factor_pos_degree f witnesses h
  have hprod := splitWithWitnesses?_product_spec f witnesses h
  have hfac_ne : r.factor ≠ 0 := ne_zero_of_pos_degree hfac_pos
  have hcof_ne : r.cofactor ≠ 0 := by
    intro hr
    rw [hr, FpPoly.mul_zero] at hprod
    exact hf_ne hprod.symm
  have hfac_ge_2 : 2 ≤ r.factor.size := size_ge_two_of_pos_degree hfac_pos
  have hsize_sum : r.factor.size + r.cofactor.size = f.size + 1 := by
    have hf_size_eq : f.size = (r.factor * r.cofactor).size := by rw [hprod]
    rw [hf_size_eq, FpPoly.size_mul_eq_add_sub_one r.factor r.cofactor hfac_ne hcof_ne]
    have hfac_size_pos := FpPoly.size_pos_of_ne_zero hfac_ne
    have hcof_size_pos := FpPoly.size_pos_of_ne_zero hcof_ne
    omega
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

/-- Two distinct elements of a `Nodup` list of `FpPoly p` have a product that
divides the list's product. -/
theorem mul_dvd_factorProduct_of_mem_of_ne
    [ZMod64.PrimeModulus p]
    {xs : List (FpPoly p)} (h_nodup : xs.Nodup)
    {a b : FpPoly p} (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) :
    a * b ∣ factorProduct xs := by
  induction xs with
  | nil => exact absurd ha List.not_mem_nil
  | cons x rest ih =>
    have h_rest_nodup : rest.Nodup := (List.nodup_cons.mp h_nodup).2
    rw [factorProduct_cons]
    rcases List.mem_cons.mp ha with hax | har
    · -- a = x
      subst hax
      rcases List.mem_cons.mp hb with hbx | hbr
      · subst hbx; exact absurd rfl hab
      · -- a = x, b ∈ rest. factorProduct (x :: rest) = a * factorProduct rest.
        rcases dvd_factorProduct_of_mem rest hbr with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [hq]
        exact (DensePoly.mul_assoc_poly a b q).symm
    · -- a ∈ rest
      rcases List.mem_cons.mp hb with hbx | hbr
      · -- a ∈ rest, b = x. factorProduct (x :: rest) = b * factorProduct rest.
        subst hbx
        rcases dvd_factorProduct_of_mem rest har with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [hq]
        -- Goal: b * (a * q) = a * b * q
        calc b * (a * q)
            = (b * a) * q := (DensePoly.mul_assoc_poly _ _ _).symm
          _ = (a * b) * q :=
              congrArg (· * q) (DensePoly.mul_comm_poly _ _)
      · -- both a, b ∈ rest
        rcases ih h_rest_nodup har hbr with ⟨q, hq⟩
        refine ⟨x * q, ?_⟩
        rw [hq]
        -- Goal: x * (a * b * q) = a * b * (x * q)
        calc x * (a * b * q)
            = (x * (a * b)) * q := (DensePoly.mul_assoc_poly _ _ _).symm
          _ = ((a * b) * x) * q :=
              congrArg (· * q) (DensePoly.mul_comm_poly _ _)
          _ = (a * b) * (x * q) := DensePoly.mul_assoc_poly _ _ _

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

/-- Tree invariant for `fullySplit`: when `f` has positive degree and no
positive-degree polynomial squares to a divisor of `f`, the witness-irreducible
pieces form a `Nodup` list whose entries all have positive degree.  Distinctness
comes from the no-squared hypothesis: a factor shared by the two subtrees would
square-divide `f`. -/
private theorem fullySplit_nodup_pos
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) (fuel : Nat) (f : FpPoly p)
    (h_pos : 0 < f.degree?.getD 0)
    (h_no_squared : ∀ g : FpPoly p,
        g * g ∣ f → ¬ (0 < g.degree?.getD 0)) :
    (fullySplit witnesses fuel f).Nodup ∧
      (∀ g ∈ fullySplit witnesses fuel f, 0 < g.degree?.getD 0) := by
  induction fuel generalizing f with
  | zero =>
      refine ⟨?_, ?_⟩
      · show ([f] : List (FpPoly p)).Nodup
        exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      · intro g hg
        have hgf := List.eq_of_mem_singleton hg
        subst hgf
        exact h_pos
  | succ fuel ih =>
      rw [fullySplit]
      cases hsplit : splitWithWitnesses? f witnesses with
      | none =>
          refine ⟨?_, ?_⟩
          · show ([f] : List (FpPoly p)).Nodup
            exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
          · intro g hg
            rw [List.mem_singleton] at hg
            subst hg
            exact h_pos
      | some split =>
          have hf_ne : f ≠ 0 := ne_zero_of_pos_degree h_pos
          have h_factor_pos := splitWithWitnesses?_factor_pos_degree f witnesses hsplit
          have h_cofactor_pos :=
            splitWithWitnesses?_cofactor_pos_degree f witnesses hf_ne hsplit
          have h_prod := splitWithWitnesses?_product_spec f witnesses hsplit
          have h_fac_dvd : split.factor ∣ f := ⟨split.cofactor, h_prod.symm⟩
          have h_cof_dvd : split.cofactor ∣ f :=
            ⟨split.factor, by rw [← h_prod]; exact FpPoly.mul_comm _ _⟩
          have h_no_sq_fac : ∀ g : FpPoly p,
              g * g ∣ split.factor → ¬ (0 < g.degree?.getD 0) :=
            fun g hgg => h_no_squared g (dvd_trans_fp hgg h_fac_dvd)
          have h_no_sq_cof : ∀ g : FpPoly p,
              g * g ∣ split.cofactor → ¬ (0 < g.degree?.getD 0) :=
            fun g hgg => h_no_squared g (dvd_trans_fp hgg h_cof_dvd)
          have hA := ih split.factor h_factor_pos h_no_sq_fac
          have hB := ih split.cofactor h_cofactor_pos h_no_sq_cof
          have hA_prod : factorProduct (fullySplit witnesses fuel split.factor) = split.factor :=
            factorProduct_fullySplit witnesses fuel split.factor
          have hB_prod : factorProduct (fullySplit witnesses fuel split.cofactor) = split.cofactor :=
            factorProduct_fullySplit witnesses fuel split.cofactor
          refine ⟨?_, ?_⟩
          · rw [List.nodup_append]
            refine ⟨hA.1, hB.1, ?_⟩
            intro a haA b hbB hab
            subst hab
            have ha_fac : a ∣ split.factor := by
              rw [← hA_prod]; exact dvd_factorProduct_of_mem _ haA
            have ha_cof : a ∣ split.cofactor := by
              rw [← hB_prod]; exact dvd_factorProduct_of_mem _ hbB
            have ha_sq : a * a ∣ f := by
              rw [← h_prod]; exact squared_dvd_of_dvd_dvd ha_fac ha_cof
            exact h_no_squared a ha_sq (hA.2 a haA)
          · intro g hg
            rw [List.mem_append] at hg
            rcases hg with hgA | hgB
            · exact hA.2 g hgA
            · exact hB.2 g hgB

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
  by_cases h_f_pos : 0 < f.degree?.getD 0
  · exact (fullySplit_nodup_pos ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f
      h_f_pos h_no_squared).1
  · -- Degree 0: `f` admits no kernel split, so the factor list is `[f]`,
    -- which is trivially `Nodup`.
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
    have h_no_split : splitWithWitnesses? f ((fixedSpaceKernel f hmonic).toList) = none := by
      rw [splitWithWitnesses?_none_iff_forall]
      intro w _hw
      cases hopt : kernelWitnessSplit? f w with
      | none => rfl
      | some r =>
          exfalso
          have hsize_lt := kernelWitnessSplit_size_lt f w r hopt
          have hfac_pos := kernelWitnessSplit_factor_pos_degree f w r hopt
          have hfac_size_ge_two : 2 ≤ r.factor.size := size_ge_two_of_pos_degree hfac_pos
          omega
    show (fullySplit ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f).Nodup
    rw [fullySplit_succ_eq_self_of_none _ _ _ h_no_split]
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩

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

/-- Positivity-only variant of the `fullySplit` invariant: every emitted
factor has positive degree, without requiring the squareness-free hypothesis.
Each side of a split has positive degree, and a witness-irreducible leaf is the
positive-degree input itself. -/
private theorem fullySplit_pos
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) (fuel : Nat) (f : FpPoly p)
    (h_pos : 0 < f.degree?.getD 0) :
    ∀ g ∈ fullySplit witnesses fuel f, 0 < g.degree?.getD 0 := by
  induction fuel generalizing f with
  | zero =>
      intro g hg
      have hgf := List.eq_of_mem_singleton hg
      subst hgf
      exact h_pos
  | succ fuel ih =>
      rw [fullySplit]
      cases hsplit : splitWithWitnesses? f witnesses with
      | none =>
          intro g hg
          rw [List.mem_singleton] at hg
          subst hg
          exact h_pos
      | some split =>
          have hf_ne : f ≠ 0 := ne_zero_of_pos_degree h_pos
          have h_factor_pos := splitWithWitnesses?_factor_pos_degree f witnesses hsplit
          have h_cofactor_pos :=
            splitWithWitnesses?_cofactor_pos_degree f witnesses hf_ne hsplit
          intro g hg
          rw [List.mem_append] at hg
          rcases hg with hgA | hgB
          · exact ih split.factor h_factor_pos g hgA
          · exact ih split.cofactor h_cofactor_pos g hgB

/-- Abstract form of `berlekampFactor`'s output factor-degree positivity: if
the input polynomial has positive degree, then every factor in the executable
Berlekamp factor list has positive degree.  The squareness-free hypothesis
needed by `berlekampFactor_factors_nodup_of_no_squared` is not needed here:
positivity is preserved by every split regardless of square-freeness. -/
theorem berlekampFactor_factors_pos_degree
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hf_pos : 0 < f.degree?.getD 0) :
    ∀ g ∈ (berlekampFactor f hmonic).factors, 0 < g.degree?.getD 0 :=
  fullySplit_pos ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f hf_pos

/-- For a monic input of size ≤ 1, the executable Berlekamp factor list is
exactly the singleton `[f]`.  A polynomial of size ≤ 1 has no positive-degree
divisors, so it admits no kernel-witness split and `fullySplit` emits it as a
leaf. -/
theorem berlekampFactor_factors_eq_singleton_of_size_le_one
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsize : f.size ≤ 1) :
    (berlekampFactor f hmonic).factors = [f] := by
  have h_no_split : splitWithWitnesses? f ((fixedSpaceKernel f hmonic).toList) = none := by
    rw [splitWithWitnesses?_none_iff_forall]
    intro w _hw
    cases hopt : kernelWitnessSplit? f w with
    | none => rfl
    | some r =>
        exfalso
        have hsize_lt := kernelWitnessSplit_size_lt f w r hopt
        have hnt := kernelWitnessSplit_nontrivial f w r hopt
        -- r.factor.size < f.size ≤ 1, so r.factor.size = 0, so r.factor = 0.
        have hfac_size_zero : r.factor.size = 0 := by omega
        have hfac_iszero : r.factor.isZero = true := by
          change r.factor.coeffs.isEmpty = true
          simpa [DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hfac_size_zero
        rw [hfac_iszero] at hnt
        simp at hnt
  show fullySplit ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f = [f]
  exact fullySplit_succ_eq_self_of_none _ _ _ h_no_split

/-- Every factor in the Berlekamp factor list is nonzero.  Splits the positive-
degree case (where every factor has positive degree via
`berlekampFactor_factors_pos_degree`) from the size-≤-1 case (where the factor
list is the singleton `[f]` and `f` is monic, hence nonzero). -/
theorem berlekampFactor_factors_ne_zero
    [Lean.Grind.Field (ZMod64 p)]
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ g ∈ (berlekampFactor f hmonic).factors, g ≠ 0 := by
  by_cases hf_pos : 0 < f.degree?.getD 0
  · intro g hg
    have hg_pos := berlekampFactor_factors_pos_degree f hmonic hf_pos g hg
    intro h
    rw [h] at hg_pos
    simp [DensePoly.degree?] at hg_pos
  · -- f.size ≤ 1: factors = [f], which is monic hence nonzero.
    have hf_size_le : f.size ≤ 1 := by
      rcases Nat.lt_or_ge f.size 2 with hlt | hge
      · omega
      · exfalso
        apply hf_pos
        have hsize_ne : f.size ≠ 0 := by omega
        have hdeg_eq : f.degree? = some (f.size - 1) := by
          unfold DensePoly.degree?
          simp [hsize_ne]
        rw [hdeg_eq]
        simp
        omega
    have hfactors_eq := berlekampFactor_factors_eq_singleton_of_size_le_one f hmonic hf_size_le
    rw [hfactors_eq]
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    intro h
    subst h
    have hlead_zero : DensePoly.leadingCoeff (0 : FpPoly p) = 0 := rfl
    unfold DensePoly.Monic at hmonic
    rw [hlead_zero] at hmonic
    exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) hmonic.symm

/-! ### Every returned factor resists all kernel-witness splits

The completeness theorem for monic divisors needs, for each returned factor,
that no fixed-space kernel witness splits it.  This is structural for
`fullySplit`: a factor is emitted only as a witness-irreducible leaf, where
`splitWithWitnesses?` already reported `none`.  The `f.size + 1` fuel never
runs out before the leaves, because `size` strictly decreases at every split. -/

/-- **Per-factor no-split.** With enough fuel (`f.size ≤ fuel`) every factor
emitted by `fullySplit` admits no kernel-witness split — it was emitted exactly
because `splitWithWitnesses?` returned `none` on it. -/
private theorem fullySplit_unsplittable
    [ZMod64.PrimeModulus p]
    (witnesses : List (FpPoly p)) :
    ∀ (fuel : Nat) (f : FpPoly p), f ≠ 0 → f.size ≤ fuel →
      ∀ g ∈ fullySplit witnesses fuel f, splitWithWitnesses? g witnesses = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro f hne hle
      exact absurd hle (by have := FpPoly.size_pos_of_ne_zero hne; omega)
  | succ fuel ih =>
      intro f hne hle g hg
      rw [fullySplit] at hg
      cases hsplit : splitWithWitnesses? f witnesses with
      | none =>
          rw [hsplit] at hg
          rw [List.mem_singleton] at hg
          subst hg
          exact hsplit
      | some split =>
          rw [hsplit] at hg
          rw [List.mem_append] at hg
          have hfac_pos := splitWithWitnesses?_factor_pos_degree f witnesses hsplit
          have hcof_pos := splitWithWitnesses?_cofactor_pos_degree f witnesses hne hsplit
          have hfac_ne : split.factor ≠ 0 := ne_zero_of_pos_degree hfac_pos
          have hcof_ne : split.cofactor ≠ 0 := ne_zero_of_pos_degree hcof_pos
          have hfac_size_lt := splitWithWitnesses?_size_lt f witnesses hsplit
          have hcof_size_lt := splitWithWitnesses?_cofactor_size_lt f witnesses hne hsplit
          rcases hg with hgA | hgB
          · exact ih split.factor hfac_ne (by omega) g hgA
          · exact ih split.cofactor hcof_ne (by omega) g hgB

/-- **Per-factor no-split.** Every factor returned by the executable Berlekamp
factorization of a monic input resists every fixed-space kernel-witness split.
The `f.size + 1` fuel always suffices to reach the witness-irreducible leaves. -/
theorem kernelWitnessSplit?_none_of_berlekampFactor_factors
    [Lean.Grind.Field (ZMod64 p)] [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ g ∈ (berlekampFactor f hmonic).factors,
      ∀ w ∈ (fixedSpaceKernel f hmonic).toList, kernelWitnessSplit? g w = none := by
  have hf_ne : f ≠ 0 := by
    intro h
    have hlead_zero : DensePoly.leadingCoeff (0 : FpPoly p) = 0 := rfl
    unfold DensePoly.Monic at hmonic
    rw [h, hlead_zero] at hmonic
    exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) hmonic.symm
  intro g hg w hw
  have hg_none : splitWithWitnesses? g ((fixedSpaceKernel f hmonic).toList) = none :=
    fullySplit_unsplittable ((fixedSpaceKernel f hmonic).toList) (f.size + 1) f hf_ne
      (by omega) g hg
  rw [splitWithWitnesses?_none_iff_forall] at hg_none
  exact hg_none w hw

/-- Every factor returned by the executable Berlekamp factorization divides the
input.  Immediate from `factorProduct_berlekampFactor`. -/
theorem berlekampFactor_factors_dvd
    [Lean.Grind.Field (ZMod64 p)] [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ g ∈ (berlekampFactor f hmonic).factors, g ∣ f := by
  intro g hg
  have hdvd := dvd_factorProduct_of_mem (berlekampFactor f hmonic).factors hg
  rwa [factorProduct_berlekampFactor f hmonic] at hdvd

end Berlekamp

end Hex
