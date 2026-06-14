import HexModArith.Prime
import HexPoly.Euclid
import Init.Data.List.Lemmas
import Init.Data.List.Perm

/-!
Core definitions for executable polynomials over `F_p`.

This module specializes the generic dense-polynomial API to
`Hex.ZMod64 p`, exposing the `FpPoly p` abbreviation together with the
constructors and instances needed by downstream finite-field
algorithms.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

instance : Zero (ZMod64 p) where
  zero := ZMod64.zero

instance : One (ZMod64 p) where
  one := ZMod64.one

instance : Add (ZMod64 p) where
  add := ZMod64.add

instance : Sub (ZMod64 p) where
  sub := ZMod64.sub

instance : Mul (ZMod64 p) where
  mul := ZMod64.mul

instance : Div (ZMod64 p) where
  div a b := ZMod64.mul a (ZMod64.inv b)

instance : DecidableEq (ZMod64 p) := by
  intro a b
  if h : a.val = b.val then
    exact isTrue (by
      cases a
      cases b
      cases h
      simp)
  else
    exact isFalse (by
      intro hab
      apply h
      exact congrArg ZMod64.val hab)

instance : DensePoly.AddZeroLaw (ZMod64 p) where
  add_zero_zero := by
    rw [eq_iff_toNat_eq]
    change (ZMod64.add ZMod64.zero ZMod64.zero).toNat = ZMod64.zero.toNat
    rw [toNat_add, toNat_zero]
    exact Nat.zero_mod p

instance : DensePoly.SubZeroLaw (ZMod64 p) where
  sub_zero_zero := by
    rw [eq_iff_toNat_eq]
    change (ZMod64.sub ZMod64.zero ZMod64.zero).toNat = ZMod64.zero.toNat
    rw [toNat_sub, toNat_zero]
    simp

instance : DensePoly.ZeroSubNegLaw (ZMod64 p) where
  zero_sub_eq_neg := by
    intro a
    rw [eq_iff_toNat_eq]
    change (ZMod64.sub ZMod64.zero a).toNat = (ZMod64.neg a).toNat
    rw [toNat_sub, toNat_neg, toNat_zero]
    simp [Nat.zero_add]

private theorem coeff_add_semiring_rw_smoke (a b : ZMod64 p) (n : Nat) :
    (DensePoly.C a + DensePoly.C b : DensePoly (ZMod64 p)).coeff n =
      (DensePoly.C a).coeff n + (DensePoly.C b).coeff n := by
  rw [DensePoly.coeff_add_semiring]

private theorem coeff_add_semiring_simp_smoke (a b : ZMod64 p) (n : Nat) :
    (DensePoly.C a + DensePoly.C b : DensePoly (ZMod64 p)).coeff n =
      (DensePoly.C a).coeff n + (DensePoly.C b).coeff n := by
  simp

private theorem coeff_sub_ring_rw_smoke (a b : ZMod64 p) (n : Nat) :
    (DensePoly.C a - DensePoly.C b : DensePoly (ZMod64 p)).coeff n =
      (DensePoly.C a).coeff n - (DensePoly.C b).coeff n := by
  rw [DensePoly.coeff_sub_ring]

private theorem coeff_sub_ring_simp_smoke (a b : ZMod64 p) (n : Nat) :
    (DensePoly.C a - DensePoly.C b : DensePoly (ZMod64 p)).coeff n =
      (DensePoly.C a).coeff n - (DensePoly.C b).coeff n := by
  simp

private theorem coeff_neg_ring_rw_smoke (a : ZMod64 p) (n : Nat) :
    (-DensePoly.C a : DensePoly (ZMod64 p)).coeff n =
      -((DensePoly.C a).coeff n) := by
  rw [DensePoly.coeff_neg_ring]

private theorem coeff_neg_ring_simp_smoke (a : ZMod64 p) (n : Nat) :
    (-DensePoly.C a : DensePoly (ZMod64 p)).coeff n =
      -((DensePoly.C a).coeff n) := by
  simp

/-- `DensePoly.divMod f g` returns a quotient-remainder pair `(q, r)` with `q * g + r = f`. -/
private theorem divMod_spec_core [PrimeModulus p] (f g : DensePoly (ZMod64 p)) :
    let qr := DensePoly.divMod f g
    qr.1 * g + qr.2 = f := by
  by_cases hgzero : g.isZero
  · have hgsize : g.size = 0 := by
      have hcoeffs : g.coeffs.size = 0 := by
        simpa [DensePoly.isZero, Array.isEmpty_iff_size_eq_zero] using hgzero
      simpa [DensePoly.size] using hcoeffs
    have hdiv := DensePoly.divMod_eq_zero_self_of_size_zero_core f g hgsize
    simp [hdiv]
    change ((0 : DensePoly (ZMod64 p)) * g) + f = f
    exact Eq.trans (congrArg (fun x : DensePoly (ZMod64 p) => x + f)
      (DensePoly.zero_mul (S := ZMod64 p) g)) (DensePoly.zero_add (S := ZMod64 p) f)
  · apply DensePoly.divMod_reconstruction
    intro a
    have hgpos : 0 < g.size := by
      have hcoeffs : g.coeffs.size ≠ 0 := by
        simpa [DensePoly.isZero, Array.isEmpty_iff_size_eq_zero] using hgzero
      simpa [DensePoly.size, Nat.pos_iff_ne_zero] using hcoeffs
    have hidx : g.coeffs.size - 1 < g.coeffs.size := by
      simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hgpos
    have hlead_eq : g.leadingCoeff = g.coeff (g.size - 1) := by
      unfold DensePoly.leadingCoeff DensePoly.coeff
      change g.coeffs.back?.getD (0 : ZMod64 p) =
        g.coeffs.getD (g.coeffs.size - 1) (Zero.zero : ZMod64 p)
      rw [Array.back?_eq_getElem?]
      rw [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_getElem hidx]
      rfl
    have hlead_ne : g.leadingCoeff ≠ (Zero.zero : ZMod64 p) := by
      rw [hlead_eq]
      exact DensePoly.coeff_last_ne_zero_of_pos_size g hgpos
    have hinv : ZMod64.inv g.leadingCoeff * g.leadingCoeff = (1 : ZMod64 p) :=
      ZMod64.inv_mul_eq_one_of_prime (PrimeModulus.prime (p := p)) hlead_ne
    have hmul : (a / g.leadingCoeff) * g.leadingCoeff = a := by
      change (ZMod64.mul a (ZMod64.inv g.leadingCoeff)) * g.leadingCoeff = a
      calc
        (ZMod64.mul a (ZMod64.inv g.leadingCoeff)) * g.leadingCoeff =
            a * (ZMod64.inv g.leadingCoeff * g.leadingCoeff) := by
              exact Lean.Grind.Semiring.mul_assoc a (ZMod64.inv g.leadingCoeff) g.leadingCoeff
        _ = a * (1 : ZMod64 p) := by rw [hinv]
        _ = a := by exact Lean.Grind.Semiring.mul_one a
    change ZMod64.sub a ((a / g.leadingCoeff) * g.leadingCoeff) = (Zero.zero : ZMod64 p)
    rw [hmul]
    change ZMod64.sub a a = (Zero.zero : ZMod64 p)
    apply ZMod64.ext
    apply UInt64.toNat_inj.mp
    change (ZMod64.sub a a).toNat = (Zero.zero : ZMod64 p).toNat
    rw [ZMod64.toNat_sub]
    have hsum : a.toNat + (p - a.toNat) = p := by
      have ha : a.toNat < p := a.toNat_lt
      omega
    rw [hsum, Nat.mod_self]
    exact ZMod64.toNat_zero.symm

/-- `f % m - f` equals `m * (0 - f / m)`, so the remainder differs from `f` by a multiple of `m`. -/
private theorem mod_sub_self_eq_mul_neg_div [PrimeModulus p] (f m : DensePoly (ZMod64 p)) :
    f % m - f = m * (0 - (f / m)) := by
  have hdiv : (f / m) * m + (f % m) = f := by
    simpa [DensePoly.div, DensePoly.mod] using divMod_spec_core f m
  calc
    f % m - f = 0 - (f / m) * m := by
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hdiv
      change (((f / m) * m + (f % m)).coeff n = f.coeff n) at hcoeff
      rw [DensePoly.coeff_add_semiring] at hcoeff
      rw [DensePoly.coeff_sub_ring]
      rw [DensePoly.coeff_sub_ring]
      rw [DensePoly.coeff_zero]
      grind
    _ = m * (0 - (f / m)) := by
      exact (DensePoly.mul_sub_zero_comm m (f / m)).symm

/-- `f % m` is congruent to `f` modulo `m`. -/
private theorem congr_mod_core [PrimeModulus p] (f m : DensePoly (ZMod64 p)) :
    DensePoly.Congr (f % m) f m := by
  exact ⟨0 - (f / m), mod_sub_self_eq_mul_neg_div f m⟩

/-- `f - g = m * r` rearranges to `f = g + m * r`. -/
private theorem eq_add_mul_of_sub_eq_mul {f g m r : DensePoly (ZMod64 p)}
    (hsub : f - g = m * r) :
    f = g + m * r := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hsub
  change (f - g).coeff n = (m * r).coeff n at hcoeff
  rw [DensePoly.coeff_sub_ring] at hcoeff
  rw [DensePoly.coeff_add_semiring]
  grind

/-- `(a + b) - (c + d)` equals `(a - c) + (b - d)` for `DensePoly` values. -/
private theorem add_sub_add_right (a b c d : DensePoly (ZMod64 p)) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_add_semiring, DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring]
  grind

/-- `(DensePoly.divMod f m).2` has degree strictly below `m` when `m` has positive degree. -/
private theorem divMod_remainder_degree_lt_core
    [PrimeModulus p] (f m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0) :
    (DensePoly.divMod f m).2.degree?.getD 0 < m.degree?.getD 0 := by
  apply DensePoly.divMod_remainder_degree_lt_of_pos_degree_core f m hdegree
  intro a
  let lead := m.leadingCoeff
  have hpos_size : 0 < m.size := by
    by_cases hzero : m.size = 0
    · have hdeg_zero : m.degree?.getD 0 = 0 := by
        simp [DensePoly.degree?, hzero]
      omega
    · exact Nat.pos_of_ne_zero hzero
  have hlead_eq : lead = m.coeff (m.size - 1) := by
    unfold lead DensePoly.leadingCoeff DensePoly.coeff
    have hidx : m.coeffs.size - 1 < m.coeffs.size := by
      simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos_size
    change m.coeffs.back?.getD (0 : ZMod64 p) =
      m.coeffs.getD (m.coeffs.size - 1) (Zero.zero : ZMod64 p)
    rw [Array.back?_eq_getElem?]
    rw [Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_getElem hidx]
    rfl
  have hlead_ne : lead ≠ (Zero.zero : ZMod64 p) := by
    rw [hlead_eq]
    exact DensePoly.coeff_last_ne_zero_of_pos_size m hpos_size
  have hinv : ZMod64.inv lead * lead = (1 : ZMod64 p) :=
    ZMod64.inv_mul_eq_one_of_prime (PrimeModulus.prime (p := p)) hlead_ne
  have hmul : (a / lead) * lead = a := by
    change (ZMod64.mul a (ZMod64.inv lead)) * lead = a
    calc
      (ZMod64.mul a (ZMod64.inv lead)) * lead =
          a * (ZMod64.inv lead * lead) := by
            exact Lean.Grind.Semiring.mul_assoc a (ZMod64.inv lead) lead
      _ = a * (1 : ZMod64 p) := by rw [hinv]
      _ = a := by exact Lean.Grind.Semiring.mul_one a
  change a - (a / lead) * lead = (Zero.zero : ZMod64 p)
  rw [hmul]
  change ZMod64.sub a a = (Zero.zero : ZMod64 p)
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change (ZMod64.sub a a).toNat = (Zero.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_sub]
  have hsum : a.toNat + (p - a.toNat) = p := by
    have ha : a.toNat < p := a.toNat_lt
    omega
  rw [hsum, Nat.mod_self]
  exact ZMod64.toNat_zero.symm

/-- `a - (a / lead) * lead` is zero in `ZMod64 p` whenever `lead` is nonzero. -/
private theorem zmod_div_mul_cancel_of_ne [PrimeModulus p]
    (a lead : ZMod64 p) (hlead : lead ≠ (Zero.zero : ZMod64 p)) :
    a - (a / lead) * lead = (Zero.zero : ZMod64 p) := by
  have hinv : ZMod64.inv lead * lead = (1 : ZMod64 p) :=
    ZMod64.inv_mul_eq_one_of_prime (PrimeModulus.prime (p := p)) hlead
  have hmul : (a / lead) * lead = a := by
    change (ZMod64.mul a (ZMod64.inv lead)) * lead = a
    calc
      (ZMod64.mul a (ZMod64.inv lead)) * lead =
          a * (ZMod64.inv lead * lead) := by
            exact Lean.Grind.Semiring.mul_assoc a (ZMod64.inv lead) lead
      _ = a * (1 : ZMod64 p) := by rw [hinv]
      _ = a := by exact Lean.Grind.Semiring.mul_one a
  rw [hmul]
  change ZMod64.sub a a = (Zero.zero : ZMod64 p)
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change (ZMod64.sub a a).toNat = (Zero.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_sub]
  have hsum : a.toNat + (p - a.toNat) = p := by
    have ha : a.toNat < p := a.toNat_lt
    omega
  rw [hsum, Nat.mod_self]
  exact ZMod64.toNat_zero.symm

/-- `f % m` has degree strictly below `m` when `m` has positive degree. -/
private theorem mod_remainder_degree_lt_core
    [PrimeModulus p] (f m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0) :
    (f % m).degree?.getD 0 < m.degree?.getD 0 := by
  simpa [DensePoly.mod] using divMod_remainder_degree_lt_core f m hdegree

/-- Folding `DensePoly.mulCoeffStep f g n i` over `List.range m` adds `f.coeff i * g.coeff (n - i)`
exactly when `i ≤ n` and `n - i < m`, and `0` otherwise. -/
private theorem foldl_mulCoeffStep_select
    (f g : DensePoly (ZMod64 p)) (n i m : Nat) (acc : ZMod64 p) :
    (List.range m).foldl (DensePoly.mulCoeffStep f g n i) acc =
      acc + (if n < i then 0
        else if n - i < m then f.coeff i * g.coeff (n - i) else 0) := by
  induction m generalizing acc with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

/-- Folding the inner `mulCoeffStep` accumulation over `xs` equals folding the directly-selected
coefficient-product terms over `xs`. -/
private theorem foldl_mulCoeffStep_outer
    (f g : DensePoly (ZMod64 p)) (n : Nat) (xs : List Nat) (acc : ZMod64 p) :
    xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc =
      xs.foldl
        (fun acc i =>
          acc + (if n < i then 0
            else if n - i < g.size then f.coeff i * g.coeff (n - i) else 0))
        acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_mulCoeffStep_select]
      exact ih _

/-- Folding `acc + (if i = k then x else 0)` over `List.range m` adds `x` exactly when `k < m`. -/
private theorem foldl_select_index
    (k m : Nat) (x : ZMod64 p) (acc : ZMod64 p) :
    (List.range m).foldl
        (fun acc i => acc + if i = k then x else 0) acc =
      if k < m then acc + x else acc := by
  induction m generalizing acc with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      by_cases hk : k < m
      · have hne : m ≠ k := by omega
        have hk' : k < m + 1 := by omega
        simp [hk, hne, hk']
      · by_cases hkm : m = k
        · subst k
          have hkk : ¬ m < m := by omega
          have hmm : m < m + 1 := by omega
          simp [hkk, hmm]
        · have hk' : ¬ k < m + 1 := by omega
          simp [hk, hk', hkm]

/-- The top coefficient of a product of nonzero `ZMod64`-valued polynomials is the
product of the leading coefficients. -/
theorem coeff_mul_at_top
    (f g : DensePoly (ZMod64 p)) (hf : 0 < f.size) (hg : 0 < g.size) :
    (f * g).coeff (f.size - 1 + (g.size - 1)) =
      f.coeff (f.size - 1) * g.coeff (g.size - 1) := by
  rw [DensePoly.coeff_mul]
  unfold DensePoly.mulCoeffSum
  rw [foldl_mulCoeffStep_outer]
  -- For each i ∈ [0, f.size), the inner term is the leading product when i = f.size - 1
  -- and 0 otherwise.
  have hfold_eq : ∀ (xs : List Nat) (acc : ZMod64 p),
      (∀ i ∈ xs, i < f.size) →
      xs.foldl
          (fun acc i => acc + (if f.size - 1 + (g.size - 1) < i then 0
            else if f.size - 1 + (g.size - 1) - i < g.size then
              f.coeff i * g.coeff (f.size - 1 + (g.size - 1) - i) else 0)) acc =
        xs.foldl
          (fun acc i => acc + if i = f.size - 1 then
            f.coeff (f.size - 1) * g.coeff (g.size - 1) else 0) acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons j xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        have hj : j < f.size := hxs j (by simp)
        have hnj : ¬ f.size - 1 + (g.size - 1) < j := by omega
        by_cases heq : j = f.size - 1
        · subst j
          have hsub : f.size - 1 + (g.size - 1) - (f.size - 1) = g.size - 1 := by omega
          have hbound : g.size - 1 < g.size := by omega
          simp [hnj, hsub, hbound]
          exact ih (acc + f.coeff (f.size - 1) * g.coeff (g.size - 1))
            (fun k hk => hxs k (by simp [hk]))
        · have hjlt : j < f.size - 1 := by omega
          have hnotbound : ¬ f.size - 1 + (g.size - 1) - j < g.size := by omega
          simp [hnj, hnotbound, heq]
          exact ih acc (fun k hk => hxs k (by simp [hk]))
  rw [hfold_eq (List.range f.size) (Zero.zero : ZMod64 p)
    (by intro i hi; exact List.mem_range.mp hi)]
  rw [foldl_select_index]
  have hfm1 : f.size - 1 < f.size := by omega
  simp [hfm1]
  -- Goal: Zero.zero + (lead_prod) = lead_prod
  show (0 : ZMod64 p) + _ = _
  grind

/-- Two polynomials of degree below `m` that are congruent modulo `m` are equal, when `m` has
positive degree. -/
private theorem canonical_remainder_unique_of_pos_degree
    [PrimeModulus p] (r s m : DensePoly (ZMod64 p))
    (hr : r.degree?.getD 0 < m.degree?.getD 0)
    (hs : s.degree?.getD 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr r s m) :
    r = s := by
  -- We have r - s = m * k for some k.
  rcases hcongr with ⟨k, hk⟩
  -- m has positive degree, so m.size ≥ 2.
  have hm_pos : 0 < m.degree?.getD 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  have hm_size_ge : 2 ≤ m.size := by
    by_cases hms : m.size = 0
    · simp [DensePoly.degree?, hms] at hm_pos
    · have hms_pos : 0 < m.size := Nat.pos_of_ne_zero hms
      have hdeg_eq : m.degree?.getD 0 = m.size - 1 := by
        simp [DensePoly.degree?, hms]
      rw [hdeg_eq] at hm_pos
      omega
  -- Both r and s have size at most m.size - 1.
  have hm_deg : m.degree?.getD 0 = m.size - 1 := by
    have hms : m.size ≠ 0 := by omega
    simp [DensePoly.degree?, hms]
  have hr_size_le : r.size ≤ m.size - 1 := by
    by_cases hrs : r.size = 0
    · omega
    · have hr_deg : r.degree?.getD 0 = r.size - 1 := by simp [DensePoly.degree?, hrs]
      rw [hr_deg, hm_deg] at hr
      omega
  have hs_size_le : s.size ≤ m.size - 1 := by
    by_cases hss : s.size = 0
    · omega
    · have hs_deg : s.degree?.getD 0 = s.size - 1 := by simp [DensePoly.degree?, hss]
      rw [hs_deg, hm_deg] at hs
      omega
  -- (r - s) has size ≤ m.size - 1.
  have hrs_top_zero : ∀ i, max r.size s.size ≤ i → (r - s).coeff i = 0 := by
    intro i hi
    rw [DensePoly.coeff_sub_ring]
    have hr_zero := DensePoly.coeff_eq_zero_of_size_le r (by omega : r.size ≤ i)
    have hs_zero := DensePoly.coeff_eq_zero_of_size_le s (by omega : s.size ≤ i)
    rw [hr_zero, hs_zero]
    grind
  have hmax_le : max r.size s.size ≤ m.size - 1 :=
    Nat.max_le.mpr ⟨hr_size_le, hs_size_le⟩
  have hrs_size_le : (r - s).size ≤ m.size - 1 := by
    by_cases hrs_zero : (r - s).size = 0
    · omega
    · have hrs_pos : 0 < (r - s).size := Nat.pos_of_ne_zero hrs_zero
      have htop := DensePoly.coeff_last_ne_zero_of_pos_size (r - s) hrs_pos
      have hbound : (r - s).size - 1 < max r.size s.size := by
        rcases Nat.lt_or_ge ((r - s).size - 1) (max r.size s.size) with h | hge
        · exact h
        · exact False.elim (htop (hrs_top_zero ((r - s).size - 1) hge))
      have hsub_lt : (r - s).size - 1 < m.size - 1 := Nat.lt_of_lt_of_le hbound hmax_le
      omega
  -- Case on k.
  by_cases hk_zero : k.size = 0
  · -- k = 0, so r - s = m * 0 = 0.
    have hk_eq : k = 0 := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le k (by omega)
    have hmul_zero : m * (0 : DensePoly (ZMod64 p)) = 0 := by
      have hcomm := DensePoly.mul_comm_poly m (0 : DensePoly (ZMod64 p))
      have hzm := DensePoly.zero_mul m
      exact hcomm.trans hzm
    rw [hk_eq] at hk
    rw [hmul_zero] at hk
    -- hk : r - s = 0; conclude r = s.
    apply DensePoly.ext_coeff
    intro i
    have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff i) hk
    change (r - s).coeff i = (0 : DensePoly (ZMod64 p)).coeff i at hcoeff
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hcoeff
    grind
  · -- k ≠ 0: derive contradiction from sizes.
    have hk_pos : 0 < k.size := Nat.pos_of_ne_zero hk_zero
    have hm_pos_size : 0 < m.size := by omega
    have htop := coeff_mul_at_top m k hm_pos_size hk_pos
    have hm_lead_ne : m.coeff (m.size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size m hm_pos_size
    have hk_lead_ne : k.coeff (k.size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size k hk_pos
    have hp_prime : Hex.Nat.Prime p := PrimeModulus.prime
    have hprod_ne : m.coeff (m.size - 1) * k.coeff (k.size - 1) ≠ 0 := by
      intro hprod
      rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp_prime hprod with hh | hh
      · exact hm_lead_ne hh
      · exact hk_lead_ne hh
    have hcoeff_ne : (m * k).coeff (m.size - 1 + (k.size - 1)) ≠ 0 := by
      rw [htop]
      exact hprod_ne
    have hmk_size_gt : m.size - 1 + (k.size - 1) < (m * k).size := by
      rcases Nat.lt_or_ge (m.size - 1 + (k.size - 1)) (m * k).size with h | hle
      · exact h
      · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le (m * k) hle))
    -- (m * k) = (r - s).
    have hmk_eq_rs : (m * k).size = (r - s).size := by rw [← hk]
    omega

private theorem mod_remainders_congr_of_congr [PrimeModulus p]
    (f g m : DensePoly (ZMod64 p))
    (hcongr : DensePoly.Congr f g m) :
    DensePoly.Congr (f % m) (g % m) m := by
  rcases congr_mod_core f m with ⟨rf, hf⟩
  rcases congr_mod_core g m with ⟨rg, hg⟩
  rcases hcongr with ⟨q, hq⟩
  refine ⟨(q + rf) + (0 - rg), ?_⟩
  have hf_add : f % m = f + m * rf := eq_add_mul_of_sub_eq_mul hf
  have hg_add : g % m = g + m * rg := eq_add_mul_of_sub_eq_mul hg
  have hneg_mul : (0 : DensePoly (ZMod64 p)) - m * rg =
      m * ((0 : DensePoly (ZMod64 p)) - rg) := by
    calc
      (0 : DensePoly (ZMod64 p)) - m * rg =
          (0 : DensePoly (ZMod64 p)) - rg * m := by
        exact congrArg (fun x : DensePoly (ZMod64 p) => (0 : DensePoly (ZMod64 p)) - x)
          (DensePoly.mul_comm_poly m rg)
      _ = m * ((0 : DensePoly (ZMod64 p)) - rg) := by
        exact (DensePoly.mul_sub_zero_comm m rg).symm
  calc
    (f % m) - (g % m)
        = (f + m * rf) - (g + m * rg) := by rw [hf_add, hg_add]
    _ = (f - g) + ((m * rf) - (m * rg)) := by
      exact add_sub_add_right f (m * rf) g (m * rg)
    _ = m * q + ((m * rf) - (m * rg)) := by rw [hq]
    _ = m * q + (m * rf + ((0 : DensePoly (ZMod64 p)) - m * rg)) := by
      exact congrArg (fun x : DensePoly (ZMod64 p) => m * q + x)
        (DensePoly.sub_eq_add_neg_poly (m * rf) (m * rg))
    _ = m * q + (m * rf + m * ((0 : DensePoly (ZMod64 p)) - rg)) := by rw [hneg_mul]
    _ = (m * q + m * rf) + m * ((0 : DensePoly (ZMod64 p)) - rg) := by
      exact (DensePoly.add_assoc_poly (m * q) (m * rf)
        (m * ((0 : DensePoly (ZMod64 p)) - rg))).symm
    _ = m * (q + rf) + m * ((0 : DensePoly (ZMod64 p)) - rg) := by
      exact congrArg
        (fun x : DensePoly (ZMod64 p) => x + m * ((0 : DensePoly (ZMod64 p)) - rg))
        (DensePoly.mul_add_right_poly m q rf).symm
    _ = m * ((q + rf) + ((0 : DensePoly (ZMod64 p)) - rg)) := by
      exact (DensePoly.mul_add_right_poly m (q + rf)
        ((0 : DensePoly (ZMod64 p)) - rg)).symm

private theorem mod_eq_mod_of_congr_pos_degree
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  apply canonical_remainder_unique_of_pos_degree
  · exact mod_remainder_degree_lt_core f m hdegree
  · exact mod_remainder_degree_lt_core g m hdegree
  · exact mod_remainders_congr_of_congr f g m hcongr

private theorem mod_zero_right_of_size_zero (f m : DensePoly (ZMod64 p))
    (hm : m.size = 0) :
    f % m = f := by
  simpa [DensePoly.mod] using
    DensePoly.divMod_remainder_eq_self_of_size_zero_core f m hm

private theorem eq_of_sub_eq_zero (f g : DensePoly (ZMod64 p))
    (hsub : f - g = 0) :
    f = g := by
  apply DensePoly.ext_coeff
  intro i
  have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff i) hsub
  change (f - g).coeff i = (0 : DensePoly (ZMod64 p)).coeff i at hcoeff
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hcoeff
  grind

private theorem mod_eq_mod_of_congr_not_pos_degree
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hdegree : ¬ 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  by_cases hm_zero : m.size = 0
  · rw [mod_zero_right_of_size_zero f m hm_zero, mod_zero_right_of_size_zero g m hm_zero]
    rcases hcongr with ⟨k, hk⟩
    have hm_eq_zero : m = 0 := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le m (by omega)
    have hmk_zero : m * k = 0 := by
      rw [hm_eq_zero]
      exact DensePoly.zero_mul k
    apply eq_of_sub_eq_zero f g
    rw [hk, hmk_zero]
  · have hm_size : m.size = 1 := by
      have hm_pos : 0 < m.size := Nat.pos_of_ne_zero hm_zero
      have hdeg : m.degree?.getD 0 = m.size - 1 := by
        simp [DensePoly.degree?, hm_zero]
      rw [hdeg] at hdegree
      omega
    have hlead_ne : m.leadingCoeff ≠ (Zero.zero : ZMod64 p) := by
      have hpos : 0 < m.size := by omega
      have hidx : m.coeffs.size - 1 < m.coeffs.size := by
        simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
      have hlead_eq : m.leadingCoeff = m.coeff (m.size - 1) := by
        unfold DensePoly.leadingCoeff DensePoly.coeff
        change m.coeffs.back?.getD (0 : ZMod64 p) =
          m.coeffs.getD (m.coeffs.size - 1) (Zero.zero : ZMod64 p)
        rw [Array.back?_eq_getElem?]
        rw [Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_getElem hidx]
        rfl
      have hcoeff_ne := DensePoly.coeff_last_ne_zero_of_pos_size m hpos
      rw [hlead_eq]
      exact hcoeff_ne
    have hfmod :
        f % m = 0 := by
      simpa [DensePoly.mod] using
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core f m hm_size
          (fun a => zmod_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    have hgmod :
        g % m = 0 := by
      simpa [DensePoly.mod] using
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core g m hm_size
          (fun a => zmod_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    rw [hfmod, hgmod]

private theorem mod_eq_mod_of_congr_core
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  by_cases hdegree : 0 < m.degree?.getD 0
  · exact mod_eq_mod_of_congr_pos_degree f g m hdegree hcongr
  · exact mod_eq_mod_of_congr_not_pos_degree f g m hdegree hcongr

private theorem sub_zero_poly (f : DensePoly (ZMod64 p)) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero]
  grind

private theorem mod_eq_zero_of_dvd_core
    [PrimeModulus p] (f g : DensePoly (ZMod64 p)) (hdiv : g ∣ f) :
    f % g = 0 := by
  rcases hdiv with ⟨k, hk⟩
  have hcongr : DensePoly.Congr f 0 g := by
    refine ⟨k, ?_⟩
    rw [sub_zero_poly f]
    exact hk
  have hmod := mod_eq_mod_of_congr_core f 0 g hcongr
  exact Eq.trans hmod (DensePoly.zero_mod_eq_zero_core (S := ZMod64 p) g)

private theorem sub_self_right_add (a b : DensePoly (ZMod64 p)) :
    (a + b) - a = b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_add_semiring]
  grind

private theorem mul_left_remainder_delta (f g m rf rg : DensePoly (ZMod64 p))
    (hf : f % m = f + m * rf)
    (hg : g % m = g + m * rg) :
    (f % m * (g % m)) - (f * g) = m * (rf * (g % m) + f * rg) := by
  have hleft :
      (f + m * rf) * (g % m) =
        f * (g % m) + (m * rf) * (g % m) :=
    DensePoly.mul_add_left_poly f (m * rf) (g % m)
  have hright :
      f * (g % m) = f * g + f * (m * rg) := by
    rw [hg]
    exact DensePoly.mul_add_right_poly f g (m * rg)
  calc
    (f % m * (g % m)) - (f * g)
        = ((f + m * rf) * (g % m)) - (f * g) := by rw [hf]
    _ = (f * (g % m) + (m * rf) * (g % m)) - (f * g) := by rw [hleft]
    _ = ((f * g + f * (m * rg)) + (m * rf) * (g % m)) - (f * g) := by
      rw [hright]
    _ = (f * g + (f * (m * rg) + (m * rf) * (g % m))) - (f * g) := by
      exact congrArg (fun x => x - f * g)
        (DensePoly.add_assoc_poly (f * g) (f * (m * rg)) ((m * rf) * (g % m)))
    _ = f * (m * rg) + (m * rf) * (g % m) := by
      rw [sub_self_right_add]
    _ = m * (f * rg) + (m * rf) * (g % m) := by
      apply congrArg (fun x => x + (m * rf) * (g % m))
      calc
        f * (m * rg) = (f * m) * rg := by
          exact (DensePoly.mul_assoc_poly f m rg).symm
        _ = (m * f) * rg := by
          exact congrArg (fun x => x * rg) (DensePoly.mul_comm_poly f m)
        _ = m * (f * rg) := by
          exact DensePoly.mul_assoc_poly m f rg
    _ = m * (f * rg) + m * (rf * (g % m)) := by
      exact congrArg (fun x => m * (f * rg) + x)
        (DensePoly.mul_assoc_poly m rf (g % m))
    _ = m * (f * rg + rf * (g % m)) := by
      exact (DensePoly.mul_add_right_poly m (f * rg) (rf * (g % m))).symm
    _ = m * (rf * (g % m) + f * rg) := by
      exact congrArg (fun x => m * x)
        (DensePoly.add_comm_poly (f * rg) (rf * (g % m)))

private theorem zmod_one_ne_zero [PrimeModulus p] :
    (1 : ZMod64 p) ≠ (0 : ZMod64 p) := by
  intro h
  have h2 : 2 ≤ p := (PrimeModulus.prime (p := p)).two_le
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

/-- Division by `1` is the identity on `ZMod64 p`. Callers normalizing a
value against a unit denominator (for example a leading coefficient already
equal to `1`) can discharge the division outright. -/
theorem zmod_div_one [PrimeModulus p] (a : ZMod64 p) :
    a / (1 : ZMod64 p) = a := by
  have h1ne : (1 : ZMod64 p) ≠ 0 := zmod_one_ne_zero
  have hinv : ZMod64.inv (1 : ZMod64 p) * 1 = 1 :=
    ZMod64.inv_mul_eq_one_of_prime (PrimeModulus.prime (p := p)) h1ne
  have hmul1 : ZMod64.inv (1 : ZMod64 p) * 1 = ZMod64.inv 1 :=
    Lean.Grind.Semiring.mul_one (ZMod64.inv (1 : ZMod64 p))
  have hinv1 : ZMod64.inv (1 : ZMod64 p) = 1 := by
    rw [hmul1] at hinv
    exact hinv
  change ZMod64.mul a (ZMod64.inv 1) = a
  rw [hinv1]
  exact Lean.Grind.Semiring.mul_one a

private theorem cancel_lead_at_pos_size_core [PrimeModulus p]
    (m : DensePoly (ZMod64 p)) (hsize : 0 < m.size) (a : ZMod64 p) :
    a - (a / m.leadingCoeff) * m.leadingCoeff = (Zero.zero : ZMod64 p) := by
  have hidx : m.coeffs.size - 1 < m.coeffs.size := by
    simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hsize
  have hlead_eq : m.leadingCoeff = m.coeff (m.size - 1) := by
    unfold DensePoly.leadingCoeff DensePoly.coeff
    change m.coeffs.back?.getD (0 : ZMod64 p) =
      m.coeffs.getD (m.coeffs.size - 1) (Zero.zero : ZMod64 p)
    rw [Array.back?_eq_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hidx]
    rfl
  have hlead_ne : m.leadingCoeff ≠ (Zero.zero : ZMod64 p) := by
    rw [hlead_eq]
    exact DensePoly.coeff_last_ne_zero_of_pos_size m hsize
  exact zmod_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne

/-- The `F_p[x]` division law obligations used by quotient constructions.

These are the concrete finite-field instances of the generic `DensePoly.DivModLaws` proof
surface used by downstream quotient-ring code; the executable division operations
themselves are inherited from `DensePoly`. -/
instance instDivModLawsZMod64Fp (p : Nat) [Bounds p] [PrimeModulus p] :
    DensePoly.DivModLaws (ZMod64 p) where
  divMod_spec := by
    intro f g
    exact divMod_spec_core f g
  divMod_remainder_degree_lt_of_pos_degree := by
    intro f g hdegree
    exact divMod_remainder_degree_lt_core f g hdegree
  divModMonic_eq_divMod_of_monic := by
    intro f g hmonic
    by_cases hdeg : f.degree?.getD 0 < g.degree?.getD 0
    · show DensePoly.divModMonic f g hmonic = DensePoly.divMod f g
      unfold DensePoly.divModMonic
      rw [DensePoly.divModArray_eq_zero_self_of_degree_lt f g id hdeg]
      unfold DensePoly.divMod
      simp [hdeg]
    · apply DensePoly.divModMonic_eq_divMod_of_monic_core f g hmonic hdeg
      intro a
      have hlead : g.leadingCoeff = (1 : ZMod64 p) := hmonic
      show a / g.leadingCoeff = a
      rw [hlead]
      exact zmod_div_one a
  mod_self_eq_zero := by
    intro f
    exact mod_eq_zero_of_dvd_core f f (DensePoly.dvd_refl_poly f)
  mod_eq_zero_of_dvd := by
    intro f g hdiv
    exact mod_eq_zero_of_dvd_core f g hdiv
  mod_mod_of_not_pos_degree := by
    intro f g hdegree
    by_cases hsize0 : g.size = 0
    · have h2 : (DensePoly.divMod (f % g) g).2 = (f % g) :=
        DensePoly.divMod_remainder_eq_self_of_size_zero_core (f % g) g hsize0
      exact h2
    · have hpos_size : 0 < g.size := Nat.pos_of_ne_zero hsize0
      have hsize1 : g.size = 1 := by
        have hdeg_eq : g.degree?.getD 0 = g.size - 1 := by
          simp [DensePoly.degree?, hsize0]
        have hnot_pos : ¬ 0 < g.size - 1 := by
          intro h
          apply hdegree
          rw [hdeg_eq]
          exact h
        omega
      have hcancel := cancel_lead_at_pos_size_core g hpos_size
      have h1 : (DensePoly.divMod f g).2 = 0 :=
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core f g hsize1 hcancel
      have h2 : (DensePoly.divMod (f % g) g).2 = 0 :=
        DensePoly.divMod_remainder_eq_zero_of_degree_zero_core (f % g) g hsize1 hcancel
      change (DensePoly.divMod (f % g) g).2 = (DensePoly.divMod f g).2
      rw [h1, h2]
  mod_eq_mod_of_congr := by
    intro f g m hcongr
    exact mod_eq_mod_of_congr_core f g m hcongr
  mod_add_mod := by
    intro f g m
    apply Eq.symm
    apply mod_eq_mod_of_congr_core
    rcases congr_mod_core f m with ⟨rf, hf⟩
    rcases congr_mod_core g m with ⟨rg, hg⟩
    exact ⟨rf + rg, by
      calc
        (f % m + g % m) - (f + g)
            = (f % m - f) + (g % m - g) := add_sub_add_right (f % m) (g % m) f g
        _ = m * rf + m * rg := by rw [hf, hg]
        _ = m * (rf + rg) := by exact (DensePoly.mul_add_right_poly m rf rg).symm⟩
  mod_mul_mod := by
    intro f g m
    apply Eq.symm
    apply mod_eq_mod_of_congr_core
    rcases congr_mod_core f m with ⟨rf, hf⟩
    rcases congr_mod_core g m with ⟨rg, hg⟩
    exact ⟨rf * (g % m) + f * rg, by
      have hf' : f % m = f + m * rf := by
        apply DensePoly.ext_coeff
        intro n
        have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hf
        change (f % m - f).coeff n = (m * rf).coeff n at hcoeff
        rw [DensePoly.coeff_sub_ring] at hcoeff
        rw [DensePoly.coeff_add_semiring]
        grind
      have hg' : g % m = g + m * rg := by
        apply DensePoly.ext_coeff
        intro n
        have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hg
        change (g % m - g).coeff n = (m * rg).coeff n at hcoeff
        rw [DensePoly.coeff_sub_ring] at hcoeff
        rw [DensePoly.coeff_add_semiring]
        grind
      exact mul_left_remainder_delta f g m rf rg hf' hg'⟩

private theorem divMod_remainder_eq_zero_of_not_pos_degree_core
    [PrimeModulus p] (f m : DensePoly (ZMod64 p))
    (hmzero : m.isZero = false)
    (hdegree : ¬ 0 < m.degree?.getD 0) :
    (DensePoly.divMod f m).2 = 0 := by
  have hpos_size : 0 < m.size := by
    have hsize : m.coeffs.size ≠ 0 := by
      simpa [DensePoly.isZero, Array.isEmpty_iff_size_eq_zero] using hmzero
    simpa [DensePoly.size, Nat.pos_iff_ne_zero] using hsize
  have hsize0 : m.size ≠ 0 := Nat.pos_iff_ne_zero.mp hpos_size
  have hsize1 : m.size = 1 := by
    have hdeg_eq : m.degree?.getD 0 = m.size - 1 := by
      simp [DensePoly.degree?, hsize0]
    have hnot_pos : ¬ 0 < m.size - 1 := by
      intro h
      apply hdegree
      rw [hdeg_eq]
      exact h
    omega
  have hcancel := cancel_lead_at_pos_size_core m hpos_size
  exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core f m hsize1 hcancel

/-- The `F_p[x]` gcd law obligations used by finite-field inverse construction. -/
instance instGcdLawsZMod64Fp [PrimeModulus p] : DensePoly.GcdLaws (ZMod64 p) where
  gcd_dvd_left := by
    intro f g
    exact @DensePoly.gcd_dvd_left_of_divModLaws (ZMod64 p) _ _ _
      (instDivModLawsZMod64Fp p)
      (fun a b => divMod_remainder_eq_zero_of_not_pos_degree_core a b) f g
  gcd_dvd_right := by
    intro f g
    exact @DensePoly.gcd_dvd_right_of_divModLaws (ZMod64 p) _ _ _
      (instDivModLawsZMod64Fp p)
      (fun a b => divMod_remainder_eq_zero_of_not_pos_degree_core a b) f g
  dvd_gcd := by
    intro d f g hdf hdg
    exact @DensePoly.dvd_gcd_of_divModLaws (ZMod64 p) _ _ _ (instDivModLawsZMod64Fp p)
      d f g hdf hdg
  xgcd_bezout := by
    intro f g
    exact @DensePoly.xgcd_bezout_of_divModLaws (ZMod64 p) _ _ _ (instDivModLawsZMod64Fp p) f g

end ZMod64

/-- Executable dense polynomials over the prime-field candidate `ZMod64 p`. -/
abbrev FpPoly (p : Nat) [ZMod64.Bounds p] := DensePoly (ZMod64 p)

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Polynomial irreducibility over `F_p` phrased as the absence of nontrivial
factorizations inside the executable dense-polynomial model. -/
def Irreducible (f : FpPoly p) : Prop :=
  f ≠ 0 ∧
    ∀ a b : FpPoly p, a * b = f → a.degree? = some 0 ∨ b.degree? = some 0

/-- Build an `FpPoly` from raw coefficients, trimming trailing zero residues. -/
def ofCoeffs (coeffs : Array (ZMod64 p)) : FpPoly p :=
  DensePoly.ofCoeffs coeffs

/-- Constant polynomial in `F_p[x]`. -/
def C (c : ZMod64 p) : FpPoly p :=
  DensePoly.C c

/-- The polynomial indeterminate `X`. -/
def X : FpPoly p :=
  DensePoly.monomial 1 (1 : ZMod64 p)

/-- Reduction modulo a monic polynomial over `F_p[x]`. -/
def modByMonic (f g : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  DensePoly.modByMonic g f hmonic

private theorem zmod_eq_of_toNat_eq {a b : ZMod64 p} (h : a.toNat = b.toNat) : a = b := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using h

private theorem zmod_add_zero (a : ZMod64 p) : a + 0 = a := by
  grind

private theorem zmod_zero_add (a : ZMod64 p) : 0 + a = a := by
  grind

private theorem zmod_add_zero_zero :
    (Zero.zero : ZMod64 p) + (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) :=
  zmod_add_zero Zero.zero

private theorem zmod_mul_zero (a : ZMod64 p) : a * 0 = 0 := by
  grind

private theorem zmod_zero_mul (a : ZMod64 p) : 0 * a = 0 :=
  Lean.Grind.Semiring.zero_mul a

private theorem zmod_one_mul (a : ZMod64 p) : 1 * a = a := by
  grind

private theorem zmod_mul_one (a : ZMod64 p) : a * 1 = a := by
  grind

private theorem coeff_one (n : Nat) :
    (1 : FpPoly p).coeff n = if n = 0 then (1 : ZMod64 p) else 0 := by
  change (DensePoly.C (1 : ZMod64 p)).coeff n = if n = 0 then (1 : ZMod64 p) else 0
  exact DensePoly.coeff_C (1 : ZMod64 p) n

/-- A constant polynomial evaluates to its constant at every point. This is
the base case from which the evaluation map's homomorphism laws are built. -/
theorem eval_C (c x : ZMod64 p) :
    DensePoly.eval (FpPoly.C c) x = c := by
  unfold FpPoly.C
  exact DensePoly.eval_C c x (zmod_zero_mul x) (zmod_zero_add c)

/-- The variable `X` evaluates to the evaluation point. The companion base
case to `eval_C` for reasoning about the evaluation map. -/
theorem eval_X [ZMod64.PrimeModulus p] (x : ZMod64 p) :
    DensePoly.eval (FpPoly.X : FpPoly p) x = x := by
  unfold FpPoly.X DensePoly.eval DensePoly.toArray DensePoly.monomial
  have h1 : (1 : ZMod64 p) ≠ (Zero.zero : ZMod64 p) := by
    intro h
    have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
    have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
      congrArg ZMod64.toNat h
    rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
        show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
        Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
    exact absurd htoNat (by omega)
  rw [dif_neg h1]
  simp
  change (((0 : ZMod64 p) * x + 1) * x + 0 = x)
  rw [zmod_zero_mul, zmod_zero_add, zmod_one_mul, zmod_add_zero]

private theorem foldl_eval_replicate_zero (x : ZMod64 p) :
    ∀ n acc,
      (List.replicate n (0 : ZMod64 p)).foldl
          (fun acc coeff => acc * x + coeff) acc =
        acc * x ^ n := by
  intro n
  induction n with
  | zero =>
      intro acc
      rw [Lean.Grind.Semiring.pow_zero]
      exact (zmod_mul_one acc).symm
  | succ n ih =>
      intro acc
      simp only [List.replicate_succ, List.foldl_cons]
      rw [zmod_add_zero]
      rw [ih (acc * x)]
      rw [Lean.Grind.Semiring.pow_succ x n]
      rw [Lean.Grind.Semiring.mul_assoc acc x (x ^ n)]
      rw [Lean.Grind.CommSemiring.mul_comm x (x ^ n)]

/-- Evaluating a monomial gives the coefficient times the corresponding power. -/
theorem eval_monomial (n : Nat) (c x : ZMod64 p) :
    DensePoly.eval (DensePoly.monomial n c : FpPoly p) x = c * x ^ n := by
  by_cases hc : c = 0
  · subst c
    unfold DensePoly.monomial
    rw [dif_pos (show (0 : ZMod64 p) = Zero.zero from rfl)]
    exact (zmod_zero_mul (x ^ n)).symm
  · unfold DensePoly.eval DensePoly.toArray DensePoly.monomial
    have hc0 : ¬ c = (Zero.zero : ZMod64 p) := hc
    rw [dif_neg hc0]
    simp only [Array.toList_push, Array.toList_replicate, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.foldl_cons]
    change (List.replicate n (0 : ZMod64 p)).reverse.foldl
        (fun acc coeff => acc * x + coeff) ((0 : ZMod64 p) * x + c) =
      c * x ^ n
    rw [zmod_zero_mul, zmod_zero_add, List.reverse_replicate]
    exact foldl_eval_replicate_zero x n c

/-- Coefficients of the constant polynomial wrapper are constant at degree zero and zero elsewhere. -/
@[simp] theorem coeff_C (c : ZMod64 p) (n : Nat) :
    (FpPoly.C c).coeff n = if n = 0 then c else 0 := by
  unfold FpPoly.C
  exact DensePoly.coeff_C c n

/-- The degree-zero coefficient of the indeterminate wrapper is zero. -/
@[simp] theorem coeff_X_zero :
    ((FpPoly.X : FpPoly p)).coeff 0 = 0 := by
  unfold FpPoly.X
  exact DensePoly.coeff_monomial 1 (1 : ZMod64 p) 0

/-- The degree-one coefficient of the indeterminate wrapper is one. -/
@[simp] theorem coeff_X_one :
    ((FpPoly.X : FpPoly p)).coeff 1 = 1 := by
  unfold FpPoly.X
  exact DensePoly.coeff_monomial 1 (1 : ZMod64 p) 1

/-- Coefficients of the indeterminate wrapper are one at degree one and zero elsewhere. -/
@[simp] theorem coeff_X (n : Nat) :
    ((FpPoly.X : FpPoly p)).coeff n = if n = 1 then 1 else 0 := by
  unfold FpPoly.X
  exact DensePoly.coeff_monomial 1 (1 : ZMod64 p) n

/-- `evalCoeffPowerSumFrom coeffs base x` is the power sum `Σ coeffᵢ * x^(base+i)`
of a coefficient list starting at exponent `base`. -/
private def evalCoeffPowerSumFrom :
    List (ZMod64 p) → Nat → ZMod64 p → ZMod64 p
  | [], _, _ => 0
  | coeff :: coeffs, base, x =>
      coeff * x ^ base + evalCoeffPowerSumFrom coeffs (base + 1) x

/-- `evalScalarCoeffList coeffs x` is the Horner-form evaluation
`c₀ + x * (c₁ + x * (⋯))` of a coefficient list. -/
private def evalScalarCoeffList :
    List (ZMod64 p) → ZMod64 p → ZMod64 p
  | [], _ => 0
  | coeff :: coeffs, x => coeff + x * evalScalarCoeffList coeffs x

/-- Multiplying an `evalCoeffPowerSumFrom` value by `x` shifts its base exponent
up by one. -/
private theorem mul_evalCoeffPowerSumFrom_eq_succ
    (x : ZMod64 p) :
    ∀ coeffs base,
      x * evalCoeffPowerSumFrom coeffs base x =
        evalCoeffPowerSumFrom coeffs (base + 1) x
  | [], _ => by
      simp [evalCoeffPowerSumFrom, Lean.Grind.Semiring.mul_zero]
  | coeff :: coeffs, base => by
      simp only [evalCoeffPowerSumFrom]
      rw [Lean.Grind.Semiring.left_distrib]
      rw [mul_evalCoeffPowerSumFrom_eq_succ x coeffs (base + 1)]
      rw [← Lean.Grind.Semiring.mul_assoc x coeff (x ^ base)]
      rw [Lean.Grind.CommSemiring.mul_comm x coeff]
      rw [Lean.Grind.Semiring.mul_assoc coeff x (x ^ base)]
      rw [Lean.Grind.CommSemiring.mul_comm x (x ^ base)]
      rw [← Lean.Grind.Semiring.mul_assoc coeff (x ^ base) x]
      rw [Lean.Grind.Semiring.pow_succ x base]
      rw [Lean.Grind.Semiring.mul_assoc coeff (x ^ base) x]

/-- The Horner evaluation of a coefficient list equals its power sum based at
exponent zero. -/
private theorem evalScalarCoeffList_eq_powerSumFrom_zero
    (x : ZMod64 p) :
    ∀ coeffs,
      evalScalarCoeffList coeffs x = evalCoeffPowerSumFrom coeffs 0 x
  | [] => by
      simp [evalScalarCoeffList, evalCoeffPowerSumFrom]
  | coeff :: coeffs => by
      simp only [evalScalarCoeffList, evalCoeffPowerSumFrom]
      rw [evalScalarCoeffList_eq_powerSumFrom_zero x coeffs]
      rw [mul_evalCoeffPowerSumFrom_eq_succ x coeffs 0]
      grind

/-- The Horner-step left fold over the reversed coefficient list equals
`evalScalarCoeffList`. -/
private theorem foldl_eval_reverse_eq_evalScalarCoeffList
    (x : ZMod64 p) :
    ∀ coeffs,
      coeffs.reverse.foldl (fun acc coeff => acc * x + coeff) (Zero.zero : ZMod64 p) =
        evalScalarCoeffList coeffs x
  | [] => by
      rfl
  | coeff :: coeffs => by
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_eval_reverse_eq_evalScalarCoeffList x coeffs]
      rw [Lean.Grind.CommSemiring.mul_comm]
      rw [Lean.Grind.Semiring.add_comm]
      rfl

/-- `DensePoly.eval f x` equals the power sum of `f`'s coefficient list based at
exponent zero. -/
private theorem eval_eq_coeff_power_sum (f : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval f x = evalCoeffPowerSumFrom f.toArray.toList 0 x := by
  unfold DensePoly.eval
  rw [foldl_eval_reverse_eq_evalScalarCoeffList x f.toArray.toList]
  exact evalScalarCoeffList_eq_powerSumFrom_zero x f.toArray.toList

/-- Indexing `f`'s coefficient list with default zero recovers `f.coeff n`. -/
private theorem eval_coeff_list_getD_eq_coeff (f : FpPoly p) (n : Nat) :
    f.toArray.toList.getD n (0 : ZMod64 p) = f.coeff n := by
  unfold DensePoly.toArray DensePoly.coeff
  rw [Array.getD_eq_getD_getElem?]
  change f.coeffs.toList[n]?.getD (0 : ZMod64 p) =
    f.coeffs[n]?.getD (Zero.zero : ZMod64 p)
  rw [Array.getElem?_toList]
  rfl

/-- Indexing the `range`-mapped coefficient list returns `coeff n` inside the
range and zero outside it. -/
private theorem list_getD_map_range_zmod (bound n : Nat) (coeff : Nat → ZMod64 p) :
    ((List.range bound).map coeff).getD n (0 : ZMod64 p) =
      if n < bound then coeff n else 0 := by
  by_cases hn : n < bound
  · simp [hn, List.getD]
  · simp [hn, List.getD]

/-- Two coefficient lists of equal length that agree at every default-zero index
are equal. -/
private theorem list_eq_of_length_eq_of_getD_eq
    {xs ys : List (ZMod64 p)}
    (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i 0 = ys.getD i 0) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hhead : x = y := by
            have h := hget 0 (by simp)
            simpa using h
          have hlen_tail : xs.length = ys.length := Nat.succ.inj hlen
          have htail : xs = ys := by
            apply ih hlen_tail
            intro i hi
            have h := hget (i + 1) (by simp [hi])
            simpa using h
          rw [hhead, htail]

/-- `f`'s coefficient array, viewed as a list, equals `range f.size` mapped
through `f.coeff`. -/
private theorem toArray_toList_eq_coeff_range (f : FpPoly p) :
    f.toArray.toList = (List.range f.size).map (fun i => f.coeff i) := by
  apply list_eq_of_length_eq_of_getD_eq
  · simp [DensePoly.toArray, DensePoly.size]
  · intro i hi
    have hi_size : i < f.size := by
      simpa [DensePoly.toArray, DensePoly.size] using hi
    rw [eval_coeff_list_getD_eq_coeff]
    rw [list_getD_map_range_zmod]
    simp [hi_size]

/-- `evalCoeffPowerSumUpTo coeff n base x` is the power sum
`Σ coeff(base+i) * x^(base+i)` over the first `n` exponents from `base`, taking the
coefficients from a function rather than a list. -/
private def evalCoeffPowerSumUpTo
    (coeff : Nat → ZMod64 p) :
    Nat → Nat → ZMod64 p → ZMod64 p
  | 0, _, _ => 0
  | n + 1, base, x =>
      coeff base * x ^ base + evalCoeffPowerSumUpTo coeff n (base + 1) x

/-- The list-based power sum over a `range`-mapped coefficient function equals the
function-based `evalCoeffPowerSumUpTo`. -/
private theorem evalCoeffPowerSumFrom_range_eq_upTo
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumFrom ((List.range n).map (fun i => coeff (base + i))) base x =
        evalCoeffPowerSumUpTo coeff n base x
  | 0, base => by
      simp [evalCoeffPowerSumFrom, evalCoeffPowerSumUpTo]
  | n + 1, base => by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      simp only [evalCoeffPowerSumFrom, evalCoeffPowerSumUpTo]
      congr 1
      simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using evalCoeffPowerSumFrom_range_eq_upTo coeff x n (base + 1)

/-- `DensePoly.eval f x` equals the function-based power sum over `f`'s
coefficients up to `f.size`. -/
private theorem eval_eq_coeff_power_sum_upTo_size (f : FpPoly p)
    (x : ZMod64 p) :
    DensePoly.eval f x = evalCoeffPowerSumUpTo (fun i => f.coeff i) f.size 0 x := by
  rw [eval_eq_coeff_power_sum]
  rw [toArray_toList_eq_coeff_range]
  simpa using evalCoeffPowerSumFrom_range_eq_upTo (fun i => f.coeff i) x f.size 0

/-- Extending the power sum by one more term leaves it unchanged when the next
coefficient is zero. -/
private theorem evalCoeffPowerSumUpTo_succ_of_next_zero
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ n base,
      coeff (base + n) = 0 →
        evalCoeffPowerSumUpTo coeff n base x =
          evalCoeffPowerSumUpTo coeff (n + 1) base x
  | 0, base, hzero => by
      have hz : coeff base = 0 := by simpa using hzero
      rw [evalCoeffPowerSumUpTo, evalCoeffPowerSumUpTo, hz]
      rw [evalCoeffPowerSumUpTo]
      rw [Lean.Grind.Semiring.add_zero]
      exact (Lean.Grind.Semiring.zero_mul (x ^ base)).symm
  | n + 1, base, hzero => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_succ_of_next_zero coeff x n (base + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzero)]
      simp only [evalCoeffPowerSumUpTo]

/-- Extending the upper bound of the power sum by any amount leaves it unchanged
when all coefficients past the bound vanish, for an arbitrary starting base. -/
private theorem evalCoeffPowerSumUpTo_le_extend_base
    (coeff : Nat → ZMod64 p) (x : ZMod64 p)
    (hzero : ∀ i, base + bound ≤ i → coeff i = 0) :
    ∀ extra,
      evalCoeffPowerSumUpTo coeff bound base x =
        evalCoeffPowerSumUpTo coeff (bound + extra) base x
  | 0 => by
      simp
  | extra + 1 => by
      rw [evalCoeffPowerSumUpTo_le_extend_base coeff x hzero extra]
      rw [Nat.add_succ]
      exact evalCoeffPowerSumUpTo_succ_of_next_zero
        coeff x (bound + extra) base (hzero (base + (bound + extra)) (by omega))

/-- Extending the upper bound of the power sum based at zero leaves it unchanged
when all coefficients past the bound vanish. -/
private theorem evalCoeffPowerSumUpTo_le_extend
    (coeff : Nat → ZMod64 p) (x : ZMod64 p)
    (hzero : ∀ i, bound ≤ i → coeff i = 0) :
    ∀ extra,
      evalCoeffPowerSumUpTo coeff bound 0 x =
        evalCoeffPowerSumUpTo coeff (bound + extra) 0 x := by
  intro extra
  exact evalCoeffPowerSumUpTo_le_extend_base
    coeff x (base := 0) (bound := bound) (by simpa using hzero) extra

/-- `DensePoly.eval f x` equals the power sum of `f`'s coefficients up to any
bound at least `f.size`. -/
private theorem eval_eq_coeff_power_sum_upTo_bound (f : FpPoly p)
    (x : ZMod64 p) {bound : Nat} (hbound : f.size ≤ bound) :
    DensePoly.eval f x = evalCoeffPowerSumUpTo (fun i => f.coeff i) bound 0 x := by
  rw [eval_eq_coeff_power_sum_upTo_size]
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hbound
  exact evalCoeffPowerSumUpTo_le_extend
    (fun i => f.coeff i) x
    (fun i hi => DensePoly.coeff_eq_zero_of_size_le f hi) extra

/-- The power sum of a coefficientwise sum is the sum of the two power sums. -/
private theorem evalCoeffPowerSumUpTo_add
    (f h : FpPoly p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumUpTo (fun i => f.coeff i + h.coeff i) n base x =
        evalCoeffPowerSumUpTo (fun i => f.coeff i) n base x +
          evalCoeffPowerSumUpTo (fun i => h.coeff i) n base x
  | 0, _ => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_add f h x n (base + 1)]
      grind

/-- The power sum of a coefficientwise difference is the difference of the two
power sums. -/
private theorem evalCoeffPowerSumUpTo_sub
    (f h : FpPoly p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumUpTo (fun i => f.coeff i - h.coeff i) n base x =
        evalCoeffPowerSumUpTo (fun i => f.coeff i) n base x -
          evalCoeffPowerSumUpTo (fun i => h.coeff i) n base x
  | 0, _ => by
      simp [evalCoeffPowerSumUpTo]
      grind
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_sub f h x n (base + 1)]
      grind

/-- Scaling every coefficient by a constant scales the power sum by that
constant. -/
private theorem evalCoeffPowerSumUpTo_const_mul
    (c : ZMod64 p) (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ n base,
      evalCoeffPowerSumUpTo (fun i => c * coeff i) n base x =
        c * evalCoeffPowerSumUpTo coeff n base x
  | 0, _ => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_const_mul c coeff x n (base + 1)]
      grind

/-- Multiplying a shifted-coefficient power sum by `x^shift` rebases it to start
at exponent `shift + base`. -/
private theorem evalCoeffPowerSumUpTo_rebase_mul
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) (shift : Nat) :
    ∀ n base,
      x ^ shift *
          evalCoeffPowerSumUpTo (fun i => coeff (shift + i)) n base x =
        evalCoeffPowerSumUpTo coeff n (shift + base) x
  | 0, base => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [Lean.Grind.Semiring.left_distrib]
      rw [evalCoeffPowerSumUpTo_rebase_mul coeff x shift n (base + 1)]
      have hpow :
          x ^ shift * x ^ base = x ^ (shift + base) := by
        exact (Lean.Grind.Semiring.pow_add x shift base).symm
      have hterm :
          x ^ shift * (coeff (shift + base) * x ^ base) =
            coeff (shift + base) * x ^ (shift + base) := by
        rw [← Lean.Grind.Semiring.mul_assoc]
        rw [Lean.Grind.CommSemiring.mul_comm (x ^ shift) (coeff (shift + base))]
        rw [Lean.Grind.Semiring.mul_assoc]
        rw [hpow]
      rw [hterm]
      grind

/-- Prepending `shift` zero coefficients multiplies the power sum by `x^shift`. -/
private theorem evalCoeffPowerSumUpTo_zero_prefix_shift
    (coeff : Nat → ZMod64 p) (x : ZMod64 p) :
    ∀ shift n,
      evalCoeffPowerSumUpTo
          (fun k => if k < shift then 0 else coeff (k - shift))
          (shift + n) 0 x =
        x ^ shift * evalCoeffPowerSumUpTo coeff n 0 x
  | 0, n => by
      simp only [Nat.zero_add]
      rw [Lean.Grind.Semiring.pow_zero]
      rw [Lean.Grind.Semiring.one_mul]
      rfl
  | shift + 1, n => by
      rw [Nat.succ_add]
      simp only [evalCoeffPowerSumUpTo]
      have hhead :
          (if 0 < shift + 1 then 0 else coeff (0 - (shift + 1))) *
              x ^ 0 = (0 : ZMod64 p) := by
        grind
      rw [hhead, zmod_zero_add]
      have htail :
          evalCoeffPowerSumUpTo
              (fun k => if k < shift + 1 then 0 else coeff (k - (shift + 1)))
              (shift + n) 1 x =
            x *
              evalCoeffPowerSumUpTo
                (fun k => if k < shift then 0 else coeff (k - shift))
                (shift + n) 0 x := by
        rw [← evalCoeffPowerSumUpTo_rebase_mul
          (fun k => if k < shift + 1 then 0 else coeff (k - (shift + 1)))
          x 1 (shift + n) 0]
        have hx_one : x ^ 1 = x := by
          rw [Lean.Grind.Semiring.pow_succ x 0]
          rw [Lean.Grind.Semiring.pow_zero]
          grind
        rw [hx_one]
        have hfun :
            (fun i => if 1 + i < shift + 1 then 0 else coeff (1 + i - (shift + 1))) =
              (fun k => if k < shift then 0 else coeff (k - shift)) := by
          funext k
          by_cases hk : k < shift
          · have hk' : 1 + k < shift + 1 := by omega
            simp [hk, hk']
          · have hk' : ¬ 1 + k < shift + 1 := by omega
            have hsub : 1 + k - (shift + 1) = k - shift := by omega
            simp [hk, hk', hsub]
        rw [hfun]
      rw [htail]
      rw [evalCoeffPowerSumUpTo_zero_prefix_shift coeff x shift n]
      rw [Lean.Grind.Semiring.pow_succ x shift]
      grind

/-- A polynomial's size is at most `bound` when all coefficients from `bound`
onward vanish. -/
private theorem size_le_of_coeff_eq_zero_from (f : FpPoly p) (bound : Nat)
    (hzero : ∀ i, bound ≤ i → f.coeff i = 0) :
    f.size ≤ bound := by
  by_cases hle : f.size ≤ bound
  · exact hle
  · have hgt : bound < f.size := Nat.lt_of_not_ge hle
    have hpos : 0 < f.size := by omega
    have htop_zero : f.coeff (f.size - 1) = 0 := hzero (f.size - 1) (by omega)
    exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f hpos htop_zero)

/-- Evaluating the monomial row `c · Xⁱ · f` at `x` multiplies the value of
`f` by `c * xⁱ`. This isolates one term of a product so that `eval_mul` and
related multiplicative laws can be assembled row by row. -/
theorem eval_shift_scale_row (i : Nat) (c : ZMod64 p) (f : FpPoly p)
    (x : ZMod64 p) :
    DensePoly.eval (DensePoly.shift i (DensePoly.scale c f)) x =
      (c * x ^ i) * DensePoly.eval f x := by
  rw [eval_eq_coeff_power_sum_upTo_bound
    (DensePoly.shift i (DensePoly.scale c f)) x (bound := i + f.size)]
  · rw [eval_eq_coeff_power_sum_upTo_size f x]
    have hcoeff :
        (fun k => (DensePoly.shift i (DensePoly.scale c f)).coeff k) =
          (fun k => if k < i then 0 else c * f.coeff (k - i)) := by
      funext k
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_shift_scale i c f k hzero]
      rfl
    rw [hcoeff]
    rw [evalCoeffPowerSumUpTo_zero_prefix_shift
      (fun k => c * f.coeff k) x i f.size]
    rw [evalCoeffPowerSumUpTo_const_mul c (fun k => f.coeff k) x f.size 0]
    grind
  · apply size_le_of_coeff_eq_zero_from
    intro k hk
    have hzero : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_shift_scale i c f k hzero]
    by_cases hki : k < i
    · simp [hki]
      rfl
    · have hf : f.size ≤ k - i := by omega
      simp [hki, DensePoly.coeff_eq_zero_of_size_le f hf]
      exact hzero

/-- Evaluation is additive: the value of a sum is the sum of the values.
One half of the statement that evaluation at a point is a ring homomorphism. -/
theorem eval_add (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (f + h) x = DensePoly.eval f x + DensePoly.eval h x := by
  let bound := max f.size h.size
  rw [eval_eq_coeff_power_sum_upTo_bound (f + h) x (bound := bound)]
  · rw [eval_eq_coeff_power_sum_upTo_bound f x (bound := bound)
      (Nat.le_max_left f.size h.size)]
    rw [eval_eq_coeff_power_sum_upTo_bound h x (bound := bound)
      (Nat.le_max_right f.size h.size)]
    have hcoeff :
        (fun i => (f + h).coeff i) =
          (fun i => f.coeff i + h.coeff i) := by
      funext i
      rw [DensePoly.coeff_add_semiring]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_add f h x bound 0
  · change (f + h).size ≤ max f.size h.size
    apply size_le_of_coeff_eq_zero_from
    intro i hi
    rw [DensePoly.coeff_add_semiring]
    rw [DensePoly.coeff_eq_zero_of_size_le f
        (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
      DensePoly.coeff_eq_zero_of_size_le h
        (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
    exact zmod_add_zero_zero

/-- Evaluation respects subtraction. Lets callers push an evaluation through
a difference of polynomials, for example when checking that two polynomials
agree at a point. -/
theorem eval_sub (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (f - h) x = DensePoly.eval f x - DensePoly.eval h x := by
  let bound := max f.size h.size
  rw [eval_eq_coeff_power_sum_upTo_bound (f - h) x (bound := bound)]
  · rw [eval_eq_coeff_power_sum_upTo_bound f x (bound := bound)
      (Nat.le_max_left f.size h.size)]
    rw [eval_eq_coeff_power_sum_upTo_bound h x (bound := bound)
      (Nat.le_max_right f.size h.size)]
    have hcoeff :
        (fun i => (f - h).coeff i) =
          (fun i => f.coeff i - h.coeff i) := by
      funext i
      rw [DensePoly.coeff_sub_ring]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_sub f h x bound 0
  · change (f - h).size ≤ max f.size h.size
    apply size_le_of_coeff_eq_zero_from
    intro i hi
    rw [DensePoly.coeff_sub_ring]
    rw [DensePoly.coeff_eq_zero_of_size_le f
        (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
      DensePoly.coeff_eq_zero_of_size_le h
        (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
    grind

@[simp] theorem add_zero (f : FpPoly p) :
    f + 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_zero]
  grind

@[simp] theorem zero_add (f : FpPoly p) :
    0 + f = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_zero]
  grind

/-- Polynomial addition is commutative. Part of the commutative-ring
structure on `FpPoly p` that downstream algebra relies on. -/
theorem add_comm (f g : FpPoly p) :
    f + g = g + f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  grind

/-- Polynomial addition is associative, letting callers regroup sums freely.
Part of the commutative-ring structure on `FpPoly p`. -/
theorem add_assoc (f g h : FpPoly p) :
    f + g + h = f + (g + h) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  grind

@[simp] theorem neg_zero :
    -(0 : FpPoly p) = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_neg_ring]
  rw [DensePoly.coeff_zero]
  grind

@[simp] theorem add_left_neg (f : FpPoly p) :
    -f + f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_neg_ring]
  rw [DensePoly.coeff_zero]
  grind

@[simp] theorem add_right_neg (f : FpPoly p) :
    f + -f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_neg_ring]
  rw [DensePoly.coeff_zero]
  grind

@[simp] theorem sub_zero (f : FpPoly p) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_zero]
  grind

@[simp] theorem zero_sub (f : FpPoly p) :
    0 - f = -f := by
  rfl

@[simp] theorem sub_self (f : FpPoly p) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_zero]
  grind

/-- Subtraction unfolds to adding the negation. Rewrites subtraction in terms
of the additive operations, so results proved for `+` transfer to `-`. -/
theorem sub_eq_add_neg (f g : FpPoly p) :
    f - g = f + -g := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_neg_ring]
  grind

example (f : FpPoly p) :
    (f + 0) - f = 0 := by
  simp

@[simp] theorem zero_mul (f : FpPoly p) :
    0 * f = 0 := by
  rfl

@[simp] theorem mul_zero (f : FpPoly p) :
    f * 0 = 0 := by
  exact (DensePoly.mul_comm_poly f 0).trans (DensePoly.zero_mul f)

private theorem coeff_mul_one_fold (f : FpPoly p) (n k : Nat) :
    ((List.range n).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (1 : FpPoly p)))
        (0 : FpPoly p)).coeff k =
      if k < n then f.coeff k else 0 := by
  induction n with
  | zero =>
      exact DensePoly.coeff_zero k
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [DensePoly.coeff_add_semiring, ih]
      rw [DensePoly.coeff_shift_scale]
      · rw [coeff_one]
        by_cases hk : k < n
        · have hks : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
          simp [hk, hks]
          exact zmod_add_zero (f.coeff k)
        · by_cases hkn : k = n
          · subst k
            simp
          · have hks : ¬ k < n + 1 := by omega
            have hsub : k - n ≠ 0 := by omega
            simp [hk, hks, hsub]
      · exact zmod_mul_zero (f.coeff n)

@[simp] theorem one_mul (f : FpPoly p) :
    1 * f = f := by
  exact (DensePoly.mul_comm_poly (1 : FpPoly p) f).trans (DensePoly.mul_one_right_poly f)

@[simp] theorem mul_one (f : FpPoly p) :
    f * 1 = f := by
  exact DensePoly.mul_one_right_poly f

/-! ### Schoolbook coefficient helpers (proof-facing Hensel scaffolding)

`mulCoeffTerm` and `mulCoeffSum` are kept public only because
`HexHensel/Linear.lean` reasons about the per-coefficient diagonal
contribution of `FpPoly` multiplication when establishing the linear
Hensel lift congruence. They are not part of the ordinary `FpPoly`
multiplication API — callers who only need a characterisation of
`(f * g).coeff n` should use the public `coeff_mul` lemma below, which
gives the same value without committing to the schoolbook fold shape.

The private cluster of lemmas that follows these two definitions
(`coeff_mul_fold`, `foldl_mulCoeffStep_*`, `mulCoeffTerm_*`,
`fold_mulCoeff_*`, `mulCoeffSum_eq_bound`, etc.) is proof plumbing for
the multiplication characterisations and is intentionally not exported. -/

/-- The `i`th schoolbook contribution to coefficient `n` of `f * g`.
Proof-facing Hensel scaffolding: ordinary `FpPoly` multiplication callers
should use `coeff_mul`, not this definition. -/
def mulCoeffTerm (f g : FpPoly p) (n i : Nat) : ZMod64 p :=
  if n < i then 0 else f.coeff i * g.coeff (n - i)

/-- The executable schoolbook coefficient sum matching `FpPoly`
multiplication. Proof-facing Hensel scaffolding: ordinary `FpPoly`
multiplication callers should use `coeff_mul`, not this definition. -/
def mulCoeffSum (f g : FpPoly p) (n : Nat) : ZMod64 p :=
  (List.range f.size).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0

private theorem coeff_mul_fold (xs : List Nat) (acc f g : FpPoly p) (n : Nat) :
    (xs.foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) g))
        acc).coeff n =
      xs.foldl (fun coeff i => coeff + mulCoeffTerm f g n i) (acc.coeff n) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      have hzero : f.coeff i * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_add_semiring,
        DensePoly.coeff_shift_scale i (f.coeff i) g n hzero]
      rfl

private theorem foldl_mulCoeffStep_select_fp
    (f g : FpPoly p) (n i m : Nat) (acc : ZMod64 p) :
    (List.range m).foldl (DensePoly.mulCoeffStep f g n i) acc =
      acc + (if n < i then 0
        else if n - i < m then f.coeff i * g.coeff (n - i) else 0) := by
  induction m generalizing acc with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases hlt : n < i
      · have hne : i + m ≠ n := by omega
        simp [hlt, hne]
      · by_cases hm : n - i < m
        · have hne : i + m ≠ n := by omega
          simp [hlt, hm, hne]
          grind
        · by_cases heq : i + m = n
          · have hsub : n - i = m := by omega
            simp [hlt, heq, hsub]
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

private theorem foldl_mulCoeffStep_outer_fp
    (f g : FpPoly p) (n : Nat) (xs : List Nat) (acc : ZMod64 p) :
    xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc =
      xs.foldl
        (fun acc i =>
          acc + (if n < i then 0
            else if n - i < g.size then f.coeff i * g.coeff (n - i) else 0))
        acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_mulCoeffStep_select_fp]
      exact ih _

private theorem foldl_mulCoeffStep_outer_eq_mulCoeffTerm
    (f g : FpPoly p) (n : Nat) (xs : List Nat) (acc : ZMod64 p) :
    xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc =
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) acc := by
  rw [foldl_mulCoeffStep_outer_fp]
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      unfold mulCoeffTerm
      by_cases hlt : n < i
      · simp [hlt]
      · by_cases hbound : n - i < g.size
        · simp [hlt, hbound]
        · have hcoeff : g.coeff (n - i) = 0 :=
            DensePoly.coeff_eq_zero_of_size_le g (Nat.le_of_not_gt hbound)
          simp [hlt, hbound, hcoeff]

/-- The `n`-th coefficient of a product is the convolution sum `mulCoeffSum`.
This is the coefficient-level specification of the executable multiplication,
the entry point for proving every higher multiplicative law. -/
theorem coeff_mul (f g : FpPoly p) (n : Nat) :
    (f * g).coeff n = mulCoeffSum f g n := by
  rw [DensePoly.coeff_mul]
  unfold DensePoly.mulCoeffSum mulCoeffSum
  exact foldl_mulCoeffStep_outer_eq_mulCoeffTerm f g n (List.range f.size) 0

private theorem mulCoeffTerm_eq_zero_of_size_le
    (f g : FpPoly p) (n i : Nat) (hi : f.size ≤ i) :
    mulCoeffTerm f g n i = 0 := by
  unfold mulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f hi
    simp [hn, hcoeff]

private theorem fold_mulCoeff_extend (f g : FpPoly p) (n d : Nat) :
    (List.range (f.size + d)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range f.size).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : mulCoeffTerm f g n (f.size + d) = 0 :=
        mulCoeffTerm_eq_zero_of_size_le f g n (f.size + d) (by omega)
      simp [hterm]

private theorem mulCoeffSum_eq_bound
    (f g : FpPoly p) (n m : Nat) (hm : f.size ≤ m) :
    mulCoeffSum f g n =
      (List.range m).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  unfold mulCoeffSum
  have hm' : f.size + (m - f.size) = m := by omega
  rw [← hm', fold_mulCoeff_extend]

private theorem coeff_mul_of_size_le
    (f g : FpPoly p) (n m : Nat) (hm : f.size ≤ m) :
    (f * g).coeff n =
      (List.range m).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  rw [coeff_mul, mulCoeffSum_eq_bound f g n m hm]

private theorem mulCoeffTerm_eq_zero_of_degree_lt
    (f g : FpPoly p) (n i : Nat) (hi : n < i) :
    mulCoeffTerm f g n i = 0 := by
  simp [mulCoeffTerm, hi]

private theorem fold_mulCoeff_truncate_degree
    (f g : FpPoly p) (n d : Nat) :
    (List.range (n + 1 + d)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : mulCoeffTerm f g n (n + 1 + d) = 0 :=
        mulCoeffTerm_eq_zero_of_degree_lt f g n (n + 1 + d) (by omega)
      simp [hterm]

private theorem mulCoeffSum_eq_degree_bound
    (f g : FpPoly p) (n : Nat) :
    mulCoeffSum f g n =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  unfold mulCoeffSum
  by_cases hsize : f.size ≤ n + 1
  · exact mulCoeffSum_eq_bound f g n (n + 1) hsize
  · have hle : n + 1 ≤ f.size := Nat.le_of_not_ge hsize
    have hsize' : n + 1 + (f.size - (n + 1)) = f.size := by omega
    rw [← hsize']
    exact fold_mulCoeff_truncate_degree f g n (f.size - (n + 1))

private theorem fold_add_right
    (xs : List (ZMod64 p)) (a b : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) (a + b) =
      xs.foldl (fun acc x => acc + x) a + b := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + x = (a + x) + b := by grind
      rw [hacc]
      exact ih (a + x)

private theorem fold_add_reverse
    (xs : List (ZMod64 p)) (a : ZMod64 p) :
    xs.reverse.foldl (fun acc x => acc + x) a =
      xs.foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      rw [fold_add_right xs a x]

private theorem range_succ_reverse_eq_map_sub (n : Nat) :
    (List.range (n + 1)).reverse = (List.range (n + 1)).map (fun i => n - i) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.length_reverse] at hleft hright
    rw [List.getElem_reverse]
    simp [List.getElem_map, List.getElem_range]

private theorem mulCoeffTerm_comm_reindex
    (f g : FpPoly p) (n i : Nat) (hi : i < n + 1) :
    mulCoeffTerm f g n (n - i) = mulCoeffTerm g f n i := by
  have hile : i ≤ n := by omega
  have hleft : ¬ n < n - i := by omega
  have hright : ¬ n < i := by omega
  simp [mulCoeffTerm, hleft, hright, Nat.sub_sub_self hile]
  grind

private theorem fold_mulCoeff_comm_reindex_list
    (f g : FpPoly p) (n : Nat) (xs : List Nat)
    (hxs : ∀ i, i ∈ xs → i < n + 1) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + mulCoeffTerm f g n (n - i)) acc =
      xs.foldl (fun acc i => acc + mulCoeffTerm g f n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : i < n + 1 := hxs i (by simp)
      rw [mulCoeffTerm_comm_reindex f g n i hi]
      exact ih (by
        intro j hj
        exact hxs j (by simp [hj])) (acc + mulCoeffTerm g f n i)

private theorem fold_mulCoeff_comm
    (f g : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm g f n i) 0 := by
  have hrev :
      (List.range (n + 1)).reverse.foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
        (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
    simpa [List.foldl_map, ← List.map_reverse] using
      fold_add_reverse (p := p)
        ((List.range (n + 1)).map (fun i => mulCoeffTerm f g n i)) 0
  rw [← hrev]
  rw [range_succ_reverse_eq_map_sub]
  rw [List.foldl_map]
  exact fold_mulCoeff_comm_reindex_list f g n (List.range (n + 1)) (by
    intro i hi
    exact List.mem_range.mp hi) 0

/-- Polynomial multiplication is commutative. Part of the commutative-ring
structure on `FpPoly p`, and lets callers swap factors to match a lemma's
expected orientation. -/
theorem mul_comm (f g : FpPoly p) :
    f * g = g * f := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_degree_bound f g n]
  rw [mulCoeffSum_eq_degree_bound g f n]
  exact fold_mulCoeff_comm f g n

private theorem mulCoeffTerm_left_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm f (g + h) n i =
      mulCoeffTerm f g n i + mulCoeffTerm f h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
  · rw [DensePoly.coeff_add_semiring]
    simp [hi]
    grind

private theorem mulCoeffTerm_right_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm (f + g) h n i =
      mulCoeffTerm f h n i + mulCoeffTerm g h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
  · rw [DensePoly.coeff_add_semiring]
    simp [hi]
    grind

private theorem fold_distrib_acc
    (xs : List Nat) (a b : ZMod64 p)
    (term term₁ term₂ : Nat → ZMod64 p)
    (hterm : ∀ i, term i = term₁ i + term₂ i) :
    xs.foldl (fun acc i => acc + term i) (a + b) =
      xs.foldl (fun acc i => acc + term₁ i) a +
        xs.foldl (fun acc i => acc + term₂ i) b := by
  induction xs generalizing a b with
  | nil =>
      rfl
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [hterm i]
    have hacc :
        a + b + (term₁ i + term₂ i) =
          (a + term₁ i) + (b + term₂ i) := by
      grind
    rw [hacc]
    exact ih (a + term₁ i) (b + term₂ i)

private theorem fold_mul_right
    (xs : List Nat) (term : Nat → ZMod64 p) (c : ZMod64 p) :
    xs.foldl (fun acc i => acc + term i) 0 * c =
      xs.foldl (fun acc i => acc + term i * c) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hfold :
          xs.foldl (fun acc j => acc + term j) (0 + term i) =
            xs.foldl (fun acc j => acc + term j) 0 + term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map term) 0 (term i)
      have hfold' :
          xs.foldl (fun acc j => acc + term j * c) (0 + term i * c) =
            xs.foldl (fun acc j => acc + term j * c) 0 + term i * c := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map (fun j => term j * c)) 0 (term i * c)
      calc
        xs.foldl (fun acc j => acc + term j) (0 + term i) * c
            = (xs.foldl (fun acc j => acc + term j) 0 + term i) * c := by
                rw [hfold]
        _ = xs.foldl (fun acc j => acc + term j) 0 * c + term i * c := by
                grind
        _ = xs.foldl (fun acc j => acc + term j * c) 0 + term i * c := by
                rw [ih]
        _ = xs.foldl (fun acc j => acc + term j * c) (0 + term i * c) := by
                rw [hfold']

private theorem fold_mul_left
    (xs : List Nat) (term : Nat → ZMod64 p) (c : ZMod64 p) :
    c * xs.foldl (fun acc i => acc + term i) 0 =
      xs.foldl (fun acc i => acc + c * term i) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hfold :
          xs.foldl (fun acc j => acc + term j) (0 + term i) =
            xs.foldl (fun acc j => acc + term j) 0 + term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map term) 0 (term i)
      have hfold' :
          xs.foldl (fun acc j => acc + c * term j) (0 + c * term i) =
            xs.foldl (fun acc j => acc + c * term j) 0 + c * term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map (fun j => c * term j)) 0 (c * term i)
      calc
        c * xs.foldl (fun acc j => acc + term j) (0 + term i)
            = c * (xs.foldl (fun acc j => acc + term j) 0 + term i) := by
                rw [hfold]
        _ = c * xs.foldl (fun acc j => acc + term j) 0 + c * term i := by
                grind
        _ = xs.foldl (fun acc j => acc + c * term j) 0 + c * term i := by
                rw [ih]
        _ = xs.foldl (fun acc j => acc + c * term j) (0 + c * term i) := by
                rw [hfold']

private theorem mulCoeffTerm_mul_left_expand
    (f g h : FpPoly p) (n i : Nat) (hi : ¬ n < i) :
    mulCoeffTerm (f * g) h n i =
      (List.range (i + 1)).foldl
        (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0 := by
  unfold mulCoeffTerm
  simp [hi]
  rw [coeff_mul, mulCoeffSum_eq_degree_bound f g i]
  exact fold_mul_right (p := p) (List.range (i + 1))
    (fun j => mulCoeffTerm f g i j) (h.coeff (n - i))

private theorem mulCoeffTerm_mul_right_expand
    (f g h : FpPoly p) (n i : Nat) (hi : ¬ n < i) :
    mulCoeffTerm f (g * h) n i =
      (List.range (n - i + 1)).foldl
        (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0 := by
  unfold mulCoeffTerm
  simp [hi]
  rw [coeff_mul, mulCoeffSum_eq_degree_bound g h (n - i)]
  exact fold_mul_left (p := p) (List.range (n - i + 1))
    (fun j => mulCoeffTerm g h (n - i) j) (f.coeff i)

private def leftAssocTriples (n : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (i + 1)).map fun j => ((j, i - j), n - i)

private def rightAssocTriples (n : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (n - i + 1)).map fun j => ((i, j), n - i - j)

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hxy' : x = y := hinj x (by simp) y (by simp [hy]) hxy.symm
        exact hxs.1 (by simpa [hxy'] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

private theorem nodup_flatMap_of_disjoint
    {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hrow : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisj :
      ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
        ∀ z, z ∈ f x → z ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hrow x (by simp), ?_, ?_⟩
      · exact ih hxs.2
          (by intro y hy; exact hrow y (by simp [hy]))
          (by
            intro y hy z hz hyz t hty htz
            exact hdisj y (by simp [hy]) z (by simp [hz]) hyz t hty htz)
      · intro a ha b hb hab
        rcases List.mem_flatMap.mp hb with ⟨y, hy, hby⟩
        exact hdisj x (by simp) y (by simp [hy]) (by
          intro hxy
          exact hxs.1 (hxy ▸ hy)) a ha (hab ▸ hby)

private theorem leftAssocTriples_nodup (n : Nat) :
    (leftAssocTriples n).Nodup := by
  unfold leftAssocTriples
  apply nodup_flatMap_of_disjoint List.nodup_range
  · intro i hi
    apply nodup_map_of_injective List.nodup_range
    intro a ha b hb hab
    injection hab with hfst _
    exact Prod.ext_iff.mp hfst |>.1
  · intro i hi k hk hik z hzi hzk
    rcases List.mem_map.mp hzi with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, hEq⟩
    injection hEq with hpair hlast
    injection hpair with hfirst hsecond
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hk' : k < n + 1 := List.mem_range.mp hk
    omega

private theorem rightAssocTriples_nodup (n : Nat) :
    (rightAssocTriples n).Nodup := by
  unfold rightAssocTriples
  apply nodup_flatMap_of_disjoint List.nodup_range
  · intro i hi
    apply nodup_map_of_injective List.nodup_range
    intro a ha b hb hab
    injection hab with hfst _
    exact Prod.ext_iff.mp hfst |>.2
  · intro i hi k hk hik z hzi hzk
    rcases List.mem_map.mp hzi with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, hEq⟩
    injection hEq with hpair _
    exact hik (Prod.ext_iff.mp hpair |>.1).symm

private theorem leftAssocTriples_mem_iff (n : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ leftAssocTriples n ↔ abc.1.1 + abc.1.2 + abc.2 = n := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [leftAssocTriples]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨a + b, ?_, a, ?_, ?_⟩ <;> omega

private theorem rightAssocTriples_mem_iff (n : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ rightAssocTriples n ↔ abc.1.1 + abc.1.2 + abc.2 = n := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [rightAssocTriples]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨a, ?_, b, ?_, ?_⟩ <;> omega

private theorem leftAssocTriples_perm_rightAssocTriples (n : Nat) :
    List.Perm (leftAssocTriples n) (rightAssocTriples n) := by
  rw [List.perm_iff_count]
  intro abc
  rw [(leftAssocTriples_nodup n).count, (rightAssocTriples_nodup n).count]
  simp [leftAssocTriples_mem_iff, rightAssocTriples_mem_iff]

private theorem fold_add_perm {xs ys : List (ZMod64 p)}
    (h : List.Perm xs ys) (acc : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) acc =
      ys.foldl (fun acc x => acc + x) acc := by
  induction h generalizing acc with
  | nil =>
      rfl
  | cons x _ ih =>
      simp only [List.foldl_cons]
      exact ih (acc + x)
  | swap x y _ =>
      simp only [List.foldl_cons]
      have hxy : acc + x + y = acc + y + x := by grind
      rw [hxy]
  | trans _ _ ih₁ ih₂ =>
      exact Eq.trans (ih₁ acc) (ih₂ acc)

private theorem fold_add_acc
    (xs : List (ZMod64 p)) (acc : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) acc =
      acc + xs.foldl (fun acc x => acc + x) 0 := by
  have h := fold_add_right (p := p) xs 0 acc
  simp only [zmod_zero_add] at h
  rw [h]
  grind

private theorem fold_flatMap_map_add
    {α β : Type} (xs : List α) (row : α → List β)
    (term : α → β → ZMod64 p) (acc : ZMod64 p) :
    (xs.flatMap fun x => (row x).map (term x)).foldl
        (fun acc x => acc + x) acc =
      xs.foldl
        (fun acc x =>
          acc + (row x).foldl (fun acc y => acc + term x y) 0) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.foldl_append]
      rw [fold_add_acc (p := p) ((row x).map (term x)) acc]
      rw [ih]
      simp [List.foldl_map]

private theorem fold_triangular_assoc_reindex
    (n : Nat) (term : Nat → Nat → Nat → ZMod64 p) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + term j (i - j) (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + term i j (n - i - j)) 0) 0 := by
  have hperm :
      List.Perm
        ((leftAssocTriples n).map (fun abc => term abc.1.1 abc.1.2 abc.2))
        ((rightAssocTriples n).map (fun abc => term abc.1.1 abc.1.2 abc.2)) :=
    (leftAssocTriples_perm_rightAssocTriples n).map _
  have hfold := fold_add_perm (p := p) hperm 0
  rw [← fold_flatMap_map_add (p := p) (List.range (n + 1))
    (fun i => List.range (i + 1))
    (fun i j => term j (i - j) (n - i)) 0]
  rw [← fold_flatMap_map_add (p := p) (List.range (n + 1))
    (fun i => List.range (n - i + 1))
    (fun i j => term i j (n - i - j)) 0]
  simpa [leftAssocTriples, rightAssocTriples, List.map_flatMap] using hfold

private theorem fold_add_congr
    (xs : List Nat) {term₁ term₂ : Nat → ZMod64 p}
    (hterm : ∀ i, i ∈ xs → term₁ i = term₂ i) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + term₁ i) acc =
      xs.foldl (fun acc i => acc + term₂ i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm i (by simp)]
      exact ih (by
        intro j hj
        exact hterm j (by simp [hj])) (acc + term₂ i)

private theorem fold_add_zero_terms_acc
    (xs : List Nat) (term : Nat → ZMod64 p)
    (hterm : ∀ i, i ∈ xs → term i = 0) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + term i) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm i (by simp)]
      rw [zmod_add_zero]
      exact ih (by
        intro j hj
        exact hterm j (by simp [hj])) acc

private theorem fold_add_zero_terms
    (xs : List Nat) (term : Nat → ZMod64 p)
    (hterm : ∀ i, i ∈ xs → term i = 0) :
    xs.foldl (fun acc i => acc + term i) 0 = 0 := by
  exact fold_add_zero_terms_acc xs term hterm 0

private theorem fold_add_single_range
    (n t : Nat) (a : ZMod64 p) (ht : t < n + 1) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + if i = t then a else 0) 0 = a := by
  induction n with
  | zero =>
      have ht0 : t = 0 := by omega
      simp [ht0]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hlast : t = n + 1
      · subst t
        have hzero :
            (List.range (n + 1)).foldl
                (fun acc i => acc + if i = n + 1 then a else 0) 0 = 0 := by
          apply fold_add_zero_terms
          intro i hi
          have hi' : i < n + 1 := List.mem_range.mp hi
          have hne : i ≠ n + 1 := by omega
          rw [if_neg hne]
        rw [hzero]
        rw [if_pos rfl]
        exact zmod_zero_add a
      · have ht' : t < n + 1 := by omega
        rw [ih ht']
        have hne : n + 1 ≠ t := by omega
        rw [if_neg hne]
        exact zmod_add_zero a

private theorem fold_add_single_range_zero
    (n t : Nat) (a : ZMod64 p) (ht : ¬ t < n + 1) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + if i = t then a else 0) 0 = 0 := by
  apply fold_add_zero_terms
  intro i hi
  have hi' : i < n + 1 := List.mem_range.mp hi
  have hit : i ≠ t := by omega
  simp [hit]

/-- Multiplying `f` by the scaled monomial `c · Xⁱ` shifts each coefficient up
by `i` and scales it by `c`. Gives a closed form for the coefficients produced
when a polynomial is multiplied by a single monomial term. -/
theorem coeff_mul_shift_scale_one
    (f : FpPoly p) (c : ZMod64 p) (i n : Nat) :
    (f * DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))).coeff n =
      if i ≤ n then f.coeff (n - i) * c else 0 := by
  rw [coeff_mul, mulCoeffSum_eq_degree_bound f
    (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n]
  by_cases hin : i ≤ n
  · calc
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + mulCoeffTerm f
              (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n j) 0
          =
        (List.range (n + 1)).foldl
          (fun acc j => acc + if j = n - i then f.coeff (n - i) * c else 0) 0 := by
            apply fold_add_congr
            intro j hj
            have hjn : j < n + 1 := List.mem_range.mp hj
            unfold mulCoeffTerm
            by_cases hnj : n < j
            · have hne : j ≠ n - i := by omega
              rw [if_pos hnj, if_neg hne]
            · simp [hnj, -DensePoly.coeff_shift]
              have hzero : c * (0 : ZMod64 p) = 0 := by grind
              rw [DensePoly.coeff_shift_scale i c (1 : FpPoly p) (n - j) hzero]
              by_cases hlt : n - j < i
              · have hne : j ≠ n - i := by
                  intro hji
                  subst j
                  have hnot : ¬ n - (n - i) < i := by
                    rw [Nat.sub_sub_self hin]
                    omega
                  exact hnot hlt
                rw [if_neg hne]
                simp [hlt]
                exact zmod_mul_zero (f.coeff j)
              · by_cases hji : j = n - i
                · subst j
                  rw [if_pos rfl]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - (n - i) - i = 0 := by
                    rw [Nat.sub_sub_self hin]
                    simp
                  simp [hsub]
                · rw [if_neg hji]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - j - i ≠ 0 := by omega
                  simp [hsub]
      _ = f.coeff (n - i) * c := by
            exact fold_add_single_range n (n - i) (f.coeff (n - i) * c) (by omega)
      _ = if i ≤ n then f.coeff (n - i) * c else 0 := by
            rw [if_pos hin]
  · have hzero :
        (List.range (n + 1)).foldl
            (fun acc j =>
              acc + mulCoeffTerm f
                (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n j) 0 = 0 := by
      apply fold_add_zero_terms
      intro j hj
      have hjn : j < n + 1 := List.mem_range.mp hj
      unfold mulCoeffTerm
      by_cases hnj : n < j
      · simp [hnj]
      · simp [hnj, -DensePoly.coeff_shift]
        have hzero : c * (0 : ZMod64 p) = 0 := by grind
        rw [DensePoly.coeff_shift_scale i c (1 : FpPoly p) (n - j) hzero]
        have hlt : n - j < i := by omega
        simp [hlt]
        exact zmod_mul_zero (f.coeff j)
    rw [hzero]
    rw [if_neg hin]

private theorem fold_mulCoeff_assoc_left_expand
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm (f * g) h n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 := by
  apply fold_add_congr
  intro i hi
  exact mulCoeffTerm_mul_left_expand f g h n i (by
    have hi' : i < n + 1 := List.mem_range.mp hi
    omega)

private theorem fold_mulCoeff_assoc_right_expand
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm f (g * h) n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
  apply fold_add_congr
  intro i hi
  exact mulCoeffTerm_mul_right_expand f g h n i (by
    have hi' : i < n + 1 := List.mem_range.mp hi
    omega)

private theorem fold_mulCoeff_assoc_left_normalize
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + (f.coeff j * g.coeff (i - j)) * h.coeff (n - i)) 0) 0 := by
  apply fold_add_congr
  intro i _hi
  apply fold_add_congr
  intro j hj
  have hji : ¬ i < j := by
    have hj' : j < i + 1 := List.mem_range.mp hj
    omega
  simp [mulCoeffTerm, hji]

private theorem fold_mulCoeff_assoc_right_normalize
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + (f.coeff i * g.coeff j) * h.coeff (n - i - j)) 0) 0 := by
  apply fold_add_congr
  intro i _hi
  apply fold_add_congr
  intro j hj
  have hji : ¬ n - i < j := by
    have hj' : j < n - i + 1 := List.mem_range.mp hj
    omega
  simp [mulCoeffTerm, hji]
  grind

private theorem mulCoeff_assoc_reindex
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
  calc
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0
        = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (i + 1)).foldl
                  (fun acc j => acc + (f.coeff j * g.coeff (i - j)) * h.coeff (n - i)) 0) 0 := by
            exact fold_mulCoeff_assoc_left_normalize f g h n
    _ = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (n - i + 1)).foldl
                  (fun acc j => acc + (f.coeff i * g.coeff j) * h.coeff (n - i - j)) 0) 0 := by
            exact fold_triangular_assoc_reindex n
              (fun a b c => (f.coeff a * g.coeff b) * h.coeff c)
    _ = (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
            exact (fold_mulCoeff_assoc_right_normalize f g h n).symm

private theorem fold_left_distrib (xs : List Nat) (f g h : FpPoly p) (n : Nat) :
    xs.foldl (fun acc i => acc + mulCoeffTerm f (g + h) n i) 0 =
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 +
        xs.foldl (fun acc i => acc + mulCoeffTerm f h n i) 0 := by
  simpa [show (0 : ZMod64 p) + 0 = 0 by grind] using
    fold_distrib_acc (p := p) xs 0 0
      (fun i => mulCoeffTerm f (g + h) n i)
      (fun i => mulCoeffTerm f g n i)
      (fun i => mulCoeffTerm f h n i)
      (mulCoeffTerm_left_distrib f g h n)

private theorem fold_right_distrib (xs : List Nat) (f g h : FpPoly p) (n : Nat) :
    xs.foldl (fun acc i => acc + mulCoeffTerm (f + g) h n i) 0 =
      xs.foldl (fun acc i => acc + mulCoeffTerm f h n i) 0 +
        xs.foldl (fun acc i => acc + mulCoeffTerm g h n i) 0 := by
  simpa [show (0 : ZMod64 p) + 0 = 0 by grind] using
    fold_distrib_acc (p := p) xs 0 0
      (fun i => mulCoeffTerm (f + g) h n i)
      (fun i => mulCoeffTerm f h n i)
      (fun i => mulCoeffTerm g h n i)
      (mulCoeffTerm_right_distrib f g h n)

/-- Multiplication distributes over addition on the left. Part of the
commutative-ring structure on `FpPoly p`. -/
theorem left_distrib (f g h : FpPoly p) :
    f * (g + h) = f * g + f * h := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring]
  simp [coeff_mul, mulCoeffSum, fold_left_distrib]

/-- Multiplication distributes over addition on the right. Part of the
commutative-ring structure on `FpPoly p`. -/
theorem right_distrib (f g h : FpPoly p) :
    (f + g) * h = f * h + g * h := by
  apply DensePoly.ext_coeff
  intro n
  let m := max (max (f + g).size f.size) g.size
  rw [DensePoly.coeff_add_semiring]
  rw [coeff_mul_of_size_le (f + g) h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le f h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le g h n m (by dsimp [m]; omega)]
  exact fold_right_distrib (List.range m) f g h n

/-- Polynomial multiplication is associative, letting callers regroup products
freely. Part of the commutative-ring structure on `FpPoly p`. -/
theorem mul_assoc (f g h : FpPoly p) :
    (f * g) * h = f * (g * h) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_degree_bound (f * g) h n]
  rw [mulCoeffSum_eq_degree_bound f (g * h) n]
  calc
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm (f * g) h n i) 0
        = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (i + 1)).foldl
                  (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 := by
            exact fold_mulCoeff_assoc_left_expand f g h n
    _ = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (n - i + 1)).foldl
                  (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
            exact mulCoeff_assoc_reindex f g h n
    _ = (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm f (g * h) n i) 0 := by
            exact (fold_mulCoeff_assoc_right_expand f g h n).symm

/-- Scalar scaling distributes over polynomial addition. Lets callers move a
scalar across a sum, for example when normalizing a linear combination. -/
theorem scale_add (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f + g) =
      DensePoly.scale c f + DensePoly.scale c g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

/-- Scaling a product equals scaling its left factor. With `mul_comm` this lets
a scalar be absorbed into either factor of a product. -/
theorem scale_mul_left (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f * g) =
      DensePoly.scale c f * g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_degree_bound (DensePoly.scale c f) g n]
  rw [mulCoeffSum_eq_degree_bound f g n]
  rw [fold_mul_left]
  apply fold_add_congr
  intro i _hi
  unfold mulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · simp [hn]
    rw [DensePoly.coeff_scale _ _ _ hzero]
    grind

/-- Scaling the unit polynomial by `c` yields the constant polynomial `C c`.
Identifies the scalar action on `1` with the constant embedding. -/
theorem scale_one_poly (c : ZMod64 p) :
    DensePoly.scale c (1 : FpPoly p) = DensePoly.C c := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  change c * (DensePoly.C (1 : ZMod64 p)).coeff n = (DensePoly.C c).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n => exact hzero

/-- Multiplying by a constant polynomial coincides with scalar scaling. Lets
callers convert between the `C c * f` and `scale c f` representations so the
scale-specific lemmas apply to constant multiplications. -/
theorem C_mul_eq_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.C c * f = DensePoly.scale c f := by
  have hscale := scale_mul_left c (1 : FpPoly p) f
  rw [one_mul, scale_one_poly] at hscale
  exact hscale.symm

/-- Evaluating `C c * f` at `x` multiplies the value of `f` by the scalar `c`.
The constant-multiplication special case of `eval_mul`. -/
theorem eval_C_mul (c : ZMod64 p) (f : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (DensePoly.C c * f) x = c * DensePoly.eval f x := by
  rw [C_mul_eq_scale]
  rw [eval_eq_coeff_power_sum_upTo_bound (DensePoly.scale c f) x (bound := f.size)]
  · rw [eval_eq_coeff_power_sum_upTo_size f x]
    have hcoeff :
        (fun i => (DensePoly.scale c f).coeff i) =
          (fun i => c * f.coeff i) := by
      funext i
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_scale _ _ _ hzero]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_const_mul c (fun i => f.coeff i) x f.size 0
  · apply size_le_of_coeff_eq_zero_from
    intro i hi
    have hzero : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_scale _ _ _ hzero]
    rw [DensePoly.coeff_eq_zero_of_size_le f hi]
    exact hzero

private theorem eval_one (x : ZMod64 p) :
    DensePoly.eval (1 : FpPoly p) x = 1 := by
  change DensePoly.eval (FpPoly.C (1 : ZMod64 p)) x = 1
  exact eval_C 1 x

private theorem fold_eval_shift_scale_rows
    (xs : List Nat) (acc : FpPoly p) (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval
        (xs.foldl
          (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) h))
          acc) x =
      xs.foldl
        (fun acc i => acc + (f.coeff i * x ^ i) * DensePoly.eval h x)
        (DensePoly.eval acc x) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + DensePoly.shift i (DensePoly.scale (f.coeff i) h))]
      rw [eval_add]
      rw [eval_shift_scale_row]

private theorem fold_shift_scale_one_eq_self (f : FpPoly p) :
    (List.range f.size).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (1 : FpPoly p)))
        (0 : FpPoly p) = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul_one_fold]
  by_cases hn : n < f.size
  · simp [hn]
  · have hzero : f.coeff n = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hn)
    simp [hn, hzero]

private theorem mul_eq_fold_shift_scale_rows (f h : FpPoly p) :
    f * h =
      (List.range f.size).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) h))
        (0 : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul]
  rw [coeff_mul_fold]
  unfold mulCoeffSum
  rw [DensePoly.coeff_zero]
  rfl

/-- Evaluation is multiplicative: the value of a product is the product of the
values. Together with `eval_add` this is the ring-homomorphism property of
evaluation, used wherever a root or factorization is checked pointwise. -/
theorem eval_mul (f h : FpPoly p) (x : ZMod64 p) :
    DensePoly.eval (f * h) x = DensePoly.eval f x * DensePoly.eval h x := by
  rw [mul_eq_fold_shift_scale_rows]
  rw [fold_eval_shift_scale_rows]
  rw [DensePoly.eval_zero]
  have hf :
      DensePoly.eval f x =
        (List.range f.size).foldl
          (fun acc i => acc + (f.coeff i * x ^ i) * DensePoly.eval (1 : FpPoly p) x)
          (DensePoly.eval (0 : FpPoly p) x) := by
    rw [← fold_eval_shift_scale_rows
      (List.range f.size) (0 : FpPoly p) f (1 : FpPoly p) x]
    rw [fold_shift_scale_one_eq_self]
  rw [hf]
  rw [DensePoly.eval_zero, eval_one]
  have hone :
      (List.range f.size).foldl
          (fun acc i => acc + (f.coeff i * x ^ i) * (1 : ZMod64 p)) 0 =
        (List.range f.size).foldl
          (fun acc i => acc + f.coeff i * x ^ i) 0 := by
    apply fold_add_congr
    intro i _hi
    grind
  calc
    (List.range f.size).foldl
        (fun acc i => acc + (f.coeff i * x ^ i) * DensePoly.eval h x) 0
        =
      (List.range f.size).foldl
          (fun acc i => acc + f.coeff i * x ^ i) 0 * DensePoly.eval h x := by
        exact (fold_mul_right (p := p) (List.range f.size)
          (fun i => f.coeff i * x ^ i) (DensePoly.eval h x)).symm
    _ =
      (List.range f.size).foldl
          (fun acc i => acc + (f.coeff i * x ^ i) * (1 : ZMod64 p)) 0 *
        DensePoly.eval h x := by
        rw [hone]

/-- Two successive scalings compose into a single scaling by the product of the
scalars. Lets callers collapse a chain of scalar adjustments into one. -/
theorem scale_scale (c d : ZMod64 p) (f : FpPoly p) :
    DensePoly.scale c (DensePoly.scale d f) = DensePoly.scale (c * d) f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
  have hzero_d : d * (0 : ZMod64 p) = 0 := by grind
  have hzero_cd : (c * d) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_c]
  rw [DensePoly.coeff_scale _ _ _ hzero_d]
  rw [DensePoly.coeff_scale _ _ _ hzero_cd]
  grind

/-- Scaling by `1` leaves the polynomial unchanged. The identity law of the
scalar action, needed to recognize a trivial scaling as a no-op. -/
theorem scale_one_left (f : FpPoly p) :
    DensePoly.scale (1 : ZMod64 p) f = f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : (1 : ZMod64 p) * 0 = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

private theorem zmod64_one_ne_zero [ZMod64.PrimeModulus p] :
    (1 : ZMod64 p) ≠ (0 : ZMod64 p) := by
  intro h
  have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

/-- Scaling never increases the coefficient-array size. The unconditional size
bound, valid even when `c = 0` collapses leading coefficients to zero. -/
theorem scale_size_le (c : ZMod64 p) (f : FpPoly p) :
    (DensePoly.scale c f).size ≤ f.size := by
  by_cases hle : (DensePoly.scale c f).size ≤ f.size
  · exact hle
  · exfalso
    let i := (DensePoly.scale c f).size - 1
    have hscale_pos : 0 < (DensePoly.scale c f).size := by omega
    have htop_ne :
        (DensePoly.scale c f).coeff i ≠ (0 : ZMod64 p) :=
      DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.scale c f) hscale_pos
    have hfi : f.size ≤ i := by
      dsimp [i]
      omega
    have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_scale _ _ _ hzero_c] at htop_ne
    rw [DensePoly.coeff_eq_zero_of_size_le f hfi] at htop_ne
    exact htop_ne hzero_c

/-- Scaling by a nonzero scalar preserves the coefficient-array size: over a
field the top coefficient cannot be cancelled. Callers use this to know that
a unit scaling preserves degree. -/
theorem scale_size_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).size = f.size := by
  apply Nat.le_antisymm
  · exact scale_size_le c f
  · by_cases hfsize : f.size = 0
    · omega
    · let i := f.size - 1
      have hf_pos : 0 < f.size := Nat.pos_of_ne_zero hfsize
      have hf_top : f.coeff i ≠ (0 : ZMod64 p) :=
        DensePoly.coeff_last_ne_zero_of_pos_size f hf_pos
      have hprod_ne : c * f.coeff i ≠ (0 : ZMod64 p) := by
        intro hprod
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero
            (ZMod64.PrimeModulus.prime (p := p)) hprod with hcz | hfz
        · exact hc hcz
        · exact hf_top hfz
      have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
      have hcoeff :
          (DensePoly.scale c f).coeff i ≠ (0 : ZMod64 p) := by
        rw [DensePoly.coeff_scale _ _ _ hzero_c]
        exact hprod_ne
      by_cases hle : f.size ≤ (DensePoly.scale c f).size
      · exact hle
      · exfalso
        have hle' : (DensePoly.scale c f).size ≤ i := by
          dsimp [i]
          omega
        exact hcoeff (DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale c f) hle')

/-- Scaling by a nonzero scalar preserves the optional degree. The degree-level
counterpart of `scale_size_eq_of_ne_zero`, used when reasoning in terms of
`degree?` rather than `size`. -/
theorem scale_degree?_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).degree? = f.degree? := by
  have hsize := scale_size_eq_of_ne_zero (p := p) hc f
  unfold DensePoly.degree?
  rw [hsize]

/-- Nonzero scaling preserves the degree in the `degree?.getD 0` form callers
commonly carry, sparing them an `Option` unfolding at each use site. -/
theorem scale_degree?_getD_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).degree?.getD 0 = f.degree?.getD 0 := by
  rw [scale_degree?_eq_of_ne_zero (p := p) hc f]

/-- For a nonempty polynomial the leading coefficient is the coefficient at the
top index `size - 1`. Gives callers a concrete index for the leading
coefficient when they need to compute or rewrite it. -/
theorem leadingCoeff_eq_coeff_pred
    (f : FpPoly p) (hpos : 0 < f.size) :
    DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
  unfold DensePoly.leadingCoeff DensePoly.coeff
  rw [Array.back?_eq_getElem?]
  have hidx : f.coeffs.size - 1 < f.coeffs.size := by
    simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
  simp [Array.getD, DensePoly.size, hidx]

/-- A polynomial of positive degree has a nonzero leading coefficient. The
nondegeneracy fact that justifies inverting the leading coefficient during
monic normalization. -/
theorem leadingCoeff_ne_zero_of_pos_degree
    (f : FpPoly p) (hpos : 0 < f.degree?.getD 0) :
    DensePoly.leadingCoeff f ≠ 0 := by
  have hfsize : 0 < f.size := by
    by_cases h : 0 < f.size
    · exact h
    · exfalso
      have hsize : f.size = 0 := by omega
      simp [DensePoly.degree?, hsize] at hpos
  rw [leadingCoeff_eq_coeff_pred f hfsize]
  exact DensePoly.coeff_last_ne_zero_of_pos_size f hfsize

/-- For a nonzero scalar and a positive-degree polynomial the leading
coefficient scales by `c`. Lets callers track how the leading coefficient moves
under a unit scaling, the key step in computing a monic-normalizing scalar. -/
theorem leadingCoeff_scale_of_ne_zero_of_pos_degree [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p)
    (hpos : 0 < f.degree?.getD 0) :
    DensePoly.leadingCoeff (DensePoly.scale c f) =
      c * DensePoly.leadingCoeff f := by
  have hfpos : 0 < f.size := by
    by_cases h : 0 < f.size
    · exact h
    · exfalso
      have hsize : f.size = 0 := by omega
      simp [DensePoly.degree?, hsize] at hpos
  have hs : (DensePoly.scale c f).size = f.size :=
    scale_size_eq_of_ne_zero (p := p) hc f
  have hscale_pos : 0 < (DensePoly.scale c f).size := by omega
  have hscale_zero : c * (0 : ZMod64 p) = 0 := by grind
  rw [leadingCoeff_eq_coeff_pred (DensePoly.scale c f) hscale_pos]
  rw [leadingCoeff_eq_coeff_pred f hfpos]
  rw [show (DensePoly.scale c f).size - 1 = f.size - 1 by omega]
  rw [DensePoly.coeff_scale _ _ _ hscale_zero]

/-- The same leading-coefficient scaling law as
`leadingCoeff_scale_of_ne_zero_of_pos_degree`, stated from the weaker nonempty
hypothesis `f.size ≠ 0` so it applies to constants as well as higher-degree
polynomials. -/
theorem leadingCoeff_scale_of_ne_zero_of_nonzero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p)
    (hfsize : f.size ≠ 0) :
    DensePoly.leadingCoeff (DensePoly.scale c f) =
      c * DensePoly.leadingCoeff f := by
  have hfpos : 0 < f.size := Nat.pos_of_ne_zero hfsize
  have hscale_size : (DensePoly.scale c f).size = f.size :=
    scale_size_eq_of_ne_zero (p := p) hc f
  have hscale_pos : 0 < (DensePoly.scale c f).size := by omega
  have hscale_zero : c * (0 : ZMod64 p) = 0 := by grind
  rw [leadingCoeff_eq_coeff_pred (DensePoly.scale c f) hscale_pos]
  rw [leadingCoeff_eq_coeff_pred f hfpos]
  rw [show (DensePoly.scale c f).size - 1 = f.size - 1 by omega]
  rw [DensePoly.coeff_scale _ _ _ hscale_zero]

/-- Scaling a positive-degree polynomial by the inverse of its leading
coefficient produces a monic polynomial. This is the monic-normalization step
that puts a polynomial into the canonical leading-`1` form. -/
theorem scale_inv_leadingCoeff_monic [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hpos : 0 < f.degree?.getD 0) :
    DensePoly.Monic (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) := by
  have hlead_ne := leadingCoeff_ne_zero_of_pos_degree f hpos
  have hinv_ne : (DensePoly.leadingCoeff f)⁻¹ ≠ (0 : ZMod64 p) := by
    intro hinv
    change ZMod64.inv (DensePoly.leadingCoeff f) = (0 : ZMod64 p) at hinv
    have hone := ZMod64.inv_mul_eq_one_of_prime
      (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
    rw [hinv] at hone
    have hzero : (0 : ZMod64 p) * DensePoly.leadingCoeff f = 0 := by grind
    rw [hzero] at hone
    exact zmod64_one_ne_zero hone.symm
  unfold DensePoly.Monic
  rw [leadingCoeff_scale_of_ne_zero_of_pos_degree (p := p) hinv_ne f hpos]
  exact ZMod64.inv_mul_eq_one_of_prime
    (ZMod64.PrimeModulus.prime (p := p)) hlead_ne

/-- Scaling by a nonzero (hence unit) scalar preserves irreducibility in both
directions. Lets callers normalize a polynomial to monic form without changing
whether it is irreducible. -/
theorem irreducible_scale_iff_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    FpPoly.Irreducible (DensePoly.scale c f) ↔ FpPoly.Irreducible f := by
  constructor
  · intro hcf
    have hcinv : c⁻¹ ≠ (0 : ZMod64 p) := by
      intro hinv
      change ZMod64.inv c = (0 : ZMod64 p) at hinv
      have hone := ZMod64.inv_mul_eq_one_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hc
      rw [hinv] at hone
      have hzero : (0 : ZMod64 p) * c = 0 := by grind
      rw [hzero] at hone
      exact zmod64_one_ne_zero hone.symm
    have hscale_back : DensePoly.scale c⁻¹ (DensePoly.scale c f) = f := by
      rw [scale_scale]
      have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
        ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
      rw [hmul]
      exact scale_one_left f
    constructor
    · intro hfzero
      apply hcf.1
      rw [hfzero]
      apply DensePoly.ext_coeff
      intro n
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_scale _ _ _ hzero]
      rw [DensePoly.coeff_zero]
      exact hzero
    · intro a b hab
      have hab' : DensePoly.scale c (a * b) = DensePoly.scale c f := by
        rw [hab]
      rw [scale_mul_left] at hab'
      rcases hcf.2 (DensePoly.scale c a) b hab' with ha | hb
      · left
        rwa [scale_degree?_eq_of_ne_zero (p := p) hc a] at ha
      · right
        exact hb
  · intro hf
    constructor
    · intro hcfzero
      apply hf.1
      have hback : DensePoly.scale c⁻¹ (DensePoly.scale c f) = f := by
        rw [scale_scale]
        have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
          ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
        rw [hmul]
        exact scale_one_left f
      rw [hcfzero] at hback
      have hzero : DensePoly.scale c⁻¹ (0 : FpPoly p) = 0 := by
        apply DensePoly.ext_coeff
        intro n
        have hz : c⁻¹ * (0 : ZMod64 p) = 0 := by grind
        rw [DensePoly.coeff_scale _ _ _ hz]
        rw [DensePoly.coeff_zero]
        exact hz
      rw [hzero] at hback
      exact hback.symm
    · intro a b hab
      have hab_scaled : DensePoly.scale c⁻¹ (a * b) = f := by
        rw [hab, scale_scale]
        have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
          ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
        rw [hmul]
        exact scale_one_left f
      rw [scale_mul_left] at hab_scaled
      rcases hf.2 (DensePoly.scale c⁻¹ a) b hab_scaled with ha | hb
      · left
        have hcinv : c⁻¹ ≠ (0 : ZMod64 p) := by
          intro hinv
          change ZMod64.inv c = (0 : ZMod64 p) at hinv
          have hone := ZMod64.inv_mul_eq_one_of_prime
            (ZMod64.PrimeModulus.prime (p := p)) hc
          rw [hinv] at hone
          have hzero : (0 : ZMod64 p) * c = 0 := by grind
          rw [hzero] at hone
          exact zmod64_one_ne_zero hone.symm
        rwa [scale_degree?_eq_of_ne_zero (p := p) hcinv a] at ha
      · right
        exact hb

/-- Forward direction of `irreducible_scale_iff_of_ne_zero`: a nonzero scaling
of an irreducible polynomial is irreducible. The convenient form when the
hypothesis is irreducibility of the unscaled polynomial. -/
theorem irreducible_scale_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f : FpPoly p}
    (hf : FpPoly.Irreducible f) :
    FpPoly.Irreducible (DensePoly.scale c f) :=
  (irreducible_scale_iff_of_ne_zero (p := p) hc f).2 hf

/-- Reverse direction of `irreducible_scale_iff_of_ne_zero`: if a nonzero
scaling is irreducible then so is the unscaled polynomial. Lets callers
transfer irreducibility back from a normalized representative. -/
theorem irreducible_of_scale_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f : FpPoly p}
    (hf : FpPoly.Irreducible (DensePoly.scale c f)) :
    FpPoly.Irreducible f :=
  (irreducible_scale_iff_of_ne_zero (p := p) hc f).1 hf

/-- Divisibility is preserved when both sides are scaled by the same scalar.
Holds for any `c`, so callers can scale a divisibility relation without a
nonzero hypothesis. -/
theorem dvd_scale_of_dvd {c : ZMod64 p} {f g : FpPoly p}
    (hfg : f ∣ g) : DensePoly.scale c f ∣ DensePoly.scale c g := by
  rcases hfg with ⟨q, hq⟩
  exact ⟨q, by rw [← scale_mul_left, hq]⟩

/-- Converse of `dvd_scale_of_dvd` for a nonzero scalar: a divisibility between
equally scaled polynomials reflects back to the originals. Lets callers strip a
common unit scaling from both sides of a divisibility. -/
theorem dvd_of_scale_dvd [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f g : FpPoly p}
    (hfg : DensePoly.scale c f ∣ DensePoly.scale c g) : f ∣ g := by
  rcases hfg with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hscaled : DensePoly.scale c⁻¹ (DensePoly.scale c g) =
      DensePoly.scale c⁻¹ (DensePoly.scale c f * q) := by
    rw [hq]
  rw [scale_scale] at hscaled
  rw [scale_mul_left, scale_scale] at hscaled
  have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
    ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
  rw [hmul, scale_one_left, scale_one_left] at hscaled
  exact hscaled

/-- A nonzero scaling of `f` divides `f` itself: scaling by a unit produces an
associate. Lets callers treat a unit-scaled polynomial and the original as
mutually divisible. -/
theorem dvd_scale_self_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    DensePoly.scale c f ∣ f := by
  refine ⟨DensePoly.C c⁻¹, ?_⟩
  rw [mul_comm, C_mul_eq_scale, scale_scale]
  have hmul : c⁻¹ * c = (1 : ZMod64 p) :=
    ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hc
  rw [hmul, scale_one_left]

private theorem mulCoeffTerm_eq_zero_above_top
    (f g : FpPoly p) {n i : Nat} (hi : i < f.size)
    (hbound : f.size - 1 + (g.size - 1) < n) :
    mulCoeffTerm f g n i = 0 := by
  unfold mulCoeffTerm
  have hni : ¬ n < i := by omega
  have h_gi : g.size ≤ n - i := by omega
  have hg_zero : g.coeff (n - i) = 0 :=
    DensePoly.coeff_eq_zero_of_size_le g h_gi
  simp [hni, hg_zero]

private theorem coeff_mul_eq_zero_above_top
    (f g : FpPoly p) {n : Nat}
    (hbound : f.size - 1 + (g.size - 1) < n) :
    (f * g).coeff n = 0 := by
  rw [coeff_mul]
  unfold mulCoeffSum
  have hfold : ∀ (xs : List Nat) (acc : ZMod64 p),
      (∀ j ∈ xs, j < f.size) →
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) acc = acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons j xs ih =>
        intro acc hxs
        have hj : j < f.size := hxs j (by simp)
        simp only [List.foldl_cons]
        have hzero : mulCoeffTerm f g n j = 0 :=
          mulCoeffTerm_eq_zero_above_top f g hj hbound
        rw [hzero]
        have hadd : acc + (0 : ZMod64 p) = acc := zmod_add_zero acc
        rw [hadd]
        exact ih acc (fun k hk => hxs k (by simp [hk]))
  exact hfold (List.range f.size) 0 (fun j hj => List.mem_range.mp hj)

/--
Over a prime modulus, the degree of a product of nonzero polynomials in
`FpPoly p` equals the sum of the degrees. This is the no-zero-divisors
identity expressed at the level of `degree?.getD 0`.
-/
theorem degree?_mul_eq_add_degree?
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).degree?.getD 0 = a.degree?.getD 0 + b.degree?.getD 0 := by
  have ha_size_pos : 0 < a.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply ha
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
  have hb_size_pos : 0 < b.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hb
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le b (by omega)
  have ha_lead_ne : a.coeff (a.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size a ha_size_pos
  have hb_lead_ne : b.coeff (b.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size b hb_size_pos
  have hp_prime : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime
  have hprod_ne : a.coeff (a.size - 1) * b.coeff (b.size - 1) ≠ 0 := by
    intro hprod
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp_prime hprod with hh | hh
    · exact ha_lead_ne hh
    · exact hb_lead_ne hh
  have htop_ne : (a * b).coeff (a.size - 1 + (b.size - 1)) ≠ 0 := by
    rw [ZMod64.coeff_mul_at_top a b ha_size_pos hb_size_pos]
    exact hprod_ne
  have hab_size_lower : a.size - 1 + (b.size - 1) < (a * b).size := by
    rcases Nat.lt_or_ge (a.size - 1 + (b.size - 1)) (a * b).size with h | hle
    · exact h
    · exact False.elim (htop_ne (DensePoly.coeff_eq_zero_of_size_le _ hle))
  have hab_size_upper : (a * b).size ≤ a.size + b.size - 1 := by
    rcases Nat.lt_or_ge (a.size + b.size - 1) (a * b).size with hgt | hle
    · exfalso
      have hab_size_pos : 0 < (a * b).size := by omega
      have hbound : a.size - 1 + (b.size - 1) < (a * b).size - 1 := by omega
      have htop_zero : (a * b).coeff ((a * b).size - 1) = 0 :=
        coeff_mul_eq_zero_above_top a b hbound
      exact DensePoly.coeff_last_ne_zero_of_pos_size (a * b) hab_size_pos htop_zero
    · exact hle
  have hab_size : (a * b).size = a.size + b.size - 1 := by omega
  have hab_size_ne_zero : (a * b).size ≠ 0 := by omega
  have ha_size_ne_zero : a.size ≠ 0 := Nat.pos_iff_ne_zero.mp ha_size_pos
  have hb_size_ne_zero : b.size ≠ 0 := Nat.pos_iff_ne_zero.mp hb_size_pos
  have hab_deg : (a * b).degree? = some ((a * b).size - 1) := by
    unfold DensePoly.degree?
    simp [hab_size_ne_zero]
  have ha_deg : a.degree? = some (a.size - 1) := by
    unfold DensePoly.degree?
    simp [ha_size_ne_zero]
  have hb_deg : b.degree? = some (b.size - 1) := by
    unfold DensePoly.degree?
    simp [hb_size_ne_zero]
  rw [hab_deg, ha_deg, hb_deg]
  simp
  omega

/-- An `FpPoly p` polynomial is nonzero exactly when its stored coefficient array is nonempty. -/
theorem size_pos_of_ne_zero {f : FpPoly p} (hf : f ≠ 0) : 0 < f.size := by
  apply Nat.pos_of_ne_zero
  intro hsize
  apply hf
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_zero]
  exact DensePoly.coeff_eq_zero_of_size_le f (by omega)

/--
Over a prime modulus, the executable size of a product of two nonzero polynomials in
`FpPoly p` is the sum of their sizes minus one. This is the no-zero-divisors identity at
the level of `DensePoly.size`.
-/
theorem size_mul_eq_add_sub_one
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).size = a.size + b.size - 1 := by
  have ha_size_pos : 0 < a.size := size_pos_of_ne_zero ha
  have hb_size_pos : 0 < b.size := size_pos_of_ne_zero hb
  have ha_lead_ne : a.coeff (a.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size a ha_size_pos
  have hb_lead_ne : b.coeff (b.size - 1) ≠ 0 :=
    DensePoly.coeff_last_ne_zero_of_pos_size b hb_size_pos
  have hp_prime : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime
  have hprod_ne : a.coeff (a.size - 1) * b.coeff (b.size - 1) ≠ 0 := by
    intro hprod
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp_prime hprod with hh | hh
    · exact ha_lead_ne hh
    · exact hb_lead_ne hh
  have htop_ne : (a * b).coeff (a.size - 1 + (b.size - 1)) ≠ 0 := by
    rw [ZMod64.coeff_mul_at_top a b ha_size_pos hb_size_pos]
    exact hprod_ne
  have hab_size_lower : a.size - 1 + (b.size - 1) < (a * b).size := by
    rcases Nat.lt_or_ge (a.size - 1 + (b.size - 1)) (a * b).size with h | hle
    · exact h
    · exact False.elim (htop_ne (DensePoly.coeff_eq_zero_of_size_le _ hle))
  have hab_size_upper : (a * b).size ≤ a.size + b.size - 1 := by
    rcases Nat.lt_or_ge (a.size + b.size - 1) (a * b).size with hgt | hle
    · exfalso
      have hab_size_pos : 0 < (a * b).size := by omega
      have hbound : a.size - 1 + (b.size - 1) < (a * b).size - 1 := by omega
      have htop_zero : (a * b).coeff ((a * b).size - 1) = 0 :=
        coeff_mul_eq_zero_above_top a b hbound
      exact DensePoly.coeff_last_ne_zero_of_pos_size (a * b) hab_size_pos htop_zero
    · exact hle
  omega

/--
Over a prime modulus, multiplying two nonzero polynomials in `FpPoly p` gives a nonzero
polynomial: prime-field polynomials form an integral domain.
-/
theorem mul_ne_zero_of_ne_zero
    [ZMod64.PrimeModulus p] {a b : FpPoly p}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hmul
  have ha_size_pos : 0 < a.size := size_pos_of_ne_zero ha
  have hb_size_pos : 0 < b.size := size_pos_of_ne_zero hb
  have hsize := size_mul_eq_add_sub_one a b ha hb
  have habsize : (a * b).size = 0 := by rw [hmul]; rfl
  omega

/-- Leading coefficient of a product equals the product of leading coefficients
on nonzero `FpPoly p` factors: the top-coefficient lemma `coeff_mul_at_top` plus
the size identity `size_mul_eq_add_sub_one` give this directly. -/
theorem leadingCoeff_mul
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    DensePoly.leadingCoeff (a * b)
      = DensePoly.leadingCoeff a * DensePoly.leadingCoeff b := by
  have ha_pos : 0 < a.size := size_pos_of_ne_zero ha
  have hb_pos : 0 < b.size := size_pos_of_ne_zero hb
  have hab_ne : a * b ≠ 0 := mul_ne_zero_of_ne_zero ha hb
  have hab_pos : 0 < (a * b).size := size_pos_of_ne_zero hab_ne
  have hsize := size_mul_eq_add_sub_one a b ha hb
  have hindex : (a * b).size - 1 = a.size - 1 + (b.size - 1) := by omega
  rw [DensePoly.leadingCoeff_eq_coeff_last (a * b) hab_pos]
  rw [hindex]
  rw [DensePoly.leadingCoeff_eq_coeff_last a ha_pos]
  rw [DensePoly.leadingCoeff_eq_coeff_last b hb_pos]
  exact ZMod64.coeff_mul_at_top a b ha_pos hb_pos

/-- Right cancellation for multiplication by a nonzero `FpPoly p` polynomial. -/
theorem mul_right_cancel_of_ne_zero
    [ZMod64.PrimeModulus p] {a b c : FpPoly p}
    (hc : c ≠ 0) (h : a * c = b * c) :
    a = b := by
  apply Classical.byContradiction
  intro hab
  have hsub_ne : a - b ≠ 0 := by
    intro hsub
    apply hab
    apply DensePoly.ext_coeff
    intro n
    have hcoeff := congrArg (fun s : FpPoly p => s.coeff n) hsub
    change (a - b).coeff n = (0 : FpPoly p).coeff n at hcoeff
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hcoeff
    grind
  have hmul_ne : (a - b) * c ≠ 0 := mul_ne_zero_of_ne_zero hsub_ne hc
  apply hmul_ne
  rw [sub_eq_add_neg, right_distrib]
  have hneg : (-(b : FpPoly p)) * c = -(b * c) := by
    show (0 - b) * c = 0 - b * c
    exact DensePoly.neg_mul_right_poly b c
  rw [hneg, h, add_right_neg]

/--
Over a prime modulus, divisibility implies a size bound: if `a ∣ b` and `b ≠ 0`, then
`a.size ≤ b.size`. The standard polynomial fact that a divisor has degree at most the
degree of the dividend, expressed at the level of `DensePoly.size`.
-/
theorem size_le_of_dvd_of_ne_zero
    [ZMod64.PrimeModulus p] {a b : FpPoly p}
    (hab : a ∣ b) (hb : b ≠ 0) :
    a.size ≤ b.size := by
  rcases hab with ⟨c, hc⟩
  have ha_ne : a ≠ 0 := by
    intro ha
    apply hb
    rw [hc, ha, zero_mul]
  have hc_ne : c ≠ 0 := by
    intro hc_zero
    apply hb
    rw [hc, hc_zero, mul_zero]
  have ha_size_pos : 0 < a.size := size_pos_of_ne_zero ha_ne
  have hc_size_pos : 0 < c.size := size_pos_of_ne_zero hc_ne
  have hsize := size_mul_eq_add_sub_one a c ha_ne hc_ne
  rw [hc, hsize]
  omega

/--
Over a prime modulus, when `d` divides a nonzero polynomial `c`, the executable sizes
satisfy `(c / d).size + d.size = c.size + 1`. This is degree-additivity for exact
division translated to the `size` indexing.
-/
theorem size_div_add_size_eq_size_add_one_of_dvd
    [ZMod64.PrimeModulus p] {c d : FpPoly p}
    (hdc : d ∣ c) (hc : c ≠ 0) :
    (c / d).size + d.size = c.size + 1 := by
  have hd_ne : d ≠ 0 := by
    intro hd
    rcases hdc with ⟨e, he⟩
    apply hc
    rw [he, hd, zero_mul]
  have hmod : c % d = 0 := DensePoly.mod_eq_zero_of_dvd c d hdc
  have hrec : (c / d) * d + (c % d) = c := DensePoly.div_mul_add_mod c d
  have hquot_mul : (c / d) * d = c := by
    rw [hmod] at hrec
    rwa [add_zero ((c / d) * d)] at hrec
  have hquot_ne : c / d ≠ 0 := by
    intro hquot
    apply hc
    rw [← hquot_mul, hquot, zero_mul]
  have hsize_mul := size_mul_eq_add_sub_one (c / d) d hquot_ne hd_ne
  have hd_size_pos : 0 < d.size := size_pos_of_ne_zero hd_ne
  have hquot_size_pos : 0 < (c / d).size := size_pos_of_ne_zero hquot_ne
  have hc_size : ((c / d) * d).size = c.size := by rw [hquot_mul]
  rw [hsize_mul] at hc_size
  omega

/--
Specialised quotient-size strict decrease: if `gcd c w` is nonconstant (size ≥ 2) and
`c ≠ 0`, then `c / gcd c w` has strictly smaller size than `c`. This is the size-strict
descent step that powers Yun-style square-free decomposition termination.
-/
theorem size_div_lt_of_size_gcd_pos
    [ZMod64.PrimeModulus p] (c w : FpPoly p)
    (hgcd_pos : 1 < (DensePoly.gcd c w).size)
    (hc : c.isZero = false) :
    (c / DensePoly.gcd c w).size < c.size := by
  have hc_ne : c ≠ 0 := by
    intro hzero
    rw [hzero] at hc
    exact (Bool.eq_not_self _).mp hc.symm
  have hgcd_dvd : DensePoly.gcd c w ∣ c := DensePoly.gcd_dvd_left c w
  have hsize := size_div_add_size_eq_size_add_one_of_dvd hgcd_dvd hc_ne
  omega

/-- A monic finite-field polynomial that divides the unit polynomial is the unit polynomial. -/
theorem eq_one_of_monic_dvd_one
    [ZMod64.PrimeModulus p] {g : FpPoly p}
    (hmonic : DensePoly.Monic g) (hdiv : g ∣ 1) :
    g = 1 := by
  rcases hdiv with ⟨u, hu⟩
  have hone_ne : (1 : FpPoly p) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
    change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
    rw [coeff_one, DensePoly.coeff_zero] at hcoeff
    exact zmod64_one_ne_zero hcoeff
  have hg_ne : g ≠ 0 := by
    intro hg
    apply hone_ne
    rw [hu, hg, zero_mul]
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    apply hone_ne
    rw [hu, hu_zero, mul_zero]
  have hdeg_mul := degree?_mul_eq_add_degree? g u hg_ne hu_ne
  have hdeg_one : (1 : FpPoly p).degree?.getD 0 = 0 := by
    exact DensePoly.degree?_C_getD (1 : ZMod64 p)
  have hdeg_eq :
      (g * u).degree?.getD 0 = (1 : FpPoly p).degree?.getD 0 :=
    congrArg (fun f : FpPoly p => f.degree?.getD 0) hu.symm
  have hg_degree_zero : g.degree?.getD 0 = 0 := by
    rw [hdeg_mul, hdeg_one] at hdeg_eq
    omega
  have hg_size_pos : 0 < g.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hg_ne
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le g (by omega)
  have hg_degree_size : g.degree?.getD 0 = g.size - 1 := by
    unfold DensePoly.degree?
    have hsize_ne : g.size ≠ 0 := Nat.pos_iff_ne_zero.mp hg_size_pos
    simp [hsize_ne]
  have hg_size_one : g.size = 1 := by
    omega
  have hg_coeff_zero : g.coeff 0 = 1 := by
    have hlead := leadingCoeff_eq_coeff_pred g hg_size_pos
    rw [hg_size_one] at hlead
    change DensePoly.leadingCoeff g = g.coeff 0 at hlead
    unfold DensePoly.Monic at hmonic
    rw [hlead] at hmonic
    exact hmonic
  apply DensePoly.ext_coeff
  intro n
  by_cases hn : n = 0
  · subst n
    rw [hg_coeff_zero, coeff_one]
    simp
  · have hsize_le : g.size ≤ n := by omega
    rw [DensePoly.coeff_eq_zero_of_size_le g hsize_le, coeff_one]
    simp [hn]
    rfl

/--
Turn the executable gcd into the equality `gcd a b = 1` once the gcd is known
monic and every common divisor of `a` and `b` divides `1`.
-/
theorem gcd_eq_one_of_monic_of_common_dvd_one
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hmonic : DensePoly.Monic (DensePoly.gcd a b))
    (hcommon :
      ∀ d : FpPoly p, d ∣ a → d ∣ b → d ∣ (1 : FpPoly p)) :
    DensePoly.gcd a b = 1 := by
  apply eq_one_of_monic_dvd_one hmonic
  exact hcommon (DensePoly.gcd a b)
    (DensePoly.gcd_dvd_left a b)
    (DensePoly.gcd_dvd_right a b)

/--
Bezout-style coprime cancellation for `FpPoly p`. If `g ∣ c * h` and every
common divisor of `c` and `g` divides the unit polynomial `1`, then `g ∣ h`.

The proof uses the extended Euclidean algorithm `DensePoly.xgcd`: from the
Bezout identity `r.left * c + r.right * g = DensePoly.gcd c g` and the fact
that `DensePoly.gcd c g ∣ 1` (via the coprime hypothesis), one concludes that
`g` divides `h`.
-/
theorem dvd_of_dvd_mul_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    {g c h : FpPoly p}
    (hdvd : g ∣ c * h)
    (hcoprime : ∀ d : FpPoly p, d ∣ c → d ∣ g → d ∣ (1 : FpPoly p)) :
    g ∣ h := by
  -- The gcd of `(c, g)` divides `c`, `g`, hence `1` by hypothesis.
  have hDc : DensePoly.gcd c g ∣ c := DensePoly.gcd_dvd_left c g
  have hDg : DensePoly.gcd c g ∣ g := DensePoly.gcd_dvd_right c g
  have hD1 : DensePoly.gcd c g ∣ (1 : FpPoly p) :=
    hcoprime (DensePoly.gcd c g) hDc hDg
  rcases hD1 with ⟨e, he⟩
  -- Extract the Bezout coefficients as free variables (not let-bindings).
  obtain ⟨s, t, hbez⟩ :
      ∃ s t : FpPoly p, s * c + t * g = DensePoly.gcd c g :=
    ⟨(DensePoly.xgcd c g).left, (DensePoly.xgcd c g).right,
     DensePoly.xgcd_bezout c g⟩
  -- `g` divides each summand of `(s * c + t * g) * h`.
  have hg_left : g ∣ s * c * h := by
    have h_assoc : s * c * h = s * (c * h) := DensePoly.mul_assoc_poly s c h
    exact h_assoc ▸ DensePoly.dvd_mul_left_poly s hdvd
  have hg_right : g ∣ t * g * h := by
    have h_rearrange : t * g * h = (t * h) * g := by
      calc t * g * h
          = t * (g * h) := DensePoly.mul_assoc_poly _ _ _
        _ = t * (h * g) := congrArg (fun x => t * x) (DensePoly.mul_comm_poly g h)
        _ = (t * h) * g := (DensePoly.mul_assoc_poly _ _ _).symm
    exact h_rearrange ▸ DensePoly.dvd_mul_left_poly (t * h) (DensePoly.dvd_refl_poly g)
  -- Combine to get `g ∣ DensePoly.gcd c g * h`.
  have hbez_h :
      s * c * h + t * g * h = DensePoly.gcd c g * h := by
    calc s * c * h + t * g * h
        = (s * c + t * g) * h :=
          (DensePoly.mul_add_left_poly (s * c) (t * g) h).symm
      _ = DensePoly.gcd c g * h := congrArg (fun x => x * h) hbez
  have hg_Dh : g ∣ DensePoly.gcd c g * h :=
    hbez_h ▸ DensePoly.dvd_add_poly hg_left hg_right
  -- Use `DensePoly.gcd c g ∣ 1` to conclude `g ∣ h`.
  have hh_eq : h = e * (DensePoly.gcd c g * h) := by
    calc h
        = h * 1 := (DensePoly.mul_one_right_poly h).symm
      _ = h * (DensePoly.gcd c g * e) :=
          congrArg (fun x => h * x) he
      _ = (h * DensePoly.gcd c g) * e :=
          (DensePoly.mul_assoc_poly h (DensePoly.gcd c g) e).symm
      _ = (DensePoly.gcd c g * h) * e :=
          congrArg (fun x => x * e) (DensePoly.mul_comm_poly h (DensePoly.gcd c g))
      _ = e * (DensePoly.gcd c g * h) :=
          DensePoly.mul_comm_poly (DensePoly.gcd c g * h) e
  exact hh_eq ▸ DensePoly.dvd_mul_left_poly e hg_Dh

/-! ### Monomial multiplication and geometric-series divisibility

These lemmas support the `xPowSubX` divisibility chain in
`HexBerlekamp/RabinSoundness.lean`. -/

private theorem mulCoeffTerm_monomial_eq_zero_of_ne
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n i : Nat) (hi : i ≠ k) :
    mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n i = 0 := by
  unfold mulCoeffTerm
  by_cases hni : n < i
  · simp [hni]
  · have hcoeff : (DensePoly.monomial k c : FpPoly p).coeff i = 0 := by
      rw [DensePoly.coeff_monomial]
      simp [hi]
      rfl
    simp [hni, hcoeff]

private theorem mulCoeffTerm_monomial_self_le
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) (hk : ¬ n < k) :
    mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n k = c * g.coeff (n - k) := by
  unfold mulCoeffTerm
  rw [DensePoly.coeff_monomial]
  simp [hk]

private theorem mulCoeffTerm_monomial_self_lt
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) (hk : n < k) :
    mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n k = 0 := by
  unfold mulCoeffTerm
  simp [hk]

private theorem fold_mulCoeffTerm_monomial_eq
    (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) :
    ∀ (m : Nat) (acc : ZMod64 p),
      (List.range m).foldl
          (fun acc i =>
            acc + mulCoeffTerm (DensePoly.monomial k c : FpPoly p) g n i) acc =
        acc + (if k < m ∧ ¬ n < k then c * g.coeff (n - k) else 0) := by
  intro m
  induction m with
  | zero =>
      intro acc
      simp
  | succ m ih =>
      intro acc
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih]
      by_cases hkm : k < m
      · -- k < m, so the new index m is not k.
        have hm_ne : m ≠ k := by omega
        rw [mulCoeffTerm_monomial_eq_zero_of_ne k c g n m hm_ne]
        rw [zmod_add_zero]
        have hkm' : k < m + 1 := by omega
        by_cases hkn : ¬ n < k
        · simp [hkm, hkn, hkm']
        · simp [hkm, hkn, hkm']
      · -- ¬ k < m
        by_cases hkm_eq : k = m
        · subst hkm_eq
          -- index m = k in the new step
          by_cases hkn : ¬ n < k
          · rw [mulCoeffTerm_monomial_self_le k c g n hkn]
            simp [hkn]
          · rw [mulCoeffTerm_monomial_self_lt k c g n (by omega)]
            simp [hkn]
        · -- ¬ k < m and k ≠ m. So k > m, in particular k ≥ m + 1.
          have hkm' : ¬ k < m + 1 := by omega
          have hm_ne : m ≠ k := fun h => hkm_eq h.symm
          rw [mulCoeffTerm_monomial_eq_zero_of_ne k c g n m hm_ne]
          rw [zmod_add_zero]
          simp [hkm, hkm']

/-- Coefficient of `monomial k c * g` at degree `n`: zero below `k`, `c · g[n-k]`
above. -/
theorem coeff_monomial_mul (k : Nat) (c : ZMod64 p) (g : FpPoly p) (n : Nat) :
    ((DensePoly.monomial k c : FpPoly p) * g).coeff n =
      if n < k then 0 else c * g.coeff (n - k) := by
  rw [coeff_mul, mulCoeffSum_eq_degree_bound]
  rw [fold_mulCoeffTerm_monomial_eq k c g n (n + 1) 0]
  rw [zmod_zero_add]
  by_cases hnk : n < k
  · simp [hnk]
  · have hkn : k < n + 1 := by omega
    simp [hnk, hkn]

private def scalarDividedDifferenceCoeffs :
    List (ZMod64 p) → ZMod64 p → List (ZMod64 p)
  | [], _ => []
  | [_], _ => []
  | _ :: c :: cs, α =>
      evalScalarCoeffList (c :: cs) α :: scalarDividedDifferenceCoeffs (c :: cs) α

private theorem zmod_Zero_zero_eq_zero :
    (Zero.zero : ZMod64 p) = (0 : ZMod64 p) := by
  apply zmod_eq_of_toNat_eq
  change (Zero.zero : ZMod64 p).toNat = 0
  exact ZMod64.toNat_zero

private theorem scalarDividedDifferenceCoeffs_getD
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    (scalarDividedDifferenceCoeffs cs α).getD n (0 : ZMod64 p) =
      evalScalarCoeffList (cs.drop (n + 1)) α := by
  induction cs generalizing n with
  | nil =>
      simp [scalarDividedDifferenceCoeffs, evalScalarCoeffList]
  | cons c cs ih =>
      cases cs with
      | nil =>
          cases n <;> simp [scalarDividedDifferenceCoeffs, evalScalarCoeffList]
      | cons d ds =>
          cases n with
          | zero =>
              simp [scalarDividedDifferenceCoeffs]
          | succ n =>
              simpa [scalarDividedDifferenceCoeffs, Nat.succ_eq_add_one, Nat.add_assoc]
                using ih (n := n)

private theorem evalScalarCoeffList_drop_eq_getD_add
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    evalScalarCoeffList (cs.drop n) α =
      cs.getD n (0 : ZMod64 p) +
        α * evalScalarCoeffList (cs.drop (n + 1)) α := by
  induction cs generalizing n with
  | nil =>
      simp [evalScalarCoeffList]
  | cons c cs ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih (n := n)

private theorem ofCoeffs_toArray_fp (f : FpPoly p) :
    (DensePoly.ofCoeffs f.toArray : FpPoly p) = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_ofCoeffs]
  rfl

private theorem scalarDividedDifferenceCoeffs_getElem?_getD
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    (scalarDividedDifferenceCoeffs cs α)[n]?.getD (0 : ZMod64 p) =
      evalScalarCoeffList (cs.drop (n + 1)) α := by
  simpa [List.getD] using scalarDividedDifferenceCoeffs_getD cs α n

private theorem C_zero_fp :
    FpPoly.C (0 : ZMod64 p) = (0 : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  unfold FpPoly.C
  rw [DensePoly.coeff_C, DensePoly.coeff_zero]
  cases n <;> rfl

private theorem scalar_linear_factor_mul_dividedDifference_coeff
    (cs : List (ZMod64 p)) (α : ZMod64 p) (n : Nat) :
    let q : FpPoly p :=
      DensePoly.ofCoeffs (scalarDividedDifferenceCoeffs cs α).toArray
    ((FpPoly.X - FpPoly.C α) * q).coeff n =
      (if n = 0 then 0 else evalScalarCoeffList (cs.drop n) α) -
        α * evalScalarCoeffList (cs.drop (n + 1)) α := by
  intro q
  have hzero_mul : α * (0 : ZMod64 p) = 0 := by grind
  have hneg_mul : (-(FpPoly.C α) : FpPoly p) * q = -(FpPoly.C α * q) := by
    show (0 - FpPoly.C α) * q = 0 - FpPoly.C α * q
    exact DensePoly.neg_mul_right_poly (FpPoly.C α) q
  rw [sub_eq_add_neg, right_distrib]
  rw [DensePoly.coeff_add_semiring]
  rw [hneg_mul]
  rw [DensePoly.coeff_neg_ring]
  have hCmul : FpPoly.C α * q = DensePoly.scale α q := C_mul_eq_scale α q
  rw [hCmul]
  rw [DensePoly.coeff_scale _ _ _ hzero_mul]
  rw [show FpPoly.X = (DensePoly.monomial 1 (1 : ZMod64 p) : FpPoly p) from rfl]
  rw [coeff_monomial_mul]
  rw [DensePoly.coeff_ofCoeffs_list, DensePoly.coeff_ofCoeffs_list]
  rw [zmod_Zero_zero_eq_zero]
  cases n with
  | zero =>
      simp
      rw [scalarDividedDifferenceCoeffs_getElem?_getD cs α 0]
      rw [show cs.drop 1 = cs.tail by cases cs <;> rfl]
      grind
  | succ n =>
      simp
      rw [scalarDividedDifferenceCoeffs_getElem?_getD cs α n]
      rw [scalarDividedDifferenceCoeffs_getElem?_getD cs α (n + 1)]
      grind

private theorem ofCoeffs_eq_C_eval_add_linear_mul_dividedDifference
    (cs : List (ZMod64 p)) (α : ZMod64 p) :
    (DensePoly.ofCoeffs cs.toArray : FpPoly p) =
      FpPoly.C (evalScalarCoeffList cs α) +
        (FpPoly.X - FpPoly.C α) *
          (DensePoly.ofCoeffs (scalarDividedDifferenceCoeffs cs α).toArray : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_ofCoeffs_list]
  rw [zmod_Zero_zero_eq_zero]
  rw [show (FpPoly.C (evalScalarCoeffList cs α)).coeff n =
      if n = 0 then evalScalarCoeffList cs α else (Zero.zero : ZMod64 p) by
    unfold FpPoly.C
    rw [DensePoly.coeff_C]]
  rw [zmod_Zero_zero_eq_zero]
  rw [scalar_linear_factor_mul_dividedDifference_coeff cs α n]
  cases n with
  | zero =>
      have hdrop := evalScalarCoeffList_drop_eq_getD_add cs α 0
      simp at hdrop ⊢
      grind
  | succ n =>
      have hdrop := evalScalarCoeffList_drop_eq_getD_add cs α (n + 1)
      simp at hdrop ⊢
      grind

/-- If `c` is a scalar root of `f`, then the linear factor `X - C c` divides `f`. -/
theorem X_sub_C_dvd_of_eval_eq_zero
    (f : FpPoly p) (c : ZMod64 p)
    (hroot : DensePoly.eval f c = 0) :
    (FpPoly.X - FpPoly.C c) ∣ f := by
  let q : FpPoly p :=
    DensePoly.ofCoeffs (scalarDividedDifferenceCoeffs f.toArray.toList c).toArray
  refine ⟨q, ?_⟩
  have hcoeffs :=
    ofCoeffs_eq_C_eval_add_linear_mul_dividedDifference
      (p := p) f.toArray.toList c
  rw [eval_eq_coeff_power_sum] at hroot
  have hroot_scalar : evalScalarCoeffList f.toArray.toList c = 0 := by
    rw [evalScalarCoeffList_eq_powerSumFrom_zero, hroot]
  rw [← ofCoeffs_toArray_fp f]
  rw [hcoeffs]
  rw [hroot_scalar]
  rw [C_zero_fp]
  change (0 : FpPoly p) +
      (FpPoly.X - FpPoly.C c) * q = (FpPoly.X - FpPoly.C c) * q
  exact zero_add ((FpPoly.X - FpPoly.C c) * q)

/-- Multiplying two monic monomials adds their exponents. -/
theorem monomial_mul_monomial (m n : Nat) :
    (DensePoly.monomial m (1 : ZMod64 p)) *
        (DensePoly.monomial n (1 : ZMod64 p)) =
      DensePoly.monomial (m + n) (1 : ZMod64 p) := by
  apply DensePoly.ext_coeff
  intro i
  rw [coeff_monomial_mul]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_monomial]
  by_cases him : i < m
  · simp [him]
    have hne : i ≠ m + n := by omega
    simp [hne]
    rfl
  · simp [him]
    by_cases hi : i = m + n
    · have hi' : i - m = n := by omega
      simp [hi]
    · simp [hi]
      have hi' : i - m ≠ n := by omega
      simp [hi']

/-- The constant `1` polynomial agrees with the zero-degree monic monomial. -/
theorem monomial_zero_one_eq_one :
    (DensePoly.monomial 0 (1 : ZMod64 p) : FpPoly p) = 1 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_monomial, coeff_one]
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]
    rfl

/-- Linear polynomial exponentiation by repeated right-multiplication.
This is the building block for the geometric-series identity used by
the `xPowSubX` divisibility chain. -/
def linearPow (f : FpPoly p) : Nat → FpPoly p
  | 0 => 1
  | n + 1 => linearPow f n * f

@[simp] theorem linearPow_zero (f : FpPoly p) : linearPow f 0 = 1 := rfl

/-- Successor exponents append one right multiplication by the base. -/
@[simp] theorem linearPow_succ (f : FpPoly p) (n : Nat) :
    linearPow f (n + 1) = linearPow f n * f := rfl

/-- Successor exponents may also be read as one left multiplication by the base. -/
theorem linearPow_succ_left (f : FpPoly p) (n : Nat) :
    linearPow f (n + 1) = f * linearPow f n := by
  induction n with
  | zero =>
      change (1 : FpPoly p) * f = f * 1
      rw [one_mul, mul_one]
  | succ n ih =>
      calc linearPow f ((n + 1) + 1)
          = linearPow f (n + 1) * f := rfl
        _ = (f * linearPow f n) * f := by rw [ih]
        _ = f * (linearPow f n * f) := mul_assoc f (linearPow f n) f
        _ = f * linearPow f (n + 1) := rfl

/-- The first `linearPow` of a polynomial is the polynomial itself. -/
@[simp] theorem linearPow_one (f : FpPoly p) :
    linearPow f 1 = f := by
  rw [linearPow_succ, linearPow_zero, one_mul]

/-- `linearPow` turns exponent addition into polynomial multiplication. -/
theorem linearPow_add (f : FpPoly p) (m n : Nat) :
    linearPow f (m + n) = linearPow f m * linearPow f n := by
  induction n with
  | zero =>
      change linearPow f m = linearPow f m * 1
      rw [mul_one]
  | succ n ih =>
      calc linearPow f (m + (n + 1))
          = linearPow f ((m + n) + 1) := by rw [Nat.add_succ]
        _ = linearPow f (m + n) * f := rfl
        _ = (linearPow f m * linearPow f n) * f := by rw [ih]
        _ = linearPow f m * (linearPow f n * f) := mul_assoc _ _ _
        _ = linearPow f m * linearPow f (n + 1) := rfl

/-- Iterated `linearPow` multiplies exponents. -/
theorem linearPow_iterate_mul (f : FpPoly p) (m : Nat) :
    ∀ n, linearPow (linearPow f m) n = linearPow f (m * n)
  | 0 => by
      simp [Nat.mul_zero]
  | n + 1 => by
      rw [linearPow_succ, linearPow_iterate_mul f m n, Nat.mul_succ,
        linearPow_add]

/-- Scalar evaluation distributes over `linearPow`: `eval (f^n) x = (eval f x)^n`. -/
theorem eval_linearPow (f : FpPoly p) (n : Nat) (x : ZMod64 p) :
    DensePoly.eval (linearPow f n) x = (DensePoly.eval f x) ^ n := by
  induction n with
  | zero =>
      rw [linearPow_zero, Lean.Grind.Semiring.pow_zero]
      exact eval_one x
  | succ n ih =>
      rw [linearPow_succ, eval_mul, ih, Lean.Grind.Semiring.pow_succ]

/-- `linearPow (monomial k 1) n = monomial (k * n) 1`. -/
theorem linearPow_monomial (k n : Nat) :
    linearPow (DensePoly.monomial k (1 : ZMod64 p)) n =
      DensePoly.monomial (k * n) (1 : ZMod64 p) := by
  induction n with
  | zero =>
      show (1 : FpPoly p) = DensePoly.monomial (k * 0) 1
      rw [Nat.mul_zero]
      exact monomial_zero_one_eq_one.symm
  | succ n ih =>
      rw [linearPow_succ, ih]
      have h := monomial_mul_monomial (p := p) (k * n) k
      have heq : k * n + k = k * (n + 1) := (Nat.mul_succ k n).symm
      rw [heq] at h
      exact h

/-- `linearPow (monomial 1 1) n = monomial n 1`. -/
theorem linearPow_monomial_one (n : Nat) :
    linearPow (DensePoly.monomial 1 (1 : ZMod64 p)) n =
      DensePoly.monomial n (1 : ZMod64 p) := by
  have h := linearPow_monomial (p := p) 1 n
  rw [Nat.one_mul] at h
  exact h

/-- `linearPow X n` is the degree-`n` monomial. -/
theorem linearPow_X (n : Nat) :
    linearPow (FpPoly.X : FpPoly p) n =
      DensePoly.monomial n (1 : ZMod64 p) := by
  exact linearPow_monomial_one (p := p) n

private theorem C_mul_C (a b : ZMod64 p) :
    FpPoly.C a * FpPoly.C b = FpPoly.C (a * b) := by
  unfold FpPoly.C
  rw [C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  have hzero : a * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => rfl
  | succ n => rfl

/-- `linearPow` of a constant polynomial stays constant. -/
theorem linearPow_C (c : ZMod64 p) (n : Nat) :
    linearPow (FpPoly.C c) n = FpPoly.C (c ^ n) := by
  induction n with
  | zero =>
      rw [linearPow_zero, Lean.Grind.Semiring.pow_zero]
      rfl
  | succ n ih =>
      rw [linearPow_succ, ih, Lean.Grind.Semiring.pow_succ, C_mul_C]

/-- The polynomial-level subtraction-multiplication identity: `(P - 1) * Y = P * Y - Y`. -/
private theorem sub_one_mul_eq (P Y : FpPoly p) :
    (P - 1) * Y = P * Y - Y := by
  rw [sub_eq_add_neg]
  rw [right_distrib]
  have hneg : (-(1 : FpPoly p)) * Y = -Y := by
    show (0 - (1 : FpPoly p)) * Y = 0 - Y
    have h := DensePoly.neg_mul_right_poly (1 : FpPoly p) Y
    have h1 : (1 : FpPoly p) * Y = Y := one_mul Y
    calc (0 - (1 : FpPoly p)) * Y = 0 - 1 * Y := h
      _ = 0 - Y := by rw [h1]
  rw [hneg]
  rw [← sub_eq_add_neg]

/-- Geometric-series divisibility: `Y - 1 ∣ Y^j - 1`. -/
theorem sub_one_dvd_linearPow_sub_one (Y : FpPoly p) (j : Nat) :
    (Y - 1) ∣ (linearPow Y j - 1) := by
  induction j with
  | zero =>
      change (Y - 1) ∣ (1 - 1 : FpPoly p)
      exact ⟨0, by rw [sub_self, mul_zero]⟩
  | succ j ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * Y + 1, ?_⟩
      -- Need: linearPow Y (j + 1) - 1 = (Y - 1) * (q * Y + 1)
      rw [linearPow_succ]
      rw [left_distrib, mul_one]
      rw [show (Y - 1) * (q * Y) = ((Y - 1) * q) * Y from (mul_assoc _ _ _).symm]
      rw [← hq]
      rw [sub_one_mul_eq]
      -- goal: linearPow Y j * Y - 1 = linearPow Y j * Y - Y + (Y - 1)
      -- A - 1 = A - Y + Y - 1, regroup at coefficient level.
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_sub_ring]
      rw [DensePoly.coeff_add_semiring]
      rw [DensePoly.coeff_sub_ring]
      rw [DensePoly.coeff_sub_ring]
      grind

/-- Geometric-series divisibility for monomials: when `k ∣ l`,
`(monomial k 1 - 1) ∣ (monomial l 1 - 1)`. -/
theorem monomial_sub_one_dvd_of_dvd
    {k l : Nat} (hdvd : k ∣ l) :
    ((DensePoly.monomial k (1 : ZMod64 p) - 1) : FpPoly p) ∣
      (DensePoly.monomial l (1 : ZMod64 p) - 1 : FpPoly p) := by
  obtain ⟨j, rfl⟩ := hdvd
  rw [show (DensePoly.monomial (k * j) (1 : ZMod64 p) : FpPoly p) =
        linearPow (DensePoly.monomial k (1 : ZMod64 p)) j from
        (linearPow_monomial k j).symm]
  exact sub_one_dvd_linearPow_sub_one _ j

end FpPoly
end Hex
