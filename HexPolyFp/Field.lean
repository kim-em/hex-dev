/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Prime
public import HexPoly.Euclid
public import Init.Data.List.Lemmas
public import Init.Data.List.Perm

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
The `ZMod64 p` coefficient field for executable prime-field polynomials:
its field instances, the `DensePoly` DivMod/Gcd law instances, and the
`FpPoly p` abbreviation.
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
      simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
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
    exact divMod_spec_core f m
  calc
    f % m - f = 0 - (f / m) * m := by
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hdiv
      change (((f / m) * m + (f % m)).coeff n = f.coeff n) at hcoeff
      rw [DensePoly.coeff_add_semiring] at hcoeff
      rw [DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring, DensePoly.coeff_zero]
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
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_add_semiring, DensePoly.coeff_add_semiring,
    DensePoly.coeff_add_semiring, DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring]
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
    simp [DensePoly.size]
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
  exact divMod_remainder_degree_lt_core f m hdegree

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

/-- `mod_remainders_congr_of_congr` shows that congruent inputs have congruent remainders modulo the same modulus, providing the general remainder-congruence step. -/
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

/-- `mod_eq_mod_of_congr_pos_degree` turns congruence modulo a positive-degree modulus into equality of canonical remainders. -/
private theorem mod_eq_mod_of_congr_pos_degree
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  apply canonical_remainder_unique_of_pos_degree
  · exact mod_remainder_degree_lt_core f m hdegree
  · exact mod_remainder_degree_lt_core g m hdegree
  · exact mod_remainders_congr_of_congr f g m hcongr

/-- `mod_zero_right_of_size_zero` identifies remainder by a size-zero modulus with the original polynomial for the degenerate modulus case. -/
private theorem mod_zero_right_of_size_zero (f m : DensePoly (ZMod64 p))
    (hm : m.size = 0) :
    f % m = f := by
  exact DensePoly.divMod_remainder_eq_self_of_size_zero_core f m hm

/-- `eq_of_sub_eq_zero` recovers equality of dense polynomials from a zero difference, supplying the algebraic cancellation used in the degenerate case. -/
private theorem eq_of_sub_eq_zero (f g : DensePoly (ZMod64 p))
    (hsub : f - g = 0) :
    f = g := by
  apply DensePoly.ext_coeff
  intro i
  have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff i) hsub
  change (f - g).coeff i = (0 : DensePoly (ZMod64 p)).coeff i at hcoeff
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hcoeff
  grind

/-- `mod_eq_mod_of_congr_not_pos_degree` handles the zero and constant modulus cases of remainder congruence when the modulus has no positive degree. -/
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
        simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
      have hcoeff_ne := DensePoly.coeff_last_ne_zero_of_pos_size m hpos
      rw [hlead_eq]
      exact hcoeff_ne
    have hfmod :
        f % m = 0 := by
      exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core f m hm_size
        (fun a => zmod_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    have hgmod :
        g % m = 0 := by
      exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core g m hm_size
        (fun a => zmod_div_mul_cancel_of_ne a m.leadingCoeff hlead_ne)
    rw [hfmod, hgmod]

/-- `mod_eq_mod_of_congr_core` combines the positive-degree and non-positive-degree branches into the core equality of congruent remainders. -/
private theorem mod_eq_mod_of_congr_core
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  by_cases hdegree : 0 < m.degree?.getD 0
  · exact mod_eq_mod_of_congr_pos_degree f g m hdegree hcongr
  · exact mod_eq_mod_of_congr_not_pos_degree f g m hdegree hcongr

/-- `sub_zero_poly` simplifies subtraction of zero for dense polynomials, feeding divisibility into the congruence form. -/
private theorem sub_zero_poly (f : DensePoly (ZMod64 p)) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero]
  grind

/-- `mod_eq_zero_of_dvd_core` converts divisibility by the modulus into a zero remainder using the core remainder-congruence theorem. -/
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
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_add_semiring]
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
    simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
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

end Hex
