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

/-- Typeclass wrapper for the prime-modulus assumption needed by field-style polynomial
division laws over `ZMod64 p`. -/
class PrimeModulus (p : Nat) : Prop where
  prime : Hex.Nat.Prime p

/-- Build the prime-modulus typeclass witness from an explicit project-local primality proof. -/
@[reducible]
def primeModulusOfPrime (hp : Hex.Nat.Prime p) : PrimeModulus p :=
  ⟨hp⟩

private theorem divMod_spec_core (f g : DensePoly (ZMod64 p)) :
    let qr := DensePoly.divMod f g
    qr.1 * g + qr.2 = f := by
  sorry

private theorem mod_sub_self_eq_mul_neg_div (f m : DensePoly (ZMod64 p)) :
    f % m - f = m * (0 - (f / m)) := by
  have hdiv : (f / m) * m + (f % m) = f := by
    simpa [DensePoly.div, DensePoly.mod] using divMod_spec_core f m
  calc
    f % m - f = 0 - (f / m) * m := by
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hdiv
      have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
      have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
      change (((f / m) * m + (f % m)).coeff n = f.coeff n) at hcoeff
      rw [DensePoly.coeff_add ((f / m) * m) (f % m) n hzero_add] at hcoeff
      rw [DensePoly.coeff_sub (f % m) f n hzero_sub]
      rw [DensePoly.coeff_sub 0 ((f / m) * m) n hzero_sub]
      rw [DensePoly.coeff_zero]
      grind
    _ = m * (0 - (f / m)) := by
      exact (DensePoly.mul_sub_zero_comm m (f / m)).symm

private theorem congr_mod_core (f m : DensePoly (ZMod64 p)) :
    DensePoly.Congr (f % m) f m := by
  exact ⟨0 - (f / m), mod_sub_self_eq_mul_neg_div f m⟩

private theorem eq_add_mul_of_sub_eq_mul {f g m r : DensePoly (ZMod64 p)}
    (hsub : f - g = m * r) :
    f = g + m * r := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hsub
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  change (f - g).coeff n = (m * r).coeff n at hcoeff
  rw [DensePoly.coeff_sub f g n hzero_sub] at hcoeff
  rw [DensePoly.coeff_add g (m * r) n hzero_add]
  grind

private theorem add_sub_add_right (a b c d : DensePoly (ZMod64 p)) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) (c + d) n hzero_sub]
  rw [DensePoly.coeff_add a b n hzero_add, DensePoly.coeff_add c d n hzero_add]
  rw [DensePoly.coeff_add (a - c) (b - d) n hzero_add]
  rw [DensePoly.coeff_sub a c n hzero_sub, DensePoly.coeff_sub b d n hzero_sub]
  grind

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

private theorem mod_remainder_degree_lt_core
    [PrimeModulus p] (f m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0) :
    (f % m).degree?.getD 0 < m.degree?.getD 0 := by
  simpa [DensePoly.mod] using divMod_remainder_degree_lt_core f m hdegree

private theorem foldl_mulCoeffStep_select
    (f g : DensePoly (ZMod64 p)) (n i m : Nat) (acc : ZMod64 p) :
    (List.range m).foldl (DensePoly.mulCoeffStep f g n i) acc =
      acc + (if n < i then 0
        else if n - i < m then f.coeff i * g.coeff (n - i) else 0) := by
  induction m generalizing acc with
  | zero =>
      simp
      grind
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
            grind
          · have hm' : ¬ n - i < m + 1 := by omega
            simp [hlt, hm, hm', heq]

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
        grind
      · by_cases hkm : m = k
        · subst k
          have hkk : ¬ m < m := by omega
          have hmm : m < m + 1 := by omega
          simp [hkk, hmm]
        · have hk' : ¬ k < m + 1 := by omega
          simp [hk, hk', hkm]
          grind

private theorem coeff_mul_at_top
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
          exact ih (acc + 0) (fun k hk => hxs k (by simp [hk]))
  rw [hfold_eq (List.range f.size) (Zero.zero : ZMod64 p)
    (by intro i hi; exact List.mem_range.mp hi)]
  rw [foldl_select_index]
  have hfm1 : f.size - 1 < f.size := by omega
  simp [hfm1]
  -- Goal: Zero.zero + (lead_prod) = lead_prod
  show (0 : ZMod64 p) + _ = _
  grind

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
  have hzero_sub : (0 : ZMod64 p) - 0 = 0 := by grind
  have hrs_top_zero : ∀ i, max r.size s.size ≤ i → (r - s).coeff i = 0 := by
    intro i hi
    rw [DensePoly.coeff_sub r s i hzero_sub]
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
    rw [DensePoly.coeff_sub r s i hzero_sub, DensePoly.coeff_zero] at hcoeff
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

private theorem mod_remainders_congr_of_congr (f g m : DensePoly (ZMod64 p))
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
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  change (f - g).coeff i = (0 : DensePoly (ZMod64 p)).coeff i at hcoeff
  rw [DensePoly.coeff_sub f g i hzero_sub, DensePoly.coeff_zero] at hcoeff
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

private theorem sub_self_right_add (a b : DensePoly (ZMod64 p)) :
    (a + b) - a = b := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) a n hzero_sub]
  rw [DensePoly.coeff_add a b n hzero_add]
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
    sorry
  mod_eq_zero_of_dvd := by
    intro f g hdiv
    sorry
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
        have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
        have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
        change (f % m - f).coeff n = (m * rf).coeff n at hcoeff
        rw [DensePoly.coeff_sub (f % m) f n hzero_sub] at hcoeff
        rw [DensePoly.coeff_add f (m * rf) n hzero_add]
        grind
      have hg' : g % m = g + m * rg := by
        apply DensePoly.ext_coeff
        intro n
        have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hg
        have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
        have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
        change (g % m - g).coeff n = (m * rg).coeff n at hcoeff
        rw [DensePoly.coeff_sub (g % m) g n hzero_sub] at hcoeff
        rw [DensePoly.coeff_add g (m * rg) n hzero_add]
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
instance [PrimeModulus p] : DensePoly.GcdLaws (ZMod64 p) where
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
    sorry
  xgcd_bezout := by
    intro f g
    sorry

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

private theorem zmod_sub_zero_zero :
    (Zero.zero : ZMod64 p) - (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) := by
  change ZMod64.sub (Zero.zero : ZMod64 p) Zero.zero = Zero.zero
  apply zmod_eq_of_toNat_eq
  change (ZMod64.sub (Zero.zero : ZMod64 p) Zero.zero).toNat =
    (Zero.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_sub]
  have hz : (Zero.zero : ZMod64 p).val.toNat = 0 := by
    change (Zero.zero : ZMod64 p).toNat = 0
    exact ZMod64.toNat_zero
  simp [hz]

private theorem zmod_mul_zero (a : ZMod64 p) : a * 0 = 0 := by
  grind

private theorem zmod_one_mul (a : ZMod64 p) : 1 * a = a := by
  grind

private theorem zmod_mul_one (a : ZMod64 p) : a * 1 = a := by
  grind

private theorem coeff_one (n : Nat) :
    (1 : FpPoly p).coeff n = if n = 0 then (1 : ZMod64 p) else 0 := by
  change (DensePoly.C (1 : ZMod64 p)).coeff n = if n = 0 then (1 : ZMod64 p) else 0
  exact DensePoly.coeff_C (1 : ZMod64 p) n

theorem add_zero (f : FpPoly p) :
    f + 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem zero_add (f : FpPoly p) :
    0 + f = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem add_comm (f g : FpPoly p) :
    f + g = g + f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  grind

theorem add_assoc (f g h : FpPoly p) :
    f + g + h = f + (g + h) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add (f + g) h i zmod_add_zero_zero]
  rw [DensePoly.coeff_add f (g + h) i zmod_add_zero_zero]
  rw [DensePoly.coeff_add f g i zmod_add_zero_zero]
  rw [DensePoly.coeff_add g h i zmod_add_zero_zero]
  grind

theorem neg_zero :
    -(0 : FpPoly p) = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem add_left_neg (f : FpPoly p) :
    -f + f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem add_right_neg (f : FpPoly p) :
    f + -f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem sub_zero (f : FpPoly p) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub _ _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem zero_sub (f : FpPoly p) :
    0 - f = -f := by
  rfl

theorem sub_self (f : FpPoly p) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub _ _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem sub_eq_add_neg (f g : FpPoly p) :
    f - g = f + -g := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_sub _ _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  grind

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
      rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero, ih]
      rw [DensePoly.coeff_shift_scale]
      · rw [coeff_one]
        by_cases hk : k < n
        · have hks : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
          simp [hk, hks]
          exact zmod_add_zero (f.coeff k)
        · by_cases hkn : k = n
          · subst k
            simp [zmod_mul_one]
            exact zmod_zero_add (f.coeff n)
          · have hks : ¬ k < n + 1 := by omega
            have hsub : k - n ≠ 0 := by omega
            simp [hk, hks, hsub, zmod_mul_zero]
            exact zmod_zero_add (0 : ZMod64 p)
      · exact zmod_mul_zero (f.coeff n)

@[simp] theorem one_mul (f : FpPoly p) :
    1 * f = f := by
  exact (DensePoly.mul_comm_poly (1 : FpPoly p) f).trans (DensePoly.mul_one_right_poly f)

@[simp] theorem mul_one (f : FpPoly p) :
    f * 1 = f := by
  exact DensePoly.mul_one_right_poly f
/-- The `i`th schoolbook contribution to coefficient `n` of `f * g`. -/
def mulCoeffTerm (f g : FpPoly p) (n i : Nat) : ZMod64 p :=
  if n < i then 0 else f.coeff i * g.coeff (n - i)

/-- The executable schoolbook coefficient sum matching `FpPoly` multiplication. -/
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
      rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero,
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
      grind
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
            grind
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
          grind

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
    grind

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
      grind

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
      grind

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
    grind
  · rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
    simp [hi]
    grind

private theorem mulCoeffTerm_right_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm (f + g) h n i =
      mulCoeffTerm f h n i + mulCoeffTerm g h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
    grind
  · rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
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
      exact zmod_zero_add a
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
            · simp [hnj]
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
                  grind
                · rw [if_neg hji]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - j - i ≠ 0 := by omega
                  simp [hsub]
                  exact zmod_mul_zero (f.coeff j)
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
      · simp [hnj]
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

theorem left_distrib (f g h : FpPoly p) :
    f * (g + h) = f * g + f * h := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  simp [coeff_mul, mulCoeffSum, fold_left_distrib]

theorem right_distrib (f g h : FpPoly p) :
    (f + g) * h = f * h + g * h := by
  apply DensePoly.ext_coeff
  intro n
  let m := max (max (f + g).size f.size) g.size
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [coeff_mul_of_size_le (f + g) h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le f h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le g h n m (by dsimp [m]; omega)]
  exact fold_right_distrib (List.range m) f g h n

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

theorem scale_add (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f + g) =
      DensePoly.scale c f + DensePoly.scale c g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

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
    exact hzero
  · simp [hn]
    rw [DensePoly.coeff_scale _ _ _ hzero]
    grind

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

theorem C_mul_eq_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.C c * f = DensePoly.scale c f := by
  have hscale := scale_mul_left c (1 : FpPoly p) f
  rw [one_mul, scale_one_poly] at hscale
  exact hscale.symm

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

theorem scale_degree?_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).degree? = f.degree? := by
  have hsize := scale_size_eq_of_ne_zero (p := p) hc f
  unfold DensePoly.degree?
  rw [hsize]

theorem scale_degree?_getD_eq_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) (f : FpPoly p) :
    (DensePoly.scale c f).degree?.getD 0 = f.degree?.getD 0 := by
  rw [scale_degree?_eq_of_ne_zero (p := p) hc f]

theorem leadingCoeff_eq_coeff_pred
    (f : FpPoly p) (hpos : 0 < f.size) :
    DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
  unfold DensePoly.leadingCoeff DensePoly.coeff
  rw [Array.back?_eq_getElem?]
  have hidx : f.coeffs.size - 1 < f.coeffs.size := by
    simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
  simp [Array.getD, DensePoly.size, hidx]

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

theorem irreducible_scale_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f : FpPoly p}
    (hf : FpPoly.Irreducible f) :
    FpPoly.Irreducible (DensePoly.scale c f) :=
  (irreducible_scale_iff_of_ne_zero (p := p) hc f).2 hf

theorem irreducible_of_scale_of_ne_zero [ZMod64.PrimeModulus p]
    {c : ZMod64 p} (hc : c ≠ 0) {f : FpPoly p}
    (hf : FpPoly.Irreducible (DensePoly.scale c f)) :
    FpPoly.Irreducible f :=
  (irreducible_scale_iff_of_ne_zero (p := p) hc f).1 hf

theorem dvd_scale_of_dvd {c : ZMod64 p} {f g : FpPoly p}
    (hfg : f ∣ g) : DensePoly.scale c f ∣ DensePoly.scale c g := by
  rcases hfg with ⟨q, hq⟩
  exact ⟨q, by rw [← scale_mul_left, hq]⟩

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
  grind

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
    grind

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
      simp [zmod_add_zero]
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
            grind
          · rw [mulCoeffTerm_monomial_self_lt k c g n (by omega)]
            simp [hkn]
            grind
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
      grind
    · simp [hi]
      have hi' : i - m ≠ n := by omega
      simp [hi']
      grind

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

theorem linearPow_succ (f : FpPoly p) (n : Nat) :
    linearPow f (n + 1) = linearPow f n * f := rfl

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
      have hzero_sub : (Zero.zero : ZMod64 p) - Zero.zero = Zero.zero := zmod_sub_zero_zero
      have hzero_add : (Zero.zero : ZMod64 p) + Zero.zero = Zero.zero := zmod_add_zero_zero
      rw [DensePoly.coeff_sub _ _ _ hzero_sub]
      rw [DensePoly.coeff_add _ _ _ hzero_add]
      rw [DensePoly.coeff_sub _ _ _ hzero_sub]
      rw [DensePoly.coeff_sub _ _ _ hzero_sub]
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
