/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Instances
public import HexResultant.FractionPoly

@[expose] public section
set_option backward.proofsInPublic true

/-!
Proof-only Gauss and common-factor algebra.

This file deliberately defines no executable multivariate gcd, content
producer, checker, or candidate route. Its finite coefficient gcd is an
existential object selected only inside proofs; the fraction embedding and
primitive descent isolate the algebra needed to lift gcd-domain laws through
polynomial arities.
-/

namespace Hex

universe u

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

section Domain

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]
  [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R]

/-- The executable gcd laws supply the proof-only gcd-domain package. -/
theorem gcdDomainOfLawful [LawfulGcdOps R] : GcdDomainLaws R where
  dvd_iff := LawfulGcdOps.dvd_iff
  one_ne_zero := LawfulGcdOps.one_ne_zero
  no_zero_div := LawfulGcdOps.no_zero_div
  gcd_exists a b :=
    ⟨GcdOps.gcd a b, LawfulGcdOps.gcd_dvd_left a b,
      LawfulGcdOps.gcd_dvd_right a b,
      fun d hda hdb => LawfulGcdOps.dvd_gcd a b d hda hdb⟩

/-- Low-priority bridge from executable lawful gcd operations to the
producer-free algebraic package. -/
instance (priority := 100) instGcdDomainLawsOfLawful [LawfulGcdOps R] :
    GcdDomainLaws R :=
  gcdDomainOfLawful

end Domain

section Cancel

variable {R : Type u} [Lean.Grind.CommRing R] [Dvd R]
  [GcdDomainLaws R]

/-- Multiplication transports a chosen gcd to a gcd of the two products. -/
private theorem mulGcd
    (m a b c : R) (hca : c ∣ a) (hcb : c ∣ b)
    (hc : ∀ d, d ∣ a → d ∣ b → d ∣ c) :
    m * c ∣ m * a ∧ m * c ∣ m * b ∧
      ∀ d, d ∣ m * a → d ∣ m * b → d ∣ m * c := by
  have hleft : m * c ∣ m * a := by
    rcases (GcdDomainLaws.dvd_iff c a).mp hca with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff (m * c) (m * a)).mpr
    refine ⟨q, ?_⟩
    rw [hq]
    grind
  have hright : m * c ∣ m * b := by
    rcases (GcdDomainLaws.dvd_iff c b).mp hcb with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff (m * c) (m * b)).mpr
    refine ⟨q, ?_⟩
    rw [hq]
    grind
  refine ⟨hleft, hright, ?_⟩
  intro d hdma hdmb
  by_cases hm : m = 0
  · apply (GcdDomainLaws.dvd_iff d (m * c)).mpr
    refine ⟨0, ?_⟩
    rw [hm, Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_zero]
  rcases GcdDomainLaws.gcd_exists (m * a) (m * b) with
    ⟨x, hxa, hxb, hxgreat⟩
  have hmcx : m * c ∣ x := hxgreat (m * c) hleft hright
  rcases (GcdDomainLaws.dvd_iff (m * c) x).mp hmcx with ⟨t, hxt⟩
  let n := c * t
  have hxn : x = m * n := by
    change x = m * (c * t)
    rw [hxt]
    grind
  have hna : n ∣ a := by
    rcases (GcdDomainLaws.dvd_iff x (m * a)).mp hxa with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff n a).mpr
    refine ⟨q, ?_⟩
    have heq : m * a = m * (n * q) := by
      calc
        m * a = x * q := hq
        _ = (m * n) * q := by rw [hxn]
        _ = m * (n * q) := by grind
    have hzero : m * (a - n * q) = 0 := by grind
    rcases GcdDomainLaws.no_zero_div m (a - n * q) hzero with hz | hz
    · exact False.elim (hm hz)
    · grind
  have hnb : n ∣ b := by
    rcases (GcdDomainLaws.dvd_iff x (m * b)).mp hxb with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff n b).mpr
    refine ⟨q, ?_⟩
    have heq : m * b = m * (n * q) := by
      calc
        m * b = x * q := hq
        _ = (m * n) * q := by rw [hxn]
        _ = m * (n * q) := by grind
    have hzero : m * (b - n * q) = 0 := by grind
    rcases GcdDomainLaws.no_zero_div m (b - n * q) hzero with hz | hz
    · exact False.elim (hm hz)
    · grind
  have hnc : n ∣ c := hc n hna hnb
  rcases (GcdDomainLaws.dvd_iff n c).mp hnc with ⟨q, hq⟩
  have hxmc : x ∣ m * c := by
    apply (GcdDomainLaws.dvd_iff x (m * c)).mpr
    refine ⟨q, ?_⟩
    rw [hq, hxn]
    grind
  rcases (GcdDomainLaws.dvd_iff d x).mp (hxgreat d hdma hdmb) with ⟨r, hr⟩
  rcases (GcdDomainLaws.dvd_iff x (m * c)).mp hxmc with ⟨s, hs⟩
  apply (GcdDomainLaws.dvd_iff d (m * c)).mpr
  refine ⟨r * s, ?_⟩
  calc
    m * c = x * s := hs
    _ = (d * r) * s := by rw [hr]
    _ = d * (r * s) := by grind

/-- A divisor of a product in a gcd domain splits into factors dividing the
two operands. This is the primal property of gcd domains. -/
private theorem dvdMulDecompose {k m n : R} (hkmn : k ∣ m * n) :
    ∃ x y : R, x ∣ m ∧ y ∣ n ∧ k = x * y := by
  rcases GcdDomainLaws.gcd_exists k m with ⟨g, hgk, hgm, hgreat⟩
  by_cases hg : g = 0
  · have hk : k = 0 := by
      rcases (GcdDomainLaws.dvd_iff g k).mp hgk with ⟨q, hq⟩
      rw [hg, Lean.Grind.Semiring.zero_mul] at hq
      exact hq
    refine ⟨0, 1, ?_, ?_, ?_⟩
    · simpa [hg] using hgm
    · apply (GcdDomainLaws.dvd_iff 1 n).mpr
      exact ⟨n, (Lean.Grind.Semiring.one_mul n).symm⟩
    · rw [hk, Lean.Grind.Semiring.zero_mul]
  · rcases (GcdDomainLaws.dvd_iff g k).mp hgk with ⟨a, hka⟩
    have hknk : k ∣ n * k := by
      apply (GcdDomainLaws.dvd_iff k (n * k)).mpr
      exact ⟨n, Lean.Grind.CommSemiring.mul_comm n k⟩
    have hknm : k ∣ n * m := by
      rw [Lean.Grind.CommSemiring.mul_comm n m]
      exact hkmn
    have hkng : k ∣ n * g :=
      (mulGcd n k m g hgk hgm hgreat).2.2 k hknk hknm
    rcases (GcdDomainLaws.dvd_iff k (n * g)).mp hkng with ⟨q, hq⟩
    have han : a ∣ n := by
      apply (GcdDomainLaws.dvd_iff a n).mpr
      refine ⟨q, ?_⟩
      have hcancel : g * (n - a * q) = 0 := by
        calc
          g * (n - a * q) = n * g - (g * a) * q := by grind
          _ = n * g - k * q := by rw [hka]
          _ = 0 := by rw [← hq]; grind
      rcases GcdDomainLaws.no_zero_div g (n - a * q) hcancel with
        hzero | hrest
      · exact False.elim (hg hzero)
      · grind
    exact ⟨g, a, hgm, han, hka⟩

/-- A gcd against a product divides the product of the two separate gcds. -/
private theorem gcdMulDvd (k m n c cm cn : R)
    (hck : c ∣ k) (hcmn : c ∣ m * n)
    (hcmGreat : ∀ d, d ∣ k → d ∣ m → d ∣ cm)
    (hcnGreat : ∀ d, d ∣ k → d ∣ n → d ∣ cn) :
    c ∣ cm * cn := by
  rcases dvdMulDecompose hcmn with ⟨x, y, hxm, hyn, hcxy⟩
  have hxc : x ∣ c := by
    apply (GcdDomainLaws.dvd_iff x c).mpr
    exact ⟨y, hcxy⟩
  have hyc : y ∣ c := by
    apply (GcdDomainLaws.dvd_iff y c).mpr
    refine ⟨x, ?_⟩
    rw [hcxy, Lean.Grind.CommSemiring.mul_comm]
  have hxk : x ∣ k := by
    rcases (GcdDomainLaws.dvd_iff x c).mp hxc with ⟨a, ha⟩
    rcases (GcdDomainLaws.dvd_iff c k).mp hck with ⟨b, hb⟩
    apply (GcdDomainLaws.dvd_iff x k).mpr
    refine ⟨a * b, ?_⟩
    rw [hb, ha]
    grind
  have hyk : y ∣ k := by
    rcases (GcdDomainLaws.dvd_iff y c).mp hyc with ⟨a, ha⟩
    rcases (GcdDomainLaws.dvd_iff c k).mp hck with ⟨b, hb⟩
    apply (GcdDomainLaws.dvd_iff y k).mpr
    refine ⟨a * b, ?_⟩
    rw [hb, ha]
    grind
  have hxcm := hcmGreat x hxk hxm
  have hycn := hcnGreat y hyk hyn
  rcases (GcdDomainLaws.dvd_iff x cm).mp hxcm with ⟨a, ha⟩
  rcases (GcdDomainLaws.dvd_iff y cn).mp hycn with ⟨b, hb⟩
  apply (GcdDomainLaws.dvd_iff c (cm * cn)).mpr
  refine ⟨a * b, ?_⟩
  rw [hcxy, ha, hb]
  grind

/-- Ordinary gcd-domain arithmetic gives Euclid cancellation in the exact
form consumed by certificate maximality. -/
theorem coprimeCancelOfGcdDomain : CoprimeCancelLaws R := by
  constructor
  intro g a b d hcop hda hdb
  rcases GcdDomainLaws.gcd_exists a b with ⟨c, hca, hcb, hc⟩
  rcases hcop c hca hcb with ⟨u, hcu⟩
  have hdgc : d ∣ g * c := (mulGcd g a b c hca hcb hc).2.2 d hda hdb
  rcases (GcdDomainLaws.dvd_iff d (g * c)).mp hdgc with ⟨q, hq⟩
  apply (GcdDomainLaws.dvd_iff d g).mpr
  refine ⟨q * u, ?_⟩
  calc
    g = g * 1 := (Lean.Grind.Semiring.mul_one g).symm
    _ = g * (c * u) := by rw [hcu]
    _ = (g * c) * u := by grind
    _ = (d * q) * u := by rw [hq]
    _ = d * (q * u) := by grind

instance (priority := 100) instCoprimeCancelLawsOfGcdDomain :
    CoprimeCancelLaws R :=
  coprimeCancelOfGcdDomain

end Cancel

section CoeffFold

variable {R : Type u} [Lean.Grind.CommRing R] [Dvd R]

/-- Proof object for a greatest common divisor of every member of a finite
coefficient list. It is not executable certificate data. -/
structure CoeffGcd (xs : List R) where
  value : R
  divides : ∀ x, x ∈ xs → value ∣ x
  greatest : ∀ d, (∀ x, x ∈ xs → d ∣ x) → d ∣ value

/-- Transitivity derived from the multiplication-oriented divisibility law. -/
theorem dvdTrans [GcdDomainLaws R] {a b c : R}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases (GcdDomainLaws.dvd_iff a b).mp hab with ⟨x, hb⟩
  rcases (GcdDomainLaws.dvd_iff b c).mp hbc with ⟨y, hc⟩
  apply (GcdDomainLaws.dvd_iff a c).mpr
  refine ⟨x * y, ?_⟩
  calc
    c = b * y := hc
    _ = (a * x) * y := by rw [hb]
    _ = a * (x * y) := Lean.Grind.Semiring.mul_assoc a x y

/-- Divisibility is preserved by multiplying two divisible pairs. -/
theorem dvdMul [GcdDomainLaws R] {a b c d : R}
    (hac : a ∣ c) (hbd : b ∣ d) : a * b ∣ c * d := by
  rcases (GcdDomainLaws.dvd_iff a c).mp hac with ⟨x, hx⟩
  rcases (GcdDomainLaws.dvd_iff b d).mp hbd with ⟨y, hy⟩
  apply (GcdDomainLaws.dvd_iff (a * b) (c * d)).mpr
  refine ⟨x * y, ?_⟩
  rw [hx, hy]
  grind

/-- Every finite coefficient list admits a greatest common divisor, including
the empty list whose gcd is chosen as zero. -/
theorem coeffGcd_nonempty [GcdDomainLaws R] (xs : List R) :
    Nonempty (CoeffGcd xs) := by
  induction xs with
  | nil =>
      refine ⟨⟨0, ?_, ?_⟩⟩
      · intro x hx
        simp at hx
      · intro d _
        apply (GcdDomainLaws.dvd_iff d 0).mpr
        refine ⟨0, ?_⟩
        exact (Lean.Grind.Semiring.mul_zero d).symm
  | cons a xs ih =>
      rcases ih with ⟨c, hc, hgreat⟩
      rcases GcdDomainLaws.gcd_exists a c with ⟨g, hga, hgc, hgreatG⟩
      refine ⟨⟨g, ?_, ?_⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hga
        · exact dvdTrans hgc (hc x hx)
      · intro d hd
        apply hgreatG d
        · exact hd a (List.mem_cons_self ..)
        · apply hgreat d
          intro x hx
          exact hd x (List.mem_cons_of_mem a hx)

/-- Proof-only choice of a finite coefficient gcd. This is intentionally
`noncomputable` and must not be called by an executable content operation. -/
noncomputable def chooseCoeffGcdData [GcdDomainLaws R]
    (xs : List R) : CoeffGcd xs :=
  Classical.choice (coeffGcd_nonempty xs)

noncomputable def chooseCoeffGcd [GcdDomainLaws R] (xs : List R) : R :=
  (chooseCoeffGcdData xs).value

theorem chooseCoeffGcd_divides [GcdDomainLaws R] (xs : List R)
    {x : R} (hx : x ∈ xs) : chooseCoeffGcd xs ∣ x :=
  (chooseCoeffGcdData xs).divides x hx

theorem dvd_chooseCoeffGcd [GcdDomainLaws R] (xs : List R) (d : R)
    (hd : ∀ x, x ∈ xs → d ∣ x) : d ∣ chooseCoeffGcd xs :=
  (chooseCoeffGcdData xs).greatest d hd

/-- Proof-only exact quotient selected from a divisibility witness. -/
noncomputable def divideDvd [GcdDomainLaws R] (a d : R) : R := by
  classical
  exact if a = 0 then 0 else if h : d ∣ a then
    Classical.choose ((GcdDomainLaws.dvd_iff d a).mp h) else 0

theorem mul_divideDvd [GcdDomainLaws R] {a d : R} (h : d ∣ a) :
    d * divideDvd a d = a := by
  by_cases ha : a = 0
  · rw [divideDvd, ite_eq_left ha, ha]
    grind
  · rw [divideDvd, ite_eq_right ha, dite_eq_left h]
    exact (Classical.choose_spec ((GcdDomainLaws.dvd_iff d a).mp h)).symm

end CoeffFold

section DenseContent

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] [Dvd R]
  [GcdDomainLaws R]

omit [DecidableEq R] in
private theorem dvdAdd {d a b : R} (ha : d ∣ a) (hb : d ∣ b) : d ∣ a + b := by
  rcases (GcdDomainLaws.dvd_iff d a).mp ha with ⟨x, hx⟩
  rcases (GcdDomainLaws.dvd_iff d b).mp hb with ⟨y, hy⟩
  apply (GcdDomainLaws.dvd_iff d (a + b)).mpr
  refine ⟨x + y, ?_⟩
  rw [hx, hy]
  grind

omit [DecidableEq R] in
private theorem dvdSub {d a b : R} (ha : d ∣ a) (hb : d ∣ b) : d ∣ a - b := by
  rcases (GcdDomainLaws.dvd_iff d a).mp ha with ⟨x, hx⟩
  rcases (GcdDomainLaws.dvd_iff d b).mp hb with ⟨y, hy⟩
  apply (GcdDomainLaws.dvd_iff d (a - b)).mpr
  refine ⟨x - y, ?_⟩
  rw [hx, hy]
  grind

omit [DecidableEq R] in
private theorem dvdMulRight {d a : R} (h : d ∣ a) (b : R) : d ∣ a * b := by
  rcases (GcdDomainLaws.dvd_iff d a).mp h with ⟨x, hx⟩
  apply (GcdDomainLaws.dvd_iff d (a * b)).mpr
  refine ⟨x * b, ?_⟩
  rw [hx]
  grind

/-- A proof-only chosen gcd of two coefficients. -/
private noncomputable def pairGcd (a b : R) : R :=
  chooseCoeffGcd [a, b]

omit [DecidableEq R] in
private theorem pairGcd_left (a b : R) : pairGcd a b ∣ a := by
  exact chooseCoeffGcd_divides [a, b] (by simp)

omit [DecidableEq R] in
private theorem pairGcd_right (a b : R) : pairGcd a b ∣ b := by
  exact chooseCoeffGcd_divides [a, b] (by simp)

omit [DecidableEq R] in
private theorem dvd_pairGcd {a b d : R} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ pairGcd a b := by
  apply dvd_chooseCoeffGcd
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact ha
  · rcases hx with rfl | hx
    · exact hb
    · contradiction

omit [DecidableEq R] in
private theorem pairGcd_comm_assoc (a b : R) :
    pairGcd a b ∣ pairGcd b a ∧ pairGcd b a ∣ pairGcd a b := by
  constructor
  · exact dvd_pairGcd (pairGcd_right a b) (pairGcd_left a b)
  · exact dvd_pairGcd (pairGcd_right b a) (pairGcd_left b a)

omit [DecidableEq R] in
private theorem pairGcd_assoc_right {a b c : R}
    (hbc : b ∣ c) (hcb : c ∣ b) :
    pairGcd a b ∣ pairGcd a c ∧ pairGcd a c ∣ pairGcd a b := by
  constructor
  · apply dvd_pairGcd (pairGcd_left a b)
    exact dvdTrans (pairGcd_right a b) hbc
  · apply dvd_pairGcd (pairGcd_left a c)
    exact dvdTrans (pairGcd_right a c) hcb

/-- Remove the leading monomial of a dense polynomial. -/
private def denseEraseLead (p : DensePoly R) : DensePoly R :=
  p - DensePoly.monomial p.natDegree p.leadingCoeff

omit [Dvd R] [GcdDomainLaws R] in
private theorem denseSizeLeOfCoeffZero (p : DensePoly R) (N : Nat)
    (h : ∀ i, N ≤ i → p.coeff i = 0) : p.size ≤ N := by
  by_cases hle : p.size ≤ N
  · exact hle
  · have hlt : N < p.size := Nat.lt_of_not_ge hle
    have hzero : p.coeff (p.size - 1) = 0 := h _ (by omega)
    exact False.elim
      (DensePoly.coeff_last_ne_zero_of_pos_size p (by omega) hzero)

omit [Dvd R] [GcdDomainLaws R] in
private theorem denseEraseLead_size_lt {p : DensePoly R} (hp : p ≠ 0) :
    (denseEraseLead p).size < p.size := by
  have hpos : 0 < p.size := by
    have hne : p.size ≠ 0 := fun h =>
      hp ((DensePoly.size_eq_zero_iff p).mp h)
    omega
  have hle : (denseEraseLead p).size ≤ p.size - 1 := by
    apply denseSizeLeOfCoeffZero
    intro i hi
    rw [denseEraseLead, DensePoly.coeff_sub_ring, DensePoly.coeff_monomial]
    have hdegree : p.natDegree = p.size - 1 :=
      DensePoly.natDegree_eq_size_sub_one p
    by_cases heq : i = p.size - 1
    · subst i
      rw [ite_eq_left hdegree.symm]
      rw [DensePoly.leadingCoeff_eq_coeff_last p hpos]
      grind
    · rw [ite_eq_right (fun h => heq (hdegree ▸ h))]
      rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]
      grind
  omega

private theorem denseEraseLead_mul_identity {p q : DensePoly R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    denseEraseLead (p * q) - denseEraseLead p * q =
      DensePoly.monomial p.natDegree p.leadingCoeff * denseEraseLead q := by
  have hpPos : 0 < p.size := by
    have hne : p.size ≠ 0 := fun h =>
      hp ((DensePoly.size_eq_zero_iff p).mp h)
    omega
  have hqPos : 0 < q.size := by
    have hne : q.size ≠ 0 := fun h =>
      hq ((DensePoly.size_eq_zero_iff q).mp h)
    omega
  have htop : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div p.leadingCoeff q.leadingCoeff hzero with
      hzero | hzero
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size p hpPos hzero
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size q hqPos hzero
  have hsize := DensePoly.size_mul_of_top_ne p q hpPos hqPos htop
  have hlc := DensePoly.leadingCoeff_mul p q hpPos hqPos htop
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree := by
    rw [DensePoly.natDegree_eq_size_sub_one,
      DensePoly.natDegree_eq_size_sub_one,
      DensePoly.natDegree_eq_size_sub_one, hsize]
    omega
  rw [denseEraseLead, denseEraseLead, denseEraseLead, hdeg, hlc,
    ← DensePoly.monomial_mul_monomial]
  grind

private theorem denseEraseLead_mul_identity_right {p q : DensePoly R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    denseEraseLead (p * q) - p * denseEraseLead q =
      denseEraseLead p * DensePoly.monomial q.natDegree q.leadingCoeff := by
  have hpPos : 0 < p.size := by
    have hne : p.size ≠ 0 := fun h =>
      hp ((DensePoly.size_eq_zero_iff p).mp h)
    omega
  have hqPos : 0 < q.size := by
    have hne : q.size ≠ 0 := fun h =>
      hq ((DensePoly.size_eq_zero_iff q).mp h)
    omega
  have htop : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div p.leadingCoeff q.leadingCoeff hzero with
      hzero | hzero
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size p hpPos hzero
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size q hqPos hzero
  have hsize := DensePoly.size_mul_of_top_ne p q hpPos hqPos htop
  have hlc := DensePoly.leadingCoeff_mul p q hpPos hqPos htop
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree := by
    rw [DensePoly.natDegree_eq_size_sub_one,
      DensePoly.natDegree_eq_size_sub_one,
      DensePoly.natDegree_eq_size_sub_one, hsize]
    omega
  rw [denseEraseLead, denseEraseLead, denseEraseLead, hdeg, hlc,
    ← DensePoly.monomial_mul_monomial]
  grind

private theorem monomial_mul_coeff_dvd (a : R) (degree : Nat)
    (p : DensePoly R) (k : Nat) :
    a ∣ (DensePoly.monomial degree a * p).coeff k := by
  have hm : DensePoly.monomial degree a =
      DensePoly.scale a (DensePoly.monomial degree 1) := by
    apply DensePoly.ext_coeff
    intro j
    rw [DensePoly.coeff_monomial, DensePoly.coeff_scale_semiring,
      DensePoly.coeff_monomial]
    by_cases hj : j = degree
    · rw [ite_eq_left hj, ite_eq_left hj, Lean.Grind.Semiring.mul_one]
    · rw [ite_eq_right hj, ite_eq_right hj]
      have hzero : (Zero.zero : R) = 0 := rfl
      rw [hzero, Lean.Grind.Semiring.mul_zero]
  rw [hm, ← DensePoly.scale_mul, DensePoly.coeff_scale_semiring]
  refine (GcdDomainLaws.dvd_iff a _).mpr
    ⟨(DensePoly.monomial degree 1 * p).coeff k, ?_⟩
  rfl

private theorem mul_monomial_coeff_dvd (a : R) (degree : Nat)
    (p : DensePoly R) (k : Nat) :
    a ∣ (p * DensePoly.monomial degree a).coeff k := by
  rw [DensePoly.mul_comm_poly]
  exact monomial_mul_coeff_dvd a degree p k

/-- Proof-only content of a dense polynomial over a gcd domain. -/
noncomputable def denseContent (p : DensePoly R) : R :=
  chooseCoeffGcd p.toList

/-- Proof-only primitive part of a dense polynomial over a gcd domain. -/
noncomputable def densePrimitivePart (p : DensePoly R) : DensePoly R :=
  DensePoly.ofList <| p.toList.map fun a => divideDvd a (denseContent p)

/-- A dense polynomial is primitive when every common coefficient divisor is
a unit. -/
private def DensePrimitive (p : DensePoly R) : Prop :=
  ∀ d, (∀ k, d ∣ p.coeff k) → ∃ u, d * u = 1

theorem denseContent_dvd_coeff (p : DensePoly R) (k : Nat) :
    denseContent p ∣ p.coeff k := by
  by_cases hk : k < p.toList.length
  · apply chooseCoeffGcd_divides
    have hcoeff : p.toList[k] = p.coeff k := by
      have hget := DensePoly.toList_getD_eq_coeff p k
      exact (List.getElem_eq_getD (h := hk) (Zero.zero : R)).trans hget
    exact hcoeff ▸ List.getElem_mem hk
  · have hpzero : p.coeff k = 0 :=
      DensePoly.coeff_eq_zero_of_size_le p (by
        simpa [DensePoly.length_toList] using Nat.le_of_not_gt hk)
    rw [hpzero]
    apply (GcdDomainLaws.dvd_iff _ _).mpr
    exact ⟨0, (Lean.Grind.Semiring.mul_zero _).symm⟩

theorem dvd_denseContent (p : DensePoly R) (d : R)
    (hd : ∀ k, d ∣ p.coeff k) : d ∣ denseContent p := by
  apply dvd_chooseCoeffGcd
  intro x hx
  rw [DensePoly.toList_eq_coeff_range] at hx
  rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
  exact hd k

private theorem getD_map_divideDvd (p : DensePoly R) (k : Nat) :
    (p.toList.map fun a => divideDvd a (denseContent p)).getD k
        (Zero.zero : R) = divideDvd (p.coeff k) (denseContent p) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : p.toList[k]? with
  | some a =>
      have hk : k < p.toList.length := (List.getElem?_eq_some_iff.mp h).1
      have ha : a = p.coeff k := by
        rw [← DensePoly.toList_getD_eq_coeff p k,
          List.getD_eq_getElem?_getD, h, Option.getD_some]
      simp [ha]
  | none =>
      have hk : p.toList.length ≤ k := List.getElem?_eq_none_iff.mp h
      have hpzero : p.coeff k = 0 :=
        DensePoly.coeff_eq_zero_of_size_le p (by
          simpa [DensePoly.length_toList] using hk)
      simp only [Option.map_none, Option.getD_none, hpzero]
      have hzero : (Zero.zero : R) = 0 := rfl
      rw [hzero]
      rw [divideDvd, ite_eq_left rfl]

/-- Dense content times the proof-only primitive part reconstructs the input. -/
theorem denseContent_mul_primitivePart (p : DensePoly R) :
    DensePoly.scale (denseContent p) (densePrimitivePart p) = p := by
  apply DensePoly.ext_coeff
  intro k
  rw [DensePoly.coeff_scale_semiring, densePrimitivePart,
    DensePoly.coeff_ofList, getD_map_divideDvd]
  by_cases hk : k < p.toList.length
  · apply mul_divideDvd
    apply chooseCoeffGcd_divides
    have hcoeff : p.toList[k] = p.coeff k := by
      have hget := DensePoly.toList_getD_eq_coeff p k
      exact (List.getElem_eq_getD (h := hk) (Zero.zero : R)).trans hget
    exact hcoeff ▸ List.getElem_mem hk
  · have hpzero : p.coeff k = 0 :=
      DensePoly.coeff_eq_zero_of_size_le p (by
        simpa [DensePoly.length_toList] using Nat.le_of_not_gt hk)
    rw [hpzero]
    rw [divideDvd, ite_eq_left rfl]
    exact Lean.Grind.Semiring.mul_zero (denseContent p)

private theorem denseContent_ne_zero {p : DensePoly R} (hp : p ≠ 0) :
    denseContent p ≠ 0 := by
  intro hc
  apply hp
  rw [← denseContent_mul_primitivePart p, hc,
    DensePoly.scale_zero_left_semiring]

private theorem densePrimitivePart_primitive {p : DensePoly R} (hp : p ≠ 0) :
    DensePrimitive (densePrimitivePart p) := by
  intro d hd
  let c := denseContent p
  let q := densePrimitivePart p
  have hc : c ≠ 0 := denseContent_ne_zero hp
  have hcoeff : ∀ k, p.coeff k = c * q.coeff k := by
    intro k
    have h := congrArg (fun r : DensePoly R => r.coeff k)
      (denseContent_mul_primitivePart p)
    simpa [c, q, DensePoly.coeff_scale_semiring] using h.symm
  have hcd : c * d ∣ c := by
    apply dvd_denseContent p
    intro k
    rcases (GcdDomainLaws.dvd_iff d (q.coeff k)).mp (hd k) with ⟨a, ha⟩
    apply (GcdDomainLaws.dvd_iff (c * d) (p.coeff k)).mpr
    refine ⟨a, ?_⟩
    rw [hcoeff k, ha]
    grind
  rcases (GcdDomainLaws.dvd_iff (c * d) c).mp hcd with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hzero : c * (1 - d * u) = 0 := by
    calc
      c * (1 - d * u) = c - (c * d) * u := by grind
      _ = 0 := by rw [← hu]; grind
  rcases GcdDomainLaws.no_zero_div c (1 - d * u) hzero with
    hzero | hrest
  · exact False.elim (hc hzero)
  · grind

private theorem dvd_monomial_coeff (a : R) (degree k : Nat) :
    a ∣ (DensePoly.monomial degree a).coeff k := by
  rw [DensePoly.coeff_monomial]
  by_cases hk : k = degree
  · rw [ite_eq_left hk]
    apply (GcdDomainLaws.dvd_iff a a).mpr
    exact ⟨1, (Lean.Grind.Semiring.mul_one a).symm⟩
  · rw [ite_eq_right hk]
    apply (GcdDomainLaws.dvd_iff a 0).mpr
    exact ⟨0, (Lean.Grind.Semiring.mul_zero a).symm⟩

/-- The coefficient gcd is, up to a unit, the gcd of the leading coefficient
and the coefficient gcd after removing the leading monomial. -/
private theorem denseContent_lead (p : DensePoly R) :
    denseContent p ∣ pairGcd p.leadingCoeff (denseContent (denseEraseLead p)) ∧
      pairGcd p.leadingCoeff (denseContent (denseEraseLead p)) ∣ denseContent p := by
  let e := denseEraseLead p
  let a := p.leadingCoeff
  let g := pairGcd a (denseContent e)
  have ha_coeff : a = p.coeff p.natDegree := by
    unfold a DensePoly.leadingCoeff DensePoly.coeff
    rw [DensePoly.natDegree_eq_size_sub_one]
    change p.coeffs.getD (p.coeffs.size - 1) (Zero.zero : R) =
      p.coeffs.getD (p.coeffs.size - 1) (Zero.zero : R)
    rfl
  have herase : ∀ k, denseContent p ∣ e.coeff k := by
    intro k
    change denseContent p ∣
      (p - DensePoly.monomial p.natDegree p.leadingCoeff).coeff k
    rw [DensePoly.coeff_sub_ring]
    apply dvdSub (denseContent_dvd_coeff p k)
    exact dvdTrans (ha_coeff ▸ denseContent_dvd_coeff p p.natDegree)
      (dvd_monomial_coeff a p.natDegree k)
  have hleft : denseContent p ∣ g := by
    apply dvd_pairGcd
    · exact ha_coeff ▸ denseContent_dvd_coeff p p.natDegree
    · exact dvd_denseContent e _ herase
  have hright : g ∣ denseContent p := by
    apply dvd_denseContent p
    intro k
    have hge : g ∣ e.coeff k :=
      dvdTrans (pairGcd_right a (denseContent e))
        (denseContent_dvd_coeff e k)
    have hgm : g ∣ (DensePoly.monomial p.natDegree a).coeff k :=
      dvdTrans (pairGcd_left a (denseContent e))
        (dvd_monomial_coeff a p.natDegree k)
    have hsum := dvdAdd hge hgm
    have hid : e + DensePoly.monomial p.natDegree a = p := by
      unfold e a denseEraseLead
      grind
    have hcoeff := congrArg (fun r : DensePoly R => r.coeff k) hid
    rw [DensePoly.coeff_add_semiring] at hcoeff
    rwa [hcoeff] at hsum
  exact ⟨hleft, hright⟩

omit [DecidableEq R] in
private theorem unit_of_dvd_unit {a b : R} (hab : a ∣ b)
    (hb : ∃ u, b * u = 1) : ∃ u, a * u = 1 := by
  rcases (GcdDomainLaws.dvd_iff a b).mp hab with ⟨q, hq⟩
  rcases hb with ⟨u, hu⟩
  refine ⟨q * u, ?_⟩
  rw [hq] at hu
  calc
    a * (q * u) = (a * q) * u := (Lean.Grind.Semiring.mul_assoc a q u).symm
    _ = 1 := hu

private theorem densePrimitive_content_unit {p : DensePoly R}
    (hp : DensePrimitive p) : ∃ u, denseContent p * u = 1 := by
  exact hp (denseContent p) (denseContent_dvd_coeff p)

/-- Adding a polynomial whose coefficients are all divisible by `a` does not
change the gcd of `a` with polynomial content, up to a unit. -/
private theorem pairGcd_content_sub (a : R) (p q : DensePoly R)
    (hsub : ∀ k, a ∣ (p - q).coeff k) :
    pairGcd a (denseContent p) ∣ pairGcd a (denseContent q) ∧
      pairGcd a (denseContent q) ∣ pairGcd a (denseContent p) := by
  let gp := pairGcd a (denseContent p)
  let gq := pairGcd a (denseContent q)
  have hgpP : ∀ k, gp ∣ p.coeff k := fun k =>
    dvdTrans (pairGcd_right a (denseContent p)) (denseContent_dvd_coeff p k)
  have hgpSub : ∀ k, gp ∣ (p - q).coeff k := fun k =>
    dvdTrans (pairGcd_left a (denseContent p)) (hsub k)
  have hgpQ : ∀ k, gp ∣ q.coeff k := by
    intro k
    have h := dvdSub (hgpP k) (hgpSub k)
    have heq : p.coeff k - (p - q).coeff k = q.coeff k := by
      rw [DensePoly.coeff_sub_ring]
      grind
    rwa [heq] at h
  have hleft : gp ∣ gq := by
    apply dvd_pairGcd (pairGcd_left a (denseContent p))
    exact dvd_denseContent q gp hgpQ
  have hgqQ : ∀ k, gq ∣ q.coeff k := fun k =>
    dvdTrans (pairGcd_right a (denseContent q)) (denseContent_dvd_coeff q k)
  have hgqSub : ∀ k, gq ∣ (p - q).coeff k := fun k =>
    dvdTrans (pairGcd_left a (denseContent q)) (hsub k)
  have hgqP : ∀ k, gq ∣ p.coeff k := by
    intro k
    have h := dvdAdd (hgqQ k) (hgqSub k)
    have heq : q.coeff k + (p - q).coeff k = p.coeff k := by
      rw [DensePoly.coeff_sub_ring]
      grind
    rwa [heq] at h
  have hright : gq ∣ gp := by
    apply dvd_pairGcd (pairGcd_left a (denseContent q))
    exact dvd_denseContent p gq hgqP
  exact ⟨hleft, hright⟩

/-- Scaling a polynomial scales its coefficient gcd, up to a unit. -/
private theorem denseContent_scale_assoc (c : R) (p : DensePoly R) :
    c * denseContent p ∣ denseContent (DensePoly.scale c p) ∧
      denseContent (DensePoly.scale c p) ∣ c * denseContent p := by
  let cp := denseContent p
  let r := DensePoly.scale c p
  let cr := denseContent r
  have hscaled : ∀ k, c * cp ∣ r.coeff k := by
    intro k
    rcases (GcdDomainLaws.dvd_iff cp (p.coeff k)).mp
        (denseContent_dvd_coeff p k) with ⟨q, hq⟩
    apply (GcdDomainLaws.dvd_iff (c * cp) (r.coeff k)).mpr
    refine ⟨q, ?_⟩
    change (DensePoly.scale c p).coeff k = (c * cp) * q
    rw [DensePoly.coeff_scale_semiring, hq]
    grind
  have hleft : c * cp ∣ cr := dvd_denseContent r _ hscaled
  have hright : cr ∣ c * cp := by
    by_cases hc : c = 0
    · rw [hc, Lean.Grind.Semiring.zero_mul]
      apply (GcdDomainLaws.dvd_iff cr 0).mpr
      exact ⟨0, (Lean.Grind.Semiring.mul_zero cr).symm⟩
    · rcases (GcdDomainLaws.dvd_iff (c * cp) cr).mp hleft with ⟨t, ht⟩
      let n := cp * t
      have hcr : cr = c * n := by
        change cr = c * (cp * t)
        rw [ht]
        grind
      have hn : ∀ k, n ∣ p.coeff k := by
        intro k
        have hcrCoeff := denseContent_dvd_coeff r k
        rcases (GcdDomainLaws.dvd_iff cr (r.coeff k)).mp hcrCoeff with ⟨q, hq⟩
        apply (GcdDomainLaws.dvd_iff n (p.coeff k)).mpr
        refine ⟨q, ?_⟩
        have hcancel : c * (p.coeff k - n * q) = 0 := by
          calc
            c * (p.coeff k - n * q) = r.coeff k - cr * q := by
              change c * (p.coeff k - n * q) =
                (DensePoly.scale c p).coeff k - cr * q
              rw [DensePoly.coeff_scale_semiring, hcr]
              grind
            _ = 0 := by rw [← hq]; grind
        rcases GcdDomainLaws.no_zero_div c (p.coeff k - n * q) hcancel with
          hzero | hrest
        · exact False.elim (hc hzero)
        · grind
      rcases (GcdDomainLaws.dvd_iff n cp).mp (dvd_denseContent p n hn) with
        ⟨s, hs⟩
      apply (GcdDomainLaws.dvd_iff cr (c * cp)).mpr
      refine ⟨s, ?_⟩
      rw [hs, hcr]
      grind
  exact ⟨hleft, hright⟩

private theorem denseSize_scale {c : R} (hc : c ≠ 0) (p : DensePoly R) :
    (DensePoly.scale c p).size = p.size := by
  have hle : (DensePoly.scale c p).size ≤ p.size := by
    rw [DensePoly.scale_eq_scaleImpl]
    exact DensePoly.size_scaleImpl_le c p
  by_cases hp : p.size = 0
  · omega
  have hpPos : 0 < p.size := Nat.pos_of_ne_zero hp
  have htop : (DensePoly.scale c p).coeff (p.size - 1) ≠ 0 := by
    rw [DensePoly.coeff_scale_semiring]
    intro hzero
    rcases GcdDomainLaws.no_zero_div c (p.coeff (p.size - 1)) hzero with
      hzero | hzero
    · exact hc hzero
    · exact DensePoly.coeff_last_ne_zero_of_pos_size p hpPos hzero
  have hlt : p.size - 1 < (DensePoly.scale c p).size := by
    rcases Nat.lt_or_ge (p.size - 1) (DensePoly.scale c p).size with h | h
    · exact h
    · exact False.elim
        (htop (DensePoly.coeff_eq_zero_of_size_le _ h))
  omega

private theorem denseContent_zero : denseContent (0 : DensePoly R) = 0 := by
  have hzeroDvd : (0 : R) ∣ denseContent (0 : DensePoly R) := by
    apply dvd_denseContent
    intro k
    rw [DensePoly.coeff_zero]
    apply (GcdDomainLaws.dvd_iff 0 0).mpr
    exact ⟨0, (Lean.Grind.Semiring.zero_mul 0).symm⟩
  rcases (GcdDomainLaws.dvd_iff 0 (denseContent (0 : DensePoly R))).mp
      hzeroDvd with ⟨q, hq⟩
  rw [Lean.Grind.Semiring.zero_mul] at hq
  exact hq

private theorem denseContent_product_dvd (p q : DensePoly R) :
    denseContent p * denseContent q ∣ denseContent (p * q) := by
  let cp := denseContent p
  let cq := denseContent q
  let pp := densePrimitivePart p
  let pq := densePrimitivePart q
  have hpRec : DensePoly.scale cp pp = p := denseContent_mul_primitivePart p
  have hqRec : DensePoly.scale cq pq = q := denseContent_mul_primitivePart q
  have hprod : DensePoly.scale (cp * cq) (pp * pq) = p * q := by
    calc
      DensePoly.scale (cp * cq) (pp * pq) =
          DensePoly.scale cp (DensePoly.scale cq (pp * pq)) :=
        (DensePoly.scale_scale cp cq (pp * pq)).symm
      _ = DensePoly.scale cp (pp * DensePoly.scale cq pq) := by
        rw [DensePoly.mul_scale]
      _ = DensePoly.scale cp pp * DensePoly.scale cq pq := by
        rw [DensePoly.scale_mul]
      _ = p * q := by rw [hpRec, hqRec]
  apply dvd_denseContent
  intro k
  apply (GcdDomainLaws.dvd_iff (cp * cq) ((p * q).coeff k)).mpr
  refine ⟨(pp * pq).coeff k, ?_⟩
  have hcoeff := congrArg (fun r : DensePoly R => r.coeff k) hprod
  simpa [DensePoly.coeff_scale_semiring] using hcoeff.symm

/-- Gauss's lemma for dense polynomials: coefficient content is
multiplicative up to a unit. -/
theorem denseContent_mul_assoc (p q : DensePoly R) :
    denseContent (p * q) ∣ denseContent p * denseContent q ∧
      denseContent p * denseContent q ∣ denseContent (p * q) := by
  generalize hN : p.size + q.size = N
  induction N using Nat.strongRecOn generalizing p q with
  | ind N ih =>
      by_cases hp : p = 0
      · subst p
        rw [DensePoly.zero_mul, denseContent_zero,
          Lean.Grind.Semiring.zero_mul]
        exact ⟨
          (GcdDomainLaws.dvd_iff 0 0).mpr
            ⟨0, (Lean.Grind.Semiring.zero_mul 0).symm⟩,
          (GcdDomainLaws.dvd_iff 0 0).mpr
            ⟨0, (Lean.Grind.Semiring.zero_mul 0).symm⟩⟩
      by_cases hq : q = 0
      · subst q
        rw [DensePoly.mul_comm_poly, DensePoly.zero_mul, denseContent_zero,
          Lean.Grind.Semiring.mul_zero]
        exact ⟨
          (GcdDomainLaws.dvd_iff 0 0).mpr
            ⟨0, (Lean.Grind.Semiring.zero_mul 0).symm⟩,
          (GcdDomainLaws.dvd_iff 0 0).mpr
            ⟨0, (Lean.Grind.Semiring.zero_mul 0).symm⟩⟩
      let cp := denseContent p
      let cq := denseContent q
      let pp := densePrimitivePart p
      let pq := densePrimitivePart q
      have hcp : cp ≠ 0 := denseContent_ne_zero hp
      have hcq : cq ≠ 0 := denseContent_ne_zero hq
      have hpRec : DensePoly.scale cp pp = p := denseContent_mul_primitivePart p
      have hqRec : DensePoly.scale cq pq = q := denseContent_mul_primitivePart q
      have hpp : pp ≠ 0 := by
        intro hzero
        rw [hzero, DensePoly.scale_zero_right] at hpRec
        exact hp hpRec.symm
      have hpq : pq ≠ 0 := by
        intro hzero
        rw [hzero, DensePoly.scale_zero_right] at hqRec
        exact hq hqRec.symm
      have hppSize : pp.size = p.size := by
        calc
          pp.size = (DensePoly.scale cp pp).size :=
            (denseSize_scale hcp pp).symm
          _ = p.size := congrArg DensePoly.size hpRec
      have hpqSize : pq.size = q.size := by
        calc
          pq.size = (DensePoly.scale cq pq).size :=
            (denseSize_scale hcq pq).symm
          _ = q.size := congrArg DensePoly.size hqRec
      have hppPrim : DensePrimitive pp := densePrimitivePart_primitive hp
      have hpqPrim : DensePrimitive pq := densePrimitivePart_primitive hq
      have hprimUnit : ∃ u, denseContent (pp * pq) * u = 1 := by
        let ep := denseEraseLead pp
        let eq := denseEraseLead pq
        let er := denseEraseLead (pp * pq)
        let a := pp.leadingCoeff
        let b := pq.leadingCoeff
        let k := denseContent er
        let ga := pairGcd k a
        let gb := pairGcd k b
        have hppPos : 0 < pp.size := by
          have hne : pp.size ≠ 0 := fun hs =>
            hpp ((DensePoly.size_eq_zero_iff pp).mp hs)
          omega
        have hpqPos : 0 < pq.size := by
          have hne : pq.size ≠ 0 := fun hs =>
            hpq ((DensePoly.size_eq_zero_iff pq).mp hs)
          omega
        have htop : a * b ≠ 0 := by
          intro hzero
          rcases GcdDomainLaws.no_zero_div a b hzero with hzero | hzero
          · exact DensePoly.leadingCoeff_ne_zero_of_pos_size pp hppPos hzero
          · exact DensePoly.leadingCoeff_ne_zero_of_pos_size pq hpqPos hzero
        have hlc : (pp * pq).leadingCoeff = a * b :=
          DensePoly.leadingCoeff_mul pp pq hppPos hpqPos htop
        have hlead := denseContent_lead (pp * pq)
        have htoPair : denseContent (pp * pq) ∣ pairGcd k (a * b) := by
          apply dvdTrans hlead.1
          have hcomm := (pairGcd_comm_assoc (a * b) k).1
          simpa [a, b, k, er, hlc] using hcomm
        have hpair : pairGcd k (a * b) ∣ ga * gb := by
          apply gcdMulDvd k a b (pairGcd k (a * b)) ga gb
          · exact pairGcd_left k (a * b)
          · exact pairGcd_right k (a * b)
          · intro d hdk hda
            exact dvd_pairGcd hdk hda
          · intro d hdk hdb
            exact dvd_pairGcd hdk hdb
        have hsubA : ∀ j, a ∣ (er - ep * pq).coeff j := by
          intro j
          have hid := denseEraseLead_mul_identity hpp hpq
          have heq : er - ep * pq =
              DensePoly.monomial pp.natDegree a * eq := by
            simpa [er, ep, eq, a] using hid
          rw [heq]
          exact monomial_mul_coeff_dvd a pp.natDegree eq j
        have hauxA := pairGcd_content_sub a er (ep * pq) hsubA
        have hEp : ep.size < pp.size := denseEraseLead_size_lt hpp
        have hihA := ih (ep.size + pq.size) (by omega) ep pq rfl
        rcases densePrimitive_content_unit hpqPrim with ⟨uq, huq⟩
        have hdropQ :
            denseContent ep * denseContent pq ∣ denseContent ep ∧
              denseContent ep ∣ denseContent ep * denseContent pq := by
          constructor
          · apply (GcdDomainLaws.dvd_iff _ _).mpr
            refine ⟨uq, ?_⟩
            grind
          · apply (GcdDomainLaws.dvd_iff _ _).mpr
            exact ⟨denseContent pq, rfl⟩
        have hEpAssoc :
            denseContent (ep * pq) ∣ denseContent ep ∧
              denseContent ep ∣ denseContent (ep * pq) :=
          ⟨dvdTrans hihA.1 hdropQ.1, dvdTrans hdropQ.2 hihA.2⟩
        have hgcdA := pairGcd_assoc_right (a := a) hEpAssoc.1 hEpAssoc.2
        have hgaContent : ga ∣ denseContent pp := by
          apply dvdTrans (pairGcd_comm_assoc k a).1
          apply dvdTrans hauxA.1
          apply dvdTrans hgcdA.1
          exact (denseContent_lead pp).2
        have hgaUnit : ∃ u, ga * u = 1 :=
          unit_of_dvd_unit hgaContent (densePrimitive_content_unit hppPrim)
        have hsubB : ∀ j, b ∣ (er - pp * eq).coeff j := by
          intro j
          have hid := denseEraseLead_mul_identity_right hpp hpq
          have heq' : er - pp * eq =
              ep * DensePoly.monomial pq.natDegree b := by
            simpa [er, ep, eq, b] using hid
          rw [heq']
          exact mul_monomial_coeff_dvd b pq.natDegree ep j
        have hauxB := pairGcd_content_sub b er (pp * eq) hsubB
        have hEq : eq.size < pq.size := denseEraseLead_size_lt hpq
        have hihB := ih (pp.size + eq.size) (by omega) pp eq rfl
        rcases densePrimitive_content_unit hppPrim with ⟨up, hup⟩
        have hdropP :
            denseContent pp * denseContent eq ∣ denseContent eq ∧
              denseContent eq ∣ denseContent pp * denseContent eq := by
          constructor
          · apply (GcdDomainLaws.dvd_iff _ _).mpr
            refine ⟨up, ?_⟩
            grind
          · apply (GcdDomainLaws.dvd_iff _ _).mpr
            refine ⟨denseContent pp, ?_⟩
            exact Lean.Grind.CommSemiring.mul_comm _ _
        have hEqAssoc :
            denseContent (pp * eq) ∣ denseContent eq ∧
              denseContent eq ∣ denseContent (pp * eq) :=
          ⟨dvdTrans hihB.1 hdropP.1, dvdTrans hdropP.2 hihB.2⟩
        have hgcdB := pairGcd_assoc_right (a := b) hEqAssoc.1 hEqAssoc.2
        have hgbContent : gb ∣ denseContent pq := by
          apply dvdTrans (pairGcd_comm_assoc k b).1
          apply dvdTrans hauxB.1
          apply dvdTrans hgcdB.1
          exact (denseContent_lead pq).2
        have hgbUnit : ∃ u, gb * u = 1 :=
          unit_of_dvd_unit hgbContent (densePrimitive_content_unit hpqPrim)
        rcases hgaUnit with ⟨ua, hua⟩
        rcases hgbUnit with ⟨ub, hub⟩
        apply unit_of_dvd_unit (dvdTrans htoPair hpair)
        refine ⟨ub * ua, ?_⟩
        grind
      let s := cp * cq
      have hprod : DensePoly.scale s (pp * pq) = p * q := by
        calc
          DensePoly.scale s (pp * pq) =
              DensePoly.scale cp (DensePoly.scale cq (pp * pq)) := by
            exact (DensePoly.scale_scale cp cq (pp * pq)).symm
          _ = DensePoly.scale cp (pp * DensePoly.scale cq pq) := by
            rw [DensePoly.mul_scale]
          _ = DensePoly.scale cp pp * DensePoly.scale cq pq := by
            rw [DensePoly.scale_mul]
          _ = p * q := by rw [hpRec, hqRec]
      have hscale := denseContent_scale_assoc s (pp * pq)
      rcases hprimUnit with ⟨u, hu⟩
      have hscaledToS : s * denseContent (pp * pq) ∣ s := by
        apply (GcdDomainLaws.dvd_iff _ _).mpr
        refine ⟨u, ?_⟩
        grind
      have hsToScaled : s ∣ s * denseContent (pp * pq) := by
        apply (GcdDomainLaws.dvd_iff _ _).mpr
        exact ⟨denseContent (pp * pq), rfl⟩
      rw [← hprod]
      exact ⟨dvdTrans hscale.2 hscaledToS, dvdTrans hsToScaled hscale.1⟩

private theorem denseScale_cancel {c : R} (hc : c ≠ 0)
    {p q : DensePoly R} (h : DensePoly.scale c p = DensePoly.scale c q) :
    p = q := by
  apply DensePoly.ext_coeff
  intro k
  have hcoeff := congrArg (fun r : DensePoly R => r.coeff k) h
  rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_scale_semiring] at hcoeff
  have hzero : c * (p.coeff k - q.coeff k) = 0 := by grind
  rcases GcdDomainLaws.no_zero_div c (p.coeff k - q.coeff k) hzero with
    hzero | hrest
  · exact False.elim (hc hzero)
  · grind

omit [Dvd R] [GcdDomainLaws R] in
private theorem denseScale_eq_C_mul (c : R) (p : DensePoly R) :
    DensePoly.scale c p = DensePoly.C c * p := by
  have hC : DensePoly.scale c (1 : DensePoly R) = DensePoly.C c := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.coeff_scale_semiring]
    change c * (DensePoly.C 1).coeff k = (DensePoly.C c).coeff k
    simp only [DensePoly.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left hk, Lean.Grind.Semiring.mul_one]
    · rw [ite_eq_right hk, ite_eq_right hk]
      have hzero : (Zero.zero : R) = 0 := rfl
      rw [hzero, Lean.Grind.Semiring.mul_zero]
  have hone : (1 : DensePoly R) * p = p := by
    rw [DensePoly.mul_comm_poly, DensePoly.mul_one_right_poly]
  calc
    DensePoly.scale c p = DensePoly.scale c ((1 : DensePoly R) * p) := by
      rw [hone]
    _ = DensePoly.scale c 1 * p := DensePoly.scale_mul c 1 p
    _ = DensePoly.C c * p := by rw [hC]

end DenseContent

namespace MvPoly

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- The scalar coefficient list used only by proof-side content. -/
def coefficientList [Zero R] (p : MvPoly n R cmp) : List R :=
  p.termsList.map Prod.snd

/-- A polynomial is primitive when every scalar common divisor of its stored
coefficients is a unit. This is a semantic predicate, not the executable
primitive-part operation. -/
def Primitive [Lean.Grind.CommRing R] [Dvd R]
    (p : MvPoly n R cmp) : Prop :=
  ∀ d, (∀ c, c ∈ coefficientList p → d ∣ c) → ∃ u, d * u = 1

section Fraction

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [Div R] [ExactDivLaws R] [Hex.Fraction.NonzeroOne R]

/-- Coefficientwise embedding into the Mathlib-free fraction field used by
the subresultant development. -/
def fractionMap (p : MvPoly n R cmp) :
    MvPoly n (Hex.Fraction R) cmp :=
  mapCoeffs Hex.Fraction.ofCoeff p

omit [Dvd R] in
@[simp] theorem fractionMap_zero :
    fractionMap (0 : MvPoly n R cmp) = 0 := by
  exact mapCoeffs_zero Hex.Fraction.ofCoeff_zero

omit [Dvd R] in
theorem fractionMap_add (f g : MvPoly n R cmp) :
    fractionMap (f + g) = fractionMap f + fractionMap g := by
  exact mapCoeffs_add Hex.Fraction.ofCoeff_zero Hex.Fraction.ofCoeff_add f g

omit [Dvd R] in
theorem fractionMap_mul (f g : MvPoly n R cmp) :
    fractionMap (f * g) = fractionMap f * fractionMap g := by
  exact mapCoeffs_mul Hex.Fraction.ofCoeff_zero Hex.Fraction.ofCoeff_add
    Hex.Fraction.ofCoeff_mul f g

omit [BEq R] [LawfulBEq R] [Dvd R] in
theorem fractionMap_injective :
    Function.Injective (fractionMap (n := n) (R := R) (cmp := cmp)) := by
  intro p q hpq
  apply ext
  intro m
  apply Hex.Fraction.ofCoeff_injective
  have hcoeff := congrArg (coeff m) hpq
  simpa [fractionMap, Hex.Fraction.ofCoeff_zero] using hcoeff

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R]
    [Hex.Fraction.NonzeroOne R] in
private theorem fraction_exists_rep (x : Hex.Fraction R) :
    ∃ r : Hex.Fraction.Rep R, Hex.Fraction.ofRep r = x := by
  induction x using Quotient.inductionOn with
  | _ r => exact ⟨r, rfl⟩

omit [BEq R] [LawfulBEq R] [Dvd R] in
private theorem clearFractions (xs : List (Hex.Fraction R)) :
    ∃ d : R, d ≠ 0 ∧ ∃ ys : List R, ys.length = xs.length ∧
      ∀ k, Hex.Fraction.ofCoeff (ys.getD k (Zero.zero : R)) =
        Hex.Fraction.ofCoeff d *
          xs.getD k (Zero.zero : Hex.Fraction R) := by
  classical
  induction xs with
  | nil =>
      refine ⟨1, Hex.Fraction.NonzeroOne.one_ne_zero, [], rfl, ?_⟩
      intro k
      change Hex.Fraction.ofCoeff 0 =
        Hex.Fraction.ofCoeff 1 * Hex.Fraction.ofCoeff 0
      rw [← Hex.Fraction.ofCoeff_mul]
      exact congrArg Hex.Fraction.ofCoeff
        (Lean.Grind.Semiring.one_mul (0 : R)).symm
  | cons x xs ih =>
      rcases fraction_exists_rep x with ⟨r, hr⟩
      rcases ih with ⟨d, hd, ys, hlen, hys⟩
      let zs := (r.num * d) :: ys.map (fun y => r.den * y)
      refine ⟨r.den * d, ExactDivLaws.mul_ne_zero r.den_ne hd,
        zs, ?_, ?_⟩
      · simp [zs, hlen]
      · intro k
        cases k with
        | zero =>
            simp only [zs, List.getD_cons_zero]
            rw [Hex.Fraction.ofCoeff_mul, Hex.Fraction.ofCoeff_mul, ← hr]
            calc
              Hex.Fraction.ofCoeff r.num * Hex.Fraction.ofCoeff d =
                  (Hex.Fraction.ofRep r * Hex.Fraction.ofCoeff r.den) *
                    Hex.Fraction.ofCoeff d := by
                    rw [Hex.Fraction.ofRep_mul_den]
              _ = (Hex.Fraction.ofCoeff r.den * Hex.Fraction.ofCoeff d) *
                    Hex.Fraction.ofRep r := by grind
        | succ k =>
            simp only [zs, List.getD_cons_succ]
            have hmap : (ys.map (fun y => r.den * y)).getD k
                  (Zero.zero : R) =
                r.den * ys.getD k (Zero.zero : R) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_map,
                List.getD_eq_getElem?_getD]
              cases h : ys[k]? with
              | none =>
                  simp only [Option.map_none, Option.getD_none]
                  exact (Lean.Grind.Semiring.mul_zero r.den).symm
              | some y => simp
            rw [hmap]
            rw [Hex.Fraction.ofCoeff_mul, Hex.Fraction.ofCoeff_mul, hys]
            grind

omit [BEq R] [LawfulBEq R] [Dvd R] in
/-- Every fraction polynomial becomes coefficientwise integral after
multiplication by one nonzero embedded denominator. -/
theorem clearFractionPoly (p : DensePoly (Hex.Fraction R)) :
    ∃ d : R, d ≠ 0 ∧ ∃ q : DensePoly R, ∀ k,
      Hex.Fraction.ofCoeff (q.coeff k) =
        Hex.Fraction.ofCoeff d * p.coeff k := by
  classical
  rcases clearFractions p.toList with ⟨d, hd, ys, _, hys⟩
  refine ⟨d, hd, DensePoly.ofList ys, ?_⟩
  intro k
  simpa only [DensePoly.coeff_ofList,
    DensePoly.toList_getD_eq_coeff] using hys k

omit [BEq R] [LawfulBEq R] in
/-- A primitive integral polynomial that divides an integral polynomial over
the fraction field already divides it over the coefficient ring. -/
private theorem primitive_dvd_of_fraction_dvd [GcdDomainLaws R]
    {h f : DensePoly R} (hh : DensePrimitive h)
    (hdiv : DensePoly.Fraction.map h ∣ DensePoly.Fraction.map f) :
    h ∣ f := by
  rcases hdiv with ⟨z, hz⟩
  rcases clearFractionPoly z with ⟨d, hd, q, hq⟩
  have hmapQ : DensePoly.Fraction.map q =
      DensePoly.scale (Hex.Fraction.ofCoeff d) z := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.Fraction.coeff_map, DensePoly.coeff_scale_semiring]
    exact hq k
  have hmapEq : DensePoly.Fraction.map (DensePoly.scale d f) =
      DensePoly.Fraction.map (q * h) := by
    rw [DensePoly.Fraction.map_scale, DensePoly.Fraction.map_mul, hz, hmapQ]
    rw [DensePoly.mul_comm_poly (DensePoly.Fraction.map h) z,
      DensePoly.scale_mul]
  have heq : DensePoly.scale d f = q * h :=
    DensePoly.Fraction.map_injective hmapEq
  by_cases hf : f = 0
  · subst f
    exact DensePoly.dvd_zero_poly h
  let cf := denseContent f
  let fp := densePrimitivePart f
  let cq := denseContent q
  let qp := densePrimitivePart q
  have hcf : cf ≠ 0 := denseContent_ne_zero hf
  have hdcf : d * cf ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div d cf hzero with hzero | hzero
    · exact hd hzero
    · exact hcf hzero
  have hfRec : DensePoly.scale cf fp = f := denseContent_mul_primitivePart f
  have hqRec : DensePoly.scale cq qp = q := denseContent_mul_primitivePart q
  have hhUnit := densePrimitive_content_unit hh
  have hscaleContent := denseContent_scale_assoc d f
  have hmulContent := denseContent_mul_assoc q h
  have hmulDrop : denseContent q * denseContent h ∣ denseContent q ∧
      denseContent q ∣ denseContent q * denseContent h := by
    rcases hhUnit with ⟨u, hu⟩
    constructor
    · apply (GcdDomainLaws.dvd_iff _ _).mpr
      refine ⟨u, ?_⟩
      grind
    · apply (GcdDomainLaws.dvd_iff _ _).mpr
      exact ⟨denseContent h, rfl⟩
  have hcontentEq : denseContent (DensePoly.scale d f) =
      denseContent (q * h) := congrArg denseContent heq
  have hdcq : d * cf ∣ cq := by
    apply dvdTrans hscaleContent.1
    rw [hcontentEq]
    exact dvdTrans hmulContent.1 hmulDrop.1
  rcases (GcdDomainLaws.dvd_iff (d * cf) cq).mp hdcq with ⟨u, hcu⟩
  have hscaled : DensePoly.scale (d * cf) fp =
      DensePoly.scale (d * cf) (DensePoly.scale u qp * h) := by
    calc
      DensePoly.scale (d * cf) fp =
          DensePoly.scale d (DensePoly.scale cf fp) :=
        (DensePoly.scale_scale d cf fp).symm
      _ = DensePoly.scale d f := by rw [hfRec]
      _ = q * h := heq
      _ = DensePoly.scale cq qp * h := by rw [hqRec]
      _ = DensePoly.scale ((d * cf) * u) qp * h := by rw [hcu]
      _ = DensePoly.scale (d * cf) (DensePoly.scale u qp) * h := by
        rw [DensePoly.scale_scale]
      _ = DensePoly.scale (d * cf) (DensePoly.scale u qp * h) := by
        rw [DensePoly.scale_mul]
  have hfp : fp = DensePoly.scale u qp * h :=
    denseScale_cancel hdcf hscaled
  refine ⟨DensePoly.scale cf (DensePoly.scale u qp), ?_⟩
  calc
    f = DensePoly.scale cf fp := hfRec.symm
    _ = DensePoly.scale cf (DensePoly.scale u qp * h) := by rw [hfp]
    _ = DensePoly.scale cf (DensePoly.scale u qp) * h :=
      DensePoly.scale_mul cf (DensePoly.scale u qp) h
    _ = h * DensePoly.scale cf (DensePoly.scale u qp) :=
      DensePoly.mul_comm_poly _ _

omit [BEq R] [LawfulBEq R] in
/-- Every nonzero fraction polynomial is associated to the embedding of a
primitive integral polynomial. -/
private theorem fractionPoly_primitive_rep [GcdDomainLaws R]
    {H : DensePoly (Hex.Fraction R)} (hH : H ≠ 0) :
    ∃ h : DensePoly R, DensePrimitive h ∧
      H ∣ DensePoly.Fraction.map h ∧ DensePoly.Fraction.map h ∣ H := by
  rcases clearFractionPoly H with ⟨d, hd, q, hq⟩
  have hmapQ : DensePoly.Fraction.map q =
      DensePoly.scale (Hex.Fraction.ofCoeff d) H := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.Fraction.coeff_map, DensePoly.coeff_scale_semiring]
    exact hq k
  have hq0 : q ≠ 0 := by
    intro hzero
    have hscale : DensePoly.scale (Hex.Fraction.ofCoeff d) H = 0 := by
      rw [← hmapQ, hzero, DensePoly.Fraction.map_zero]
    have hHPos : 0 < H.size := by
      have hne : H.size ≠ 0 := fun hs =>
        hH ((DensePoly.size_eq_zero_iff H).mp hs)
      omega
    have hcoeff := congrArg (fun p : DensePoly (Hex.Fraction R) =>
      p.coeff (H.size - 1)) hscale
    rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_zero] at hcoeff
    have hdF : Hex.Fraction.ofCoeff d ≠ 0 := fun hz =>
      hd ((Hex.Fraction.ofCoeff_eq_zero_iff d).mp hz)
    exact (ExactDivLaws.mul_ne_zero hdF
      (DensePoly.coeff_last_ne_zero_of_pos_size H hHPos)) hcoeff
  let c := denseContent q
  let h := densePrimitivePart q
  have hc : c ≠ 0 := denseContent_ne_zero hq0
  have hqRec : DensePoly.scale c h = q := denseContent_mul_primitivePart q
  have hmaps : DensePoly.scale (Hex.Fraction.ofCoeff c)
      (DensePoly.Fraction.map h) =
      DensePoly.scale (Hex.Fraction.ofCoeff d) H := by
    calc
      DensePoly.scale (Hex.Fraction.ofCoeff c) (DensePoly.Fraction.map h) =
          DensePoly.Fraction.map (DensePoly.scale c h) :=
        (DensePoly.Fraction.map_scale c h).symm
      _ = DensePoly.Fraction.map q := by rw [hqRec]
      _ = DensePoly.scale (Hex.Fraction.ofCoeff d) H := hmapQ
  have hdF : Hex.Fraction.ofCoeff d ≠ 0 := fun hz =>
    hd ((Hex.Fraction.ofCoeff_eq_zero_iff d).mp hz)
  have hcF : Hex.Fraction.ofCoeff c ≠ 0 := fun hz =>
    hc ((Hex.Fraction.ofCoeff_eq_zero_iff c).mp hz)
  let α := (Hex.Fraction.ofCoeff d)⁻¹ * Hex.Fraction.ofCoeff c
  let β := (Hex.Fraction.ofCoeff c)⁻¹ * Hex.Fraction.ofCoeff d
  have hHscale : H = DensePoly.scale α (DensePoly.Fraction.map h) := by
    apply DensePoly.ext_coeff
    intro k
    have hs := congrArg (fun p : DensePoly (Hex.Fraction R) => p.coeff k) hmaps
    rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_scale_semiring] at hs
    rw [DensePoly.coeff_scale_semiring]
    have hdinv := Hex.Fraction.mul_inv_cancel hdF
    unfold α
    calc
      H.coeff k = 1 * H.coeff k := (Lean.Grind.Semiring.one_mul _).symm
      _ = ((Hex.Fraction.ofCoeff d)⁻¹ * Hex.Fraction.ofCoeff d) * H.coeff k := by
        grind
      _ = (Hex.Fraction.ofCoeff d)⁻¹ *
          (Hex.Fraction.ofCoeff d * H.coeff k) := by grind
      _ = (Hex.Fraction.ofCoeff d)⁻¹ *
          (Hex.Fraction.ofCoeff c * (DensePoly.Fraction.map h).coeff k) := by
        rw [hs]
      _ = ((Hex.Fraction.ofCoeff d)⁻¹ * Hex.Fraction.ofCoeff c) *
          (DensePoly.Fraction.map h).coeff k := by grind
  have hhScale : DensePoly.Fraction.map h = DensePoly.scale β H := by
    apply DensePoly.ext_coeff
    intro k
    have hs := congrArg (fun p : DensePoly (Hex.Fraction R) => p.coeff k) hmaps
    rw [DensePoly.coeff_scale_semiring, DensePoly.coeff_scale_semiring] at hs
    rw [DensePoly.coeff_scale_semiring]
    have hcinv := Hex.Fraction.mul_inv_cancel hcF
    unfold β
    calc
      (DensePoly.Fraction.map h).coeff k =
          1 * (DensePoly.Fraction.map h).coeff k :=
        (Lean.Grind.Semiring.one_mul _).symm
      _ = ((Hex.Fraction.ofCoeff c)⁻¹ * Hex.Fraction.ofCoeff c) *
          (DensePoly.Fraction.map h).coeff k := by
        grind
      _ = (Hex.Fraction.ofCoeff c)⁻¹ *
          (Hex.Fraction.ofCoeff c * (DensePoly.Fraction.map h).coeff k) := by
        grind
      _ = (Hex.Fraction.ofCoeff c)⁻¹ *
          (Hex.Fraction.ofCoeff d * H.coeff k) := by rw [hs]
      _ = ((Hex.Fraction.ofCoeff c)⁻¹ * Hex.Fraction.ofCoeff d) * H.coeff k := by
        grind
  refine ⟨h, densePrimitivePart_primitive hq0, ?_, ?_⟩
  · refine ⟨DensePoly.C β, ?_⟩
    rw [hhScale, denseScale_eq_C_mul, DensePoly.mul_comm_poly]
  · refine ⟨DensePoly.C α, ?_⟩
    rw [hHscale, denseScale_eq_C_mul, DensePoly.mul_comm_poly]

/-- Coprimality after embedding the coefficients into the fraction field. -/
def CoprimeOverFraction (f g : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ fractionMap f → d ∣ fractionMap g →
    ∃ u, d * u = 1

/-- Gcd data for univariate polynomials over the fraction field. This is a
proof-side existence package and does not select a multivariate producer. -/
structure FractionPolyGcd
    (f g : DensePoly (Hex.Fraction R)) where
  value : DensePoly (Hex.Fraction R)
  dvdLeft : value ∣ f
  dvdRight : value ∣ g
  greatest : ∀ d, d ∣ f → d ∣ g → d ∣ value

omit [BEq R] [LawfulBEq R] [Dvd R] in
private theorem fractionDivCancel
    (q : DensePoly (Hex.Fraction R)) (hq : 0 < q.size) :
    ∀ a, a - (a / q.leadingCoeff) * q.leadingCoeff = 0 := by
  intro a
  rw [Hex.Fraction.div_mul_cancel a
    (DensePoly.leadingCoeff_ne_zero_of_pos_size q hq)]
  grind

omit [BEq R] [LawfulBEq R] [Dvd R] in
private theorem fractionRemSizeLt
    (p q : DensePoly (Hex.Fraction R)) (hq : q ≠ 0) :
    (DensePoly.divMod p q).2.size < q.size := by
  have hqpos : 0 < q.size := by
    have hqsize0 : q.size ≠ 0 := by
      intro hsize
      exact hq ((DensePoly.size_eq_zero_iff q).mp hsize)
    omega
  by_cases hqsize : q.size = 1
  · have hrzero :=
      DensePoly.divMod_remainder_eq_zero_of_degree_zero_of_cancel
        p q hqsize (fractionDivCancel q hqpos)
    rw [hrzero, DensePoly.size_zero]
    exact hqpos
  · have hqdeg : 0 < q.natDegree := by
      unfold Hex.DensePoly.natDegree
      rw [DensePoly.degree?_eq_some_of_pos_size q hqpos, Option.getD_some]
      omega
    have hdeg :=
      DensePoly.divMod_remainder_degree_lt_of_pos_degree_of_cancel
        p q hqdeg (fractionDivCancel q hqpos)
    let r := (DensePoly.divMod p q).2
    change r.size < q.size
    by_cases hr : r = 0
    · rw [hr, DensePoly.size_zero]
      exact hqpos
    · have hrpos : 0 < r.size := by
        have hrsize0 : r.size ≠ 0 := by
          intro hsize
          exact hr ((DensePoly.size_eq_zero_iff r).mp hsize)
        omega
      change r.natDegree < q.natDegree at hdeg
      rw [DensePoly.natDegree_eq_size_sub_one,
        DensePoly.natDegree_eq_size_sub_one] at hdeg
      omega

omit [BEq R] [LawfulBEq R] [Dvd R] in
/-- Univariate polynomials over the coefficient fraction field admit gcds. -/
theorem fractionPolyGcd_nonempty
    (f g : DensePoly (Hex.Fraction R)) :
    Nonempty (FractionPolyGcd f g) := by
  revert f
  apply (measure DensePoly.size).wf.induction g
  intro g ih f
  by_cases hg : g = 0
  · subst g
    refine ⟨⟨f, DensePoly.dvd_refl_poly f, DensePoly.dvd_zero_poly f, ?_⟩⟩
    intro d hdf _
    exact hdf
  · let qr := DensePoly.divMod f g
    have hlt : qr.2.size < g.size := by
      simpa [qr] using fractionRemSizeLt f g hg
    rcases ih qr.2 hlt g with ⟨h⟩
    have hrec : qr.1 * g + qr.2 = f := by
      simpa [qr] using
        DensePoly.divMod_reconstruction f g
          (fractionDivCancel g (by
            have hgsize0 : g.size ≠ 0 := by
              intro hsize
              exact hg ((DensePoly.size_eq_zero_iff g).mp hsize)
            omega))
    refine ⟨⟨h.value, ?_, h.dvdLeft, ?_⟩⟩
    · rw [← hrec]
      exact DensePoly.dvd_add_poly
        (DensePoly.dvd_mul_left_poly qr.1 h.dvdLeft) h.dvdRight
    · intro d hdf hdg
      apply h.greatest d hdg
      have hdr : d ∣ f - qr.1 * g :=
        DensePoly.dvd_sub_poly hdf
          (DensePoly.dvd_mul_left_poly qr.1 hdg)
      have hr : f - qr.1 * g = qr.2 := by
        grind
      rwa [hr] at hdr

omit [BEq R] [LawfulBEq R] in
private theorem denseDvdTrans {S : Type u} [Lean.Grind.CommRing S]
    [DecidableEq S] {a b c : DensePoly S} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc
    c = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := DensePoly.mul_assoc_poly a x y

omit [BEq R] [LawfulBEq R] [Dvd R] in
private theorem fractionMap_dvd {a b : DensePoly R} (h : a ∣ b) :
    DensePoly.Fraction.map a ∣ DensePoly.Fraction.map b := by
  rcases h with ⟨q, hq⟩
  refine ⟨DensePoly.Fraction.map q, ?_⟩
  rw [hq, DensePoly.Fraction.map_mul]

omit [BEq R] [LawfulBEq R] in
private theorem fractionGcd_dvd_primitivePart [GcdDomainLaws R]
    {H : DensePoly (Hex.Fraction R)}
    {p : DensePoly R} (hp : p ≠ 0)
    (hH : H ∣ DensePoly.Fraction.map p) :
    H ∣ DensePoly.Fraction.map (densePrimitivePart p) := by
  let c := denseContent p
  let pp := densePrimitivePart p
  have hc : c ≠ 0 := denseContent_ne_zero hp
  have hrec : DensePoly.scale c pp = p := denseContent_mul_primitivePart p
  rcases hH with ⟨z, hz⟩
  have hcF : Hex.Fraction.ofCoeff c ≠ 0 := fun hzero =>
    hc ((Hex.Fraction.ofCoeff_eq_zero_iff c).mp hzero)
  let inv := (Hex.Fraction.ofCoeff c)⁻¹
  have hinv := Hex.Fraction.mul_inv_cancel hcF
  refine ⟨DensePoly.scale inv z, ?_⟩
  have hmapRec := congrArg DensePoly.Fraction.map hrec
  rw [DensePoly.Fraction.map_scale] at hmapRec
  calc
    DensePoly.Fraction.map pp =
        DensePoly.scale inv (DensePoly.Fraction.map p) := by
      apply DensePoly.ext_coeff
      intro k
      have hcoeff := congrArg
        (fun r : DensePoly (Hex.Fraction R) => r.coeff k) hmapRec
      rw [DensePoly.coeff_scale_semiring] at hcoeff
      rw [DensePoly.coeff_scale_semiring]
      unfold inv
      calc
        (DensePoly.Fraction.map pp).coeff k =
            1 * (DensePoly.Fraction.map pp).coeff k :=
          (Lean.Grind.Semiring.one_mul _).symm
        _ = ((Hex.Fraction.ofCoeff c)⁻¹ * Hex.Fraction.ofCoeff c) *
            (DensePoly.Fraction.map pp).coeff k := by grind
        _ = (Hex.Fraction.ofCoeff c)⁻¹ *
            (Hex.Fraction.ofCoeff c * (DensePoly.Fraction.map pp).coeff k) := by grind
        _ = (Hex.Fraction.ofCoeff c)⁻¹ *
            (DensePoly.Fraction.map p).coeff k := by rw [hcoeff]
    _ = DensePoly.scale inv (H * z) := by rw [hz]
    _ = H * DensePoly.scale inv z := DensePoly.mul_scale inv H z

omit [BEq R] [LawfulBEq R] [Div R] [ExactDivLaws R]
    [Hex.Fraction.NonzeroOne R] in
private theorem denseContent_dvd_of_dvd [GcdDomainLaws R]
    {a b : DensePoly R} (h : a ∣ b) :
    denseContent a ∣ denseContent b := by
  rcases h with ⟨q, hq⟩
  have hmul := denseContent_mul_assoc a q
  have hfirst : denseContent a ∣ denseContent a * denseContent q := by
    apply (GcdDomainLaws.dvd_iff _ _).mpr
    exact ⟨denseContent q, rfl⟩
  rw [← hq] at hmul
  exact dvdTrans hfirst hmul.2

omit [BEq R] [LawfulBEq R] [Div R] [ExactDivLaws R]
    [Hex.Fraction.NonzeroOne R] in
private theorem densePrimitivePart_dvd [GcdDomainLaws R] (p : DensePoly R) :
    densePrimitivePart p ∣ p := by
  refine ⟨DensePoly.C (denseContent p), ?_⟩
  calc
    p = DensePoly.scale (denseContent p) (densePrimitivePart p) :=
      (denseContent_mul_primitivePart p).symm
    _ = DensePoly.C (denseContent p) * densePrimitivePart p :=
      denseScale_eq_C_mul (denseContent p) (densePrimitivePart p)
    _ = densePrimitivePart p * DensePoly.C (denseContent p) :=
      DensePoly.mul_comm_poly _ _

omit [BEq R] [LawfulBEq R] in
/-- Dense univariate polynomials over a gcd domain admit gcds. -/
theorem densePolyGcd_nonempty [GcdDomainLaws R]
    (f g : DensePoly R) :
    ∃ d : DensePoly R, d ∣ f ∧ d ∣ g ∧
      ∀ e, e ∣ f → e ∣ g → e ∣ d := by
  by_cases hzero : f = 0 ∧ g = 0
  · rcases hzero with ⟨rfl, rfl⟩
    refine ⟨0, DensePoly.dvd_refl_poly 0, DensePoly.dvd_refl_poly 0, ?_⟩
    intro e _ _
    exact DensePoly.dvd_zero_poly e
  rcases fractionPolyGcd_nonempty
      (DensePoly.Fraction.map f) (DensePoly.Fraction.map g) with ⟨G⟩
  have hG : G.value ≠ 0 := by
    intro hvalue
    have hf0 : f = 0 := by
      apply DensePoly.Fraction.map_injective
      rcases G.dvdLeft with ⟨q, hq⟩
      rw [hvalue, DensePoly.zero_mul] at hq
      exact hq
    have hg0 : g = 0 := by
      apply DensePoly.Fraction.map_injective
      rcases G.dvdRight with ⟨q, hq⟩
      rw [hvalue, DensePoly.zero_mul] at hq
      exact hq
    exact hzero ⟨hf0, hg0⟩
  rcases fractionPoly_primitive_rep hG with ⟨h, hh, hGh, hhG⟩
  let cf := denseContent f
  let cg := denseContent g
  let c := pairGcd cf cg
  let candidate := DensePoly.scale c h
  have hpart : ∀ (p : DensePoly R), G.value ∣ DensePoly.Fraction.map p →
      h ∣ densePrimitivePart p := by
    intro p hGp
    by_cases hp : p = 0
    · subst p
      rw [densePrimitivePart]
      exact DensePoly.dvd_zero_poly h
    have hGpp := fractionGcd_dvd_primitivePart hp hGp
    have hmapDiv : DensePoly.Fraction.map h ∣
        DensePoly.Fraction.map (densePrimitivePart p) :=
      denseDvdTrans hhG hGpp
    exact primitive_dvd_of_fraction_dvd hh hmapDiv
  have hhf : h ∣ densePrimitivePart f := hpart f G.dvdLeft
  have hhg : h ∣ densePrimitivePart g := hpart g G.dvdRight
  have candidateDvd : ∀ (p : DensePoly R),
      c ∣ denseContent p → h ∣ densePrimitivePart p → candidate ∣ p := by
    intro p hcp hhp
    rcases (GcdDomainLaws.dvd_iff c (denseContent p)).mp hcp with ⟨x, hx⟩
    rcases hhp with ⟨y, hy⟩
    refine ⟨DensePoly.scale x y, ?_⟩
    calc
      p = DensePoly.scale (denseContent p) (densePrimitivePart p) :=
        (denseContent_mul_primitivePart p).symm
      _ = DensePoly.scale (c * x) (h * y) := by rw [hx, hy]
      _ = DensePoly.scale c (DensePoly.scale x (h * y)) :=
        (DensePoly.scale_scale c x (h * y)).symm
      _ = DensePoly.scale c (h * DensePoly.scale x y) := by
        rw [DensePoly.mul_scale]
      _ = DensePoly.scale c h * DensePoly.scale x y :=
        DensePoly.scale_mul c h (DensePoly.scale x y)
      _ = candidate * DensePoly.scale x y := rfl
  refine ⟨candidate,
    candidateDvd f (pairGcd_left cf cg) hhf,
    candidateDvd g (pairGcd_right cf cg) hhg, ?_⟩
  intro e hef heg
  have he0 : e ≠ 0 := by
    intro he
    have hf0 : f = 0 := by
      rcases hef with ⟨q, hq⟩
      rw [he, DensePoly.zero_mul] at hq
      exact hq
    have hg0 : g = 0 := by
      rcases heg with ⟨q, hq⟩
      rw [he, DensePoly.zero_mul] at hq
      exact hq
    exact hzero ⟨hf0, hg0⟩
  let ce := denseContent e
  let ep := densePrimitivePart e
  have hep : DensePrimitive ep := densePrimitivePart_primitive he0
  have hce : ce ∣ c := dvd_pairGcd
    (denseContent_dvd_of_dvd hef) (denseContent_dvd_of_dvd heg)
  have hepE : ep ∣ e := densePrimitivePart_dvd e
  have hepF : ep ∣ f := denseDvdTrans hepE hef
  have hepG : ep ∣ g := denseDvdTrans hepE heg
  have hmapEpG : DensePoly.Fraction.map ep ∣ G.value :=
    G.greatest (DensePoly.Fraction.map ep)
      (fractionMap_dvd hepF) (fractionMap_dvd hepG)
  have hmapEph : DensePoly.Fraction.map ep ∣ DensePoly.Fraction.map h :=
    denseDvdTrans hmapEpG hGh
  have heph : ep ∣ h := primitive_dvd_of_fraction_dvd hep hmapEph
  rcases (GcdDomainLaws.dvd_iff ce c).mp hce with ⟨x, hx⟩
  rcases heph with ⟨y, hy⟩
  refine ⟨DensePoly.scale x y, ?_⟩
  calc
    candidate = DensePoly.scale c h := rfl
    _ = DensePoly.scale (ce * x) (ep * y) := by rw [hx, hy]
    _ = DensePoly.scale ce (DensePoly.scale x (ep * y)) :=
      (DensePoly.scale_scale ce x (ep * y)).symm
    _ = DensePoly.scale ce (ep * DensePoly.scale x y) := by
      rw [DensePoly.mul_scale]
    _ = DensePoly.scale ce ep * DensePoly.scale x y :=
      DensePoly.scale_mul ce ep (DensePoly.scale x y)
    _ = e * DensePoly.scale x y := by
      rw [denseContent_mul_primitivePart]

/-- Primitive descent: fraction-field coprimality of primitive inputs rules
out every nonunit common divisor back in the coefficient ring. -/
theorem primitive_descent [GcdDomainLaws R]
    {f g d : MvPoly n R cmp}
    (hf : Primitive f)
    (hcop : CoprimeOverFraction f g)
    (hdf : d ∣ f) (hdg : d ∣ g) :
    ∃ u, d * u = 1 := by
  have hmapDvdF : fractionMap d ∣ fractionMap f := by
    rcases hdf with ⟨q, hq⟩
    refine ⟨fractionMap q, ?_⟩
    calc
      fractionMap f = fractionMap (q * d) := congrArg fractionMap hq
      _ = fractionMap q * fractionMap d := fractionMap_mul q d
  have hmapDvdG : fractionMap d ∣ fractionMap g := by
    rcases hdg with ⟨q, hq⟩
    refine ⟨fractionMap q, ?_⟩
    calc
      fractionMap g = fractionMap (q * d) := congrArg fractionMap hq
      _ = fractionMap q * fractionMap d := fractionMap_mul q d
  rcases hcop (fractionMap d) hmapDvdF hmapDvdG with ⟨q, hdq⟩
  have hFracOne : (1 : Hex.Fraction R) ≠ 0 :=
    fun h => Hex.Fraction.zero_ne_one h.symm
  have hFracNoZero : ∀ a b : Hex.Fraction R,
      a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      by_cases hb : b = 0
      · exact hb
      · exact False.elim ((ExactDivLaws.mul_ne_zero ha hb) hab)
  rcases unit_eq_C hFracOne hFracNoZero hdq with ⟨_, _, hdConst, _⟩
  let c := coeff Mono.zero d
  have hdc : d = C c := by
    apply ext
    intro m
    by_cases hm : m = Mono.zero
    · subst m
      rw [coeff_C]
      simp only [ite_true]
      rfl
    · rw [coeff_C, ite_eq_right hm]
      have hcoeff := congrArg (coeff m) hdConst
      rw [fractionMap, coeff_mapCoeffs Hex.Fraction.ofCoeff_zero,
        coeff_C, ite_eq_right hm] at hcoeff
      exact (Hex.Fraction.ofCoeff_eq_zero_iff (coeff m d)).mp hcoeff
  rcases hdf with ⟨a, ha⟩
  have hcommon : ∀ x, x ∈ coefficientList f → c ∣ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨term, hterm, rfl⟩
    rcases term with ⟨m, x⟩
    have hcoeff : coeff m f = x := coeff_eq_of_mem_terms f hterm
    apply (GcdDomainLaws.dvd_iff c x).mpr
    refine ⟨coeff m a, ?_⟩
    calc
      x = coeff m f := hcoeff.symm
      _ = coeff m (a * d) := congrArg (coeff m) ha
      _ = coeff m (C c * a) := by rw [hdc, MvPoly.mul_comm]
      _ = c * coeff m a := coeff_C_mul c a m
  rcases hf c hcommon with ⟨u, hcu⟩
  refine ⟨C u, ?_⟩
  rw [hdc]
  change monomial Mono.zero c * monomial Mono.zero u = 1
  rw [monomial_mul_monomial, Mono.zero_mul, hcu]
  rfl

end Fraction

section Lift

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdDomainLaws R]

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R]
    [GcdDomainLaws R] in
private theorem vars_eq_nil_zero
    {cmp0 : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]
    (p : MvPoly 0 R cmp0) : p.vars = [] := by
  cases h : p.vars with
  | nil => rfl
  | cons i is => exact Fin.elim0 i

/-- At arity zero, coefficient gcds are polynomial gcds. -/
theorem gcdExists_zero
    {cmp0 : Mono 0 → Mono 0 → Ordering}
    [Std.TransCmp cmp0] [Std.LawfulEqCmp cmp0]
    (a b : MvPoly 0 R cmp0) : ∃ g : MvPoly 0 R cmp0,
    g ∣ a ∧ g ∣ b ∧ ∀ d, d ∣ a → d ∣ b → d ∣ g := by
  let ca := coeff Mono.zero a
  let cb := coeff Mono.zero b
  rcases GcdDomainLaws.gcd_exists ca cb with ⟨c, hca, hcb, hgreat⟩
  have ha : a = C ca := eq_C_of_vars_eq_nil a (vars_eq_nil_zero a)
  have hb : b = C cb := eq_C_of_vars_eq_nil b (vars_eq_nil_zero b)
  refine ⟨C c, ?_, ?_, ?_⟩
  · rcases (GcdDomainLaws.dvd_iff c ca).mp hca with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [ha, hq]
    unfold C
    rw [monomial_mul_monomial, Mono.zero_mul]
    exact congrArg (monomial Mono.zero)
      (Lean.Grind.CommSemiring.mul_comm c q)
  · rcases (GcdDomainLaws.dvd_iff c cb).mp hcb with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [hb, hq]
    unfold C
    rw [monomial_mul_monomial, Mono.zero_mul]
    exact congrArg (monomial Mono.zero)
      (Lean.Grind.CommSemiring.mul_comm c q)
  · intro d hda hdb
    have hd : d = C (coeff Mono.zero d) :=
      eq_C_of_vars_eq_nil d (vars_eq_nil_zero d)
    rcases hda with ⟨qa, hqa⟩
    rcases hdb with ⟨qb, hqb⟩
    have hdca : coeff Mono.zero d ∣ ca := by
      apply (GcdDomainLaws.dvd_iff _ _).mpr
      refine ⟨coeff Mono.zero qa, ?_⟩
      have hcoeff := congrArg (coeff Mono.zero) hqa
      rw [ha, coeff_C, ite_eq_left rfl, hd,
        MvPoly.mul_comm qa, coeff_C_mul] at hcoeff
      exact hcoeff
    have hdcb : coeff Mono.zero d ∣ cb := by
      apply (GcdDomainLaws.dvd_iff _ _).mpr
      refine ⟨coeff Mono.zero qb, ?_⟩
      have hcoeff := congrArg (coeff Mono.zero) hqb
      rw [hb, coeff_C, ite_eq_left rfl, hd,
        MvPoly.mul_comm qb, coeff_C_mul] at hcoeff
      exact hcoeff
    rcases (GcdDomainLaws.dvd_iff _ _).mp
        (hgreat (coeff Mono.zero d) hdca hdcb) with ⟨q, hq⟩
    refine ⟨C q, ?_⟩
    rw [hd, hq]
    unfold C
    rw [monomial_mul_monomial, Mono.zero_mul]
    exact congrArg (monomial Mono.zero)
      (Lean.Grind.CommSemiring.mul_comm (coeff Mono.zero d) q)

omit [Dvd R] [GcdDomainLaws R] in
private theorem ofUnivariate_mul_zero
    {m : Nat} {sourceCmp : Mono (m + 1) → Mono (m + 1) → Ordering}
    {cmp' : Mono m → Mono m → Ordering}
    [Std.TransCmp sourceCmp] [Std.LawfulEqCmp sourceCmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p q : DensePoly (MvPoly m R cmp')) :
    ofUnivariate (cmp := sourceCmp) 0 cmp' (p * q) =
      ofUnivariate (cmp := sourceCmp) 0 cmp' p *
        ofUnivariate (cmp := sourceCmp) 0 cmp' q := by
  have hinj : Function.Injective
      (toUnivariate (R := R) (cmp := sourceCmp) 0 cmp') := by
    intro a b hab
    calc
      a = ofUnivariate (cmp := sourceCmp) 0 cmp'
          (toUnivariate 0 cmp' a) :=
        (ofUnivariate_toUnivariate 0 a).symm
      _ = ofUnivariate (cmp := sourceCmp) 0 cmp'
          (toUnivariate 0 cmp' b) := by rw [hab]
      _ = b := ofUnivariate_toUnivariate 0 b
  apply hinj
  rw [toUnivariate_ofUnivariate, toUnivariate_mul,
    toUnivariate_ofUnivariate, toUnivariate_ofUnivariate]

omit [Dvd R] [GcdDomainLaws R] in
private theorem ofUnivariate_dvd_zero
    {m : Nat} {sourceCmp : Mono (m + 1) → Mono (m + 1) → Ordering}
    {cmp' : Mono m → Mono m → Ordering}
    [Std.TransCmp sourceCmp] [Std.LawfulEqCmp sourceCmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    {p q : DensePoly (MvPoly m R cmp')} (h : p ∣ q) :
    ofUnivariate (cmp := sourceCmp) 0 cmp' p ∣
      ofUnivariate (cmp := sourceCmp) 0 cmp' q := by
  rcases h with ⟨r, hr⟩
  refine ⟨ofUnivariate (cmp := sourceCmp) 0 cmp' r, ?_⟩
  calc
    ofUnivariate (cmp := sourceCmp) 0 cmp' q =
        ofUnivariate (cmp := sourceCmp) 0 cmp' (p * r) := by rw [hr]
    _ = ofUnivariate (cmp := sourceCmp) 0 cmp' p *
        ofUnivariate (cmp := sourceCmp) 0 cmp' r :=
      ofUnivariate_mul_zero p r
    _ = ofUnivariate (cmp := sourceCmp) 0 cmp' r *
        ofUnivariate (cmp := sourceCmp) 0 cmp' p := MvPoly.mul_comm _ _

omit [Dvd R] [GcdDomainLaws R] in
private theorem toUnivariate_dvd_zero
    {m : Nat} {sourceCmp : Mono (m + 1) → Mono (m + 1) → Ordering}
    {cmp' : Mono m → Mono m → Ordering}
    [Std.TransCmp sourceCmp] [Std.LawfulEqCmp sourceCmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    {p q : MvPoly (m + 1) R sourceCmp} (h : p ∣ q) :
    toUnivariate 0 cmp' p ∣ toUnivariate 0 cmp' q := by
  rcases h with ⟨r, hr⟩
  refine ⟨toUnivariate 0 cmp' r, ?_⟩
  calc
    toUnivariate 0 cmp' q = toUnivariate 0 cmp' (r * p) := by rw [hr]
    _ = toUnivariate 0 cmp' r * toUnivariate 0 cmp' p :=
      toUnivariate_mul 0 r p
    _ = toUnivariate 0 cmp' p * toUnivariate 0 cmp' r :=
      DensePoly.mul_comm_poly _ _

/-- Gauss's lemma lifts proof-only gcd-domain structure through every finite
multivariate arity. -/
theorem gcdDomainLaws : GcdDomainLaws (MvPoly n R cmp) := by
  induction n with
  | zero =>
      refine {
        dvd_iff := ?_
        one_ne_zero := ?_
        no_zero_div := ?_
        gcd_exists := gcdExists_zero }
      · intro a b
        constructor
        · rintro ⟨q, hq⟩
          exact ⟨q, hq.trans (MvPoly.mul_comm q a)⟩
        · rintro ⟨q, hq⟩
          exact ⟨q, hq.trans (MvPoly.mul_comm a q)⟩
      · intro hone
        have hcoeff := congrArg (coeff (Mono.zero : Mono 0)) hone
        rw [coeff_one, coeff_zero, ite_eq_left rfl] at hcoeff
        exact GcdDomainLaws.one_ne_zero hcoeff
      · intro a b hab
        exact MvPoly.zero_product GcdDomainLaws.no_zero_div hab
  | succ n ih =>
      letI lowerGcd : GcdDomainLaws (MvPoly n R Mono.lex) :=
        ih (cmp := Mono.lex)
      -- The fraction-field proof deliberately uses the locally chosen exact
      -- quotient. No executable `GcdOps` or polynomial `Div` is in scope here.
      letI proofDiv : Div (MvPoly n R Mono.lex) := ⟨divideDvd⟩
      letI lowerExact : ExactDivLaws (MvPoly n R Mono.lex) :=
        ⟨by
          intro a b hb
          change divideDvd (a * b) b = a
          have hdiv : b ∣ a * b := by
            apply (GcdDomainLaws.dvd_iff b (a * b)).mpr
            exact ⟨a, MvPoly.mul_comm a b⟩
          have hmul : b * divideDvd (a * b) b = a * b :=
            mul_divideDvd hdiv
          have hzero : b * (divideDvd (a * b) b - a) = 0 := by grind
          rcases GcdDomainLaws.no_zero_div b
              (divideDvd (a * b) b - a) hzero with hzero | hcancel
          · exact False.elim (hb hzero)
          · grind⟩
      letI lowerNonzero : Hex.Fraction.NonzeroOne (MvPoly n R Mono.lex) :=
        ⟨GcdDomainLaws.one_ne_zero⟩
      refine {
        dvd_iff := ?_
        one_ne_zero := ?_
        no_zero_div := ?_
        gcd_exists := ?_ }
      · intro a b
        constructor
        · rintro ⟨q, hq⟩
          exact ⟨q, hq.trans (MvPoly.mul_comm q a)⟩
        · rintro ⟨q, hq⟩
          exact ⟨q, hq.trans (MvPoly.mul_comm a q)⟩
      · intro hone
        have hcoeff := congrArg (coeff (Mono.zero : Mono (n + 1))) hone
        rw [coeff_one, coeff_zero, ite_eq_left rfl] at hcoeff
        exact GcdDomainLaws.one_ne_zero hcoeff
      · intro a b hab
        exact MvPoly.zero_product GcdDomainLaws.no_zero_div hab
      · intro a b
        rcases densePolyGcd_nonempty
            (toUnivariate 0 Mono.lex a) (toUnivariate 0 Mono.lex b) with
          ⟨d, hda, hdb, hgreat⟩
        refine ⟨ofUnivariate (cmp := cmp) 0 Mono.lex d, ?_, ?_, ?_⟩
        · have hdA := ofUnivariate_dvd_zero
            (R := R) (m := n) (sourceCmp := cmp) (cmp' := Mono.lex) hda
          rw [ofUnivariate_toUnivariate] at hdA
          exact hdA
        · have hdB := ofUnivariate_dvd_zero
            (R := R) (m := n) (sourceCmp := cmp) (cmp' := Mono.lex) hdb
          rw [ofUnivariate_toUnivariate] at hdB
          exact hdB
        · intro e hea heb
          have heA := toUnivariate_dvd_zero
            (R := R) (m := n) (sourceCmp := cmp) (cmp' := Mono.lex) hea
          have heB := toUnivariate_dvd_zero
            (R := R) (m := n) (sourceCmp := cmp) (cmp' := Mono.lex) heb
          have heD := ofUnivariate_dvd_zero
            (R := R) (m := n) (sourceCmp := cmp) (cmp' := Mono.lex)
            (hgreat (toUnivariate 0 Mono.lex e)
              heA heB)
          rw [ofUnivariate_toUnivariate] at heD
          exact heD

instance (priority := 100) instGcdDomainLawsMvPoly :
    GcdDomainLaws (MvPoly n R cmp) :=
  gcdDomainLaws

/-- The lifted gcd-domain laws supply the common-factor cancellation used by
checked gcd maximality. -/
theorem coprimeCancelLaws : CoprimeCancelLaws (MvPoly n R cmp) := by
  exact coprimeCancelOfGcdDomain

instance (priority := 100) instCoprimeCancelLawsMvPoly :
    CoprimeCancelLaws (MvPoly n R cmp) :=
  coprimeCancelLaws

/-- Named common-factor step consumed by `CheckedGcdResult.greatest`. -/
theorem cancelCommonFactor
    (g a b d : MvPoly n R cmp)
    (hcop : ∀ e, e ∣ a → e ∣ b → ∃ u, e * u = 1)
    (hda : d ∣ g * a) (hdb : d ∣ g * b) : d ∣ g := by
  exact CoprimeCancelLaws.cancel_coprime g a b d hcop hda hdb

end Lift

section NormalizeAssoc

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R] [LawfulGcdOps R] [IsMonomialOrder cmp]

/-- Mutually divisible polynomials have the same canonical normalization. -/
theorem eq_polyNormalize_of_dvd (a b : MvPoly n R cmp)
    (ha : polyNormalize a = a) (hab : a ∣ b) (hba : b ∣ a) :
    a = polyNormalize b := by
  rcases hab with ⟨q, hbq⟩
  by_cases hazero : a = 0
  · have hbzero : b = 0 := by
      calc
        b = q * a := hbq
        _ = 0 := by rw [hazero, MvPoly.mul_zero]
    rw [hazero, hbzero, polyNormalize_zero]
  · rcases hba with ⟨r, har⟩
    have hqr : q * r = 1 := by
      have hzero : (q * r - 1) * a = 0 := by
        rw [har, hbq]
        grind
      rcases GcdDomainLaws.no_zero_div (q * r - 1) a hzero with
        hrest | haz
      · grind
      · exact False.elim (hazero haz)
    have hqunit : polyIsUnit q = true :=
      (polyIsUnit_iff q).mpr ⟨r, hqr⟩
    symm
    calc
      polyNormalize b = polyNormalize (q * a) := congrArg polyNormalize hbq
      _ = polyNormalize q * polyNormalize a := polyNormalize_mul q a
      _ = 1 * a := by rw [polyNormalize_unit q hqunit, ha]
      _ = a := MvPoly.one_mul a

end NormalizeAssoc

end MvPoly

end Hex
