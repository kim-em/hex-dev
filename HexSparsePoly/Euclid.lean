/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePoly.Eval

@[expose] public section
set_option backward.proofsInPublic true

/-!
Gcd and division for canonical sparse polynomials, defined by conversion
through `DensePoly`. No claim is made that any of this stays sparse: the
cost is the dense cost at the degree plus the `O(n)` conversions,
whatever the term count, and the SPEC's "convert-gcd" bench family is
the measurement that decides whether a sparse division algorithm would
ever pay for itself. The one operation that does stay sparse is
`divMonomial?`.
-/

namespace Hex

open scoped Hex

universe u

namespace SparsePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Divide by a monic divisor, through the dense representation: two
`toDense` and two `ofDense` conversions around `DensePoly.divModMonic`. -/
def divModMonic [One R] [Add R] [Sub R] [Mul R] (s t : SparsePoly R)
    (ht : t.Monic) : SparsePoly R × SparsePoly R :=
  ((DensePoly.divModMonic s.toDense t.toDense
      ((monic_toDense t).mpr ht)).map ofDense ofDense)

/-- Field-style division with remainder, through the dense
representation. -/
def divMod [One R] [Add R] [Sub R] [Mul R] [Div R] (s t : SparsePoly R) :
    SparsePoly R × SparsePoly R :=
  ((DensePoly.divMod s.toDense t.toDense).map ofDense ofDense)

/-- Euclidean gcd, through the dense representation: the dense cost at
the degree, whatever the term count. A caller with a two-term input of
degree `10^6` should expect this to cost what a dense gcd at degree
`10^6` costs. -/
def gcd [One R] [Add R] [Sub R] [Mul R] [Div R] (s t : SparsePoly R) :
    SparsePoly R :=
  ofDense (DensePoly.gcd s.toDense t.toDense)

/-- Exact division by a monic divisor: `divModMonic` with a
zero-remainder test. -/
def divExactMonic? [One R] [Add R] [Sub R] [Mul R] (s t : SparsePoly R)
    (ht : t.Monic) : Option (SparsePoly R) :=
  let qr := divModMonic s t ht
  if qr.2 = 0 then some qr.1 else none

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Div (SparsePoly R) where
  div s t := (divMod s t).1

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Mod (SparsePoly R) where
  mod s t := (divMod s t).2

/-- Divide by the monomial `x^e`, the one division that stays sparse:
`none` unless every stored exponent is at least `e`, and otherwise a
subtraction on each exponent, `O(s)` with no filtering. -/
def divMonomial? (s : SparsePoly R) (e : Nat) :
    Option (SparsePoly R) :=
  if h : ∀ t ∈ s.terms.toList, e ≤ t.1 then
    some (ofCanonicalList
      (mapTerms (fun x => x - e) (fun _ c => c) s.terms.toList)
      (mapTerms_canonical s.pairwise_toList
        (fun a ha b hb hab => by
          have := h a ha
          have := h b hb
          omega)).1
      (mapTerms_canonical s.pairwise_toList
        (fun a ha b hb hab => by
          have := h a ha
          have := h b hb
          omega)).2)
  else none

/-- Multiplying back by the monomial undoes {name}`divMonomial?`. -/
theorem mulMonomial_divMonomial {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] {s q : SparsePoly C} {e : Nat}
    (h : divMonomial? s e = some q) : mulMonomial e 1 q = s := by
  unfold divMonomial? at h
  split at h
  · rename_i hall
    cases h
    apply ext_coeff
    intro f
    rw [coeff_mulMonomial, coeff_ofCanonicalList]
    by_cases hef : e ≤ f
    · rw [if_pos hef]
      have happly := coeffList_mapTerms_apply (g := fun x => x - e)
        (f := fun _ c => c) (l := s.terms.toList) (e := f)
        s.pairwise_toList
        (fun u hu hgu => by
          have := hall u hu
          omega)
        rfl
      rw [show f - e = (fun x => x - e) f from rfl, happly]
      have hone : (1 : C) * coeffList s.terms.toList f =
          coeffList s.terms.toList f := by
        grind
      rw [hone]
      rfl
    · rw [if_neg hef]
      have hzero : s.coeff f = 0 :=
        coeffList_eq_zero fun u hu huf => by
          have := hall u hu
          omega
      rw [hzero]
  · cases h

section Laws

variable {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]

omit [Div S] in
/-- Divisibility transports back from the dense representation. -/
theorem dvd_of_toDense_dvd {s t : SparsePoly S}
    (h : s.toDense ∣ t.toDense) : s ∣ t := by
  obtain ⟨r, hr⟩ := h
  exact ⟨ofDense r, toDense_inj (by
    rw [toDense_mul, toDense_ofDense, hr])⟩

omit [Div S] in
/-- Divisibility transports to the dense representation. -/
theorem toDense_dvd {s t : SparsePoly S} (h : s ∣ t) :
    s.toDense ∣ t.toDense := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r.toDense, by rw [← toDense_mul, ← hr]⟩

omit [Div S] in
/-- The degree transports through `ofDense`. -/
theorem degree?_ofDense (p : DensePoly S) :
    (ofDense p).degree? = p.degree? := by
  rw [← degree?_toDense, toDense_ofDense]

variable [DensePoly.DivModLaws S]

/-- The quotient and remainder reconstruct the dividend, transported
from `DensePoly.DivModLaws`. -/
theorem divMod_spec (s t : SparsePoly S) :
    (divMod s t).1 * t + (divMod s t).2 = s := by
  apply toDense_inj
  rw [toDense_add, toDense_mul]
  unfold divMod
  simp only [Prod.map_fst, Prod.map_snd, toDense_ofDense]
  exact DensePoly.divMod_spec s.toDense t.toDense

/-- The remainder degree drops below a positive divisor degree,
transported from `DensePoly.DivModLaws`. -/
theorem divMod_degree_lt (s t : SparsePoly S)
    (h : 0 < t.degree?.getD 0) :
    (divMod s t).2.degree?.getD 0 < t.degree?.getD 0 := by
  unfold divMod
  simp only [Prod.map_snd]
  rw [degree?_ofDense, ← degree?_toDense t]
  rw [← degree?_toDense t] at h
  exact DensePoly.DivModLaws.divMod_remainder_degree_lt_of_pos_degree
    s.toDense t.toDense h

/-- The monic division satisfies the division identity. It carries
`[Div S]` and `[DivModLaws S]` even though {name}`divModMonic` does not,
and that is not an oversight: the dense layer proves the monic identity
by routing through `divMod`, so there is no unconditional dense
statement to transport. -/
theorem divModMonic_spec (s t : SparsePoly S) (ht : t.Monic) :
    (divModMonic s t ht).1 * t + (divModMonic s t ht).2 = s := by
  apply toDense_inj
  rw [toDense_add, toDense_mul]
  unfold divModMonic
  simp only [Prod.map_fst, Prod.map_snd, toDense_ofDense]
  rw [DensePoly.DivModLaws.divModMonic_eq_divMod_of_monic s.toDense
    t.toDense ((monic_toDense t).mpr ht)]
  exact DensePoly.divMod_spec s.toDense t.toDense

/-- Divisibility forces a zero monic remainder: the dense mod of a
multiple is zero, and the sparse remainder is its `ofDense` image. -/
private theorem divModMonic_snd_eq_zero_of_dvd {s t : SparsePoly S}
    (ht : t.Monic) (h : t ∣ s) : (divModMonic s t ht).2 = 0 := by
  unfold divModMonic
  simp only [Prod.map_snd]
  rw [DensePoly.DivModLaws.divModMonic_eq_divMod_of_monic s.toDense
    t.toDense ((monic_toDense t).mpr ht)]
  have hm : (DensePoly.divMod s.toDense t.toDense).2 = 0 :=
    DensePoly.mod_eq_zero_of_dvd s.toDense t.toDense (toDense_dvd h)
  rw [hm, ofDense_zero]

omit [Div S] [DensePoly.DivModLaws S] in
/-- Monic factors cancel at the dense level: a product with a monic
polynomial vanishes only if the cofactor does. The trivial-ring case is
split off; otherwise the product's leading coefficient is the
cofactor's, which a nonzero cofactor keeps nonzero. -/
private theorem dense_eq_zero_of_mul_monic {u g : DensePoly S}
    (hg : g.Monic) (h : u * g = 0) : u = 0 := by
  by_cases h10 : (1 : S) = 0
  · apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    have h1 : u.coeff n * (1 : S) = u.coeff n := by grind
    rw [← h1, h10]
    grind
  · by_cases hu : u.size = 0
    · apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le u (by omega)
    · exfalso
      have hupos : 0 < u.size := Nat.pos_of_ne_zero hu
      have hgpos : 0 < g.size := by
        rcases Nat.eq_zero_or_pos g.size with h0 | h0
        · exfalso
          apply h10
          have hlz : g.leadingCoeff = 0 := by
            have : g = 0 := by
              apply DensePoly.ext_coeff
              intro n
              rw [DensePoly.coeff_zero]
              exact DensePoly.coeff_eq_zero_of_size_le g (by omega)
            rw [this, DensePoly.leadingCoeff_zero]
          rw [← DensePoly.leadingCoeff_eq_one_of_monic hg, hlz]
        · exact h0
      have hlu : u.leadingCoeff ≠ (Zero.zero : S) := by
        rw [DensePoly.leadingCoeff_eq_coeff_last u hupos]
        exact DensePoly.coeff_last_ne_zero_of_pos_size u hupos
      have hprod : u.leadingCoeff * g.leadingCoeff ≠ (Zero.zero : S) := by
        rw [DensePoly.leadingCoeff_eq_one_of_monic hg]
        grind
      have hlm := DensePoly.leadingCoeff_mul u g hupos hgpos hprod
      rw [h, DensePoly.leadingCoeff_zero,
        DensePoly.leadingCoeff_eq_one_of_monic hg] at hlm
      apply hlu
      show u.leadingCoeff = (0 : S)
      grind

/-- Exact monic division returns exactly the cofactors: the forward
direction is the division identity with a zero remainder, the reverse
is dense monic cancellation applied to the two reconstructions. -/
theorem divExactMonic?_eq_some {s t q : SparsePoly S} (ht : t.Monic) :
    divExactMonic? s t ht = some q ↔ s = q * t := by
  show (if (divModMonic s t ht).2 = 0 then some (divModMonic s t ht).1
    else none) = some q ↔ s = q * t
  constructor
  · intro h
    by_cases hr : (divModMonic s t ht).2 = 0
    · rw [if_pos hr, Option.some.injEq] at h
      have hspec := divModMonic_spec s t ht
      rw [hr, add_zero, h] at hspec
      exact hspec.symm
    · rw [if_neg hr] at h
      cases h
  · intro hs
    have hdvd : t ∣ s := ⟨q, by rw [hs, mul_comm]⟩
    have hr := divModMonic_snd_eq_zero_of_dvd ht hdvd
    rw [if_pos hr, Option.some.injEq]
    have hspec := divModMonic_spec s t ht
    rw [hr, add_zero] at hspec
    have hqt : (divModMonic s t ht).1 * t = q * t := by rw [hspec, hs]
    apply toDense_inj
    have hsub : ((divModMonic s t ht).1.toDense - q.toDense) * t.toDense
        = 0 := by
      rw [DensePoly.sub_mul_poly, ← toDense_mul, ← toDense_mul, hqt]
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero]
      grind
    have hz := dense_eq_zero_of_mul_monic ((monic_toDense t).mpr ht) hsub
    apply DensePoly.ext_coeff
    intro n
    have hc := congrArg (fun p => DensePoly.coeff p n) hz
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_zero] at hc
    grind

/-- Exact monic division succeeds exactly on multiples. A monic divisor
is nonzero, so no `t ≠ 0` side condition is needed. -/
theorem divExactMonic?_isSome {s t : SparsePoly S} (ht : t.Monic) :
    (divExactMonic? s t ht).isSome = true ↔ t ∣ s := by
  show (if (divModMonic s t ht).2 = 0 then some (divModMonic s t ht).1
    else none).isSome = true ↔ t ∣ s
  constructor
  · intro h
    by_cases hr : (divModMonic s t ht).2 = 0
    · have hspec := divModMonic_spec s t ht
      rw [hr, add_zero] at hspec
      refine ⟨(divModMonic s t ht).1, ?_⟩
      rw [mul_comm]
      exact hspec.symm
    · rw [if_neg hr] at h
      cases h
  · intro hdvd
    rw [if_pos (divModMonic_snd_eq_zero_of_dvd ht hdvd)]
    rfl

end Laws

section GcdLaws

variable {S : Type u} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
  [DensePoly.GcdLaws S]

/-- The gcd divides the left argument, transported from
`DensePoly.GcdLaws`. -/
theorem gcd_dvd_left (s t : SparsePoly S) : gcd s t ∣ s := by
  refine dvd_of_toDense_dvd ?_
  unfold gcd
  rw [toDense_ofDense]
  exact DensePoly.GcdLaws.gcd_dvd_left s.toDense t.toDense

/-- The gcd divides the right argument. -/
theorem gcd_dvd_right (s t : SparsePoly S) : gcd s t ∣ t := by
  refine dvd_of_toDense_dvd ?_
  unfold gcd
  rw [toDense_ofDense]
  exact DensePoly.GcdLaws.gcd_dvd_right s.toDense t.toDense

/-- Common divisors divide the gcd. -/
theorem dvd_gcd {d s t : SparsePoly S} (hs : d ∣ s) (ht : d ∣ t) :
    d ∣ gcd s t := by
  refine dvd_of_toDense_dvd ?_
  unfold gcd
  rw [toDense_ofDense]
  exact DensePoly.GcdLaws.dvd_gcd d.toDense s.toDense t.toDense
    (toDense_dvd hs) (toDense_dvd ht)

end GcdLaws

end SparsePoly

end Hex
