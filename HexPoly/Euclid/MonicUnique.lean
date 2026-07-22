/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Euclid.DivGcd
public import HexPoly.Euclid.Reconstruction

public section

/-!
Uniqueness of monic (Euclidean) division for `DensePoly` over a commutative ring.

`divMod_eq_of_reconstruction` says any reconstruction `q * g + r = num` with a
positive-degree divisor `g` whose leading coefficient is a two-sided unit for the
`Div`/`Mul` structure and with remainder of degree below `g` must be `divMod num g`.
This is the ring-hom-free counterpart of `Polynomial.div_modByMonic_unique`; the
proof reduces the difference of two reconstructions to a single division that is
simultaneously `(quotient-difference, 0)` (via `divMod_eq_of_polynomial_mul`) and
`(0, remainder-difference)` (via the degree short circuit), forcing both to vanish.
-/

namespace Hex
namespace DensePoly

/-- Right distributivity of multiplication over subtraction (Mathlib-free shim:
`DensePoly` carries only `Lean.Grind.CommRing`). -/
theorem sub_mul_poly {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S]
    (a b c : DensePoly S) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg_poly a b, mul_add_left_poly a (0 - b) c,
    mul_comm_poly (0 - b) c, mul_sub_zero_comm c b,
    ← sub_eq_add_neg_poly (a * c) (b * c)]

/-- The `degree?`-getD of a difference of two polynomials each of degree below a
positive-degree `g` is again below `g`. -/
theorem degree_getD_sub_lt {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S]
    (a b g : DensePoly S)
    (hg : 0 < g.degree?.getD 0)
    (ha : a.degree?.getD 0 < g.degree?.getD 0)
    (hb : b.degree?.getD 0 < g.degree?.getD 0) :
    (a - b).degree?.getD 0 < g.degree?.getD 0 := by
  -- `g` has size ≥ 2, and `g.degree?.getD 0 = g.size - 1`.
  have hg_pos : 0 < g.size := by
    rcases Nat.eq_zero_or_pos g.size with h0 | h0
    · have hz : g.degree?.getD 0 = 0 := by
        rw [(degree?_eq_none_iff g).mpr h0, Option.getD_none]
      omega
    · exact h0
  have hg_deg : g.degree?.getD 0 = g.size - 1 := by
    rw [degree?_eq_some_of_pos_size g hg_pos, Option.getD_some]
  -- Any polynomial of degree below `g` has size ≤ g.size - 1.
  have size_le : ∀ (p : DensePoly S), p.degree?.getD 0 < g.degree?.getD 0 →
      p.size ≤ g.size - 1 := by
    intro p hp
    rcases Nat.eq_zero_or_pos p.size with hps | hps
    · omega
    · have hpd : p.degree?.getD 0 = p.size - 1 := by
        rw [degree?_eq_some_of_pos_size p hps, Option.getD_some]
      rw [hpd, hg_deg] at hp
      omega
  have ha_size := size_le a ha
  have hb_size := size_le b hb
  -- Every coefficient of `a - b` at index ≥ g.size - 1 vanishes.
  have hzero : ∀ i, g.size - 1 ≤ i → (a - b).coeff i = (0 : S) := by
    intro i hi
    rw [coeff_sub_ring a b i,
      coeff_eq_zero_of_size_le a (by omega), coeff_eq_zero_of_size_le b (by omega)]
    grind
  -- Hence `a - b` has size ≤ g.size - 1.
  have hsub_size : (a - b).size ≤ g.size - 1 := by
    rcases Nat.lt_or_ge (g.size - 1) (a - b).size with h | h
    · exfalso
      have hlast : g.size - 1 ≤ (a - b).size - 1 := by omega
      exact coeff_last_ne_zero_of_pos_size (a - b) (by omega) (hzero _ hlast)
    · exact h
  -- Conclude on `degree?`.
  rcases Nat.eq_zero_or_pos (a - b).size with hs | hs
  · have hz : (a - b).degree?.getD 0 = 0 := by
      rw [(degree?_eq_none_iff (a - b)).mpr hs, Option.getD_none]
    omega
  · rw [degree?_eq_some_of_pos_size (a - b) hs, hg_deg]
    simp only [Option.getD_some]
    omega

/-- Uniqueness of Euclidean division by a positive-degree divisor whose leading
coefficient is a two-sided unit (in particular, a monic divisor): a reconstruction
with a small remainder is `divMod`. -/
theorem divMod_eq_of_reconstruction {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (num g q r : DensePoly S)
    (hg : 0 < g.degree?.getD 0)
    (hcancel : ∀ a : S, a - (a / g.leadingCoeff) * g.leadingCoeff = (Zero.zero : S))
    (hexact : ∀ a : S, (a * g.leadingCoeff) / g.leadingCoeff = a)
    (h_top_ne : ∀ a : S, a ≠ (Zero.zero : S) → a * g.leadingCoeff ≠ (Zero.zero : S))
    (hrec : q * g + r = num)
    (hrdeg : r.degree?.getD 0 < g.degree?.getD 0) :
    divMod num g = (q, r) := by
  -- The actual quotient/remainder.
  rcases hqr : divMod num g with ⟨q', r'⟩
  have hrec' : q' * g + r' = num := by
    have h := divMod_reconstruction num g hcancel
    rw [hqr] at h; exact h
  have hr'deg : r'.degree?.getD 0 < g.degree?.getD 0 := by
    have h := divMod_remainder_degree_lt_of_pos_degree_core num g hg hcancel
    rw [hqr] at h; exact h
  -- Difference identity: `(q - q') * g = r' - r`.
  have hmul : (q - q') * g = r' - r := by
    rw [sub_mul_poly q q' g]
    apply ext_coeff
    intro n
    have hz2 : (0 : S) + (0 : S) = 0 := by grind
    have hcoeff : (q * g).coeff n + r.coeff n = (q' * g).coeff n + r'.coeff n := by
      have h := congrArg (fun p => DensePoly.coeff p n)
        (show q * g + r = q' * g + r' from by rw [hrec, hrec'])
      rw [coeff_add _ _ n hz2, coeff_add _ _ n hz2] at h
      exact h
    rw [coeff_sub_ring, coeff_sub_ring]
    grind
  -- One division, two incompatible values unless both differences vanish.
  have hdegd : (r' - r).degree?.getD 0 < g.degree?.getD 0 :=
    degree_getD_sub_lt r' r g hg hr'deg hrdeg
  have hA : divMod (r' - r) g = (q - q', 0) :=
    divMod_eq_of_polynomial_mul (r' - r) g (q - q') hg hexact h_top_ne hmul
  have hB : divMod (r' - r) g = (0, r' - r) :=
    divMod_eq_zero_self_of_degree_lt (r' - r) g hdegd
  rw [hA] at hB
  have hqq : q - q' = 0 := (Prod.mk.injEq _ _ _ _ ▸ hB).1
  have hrr : (0 : DensePoly S) = r' - r := (Prod.mk.injEq _ _ _ _ ▸ hB).2
  have hqeq : q' = q := by
    apply ext_coeff
    intro n
    have h := congrArg (fun p => DensePoly.coeff p n) hqq
    rw [coeff_sub_ring, coeff_zero] at h
    grind
  have hreq : r' = r := by
    apply ext_coeff
    intro n
    have h := congrArg (fun p => DensePoly.coeff p n) hrr.symm
    rw [coeff_sub_ring, coeff_zero] at h
    grind
  rw [hqeq, hreq]

end DensePoly
end Hex
