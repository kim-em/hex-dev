/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Grind.Ring.Basic
public import Init.Data.List.Lemmas
public import HexPoly.Operations
public import HexPoly.Euclid.Content
import all HexPoly.Euclid.DivGcd
import all HexPoly.Euclid.MulRing
import all HexPoly.Euclid.Reconstruction
public import HexPoly.Euclid.MonicUnique
import all HexPoly.Euclid.Content

public section
set_option backward.proofsInPublic true

/-!
Executable Euclidean-algorithm operations for dense array-backed
polynomials. The division/gcd algorithms, ring structure, and integer
content machinery live in the `HexPoly.Euclid.*` submodules imported
above; this module adds the existential polynomial CRT construction and
Gauss's lemma on content multiplicativity for `DensePoly Int`.
-/
namespace Hex

universe u

namespace DensePoly
/-- Construct a polynomial with prescribed residues modulo coprime factors.

If `s * a + t * b = 1`, then `polyCRT a b u v s t` is congruent to `u`
modulo `a` and to `v` modulo `b`; see `polyCRT_congr_fst`,
`polyCRT_congr_snd`, `polyCRT_mod_fst`, and `polyCRT_mod_snd`. -/
@[expose]
def polyCRT {S : Type _} [Zero S] [DecidableEq S] [One S] [Add S] [Mul S]
    (a b u v s t : DensePoly S) : DensePoly S :=
  u * t * b + v * s * a

/-- `Congr p q m` means `p` and `q` differ by a multiple of `m`. -/
@[expose]
def Congr {S : Type _} [Zero S] [DecidableEq S] [Add S] [Sub S] [Mul S]
    (p q m : DensePoly S) : Prop :=
  m ∣ (p - q)

/-- Expresses the gap `p % m - p` as the explicit multiple `m * (0 - p / m)`, the witness
underlying the congruence `m ∣ (p % m - p)`. -/
private theorem mod_sub_self_eq_mul_neg_div {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p m : DensePoly S) :
    p % m - p = m * (0 - p / m) := by
  have hdiv : (p / m) * m + (p % m) = p := div_mul_add_mod p m
  apply ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly S => x.coeff n) hdiv
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  change (((p / m) * m + (p % m)).coeff n = p.coeff n) at hcoeff
  rw [coeff_add ((p / m) * m) (p % m) n hzero_add] at hcoeff
  rw [coeff_sub (p % m) p n hzero_sub,
    mul_sub_zero_comm m (p / m), coeff_sub 0 ((p / m) * m) n hzero_sub, coeff_zero]
  grind

/-- Packages `mod_sub_self_eq_mul_neg_div` as the divisibility `m ∣ (p % m - p)`, the core
fact behind the public `congr_mod`. -/
private theorem congr_mod_core {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (p m : DensePoly S) :
    m ∣ (p % m - p) := by
  exact ⟨0 - p / m, mod_sub_self_eq_mul_neg_div p m⟩

/-- Reduction modulo the modulus is congruent to the original polynomial over a lawful
coefficient ring. -/
theorem congr_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    (p m : DensePoly S) :
    Congr (p % m) p m := by
  exact congr_mod_core p m

/-- Rearranges a difference-as-multiple `p - q = m * r` into the additive form
`p = q + m * r`. -/
private theorem eq_add_mul_of_sub_eq_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {p q m r : DensePoly S} :
    p - q = m * r -> p = q + m * r := by
  intro hsub
  apply ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly S => x.coeff n) hsub
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  change (p - q).coeff n = (m * r).coeff n at hcoeff
  rw [coeff_sub p q n hzero_sub] at hcoeff
  rw [coeff_add q (m * r) n hzero_add]
  grind

/-- Right identity of polynomial addition, `p + 0 = p`. -/
private theorem add_zero_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p 0 n hzero_add]
  simp
  grind

/-- Left absorption of the zero polynomial under multiplication, `0 * p = 0`. -/
private theorem zero_mul_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) * p = 0 := by
  change mul 0 p = 0
  have hzero : (0 : DensePoly S).coeffs = #[] := rfl
  simp [mul, isZero, hzero]

/-- A modulus reduces to `0` against itself, `m % m = 0`. -/
private theorem mod_self_eq_zero {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m : DensePoly S) :
    m % m = 0 := by
  exact DivModLaws.mod_self_eq_zero m

/-- The zero polynomial reduces to `0` modulo any `m`, `0 % m = 0`. -/
private theorem zero_mod_eq_zero {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m : DensePoly S) :
    (0 : DensePoly S) % m = 0 := by
  change (divMod (0 : DensePoly S) m).2 = 0
  unfold divMod
  have hzero : (0 : DensePoly S).coeffs = #[] := rfl
  have hdeg_zero : (0 : DensePoly S).degree?.getD 0 = 0 := by
    simp [degree?, size, hzero]
  rw [hdeg_zero]
  by_cases hpos : 0 < m.degree?.getD 0
  · simp [hpos]
  · rw [if_neg hpos]
    unfold divModArray
    simp [hzero, isZero, size, toArray, divModArrayAux]

/-- Divisibility of a difference `m ∣ (p - q)` forces equal canonical remainders
`p % m = q % m`. -/
private theorem mod_eq_mod_of_dvd_sub {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    {p q m : DensePoly S} :
    m ∣ (p - q) -> p % m = q % m := by
  exact DivModLaws.mod_eq_mod_of_congr p q m

/-- Congruent polynomials have the same canonical remainder once the divisor law package
supplies the executable `%` invariants. -/
theorem mod_eq_mod_of_congr {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    {p q m : DensePoly S} :
    Congr p q m -> p % m = q % m := by
  exact mod_eq_mod_of_dvd_sub

/-- Reverse direction of `mod_eq_mod_of_congr`: equal canonical remainders force the
operands to be congruent modulo the divisor. -/
theorem dvd_of_mod_eq_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    {p q m : DensePoly S} (h : p % m = q % m) :
    m ∣ (p - q) := by
  refine ⟨(p / m) - (q / m), ?_⟩
  apply ext_coeff
  intro n
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  have hp := congrArg (fun x : DensePoly S => x.coeff n) (div_mul_add_mod p m)
  have hq := congrArg (fun x : DensePoly S => x.coeff n) (div_mul_add_mod q m)
  have hh := congrArg (fun x : DensePoly S => x.coeff n) h
  change ((p / m) * m + (p % m)).coeff n = p.coeff n at hp
  change ((q / m) * m + (q % m)).coeff n = q.coeff n at hq
  change (p % m).coeff n = (q % m).coeff n at hh
  rw [coeff_add ((p / m) * m) (p % m) n hzero_add] at hp
  rw [coeff_add ((q / m) * m) (q % m) n hzero_add] at hq
  rw [coeff_sub p q n hzero_sub]
  -- Reduce m * ((p/m) - (q/m)) via mul_sub_zero_comm-style manipulation.
  have hgoal :
      (m * ((p / m) - (q / m))).coeff n =
        ((p / m) * m).coeff n - ((q / m) * m).coeff n := by
    rw [show m * ((p / m) - (q / m)) = (p / m) * m + (0 - (q / m) * m) from ?_]
    · rw [coeff_add ((p / m) * m) (0 - (q / m) * m) n hzero_add]
      rw [coeff_sub 0 ((q / m) * m) n hzero_sub, coeff_zero]
      grind
    · -- m * (a - b) = a * m + (0 - b * m), via sub_eq_add_neg + mul_sub_zero_comm + mul_comm.
      rw [sub_eq_add_neg_poly, mul_add_right_poly, mul_sub_zero_comm m (q / m),
        mul_comm_poly m (p / m)]
  rw [hgoal]
  grind

/-- Equal canonical remainders produce polynomial congruence modulo the divisor. -/
theorem congr_of_mod_eq_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S]
    [Div S] [DivModLaws S]
    {p q m : DensePoly S} (h : p % m = q % m) :
    Congr p q m := by
  exact dvd_of_mod_eq_mod h

/-- Polynomial congruence modulo `m` is equivalent to equality of canonical remainders. -/
theorem mod_eq_mod_iff_congr {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S]
    [Div S] [DivModLaws S]
    {p q m : DensePoly S} :
    p % m = q % m ↔ Congr p q m := by
  constructor
  · exact congr_of_mod_eq_mod
  · exact mod_eq_mod_of_congr

/-- Reducing both summands before addition preserves the canonical remainder. -/
theorem mod_add_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    (p q m : DensePoly S) :
    (p + q) % m = ((p % m) + (q % m)) % m := by
  exact DivModLaws.mod_add_mod p q m

/-- Reducing both factors before multiplication preserves the canonical remainder. -/
theorem mod_mul_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    (p q m : DensePoly S) :
    (p * q) % m = ((p % m) * (q % m)) % m := by
  exact DivModLaws.mod_mul_mod p q m

/-- Any multiple of `m` reduces to `0` modulo `m`, `(m * r) % m = 0`. -/
private theorem mod_mul_self_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m r : DensePoly S) :
    (m * r) % m = 0 := by
  rw [mod_mul_mod, mod_self_eq_zero, zero_mul_left, zero_mod_eq_zero]

/-- Adding a multiple of `m` leaves the canonical remainder unchanged,
`(q + m * r) % m = q % m`. -/
private theorem mod_add_mul_self {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (q m r : DensePoly S) :
    (q + m * r) % m = q % m := by
  apply mod_eq_mod_of_congr
  exact ⟨r, by
    apply ext_coeff
    intro n
    have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
    have hzero_add : (0 : S) + (0 : S) = 0 := by grind
    rw [coeff_sub (q + m * r) q n hzero_sub, coeff_add q (m * r) n hzero_add, coeff_mul]
    grind⟩

/-- Under the Bezout hypothesis `s * a + t * b = 1`, exhibits `polyCRT a b u v s t - u` as
the explicit multiple `a * (v * s + (0 - u * s))`, the witness for congruence to `u`
modulo `a`. -/
private theorem polyCRT_sub_left_factor {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (a b u v s t : DensePoly S) :
    s * a + t * b = 1 ->
    polyCRT a b u v s t - u = a * (v * s + (0 - u * s)) := by
  intro hbez
  have hu_bez : u * (s * a + t * b) = u := by
    rw [hbez, mul_one_right_poly]
  calc
    polyCRT a b u v s t - u =
        (u * t * b + v * s * a) - u * (s * a + t * b) := by
          rw [hu_bez]
          rfl
    _ = (u * t * b + v * s * a) - (u * (s * a) + u * (t * b)) := by
          rw [mul_add_right_poly]
    _ = (u * t * b + v * s * a) - (u * s * a + u * t * b) := by
          rw [← mul_assoc_poly u s a, ← mul_assoc_poly u t b]
    _ = v * s * a + (0 - u * s * a) := by
          rw [add_sub_add_swap (u * t * b) (v * s * a) (u * s * a)]
    _ = (v * s + (0 - u * s)) * a := by
          rw [mul_add_left_poly, neg_mul_right_poly]
    _ = a * (v * s + (0 - u * s)) := by
          rw [mul_comm_poly]

/-- Under the Bezout hypothesis `s * a + t * b = 1`, exhibits `polyCRT a b u v s t - v` as
the explicit multiple `b * (u * t + (0 - v * t))`, the witness for congruence to `v`
modulo `b`. -/
private theorem polyCRT_sub_right_factor {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (a b u v s t : DensePoly S) :
    s * a + t * b = 1 ->
    polyCRT a b u v s t - v = b * (u * t + (0 - v * t)) := by
  intro hbez
  have hv_bez : v * (s * a + t * b) = v := by
    rw [hbez, mul_one_right_poly]
  calc
    polyCRT a b u v s t - v =
        (u * t * b + v * s * a) - v * (s * a + t * b) := by
          rw [hv_bez]
          rfl
    _ = (u * t * b + v * s * a) - (v * (s * a) + v * (t * b)) := by
          rw [mul_add_right_poly]
    _ = (u * t * b + v * s * a) - (v * s * a + v * t * b) := by
          rw [← mul_assoc_poly v s a, ← mul_assoc_poly v t b]
    _ = (v * s * a + u * t * b) - (v * s * a + v * t * b) := by
          rw [add_comm_poly (u * t * b) (v * s * a)]
    _ = u * t * b + (0 - v * t * b) := by
          rw [add_sub_add_left (v * s * a) (u * t * b) (v * t * b)]
    _ = (u * t + (0 - v * t)) * b := by
          rw [mul_add_left_poly, neg_mul_right_poly]
    _ = b * (u * t + (0 - v * t)) := by
          rw [mul_comm_poly]

/-- The CRT witness is congruent to the prescribed first residue modulo `a`. -/
theorem polyCRT_congr_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) u a := by
  intro S _ _ a b u v s t hbez
  unfold Congr polyCRT
  refine ⟨v * s + (0 - u * s), ?_⟩
  exact polyCRT_sub_left_factor a b u v s t hbez

/-- The CRT witness is congruent to the prescribed second residue modulo `b`. -/
theorem polyCRT_congr_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) v b := by
  intro S _ _ a b u v s t hbez
  unfold Congr polyCRT
  refine ⟨u * t + (0 - v * t), ?_⟩
  exact polyCRT_sub_right_factor a b u v s t hbez

/-- The CRT witness reduces to the prescribed first residue modulo `a` via monic reduction. -/
theorem polyCRT_modByMonic_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) a ha = modByMonic u a ha := by
  intro S _ _ _ _ a b u v s t ha hbez
  rw [modByMonic_eq_mod, modByMonic_eq_mod]
  exact mod_eq_mod_of_congr (polyCRT_congr_fst a b u v s t hbez)

/-- The CRT witness reduces to the prescribed first residue modulo `a`. -/
theorem polyCRT_mod_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % a = u % a := by
  intro S _ _ _ _ a b u v s t ha hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_fst a b u v s t ha hbez

/-- The CRT witness reduces to the prescribed second residue modulo `b` via monic reduction. -/
theorem polyCRT_modByMonic_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) b hb = modByMonic v b hb := by
  intro S _ _ _ _ a b u v s t hb hbez
  rw [modByMonic_eq_mod, modByMonic_eq_mod]
  exact mod_eq_mod_of_congr (polyCRT_congr_snd a b u v s t hbez)

/-- The CRT witness reduces to the prescribed second residue modulo `b`. -/
theorem polyCRT_mod_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % b = v % b := by
  intro S _ _ _ _ a b u v s t hb hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_snd a b u v s t hb hbez

/-! ## Gauss's lemma on content multiplicativity for `DensePoly Int`. -/

/-- Local primality predicate for `Nat`. `HexPoly` is foundational and does not
public import the `Hex.Nat.Prime` API; we keep a private copy of just enough machinery
to formulate Gauss's lemma on integer polynomial content. -/
private def NatPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

private theorem natPrime_coprime_of_not_dvd {p a : Nat} (hp : NatPrime p)
    (ha : ¬ p ∣ a) : Nat.Coprime p a := by
  rw [Nat.Coprime]
  have hgcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exact absurd (hgcd ▸ Nat.gcd_dvd_right p a) ha

/-- Euclid's lemma for `Nat`. -/
private theorem natPrime_dvd_mul {p a b : Nat} (hp : NatPrime p)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hb : p ∣ b
  · exact Or.inr hb
  · exact Or.inl ((natPrime_coprime_of_not_dvd hp hb).dvd_of_dvd_mul_right h)

/-- Euclid's lemma carried through `Int.natAbs`. -/
private theorem natPrime_dvd_mul_int {p : Nat} {a b : Int} (hp : NatPrime p)
    (h : (p : Int) ∣ a * b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases natPrime_dvd_mul hp h with hN | hN
  · left; rw [Int.ofNat_dvd_left]; exact hN
  · right; rw [Int.ofNat_dvd_left]; exact hN

/-- Every natural number greater than `1` has a prime divisor. -/
private theorem exists_natPrime_dvd_of_one_lt :
    ∀ (n : Nat), 1 < n → ∃ r, NatPrime r ∧ r ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      by_cases hprime : NatPrime n
      · exact ⟨n, hprime, Nat.dvd_refl n⟩
      · -- `n` is composite: extract a proper divisor manually (no `push_neg`).
        have h2 : 2 ≤ n := hn
        have hcomp : ∃ m : Nat, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
          apply Classical.byContradiction
          intro hno
          apply hprime
          refine ⟨h2, ?_⟩
          intro m hm
          apply Classical.byContradiction
          intro hcases
          apply hno
          refine ⟨m, hm, ?_, ?_⟩
          · intro hm1; exact hcases (Or.inl hm1)
          · intro hmn; exact hcases (Or.inr hmn)
        rcases hcomp with ⟨m, hmd, hm1, hmn⟩
        have hm0 : m ≠ 0 := by
          intro hm0
          subst hm0
          have hn_zero : n = 0 := Nat.eq_zero_of_zero_dvd hmd
          omega
        have hmlt : m < n := by
          have hpos : 0 < n := by omega
          have hle : m ≤ n := Nat.le_of_dvd hpos hmd
          omega
        have hm_one_lt : 1 < m := by
          cases m with
          | zero => exact absurd rfl hm0
          | succ m' =>
              cases m' with
              | zero => exact absurd rfl hm1
              | succ _ => omega
        rcases ih m hmlt hm_one_lt with ⟨r, hrp, hrm⟩
        exact ⟨r, hrp, Nat.dvd_trans hrm hmd⟩

/-- Polynomial Euclid's lemma. If a prime divides every coefficient of `p * q`,
then it divides every coefficient of `p` or every coefficient of `q`. -/
private theorem natPrime_dvd_all_or_all_of_dvd_mul_coeff
    {r : Nat} (hr : NatPrime r) (p q : DensePoly Int)
    (h : ∀ n, (r : Int) ∣ (p * q).coeff n) :
    (∀ i, (r : Int) ∣ p.coeff i) ∨ (∀ j, (r : Int) ∣ q.coeff j) := by
  apply Classical.byContradiction
  intro hno
  have hp_some : ∃ i, ¬ (r : Int) ∣ p.coeff i := by
    apply Classical.byContradiction
    intro hpno
    apply hno
    left
    intro i
    apply Classical.byContradiction
    intro hi
    exact hpno ⟨i, hi⟩
  have hq_some : ∃ j, ¬ (r : Int) ∣ q.coeff j := by
    apply Classical.byContradiction
    intro hqno
    apply hno
    right
    intro j
    apply Classical.byContradiction
    intro hj
    exact hqno ⟨j, hj⟩
  rcases exists_last_not_natCast_dvd_coeff p r hp_some with ⟨i0, hni0, hi_above⟩
  rcases exists_last_not_natCast_dvd_coeff q r hq_some with ⟨j0, hnj0, hj_above⟩
  have hsplit : (r : Int) ∣ p.coeff i0 * q.coeff j0 :=
    dvd_coeff_mul_last_of_dvd_mul_coeff_of_dvd_larger_left_products
      p q r i0 j0 (h (i0 + j0)) hj_above
      (fun a ha => Int.dvd_mul_of_dvd_left (hi_above a ha))
  rcases natPrime_dvd_mul_int hr hsplit with hpi | hqj
  · exact hni0 hpi
  · exact hnj0 hqj

/-- Content-level form of polynomial Euclid: if a prime divides every coefficient
of `p * q`, it divides the content of `p` or the content of `q`. -/
private theorem natPrime_dvd_contentNat_or_dvd_contentNat_of_dvd_mul
    {r : Nat} (hr : NatPrime r) (p q : DensePoly Int)
    (h : ∀ n, (r : Int) ∣ (p * q).coeff n) :
    r ∣ contentNat p ∨ r ∣ contentNat q := by
  rcases natPrime_dvd_all_or_all_of_dvd_mul_coeff hr p q h with hp | hq
  · exact Or.inl (dvd_contentNat_of_dvd_coeff p r hp)
  · exact Or.inr (dvd_contentNat_of_dvd_coeff q r hq)

/-- Helper: a foldl over `List.range (k+1)` whose terms vanish below `k`
collapses to the final term. -/
private theorem foldl_add_int_eq_last_of_below_zero
    (g : Nat → Int) (k : Nat)
    (h : ∀ i, i < k → g i = 0) :
    (List.range (k + 1)).foldl (fun acc i => acc + g i) 0 = g k := by
  have hzero : ∀ m, m ≤ k →
      (List.range m).foldl (fun acc i => acc + g i) 0 = 0 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m' ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (Nat.le_of_succ_le hm)]
        have hg : g m' = 0 := h m' (Nat.lt_of_succ_le hm)
        rw [hg]
        grind
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hzero k (Nat.le_refl k)]
  grind

/-- Helper variant of `foldl_add_int_eq_last_of_below_zero` indexed by the
foldl bound rather than the (bound - 1). -/
private theorem foldl_add_int_eq_at_predecessor
    (g : Nat → Int) (psize : Nat) (hpsize : 0 < psize)
    (h : ∀ i, i < psize - 1 → g i = 0) :
    (List.range psize).foldl (fun acc i => acc + g i) 0 = g (psize - 1) := by
  have hpsize_eq : psize - 1 + 1 = psize := by omega
  rw [← hpsize_eq]
  exact foldl_add_int_eq_last_of_below_zero g (psize - 1) h

/-- The top coefficient of a product of nonzero integer polynomials is the product of
their leading coefficients. -/
theorem coeff_mul_top_int (p q : DensePoly Int)
    (hp : 0 < p.size) (hq : 0 < q.size) :
    (p * q).coeff (p.size - 1 + (q.size - 1)) =
      p.coeff (p.size - 1) * q.coeff (q.size - 1) := by
  rw [coeff_mul, mulCoeffSum_eq_diagonal, foldl_add_int_eq_at_predecessor _ p.size hp]
  · unfold diagonalMulCoeffTerm
    have hno : ¬ (p.size - 1 + (q.size - 1)) < p.size - 1 := by omega
    rw [if_neg hno]
    have hsub : p.size - 1 + (q.size - 1) - (p.size - 1) = q.size - 1 := by omega
    rw [hsub]
  · intro i hi
    unfold diagonalMulCoeffTerm
    have hno : ¬ (p.size - 1 + (q.size - 1)) < i := by omega
    rw [if_neg hno]
    have hsub : (p.size - 1 + (q.size - 1)) - i ≥ q.size := by omega
    rw [coeff_eq_zero_of_size_le q hsub]
    show p.coeff i * (0 : Int) = 0
    rw [Int.mul_zero]

/-- Integral domain property for integer polynomials. -/
theorem mul_ne_zero_int (p q : DensePoly Int)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    p * q ≠ 0 := by
  have hp_size : 0 < p.size := by
    rcases Nat.lt_or_ge 0 p.size with h | h
    · exact h
    · exfalso
      apply hp
      have hsize : p.size = 0 := by omega
      apply ext_coeff
      intro n
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le p (by omega)
  have hq_size : 0 < q.size := by
    rcases Nat.lt_or_ge 0 q.size with h | h
    · exact h
    · exfalso
      apply hq
      have hsize : q.size = 0 := by omega
      apply ext_coeff
      intro n
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le q (by omega)
  intro hpq0
  have htop := coeff_mul_top_int p q hp_size hq_size
  have hpq_top_zero : (p * q).coeff (p.size - 1 + (q.size - 1)) = 0 := by
    rw [hpq0]; exact coeff_zero _
  rw [hpq_top_zero] at htop
  -- 0 = lead(p) * lead(q), but both leading coefficients are nonzero
  have hlp_ne := coeff_last_ne_zero_of_pos_size p hp_size
  have hlq_ne := coeff_last_ne_zero_of_pos_size q hq_size
  rcases Int.mul_eq_zero.mp htop.symm with h | h
  · exact hlp_ne h
  · exact hlq_ne h

/-- Integral domain property: for primitive integer polynomials, the product
is nonzero. -/
private theorem mul_ne_zero_of_primitive (p q : DensePoly Int)
    (hp : content p = 1) (hq : content q = 1) :
    p * q ≠ 0 := by
  have hcp_ne_zero : content p ≠ 0 := by rw [hp]; decide
  have hcq_ne_zero : content q ≠ 0 := by rw [hq]; decide
  have hp_ne : p ≠ 0 := by
    intro hp0
    apply hcp_ne_zero
    rw [hp0, content_zero]
  have hq_ne : q ≠ 0 := by
    intro hq0
    apply hcq_ne_zero
    rw [hq0, content_zero]
  exact mul_ne_zero_int p q hp_ne hq_ne

/-- Factoring a constant out of a `diagonalMulCoeffTerm` foldl with `scale`'d
polynomials. -/
private theorem foldl_add_int_diagonal_scaled
    (a b : Int) (r s : DensePoly Int) (n : Nat) :
    ∀ m, (List.range m).foldl
        (fun acc i => acc + diagonalMulCoeffTerm (scale a r) (scale b s) n i) 0 =
      a * b * (List.range m).foldl
        (fun acc i => acc + diagonalMulCoeffTerm r s n i) 0
  | 0 => by simp
  | m' + 1 => by
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_add_int_diagonal_scaled a b r s n m']
      have hterm : diagonalMulCoeffTerm (scale a r) (scale b s) n m' =
          a * b * diagonalMulCoeffTerm r s n m' := by
        unfold diagonalMulCoeffTerm
        by_cases hn : n < m'
        · simp [hn]
        · rw [if_neg hn]
          rw [coeff_scale a r m' (Int.mul_zero a), coeff_scale b s (n - m') (Int.mul_zero b)]
          grind
      rw [hterm]
      grind

/-- Coefficient identity: scaling both factors of a product. -/
private theorem coeff_scale_mul_scale (a b : Int) (r s : DensePoly Int) (n : Nat) :
    ((scale a r) * (scale b s)).coeff n = a * b * (r * s).coeff n := by
  rw [coeff_mul (scale a r) (scale b s) n, coeff_mul r s n]
  rw [mulCoeffSum_eq_diagonal (scale a r) (scale b s) n,
      mulCoeffSum_eq_diagonal r s n]
  rw [diagonalSum_eq_degree_bound (scale a r) (scale b s) n,
      diagonalSum_eq_degree_bound r s n]
  exact foldl_add_int_diagonal_scaled a b r s n (n + 1)

/-- Gauss's lemma for primitive integer polynomials: the product of two
primitive polynomials is primitive. -/
theorem content_mul_of_primitive (p q : DensePoly Int)
    (hp : content p = 1) (hq : content q = 1) :
    content (p * q) = 1 := by
  -- contentNat (p * q) is nonzero (since p * q ≠ 0 by integral domain).
  have hpq_ne : p * q ≠ 0 := mul_ne_zero_of_primitive p q hp hq
  have hpq_size : 0 < (p * q).size := by
    rcases Nat.lt_or_ge 0 (p * q).size with h | h
    · exact h
    · exfalso
      apply hpq_ne
      apply ext_coeff
      intro n
      rw [coeff_zero]
      exact coeff_eq_zero_of_size_le (p * q) (by omega)
  have hpq_top_ne : (p * q).coeff ((p * q).size - 1) ≠ 0 :=
    coeff_last_ne_zero_of_pos_size (p * q) hpq_size
  have hcontentNat_ne_zero : contentNat (p * q) ≠ 0 := by
    intro h0
    have hdvd : (contentNat (p * q) : Int) ∣ (p * q).coeff ((p * q).size - 1) :=
      contentNat_dvd_coeff _ _
    rw [h0] at hdvd
    apply hpq_top_ne
    rcases hdvd with ⟨k, hk⟩
    have hk0 : ((0 : Nat) : Int) * k = (0 : Int) := by
      rw [show ((0 : Nat) : Int) = 0 from rfl, Int.zero_mul]
    rw [hk0] at hk
    exact hk
  have hcp_one : contentNat p = 1 := by
    have h : Int.ofNat (contentNat p) = 1 := hp
    have h' : Int.ofNat (contentNat p) = Int.ofNat 1 := h
    exact Int.ofNat_inj.mp h'
  have hcq_one : contentNat q = 1 := by
    have h : Int.ofNat (contentNat q) = 1 := hq
    have h' : Int.ofNat (contentNat q) = Int.ofNat 1 := h
    exact Int.ofNat_inj.mp h'
  -- Suppose contentNat(pq) ≠ 1; derive contradiction.
  show Int.ofNat (contentNat (p * q)) = 1
  apply congrArg Int.ofNat
  apply Classical.byContradiction
  intro hne
  have h_gt_one : 1 < contentNat (p * q) := by
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hcontentNat_ne_zero) with heq | hlt
    · exact absurd heq.symm hne
    · exact hlt
  rcases exists_natPrime_dvd_of_one_lt _ h_gt_one with ⟨r, hr, hrd⟩
  have h_r_dvd_each : ∀ n, (r : Int) ∣ (p * q).coeff n := by
    intro n
    have hcontent_dvd : (contentNat (p * q) : Int) ∣ (p * q).coeff n :=
      contentNat_dvd_coeff _ n
    have hr_dvd_content : (r : Int) ∣ (contentNat (p * q) : Int) :=
      Int.ofNat_dvd.mpr hrd
    exact Int.dvd_trans hr_dvd_content hcontent_dvd
  rcases natPrime_dvd_contentNat_or_dvd_contentNat_of_dvd_mul hr p q h_r_dvd_each
    with hp_dvd | hq_dvd
  · rw [hcp_one] at hp_dvd
    have hr_le : r ≤ 1 := Nat.le_of_dvd (by omega) hp_dvd
    have hr_ge : 2 ≤ r := hr.1
    omega
  · rw [hcq_one] at hq_dvd
    have hr_le : r ≤ 1 := Nat.le_of_dvd (by omega) hq_dvd
    have hr_ge : 2 ≤ r := hr.1
    omega

/-- Gauss's lemma on content (multiplicative form): the content of a product
of integer polynomials is the product of their contents. Strengthens
`content_mul_of_primitive` to non-primitive inputs by decomposing each
factor into its content and primitive part. -/
theorem content_mul (p q : DensePoly Int) :
    content (p * q) = content p * content q := by
  by_cases hcp : content p = 0
  · have hp_zero : p = 0 := by
      apply ext_coeff
      intro n
      have hcnp : contentNat p = 0 := by
        have h' : Int.ofNat (contentNat p) = Int.ofNat 0 := hcp
        exact Int.ofNat_inj.mp h'
      have hdvd : (contentNat p : Int) ∣ p.coeff n := contentNat_dvd_coeff p n
      rw [hcnp] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [coeff_zero]
      simpa using hk
    rw [hp_zero, zero_mul, content_zero, Int.zero_mul]
  by_cases hcq : content q = 0
  · have hq_zero : q = 0 := by
      apply ext_coeff
      intro n
      have hcnq : contentNat q = 0 := by
        have h' : Int.ofNat (contentNat q) = Int.ofNat 0 := hcq
        exact Int.ofNat_inj.mp h'
      have hdvd : (contentNat q : Int) ∣ q.coeff n := contentNat_dvd_coeff q n
      rw [hcnq] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [coeff_zero]
      simpa using hk
    have hpzero : p * (0 : DensePoly Int) = 0 := by
      rw [mul_comm_poly p (0 : DensePoly Int)]
      exact zero_mul p
    rw [hq_zero, hpzero, content_zero, Int.mul_zero]
  have hp_prim : content (primitivePart p) = 1 := primitivePart_primitive p hcp
  have hq_prim : content (primitivePart q) = 1 := primitivePart_primitive q hcq
  have hpq_prim : content (primitivePart p * primitivePart q) = 1 :=
    content_mul_of_primitive _ _ hp_prim hq_prim
  have hpq_eq :
      p * q = scale (content p * content q) (primitivePart p * primitivePart q) := by
    apply ext_coeff
    intro n
    have hp_decomp : p = scale (content p) (primitivePart p) :=
      (content_mul_primitivePart p).symm
    have hq_decomp : q = scale (content q) (primitivePart q) :=
      (content_mul_primitivePart q).symm
    rw [show (p * q).coeff n = ((scale (content p) (primitivePart p)) *
          (scale (content q) (primitivePart q))).coeff n from by
        rw [← hp_decomp, ← hq_decomp]]
    rw [coeff_scale_mul_scale]
    rw [coeff_scale (content p * content q) (primitivePart p * primitivePart q) n
      (Int.mul_zero _)]
  rw [hpq_eq, content_scale_int, hpq_prim, Int.mul_one]
  -- The product `content p * content q` is nonneg (both are `Int.ofNat`-coerced),
  -- so its `natAbs` round-trip equals itself.
  show Int.ofNat (content p * content q).natAbs = content p * content q
  show Int.ofNat (Int.ofNat (contentNat p) * Int.ofNat (contentNat q)).natAbs =
    Int.ofNat (contentNat p) * Int.ofNat (contentNat q)
  rfl

/-- Left-cancellation for integer scaling: a nonzero scalar can be cancelled
from both sides of a scaled-polynomial equality. -/
theorem scale_left_cancel {c : Int} (hc : c ≠ 0) {a b : DensePoly Int}
    (h : scale c a = scale c b) : a = b := by
  apply ext_coeff
  intro n
  have hn : c * a.coeff n = c * b.coeff n := by
    have hcong : (scale c a).coeff n = (scale c b).coeff n := by rw [h]
    rwa [coeff_scale c a n (Int.mul_zero c), coeff_scale c b n (Int.mul_zero c)] at hcong
  calc a.coeff n = c * a.coeff n / c := (Int.mul_ediv_cancel_left _ hc).symm
    _ = c * b.coeff n / c := by rw [hn]
    _ = b.coeff n := Int.mul_ediv_cancel_left _ hc

/-- Scaling a primitive polynomial by a positive integer leaves the primitive
part unchanged: the scalar is absorbed entirely into the content. -/
theorem primitivePart_scale_of_primitive {c : Int} (hc : 0 < c)
    {r : DensePoly Int} (hr : content r = 1) :
    primitivePart (scale c r) = r := by
  have hcontent : content (scale c r) = c := by
    rw [content_scale_int, hr, Int.mul_one]
    exact Int.natAbs_of_nonneg (Int.le_of_lt hc)
  have key : scale (content (scale c r)) (primitivePart (scale c r)) = scale c r :=
    content_mul_primitivePart (scale c r)
  rw [hcontent] at key
  exact scale_left_cancel (Int.ne_of_gt hc) key

/-- Gauss's lemma in primitive-part form: the primitive part of a product is the
product of the primitive parts. The content scalars factor out via `content_mul`
and `content_mul_of_primitive`, and the positive product scalar is absorbed by
`primitivePart_scale_of_primitive`. -/
theorem primitivePart_mul (p q : DensePoly Int) :
    primitivePart (p * q) = primitivePart p * primitivePart q := by
  by_cases hcp : content p = 0
  · have hppq : content (p * q) = 0 := by rw [content_mul, hcp, Int.zero_mul]
    rw [primitivePart_eq_zero_of_content_eq_zero _ hppq,
        primitivePart_eq_zero_of_content_eq_zero _ hcp, zero_mul]
  by_cases hcq : content q = 0
  · have hppq : content (p * q) = 0 := by rw [content_mul, hcq, Int.mul_zero]
    rw [primitivePart_eq_zero_of_content_eq_zero _ hppq,
        primitivePart_eq_zero_of_content_eq_zero _ hcq, mul_comm_poly, zero_mul]
  have hp_prim : content (primitivePart p) = 1 := primitivePart_primitive p hcp
  have hq_prim : content (primitivePart q) = 1 := primitivePart_primitive q hcq
  have hpq_prim : content (primitivePart p * primitivePart q) = 1 :=
    content_mul_of_primitive _ _ hp_prim hq_prim
  have hpq_eq : p * q =
      scale (content p * content q) (primitivePart p * primitivePart q) := by
    apply ext_coeff
    intro n
    have hp_decomp : p = scale (content p) (primitivePart p) :=
      (content_mul_primitivePart p).symm
    have hq_decomp : q = scale (content q) (primitivePart q) :=
      (content_mul_primitivePart q).symm
    rw [show (p * q).coeff n = ((scale (content p) (primitivePart p)) *
          (scale (content q) (primitivePart q))).coeff n from by
        rw [← hp_decomp, ← hq_decomp]]
    rw [coeff_scale_mul_scale]
    rw [coeff_scale (content p * content q) (primitivePart p * primitivePart q) n
      (Int.mul_zero _)]
  have hcp_nat : contentNat p ≠ 0 := by
    intro h; apply hcp; show Int.ofNat (contentNat p) = 0; rw [h]; rfl
  have hcq_nat : contentNat q ≠ 0 := by
    intro h; apply hcq; show Int.ofNat (contentNat q) = 0; rw [h]; rfl
  have hp0 : 0 < content p := by
    have h : (0 : Int) < (contentNat p : Int) := by
      have := Nat.pos_of_ne_zero hcp_nat; omega
    exact h
  have hq0 : 0 < content q := by
    have h : (0 : Int) < (contentNat q : Int) := by
      have := Nat.pos_of_ne_zero hcq_nat; omega
    exact h
  have hcpos : 0 < content p * content q := Int.mul_pos hp0 hq0
  rw [hpq_eq, primitivePart_scale_of_primitive hcpos hpq_prim]

/-- Gauss's lemma on content (divisibility form): if a natural number `d`
divides every coefficient of `p * q`, then it divides `contentNat p *
contentNat q`. This is the divisibility witness needed by the McCoy row
construction in #3440 and the downstream chain `#3440 → #3435 → #3389 →
#3346 → #3252`. -/
theorem dvd_contentNat_mul_of_dvd_mul_coeff
    (p q : DensePoly Int) (d : Nat)
    (h : ∀ n, (d : Int) ∣ (p * q).coeff n) :
    d ∣ contentNat p * contentNat q := by
  -- Edge cases where one factor has zero content collapse to `d ∣ 0`.
  by_cases hcp : contentNat p = 0
  · rw [hcp, Nat.zero_mul]; exact Nat.dvd_zero d
  by_cases hcq : contentNat q = 0
  · rw [hcq, Nat.mul_zero]; exact Nat.dvd_zero d
  -- Both contents are nonzero, so the primitive parts are primitive.
  have hcp_ne : content p ≠ 0 := by
    intro h0
    apply hcp
    have h' : Int.ofNat (contentNat p) = Int.ofNat 0 := h0
    exact Int.ofNat_inj.mp h'
  have hcq_ne : content q ≠ 0 := by
    intro h0
    apply hcq
    have h' : Int.ofNat (contentNat q) = Int.ofNat 0 := h0
    exact Int.ofNat_inj.mp h'
  have hp_prim : content (primitivePart p) = 1 := primitivePart_primitive p hcp_ne
  have hq_prim : content (primitivePart q) = 1 := primitivePart_primitive q hcq_ne
  -- Gauss: the product of primitives is primitive.
  have hpq_prim : content (primitivePart p * primitivePart q) = 1 :=
    content_mul_of_primitive _ _ hp_prim hq_prim
  -- Recover `p * q` as a scaled product of primitives.
  have hp_decomp : scale (content p) (primitivePart p) = p := content_mul_primitivePart p
  have hq_decomp : scale (content q) (primitivePart q) = q := content_mul_primitivePart q
  -- Recover `p * q` as a scaled product of primitives at the algebraic level.
  have hmul_eq : scale (content p) (primitivePart p) *
      scale (content q) (primitivePart q) = p * q := by
    rw [hp_decomp, hq_decomp]
  -- (p * q).coeff n = content p * content q * (p' * q').coeff n
  have hcoeff_eq : ∀ n, (p * q).coeff n =
      (content p * content q) *
        (primitivePart p * primitivePart q).coeff n := by
    intro n
    rw [← hmul_eq]
    exact coeff_scale_mul_scale (content p) (content q)
      (primitivePart p) (primitivePart q) n
  -- The scalar `content p * content q` is annihilated by `d`.
  have h_scaled_dvd : ∀ n, (d : Int) ∣
      (content p * content q) * (primitivePart p * primitivePart q).coeff n := by
    intro n
    rw [← hcoeff_eq]
    exact h n
  have h_int_dvd : (d : Int) ∣ content p * content q :=
    nat_dvd_of_scalar_mul_primitive_coeff_dvd _ d (content p * content q)
      hpq_prim h_scaled_dvd
  -- Convert Int divisibility to Nat divisibility on the natAbs.
  rw [Int.ofNat_dvd_left] at h_int_dvd
  have hnatAbs : (content p * content q).natAbs = contentNat p * contentNat q := by
    unfold content
    rfl
  rw [hnatAbs] at h_int_dvd
  exact h_int_dvd

private theorem dvd_coeff_mul_of_dvd_contentNat_mul
    (p q : DensePoly Int) (d i j : Nat)
    (hcontent : d ∣ contentNat p * contentNat q) :
    (d : Int) ∣ p.coeff i * q.coeff j := by
  have hpcoeff : (contentNat p : Int) ∣ p.coeff i := contentNat_dvd_coeff p i
  have hqcoeff : (contentNat q : Int) ∣ q.coeff j := contentNat_dvd_coeff q j
  rcases hpcoeff with ⟨a, ha⟩
  rcases hqcoeff with ⟨b, hb⟩
  have hcontent_int : (d : Int) ∣ ((contentNat p * contentNat q : Nat) : Int) :=
    Int.ofNat_dvd.mpr hcontent
  rcases hcontent_int with ⟨c, hc⟩
  refine ⟨c * (a * b), ?_⟩
  rw [ha, hb]
  have hc' : (contentNat p : Int) * (contentNat q : Int) = (d : Int) * c := by
    simpa using hc
  calc
    (contentNat p : Int) * a * ((contentNat q : Int) * b) =
        ((contentNat p : Int) * (contentNat q : Int)) * (a * b) := by
          grind
    _ = ((d : Int) * c) * (a * b) := by
          rw [hc']
    _ = (d : Int) * (c * (a * b)) := by
          grind

/-- Content/Gauss finite-row helper for McCoy-style coefficient arrays.

If `p` and `q` are finite polynomial packages for coefficient families
`pCoeff` and `qCoeff`, and every coefficient of `p * q` is divisible by
`d`, then Gauss's content divisibility forces the whole selected row
`pCoeff i * qCoeff k` to be divisible by `d`. -/
private theorem finiteCoeffMcCoyRow_of_truncated_product_coeff_dvd
    (pCoeff qCoeff : Nat → Int) (p q : DensePoly Int) (d bound k : Nat)
    (hpCoeff : ∀ i, i ≤ bound → p.coeff i = pCoeff i)
    (hqCoeff : q.coeff k = qCoeff k)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n) :
    ∀ i, i ≤ bound → (d : Int) ∣ pCoeff i * qCoeff k := by
  have hcontent : d ∣ contentNat p * contentNat q :=
    dvd_contentNat_mul_of_dvd_mul_coeff p q d hprod
  intro i hi
  have hrow := dvd_coeff_mul_of_dvd_contentNat_mul p q d i k hcontent
  simpa [hpCoeff i hi, hqCoeff] using hrow

/-- Coefficient-family version of the content/Gauss McCoy row helper.

This is the finite-array row step after callers have normalized the convolution
hypotheses into divisibility of the truncated product polynomial's
coefficients. -/
private theorem finiteCoeffMcCoyRow_of_truncated_product_coeff_family_dvd
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod :
      ∀ n, (d : Int) ∣
        (finiteCoeffFamilyPoly pCoeff bound * finiteCoeffFamilyPoly qCoeff k).coeff n) :
    ∀ i, i ≤ bound → (d : Int) ∣ pCoeff i * qCoeff k := by
  exact finiteCoeffMcCoyRow_of_truncated_product_coeff_dvd pCoeff qCoeff
    (finiteCoeffFamilyPoly pCoeff bound) (finiteCoeffFamilyPoly qCoeff k)
    d bound k
    (fun i hi => finiteCoeffFamilyPoly_coeff_of_le pCoeff bound i hi)
    (finiteCoeffFamilyPoly_coeff_of_le qCoeff k k (Nat.le_refl k))
    hprod

private theorem finiteCoeffFamilyPoly_mul_coeff_dvd_of_finiteCoeffConvolution
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod : ∀ n, n ≤ bound + k → (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s) :
    ∀ n, (d : Int) ∣
      (finiteCoeffFamilyPoly pCoeff bound * finiteCoeffFamilyPoly qCoeff k).coeff n := by
  intro n
  rw [coeff_mul, mulCoeffSum_eq_diagonal, diagonalSum_eq_degree_bound]
  by_cases hn : n ≤ bound + k
  · exact dvd_foldl_add_term_of_dvd_congr (d : Int) (List.range (n + 1))
      (fun r => pCoeff r * qCoeff (n - r))
      (fun r => diagonalMulCoeffTerm
        (finiteCoeffFamilyPoly pCoeff bound) (finiteCoeffFamilyPoly qCoeff k) n r)
      (hprod n hn) (by
        intro r hr
        have hrlt : r < n + 1 := List.mem_range.mp hr
        have hnot : ¬ n < r := by omega
        unfold diagonalMulCoeffTerm
        simp only [hnot, ↓reduceIte]
        by_cases hrBound : r ≤ bound
        · by_cases hsK : n - r ≤ k
          · have hp := finiteCoeffFamilyPoly_coeff_of_le pCoeff bound r hrBound
            have hq := finiteCoeffFamilyPoly_coeff_of_le qCoeff k (n - r) hsK
            rw [hp, hq]
            simp
          · have hk_lt : k < n - r := Nat.lt_of_not_ge hsK
            have hq := finiteCoeffFamilyPoly_coeff_of_lt qCoeff k (n - r) hk_lt
            rw [hq]
            simpa using Int.dvd_mul_of_dvd_right (hqAbove (n - r) hk_lt)
        · have hb_lt : bound < r := Nat.lt_of_not_ge hrBound
          have hp := finiteCoeffFamilyPoly_coeff_of_lt pCoeff bound r hb_lt
          rw [hp]
          simpa using hleft r (n - r) hb_lt)
  · apply dvd_list_foldl_add_term_of_forall
    intro r hr
    have hrlt : r < n + 1 := List.mem_range.mp hr
    have hnot : ¬ n < r := by omega
    unfold diagonalMulCoeffTerm
    simp only [hnot, ↓reduceIte]
    by_cases hrBound : r ≤ bound
    · have hk_lt : k < n - r := by
        have hnbk : bound + k < n := Nat.lt_of_not_ge hn
        omega
      have hq := finiteCoeffFamilyPoly_coeff_of_lt qCoeff k (n - r) hk_lt
      rw [hq]
      simp
    · have hb_lt : bound < r := Nat.lt_of_not_ge hrBound
      have hp := finiteCoeffFamilyPoly_coeff_of_lt pCoeff bound r hb_lt
      rw [hp]
      simp

/-- Finite coefficient-array McCoy annihilator over `Int`: if every relevant
finite convolution coefficient is divisible by `d`, all right coefficients
above `k` are divisible by `d`, and the left family is supported modulo `d`
through `bound`, then the `k`-th right coefficient annihilates every left
coefficient up to `bound`. -/
private theorem finiteCoeffMcCoyAnnihilator
    (pCoeff qCoeff : Nat → Int) (d bound k : Nat)
    (hprod : ∀ n, n ≤ bound + k → (d : Int) ∣ finiteCoeffConvolution pCoeff qCoeff n)
    (hqAbove : ∀ s, k < s → (d : Int) ∣ qCoeff s)
    (hleft : ∀ r s, bound < r → (d : Int) ∣ pCoeff r * qCoeff s) :
    ∀ i, i ≤ bound → (d : Int) ∣ qCoeff k * pCoeff i := by
  intro i hi
  let p := finiteCoeffFamilyPoly pCoeff bound
  let q := finiteCoeffFamilyPoly qCoeff k
  have hmul : ∀ n, (d : Int) ∣ (p * q).coeff n := by
    intro n
    simpa [p, q] using
      finiteCoeffFamilyPoly_mul_coeff_dvd_of_finiteCoeffConvolution
        pCoeff qCoeff d bound k hprod hqAbove hleft n
  have hrow := finiteCoeffMcCoyRow_of_truncated_product_coeff_family_dvd
    pCoeff qCoeff d bound k (by simpa [p, q] using hmul) i hi
  simpa [Int.mul_comm] using hrow

/-- McCoy annihilator for `DensePoly Int`: if every coefficient of `p * q` is
divisible by `d`, then `q.coeff k` annihilates every coefficient of `p` modulo
`d`. This is the polynomial instantiation of `finiteCoeffMcCoyAnnihilator`
when `pCoeff = p.coeff` and `qCoeff = q.coeff`; downstream callers couple it
with a "last non-divisible coefficient" witness, supplying `hqAbove`. -/
private theorem dvd_last_q_coeff_mul_p_coeff_of_dvd_mul_coeff_of_q_above
    (p q : DensePoly Int) (d k : Nat)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n)
    (_hqAbove : ∀ s, k < s → (d : Int) ∣ q.coeff s) :
    ∀ i, (d : Int) ∣ q.coeff k * p.coeff i := by
  intro i
  have hrow :=
    finiteCoeffMcCoyRow_of_truncated_product_coeff_dvd
      p.coeff q.coeff p q d i k
      (fun _ _ => rfl) rfl hprod i (Nat.le_refl i)
  simpa [Int.mul_comm] using hrow

/-- Public McCoy scalar-annihilator wrapper for integer dense polynomials.

If `d` divides every coefficient of `p * q` and some coefficient of `q` is not
divisible by `d`, then a non-`d`-divisible scalar annihilates all coefficients
of `p` modulo `d`. -/
theorem exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff
    (p q : DensePoly Int) (d : Nat)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n)
    (hq : ∃ n, ¬ (d : Int) ∣ q.coeff n) :
    ∃ a : Int, (¬ (d : Int) ∣ a) ∧
      ∀ i, (d : Int) ∣ a * p.coeff i := by
  rcases exists_last_not_natCast_dvd_coeff q d hq with ⟨k, hk, hqAbove⟩
  refine ⟨q.coeff k, hk, ?_⟩
  exact dvd_last_q_coeff_mul_p_coeff_of_dvd_mul_coeff_of_q_above p q d k hprod hqAbove

/-- Coefficient divisibility transfer for primitive products: if `p` is
primitive (content one) and a natural number `d` divides every coefficient of
`p * q`, then `d` divides every coefficient of `q`. Proved by contradiction
using the McCoy scalar annihilator
`exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff` and the
primitive scalar annihilator `nat_dvd_of_scalar_mul_primitive_coeff_dvd`. -/
theorem coeff_dvd_of_primitive_mul_coeff_dvd
    (p q : DensePoly Int) (d : Nat)
    (hp : content p = 1)
    (hprod : ∀ n, (d : Int) ∣ (p * q).coeff n) :
    ∀ n, (d : Int) ∣ q.coeff n := by
  intro n
  apply Classical.byContradiction
  intro hn
  rcases exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff
    p q d hprod ⟨n, hn⟩ with ⟨a, hna, ha⟩
  exact hna (nat_dvd_of_scalar_mul_primitive_coeff_dvd p d a hp ha)


end DensePoly
end Hex
