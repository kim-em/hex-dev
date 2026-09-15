/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Terms

public section

namespace Hex.Kronecker

/-- A saturated coefficient bound and exact componentwise degree bounds. -/
structure Bounded {k : Nat} (cap : Nat) (b : Bounds) (p : MvPolynomial (Fin k) Int) : Prop where
  length : b.degrees.length = k
  degree : ∀ i, p.degreeOf i ≤ b.degrees.getD i.val 0
  norm : min (norm₁ p) cap ≤ b.height
  capped : b.height ≤ cap

namespace Bounded

variable {k cap : Nat} {a b : Bounds} {p q : MvPolynomial (Fin k) Int}

theorem inBox (h : Bounded cap a p) : InBox a.degrees p := by
  intro e he
  apply box_ofFn _ h.length
  intro i
  exact (MvPolynomial.monomial_le_degreeOf i he).trans (h.degree i)

theorem norm_le (h : Bounded cap a p) (ha : a.height < cap) : norm₁ p ≤ a.height := by
  have := h.norm
  omega

theorem zero (cap k : Nat) : Bounded cap (Bounds.zero k) (0 : MvPolynomial (Fin k) Int) := by
  constructor <;> simp [Bounds.zero]

theorem int (cap k : Nat) (z : Int) :
    Bounded cap ⟨zeroDegrees k, min z.natAbs cap⟩ (MvPolynomial.C z : MvPolynomial (Fin k) Int) := by
  constructor
  · simp
  · intro i
    change (MvPolynomial.C z : MvPolynomial (Fin k) Int).degreeOf i ≤ (zeroDegrees k).getD i.val 0
    rw [MvPolynomial.degreeOf_C, getD_zeroDegrees]
  · exact le_of_eq (congrArg (min · cap) (norm₁_monomial 0 z))
  · exact min_le_right _ _

theorem add (ha : Bounded cap a p) (hb : Bounded cap b q) :
    Bounded cap (a.add cap b) (p + q) := by
  constructor
  · simp [Bounds.add, ha.length, hb.length]
  · intro i
    exact (MvPolynomial.degreeOf_add_le i p q).trans
      (by simpa only [Bounds.add, getD_maxDegrees] using max_le_max (ha.degree i) (hb.degree i))
  · change min (norm₁ (p+q)) cap ≤ Saturating.add cap a.height b.height
    rw [Saturating.add_eq]
    calc
      _ ≤ min (norm₁ p + norm₁ q) cap := min_le_min_right _ (norm₁_add p q)
      _ = min (min (norm₁ p) cap + min (norm₁ q) cap) cap := (Saturating.min_add _ _ _).symm
      _ ≤ _ := min_le_min_right _ (Nat.add_le_add ha.norm hb.norm)
  · simp [Bounds.add, Saturating.add_eq]

theorem neg (ha : Bounded cap a p) : Bounded cap a (-p) := by
  constructor
  · exact ha.length
  · simpa only [MvPolynomial.degreeOf_neg] using ha.degree
  · simpa only [norm₁_neg] using ha.norm
  · exact ha.capped

theorem sub (ha : Bounded cap a p) (hb : Bounded cap b q) :
    Bounded cap (a.add cap b) (p-q) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem mul (ha : Bounded cap a p) (hb : Bounded cap b q) :
    Bounded cap (a.mul cap b) (p*q) := by
  constructor
  · simp [Bounds.mul, ha.length, hb.length]
  · intro i
    exact (MvPolynomial.degreeOf_mul_le i p q).trans
      (by simpa only [Bounds.mul, getD_addDegrees] using Nat.add_le_add (ha.degree i) (hb.degree i))
  · change min (norm₁ (p*q)) cap ≤ Saturating.mul cap a.height b.height
    rw [Saturating.mul_eq]
    calc
      _ ≤ min (norm₁ p * norm₁ q) cap := min_le_min_right _ (norm₁_mul p q)
      _ = min (min (norm₁ p) cap * min (norm₁ q) cap) cap := (Saturating.min_mul _ _ _).symm
      _ ≤ _ := min_le_min_right _ (Nat.mul_le_mul ha.norm hb.norm)
  · simp [Bounds.mul, Saturating.mul_eq]

end Bounded

theorem terms_bounded (cap k : Nat) (ts : Hex.MvPoly.Kernel.PolyList Int)
    (h : termShape k ts = true) : Bounded cap (termBounds cap k ts) (termsPolynomial k ts) := by
  constructor
  · exact termBounds_length cap k ts h
  · exact terms_degreeOf_le cap k ts h
  · rw [termBounds_height]
    exact min_le_min_right _ (terms_norm₁_le k ts)
  · rw [termBounds_height]; exact min_le_right _ _

theorem Expr.bounded (cap k : Nat) (e : Expr) (h : e.WellFormed k) (acc : List Bounds) :
    Bounded cap (e.analyze cap k acc).1 (e.toMvPolynomial h) := by
  rw [e.analyze_bound]
  constructor
  · exact e.length_degrees k
  · exact e.degreeOf_le h
  · rw [Expr.cappedHeight_eq]
    exact min_le_min_right _ (e.norm₁_le h)
  · rw [Expr.cappedHeight_eq]; exact min_le_right _ _

/-- Once the preflight accepts, two bounded polynomials in its common box
are equal whenever their balanced encodings are equal. -/
theorem bounded_injective (budget : Budget) (common : Bounds) (observed : List Bounds)
    (hacc : (makeSize budget common observed).accepts budget = true)
    {k : Nat} {a b : Bounds} {p q : MvPolynomial (Fin k) Int}
    (ha : Bounded (2^budget.maxPackedBits) a p) (hb : Bounded (2^budget.maxPackedBits) b q)
    (ham : a ∈ observed) (hbm : b ∈ observed)
    (hlen : common.degrees.length = k)
    (had : ∀ i : Fin k, a.degrees.getD i.val 0 ≤ common.degrees.getD i.val 0)
    (hbd : ∀ i : Fin k, b.degrees.getD i.val 0 ≤ common.degrees.getD i.val 0)
    (hah : a.height ≤ common.height) (hbh : b.height ≤ common.height)
    (he : MvPolynomial.eval₂Hom (RingHom.id Int)
      (fun i : Fin k => ((2 : Int)^(common.height.log2+2))^(makeStrides 1 common.degrees).getD i.val 0) p =
      MvPolynomial.eval₂Hom (RingHom.id Int)
      (fun i : Fin k => ((2 : Int)^(common.height.log2+2))^(makeStrides 1 common.degrees).getD i.val 0) q) :
    p = q := by
  apply balanced_injective common.degrees hlen p q
    (ha.inBox.mono hlen had) (hb.inBox.mono hlen hbd) common.height
    (common.height.log2+2) _ _ (width_bound common.height) he
  · exact (ha.norm_le (height_of_accept budget common observed hacc a ham)).trans hah
  · exact (hb.norm_le (height_of_accept budget common observed hacc b hbm)).trans hbh

/-- Specialize the common-box argument to one comparison. -/
theorem bounded_pair (budget : Budget) (observed : List Bounds)
    {k : Nat} {a b : Bounds} {p q : MvPolynomial (Fin k) Int}
    (ha : Bounded (2^budget.maxPackedBits) a p) (hb : Bounded (2^budget.maxPackedBits) b q)
    (ham : a ∈ observed) (hbm : b ∈ observed)
    (hacc : (makeSize budget (a.add (2^budget.maxPackedBits) b) observed).accepts budget = true)
    (he : let s := makeSize budget (a.add (2^budget.maxPackedBits) b) observed
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2^s.digitBits : Nat) : Int)^s.strides.getD i.val 0) p =
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2^s.digitBits : Nat) : Int)^s.strides.getD i.val 0) q) : p = q := by
  apply bounded_injective budget _ observed hacc ha hb ham hbm
  · simp [Bounds.add, ha.length, hb.length]
  · intro i; simp only [Bounds.add, getD_maxDegrees]; exact Nat.le_max_left _ _
  · intro i; simp only [Bounds.add, getD_maxDegrees]; exact Nat.le_max_right _ _
  · exact Saturating.le_add_left _ _ _ ha.capped
  · exact Saturating.le_add_right _ _ _ hb.capped
  · simpa only [makeSize, Nat.cast_pow, Nat.cast_ofNat] using he

end Hex.Kronecker
