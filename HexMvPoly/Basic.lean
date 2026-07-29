/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Mono

@[expose] public section
set_option backward.proofsInPublic true

/-!
The canonical distributed representation of multivariate polynomials,
its constructors, and ordered term-iteration API.
-/

namespace Hex

open scoped Hex

universe u

/-- A canonical distributed multivariate polynomial. The backing tree map
stores only nonzero coefficients and uses the explicit comparator `cmp`. -/
structure MvPoly (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  /-- Internal backing map. Consumers should use `termsList`, `foldTerms`,
  `monomials`, and `termCount` so the representation can change. -/
  termsInternal : Std.ExtTreeMap (Mono n) R cmp
  /-- Canonical-form invariant: zero coefficients are absent. -/
  nonzeroInternal : ∀ m : Mono n, termsInternal[m]? ≠ some 0

namespace MvPoly

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Zero R] [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- The absent coefficient of a monomial. -/
@[inline] def coeff? (m : Mono n) (p : MvPoly n R cmp) : Option R :=
  p.termsInternal[m]?

/-- Coefficient of a monomial, returning zero outside the support. -/
@[inline] def coeff (m : Mono n) (p : MvPoly n R cmp) : R :=
  (coeff? m p).getD 0

/-- Ordered term list, in increasing `cmp` order. -/
def termsList (p : MvPoly n R cmp) : List (Mono n × R) :=
  p.termsInternal.toList

/-- Compatibility spelling for consumers that iterate over all terms. -/
def toList (p : MvPoly n R cmp) : List (Mono n × R) :=
  termsList p

/-- Fold over terms in increasing `cmp` order. -/
@[inline] def foldTerms (f : α → Mono n → R → α) (init : α)
    (p : MvPoly n R cmp) : α :=
  p.termsInternal.foldl f init

/-- Monomials in the support, in increasing `cmp` order. -/
def monomials (p : MvPoly n R cmp) : List (Mono n) :=
  (termsList p).map Prod.fst

/-- Monomials in the support, in increasing `cmp` order. -/
def support (p : MvPoly n R cmp) : List (Mono n) :=
  monomials p

/-- Number of nonzero terms. -/
@[inline] def termCount (p : MvPoly n R cmp) : Nat :=
  p.termsInternal.size

/-- Greatest term in `cmp` order. -/
@[inline] def maxTerm? (p : MvPoly n R cmp) : Option (Mono n × R) :=
  p.termsInternal.maxEntry?

/-- The zero polynomial. -/
def zero : MvPoly n R cmp where
  termsInternal := ∅
  nonzeroInternal := by simp

instance : Zero (MvPoly n R cmp) where
  zero := zero

instance : Inhabited (MvPoly n R cmp) :=
  ⟨0⟩

/-- The stored representation contains no explicit zero coefficient. -/
theorem coeff?_ne_zero (p : MvPoly n R cmp) (m : Mono n) :
    coeff? m p ≠ some 0 :=
  p.nonzeroInternal m

/-- Coefficients determine a canonical multivariate polynomial. -/
@[ext] theorem ext {p q : MvPoly n R cmp}
    (h : ∀ m, coeff m p = coeff m q) : p = q := by
  sorry

/-- Boolean equality delegates to the extensional tree-map implementation
and ignores the proof field. -/
instance [BEq R] : BEq (MvPoly n R cmp) where
  beq p q := p.termsInternal == q.termsInternal

instance [BEq R] [LawfulBEq R] : LawfulBEq (MvPoly n R cmp) where
  eq_of_beq := by
    intro p q h
    change p.termsInternal == q.termsInternal at h
    have ht : p.termsInternal = q.termsInternal := eq_of_beq h
    cases p with
    | mk pt hp =>
      cases q with
      | mk qt hq =>
        simp only at ht
        subst ht
        rfl
  rfl := by
    intro p
    change p.termsInternal == p.termsInternal
    exact BEq.rfl

instance [BEq R] [LawfulBEq R] : DecidableEq (MvPoly n R cmp) :=
  _root_.instDecidableEqOfLawfulBEq

/-- A single term, dropping it when its coefficient is zero. -/
def monomial [DecidableEq R] (m : Mono n) (c : R) : MvPoly n R cmp :=
  if hc : c = 0 then
    0
  else
    { termsInternal := (∅ : Std.ExtTreeMap (Mono n) R cmp).insert m c
      nonzeroInternal := by
        intro k
        rw [Std.ExtTreeMap.getElem?_insert]
        split
        · simpa using hc
        · simp }

/-- A constant polynomial. -/
def C [DecidableEq R] (c : R) : MvPoly n R cmp :=
  monomial Mono.zero c

/-- The variable `xᵢ`. -/
def X [One R] [DecidableEq R] (i : Fin n) : MvPoly n R cmp :=
  monomial (Mono.unit i) 1

/-- Add `c` to the coefficient at `m`, deleting the term if the new
coefficient is zero. -/
def addMonomial [Add R] [DecidableEq R]
    (p : MvPoly n R cmp) (m : Mono n) (c : R) : MvPoly n R cmp where
  termsInternal := p.termsInternal.alter m fun old =>
    let c' := old.getD 0 + c
    if c' = 0 then none else some c'
  nonzeroInternal := by
    intro k
    rw [Std.ExtTreeMap.getElem?_alter]
    split
    · simp only
      split <;> simp_all
    · exact p.nonzeroInternal k

/-- Map stored coefficients without changing the support. The proof
argument records that nonzero values remain nonzero. -/
def mapCoeffs (p : MvPoly n R cmp) (f : R → R)
    (hf : ∀ c, c ≠ 0 → f c ≠ 0) : MvPoly n R cmp where
  termsInternal := p.termsInternal.map fun _ c => f c
  nonzeroInternal := by
    sorry

/-- Build a polynomial by summing duplicate monomials and dropping all
zero coefficients. -/
def ofTerms [Lean.Grind.Semiring R] [DecidableEq R]
    (ts : List (Mono n × R)) : MvPoly n R cmp :=
  ts.foldl (fun p t => addMonomial p t.1 t.2) 0

@[simp] theorem coeff_zero (m : Mono n) :
    coeff m (0 : MvPoly n R cmp) = 0 := by
  change ((∅ : Std.ExtTreeMap (Mono n) R cmp)[m]?).getD 0 = 0
  simp

theorem coeff_monomial [DecidableEq R] (m m' : Mono n) (c : R) :
    coeff m (monomial m' c : MvPoly n R cmp) =
      if m = m' then c else 0 := by
  sorry

theorem coeff_C [DecidableEq R] (m : Mono n) (c : R) :
    coeff m (C c : MvPoly n R cmp) =
      if m = Mono.zero then c else 0 := by
  simp [C, coeff_monomial]

theorem coeff_X [One R] [DecidableEq R] (m : Mono n) (i : Fin n) :
    coeff m (X i : MvPoly n R cmp) =
      if m = Mono.unit i then 1 else 0 := by
  simp [X, coeff_monomial]

theorem coeff_addMonomial [Add R] [DecidableEq R]
    (p : MvPoly n R cmp) (m k : Mono n) (c : R) :
    coeff k (addMonomial p m c) =
      if k = m then coeff k p + c else coeff k p := by
  sorry

theorem coeff_ofTerms [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (ts : List (Mono n × R)) :
    coeff m (ofTerms ts : MvPoly n R cmp) =
      (ts.filter (fun t => t.1 = m)).foldl (fun acc t => acc + t.2) 0 := by
  sorry

end MvPoly

end Hex
