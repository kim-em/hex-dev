/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Ring.TransferInstance
public import HexMvPoly

public section

/-!
The exact correspondence between `Hex.MvPoly` and Mathlib's
`MvPolynomial (Fin n)`.

Exponent vectors are first identified with finitely supported functions on the
finite variable type. The polynomial conversions then enumerate only canonical
nonzero supports; later declarations package them as a ring equivalence and
transport Mathlib's algebraic structures back to the executable type.
-/

namespace HexMvPolyMathlib

open scoped BigOperators
open scoped HexMvPolyMathlib

open Hex
open Hex.MvPoly

universe u

variable {n : Nat} {R : Type u}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

noncomputable section

/-!
Executable operations and Mathlib structures must use the same coefficient
operations. The `HexMvPolyMathlib` scope raises Mathlib's existing
`CommSemiring`/`CommRing` adapters above native Grind instances while the
bridge is in use. The scope is active throughout these implementation files,
but importing the bridge alone does not change global instance search.
-/

scoped[HexMvPolyMathlib] attribute [instance 2000]
  CommSemiring.toGrindCommSemiring CommRing.toGrindCommRing

/-- A fixed-arity exponent vector is equivalent to a finitely supported
function on the finite variable type. -/
def monoEquiv : Mono n ≃ (Fin n →₀ Nat) where
  toFun m := Finsupp.equivFunOnFinite.symm fun i => m[i]
  invFun d := Hex.Vector.ofFn' fun i => d i
  left_inv m := by
    apply Vector.ext
    intro i
    simp
  right_inv d := by
    apply Finsupp.ext
    intro i
    simp

/-- The finitely supported image of a monomial has the same exponent at every
variable. -/
@[simp] theorem monoEquiv_apply (m : Mono n) (i : Fin n) :
    monoEquiv m i = m[i] := by
  rfl

/-- Converting a finitely supported exponent function back to a monomial
preserves every exponent. -/
@[simp] theorem monoEquiv_symm_apply (d : Fin n →₀ Nat) (i : Fin n) :
    (monoEquiv.symm d).get i = d i := by
  change (Hex.Vector.ofFn' fun j => d j)[i.val] = d i
  rw [Hex.Vector.getElem_ofFn' _ i.val i.isLt]

/-- The zero monomial corresponds to the zero finitely supported function. -/
@[simp] theorem monoEquiv_zero :
    monoEquiv (Mono.zero : Mono n) = 0 := by
  apply Finsupp.ext
  intro i
  simp [Mono.zero]

/-- A monomial maps to zero exactly when it is the zero monomial. -/
@[simp] theorem monoEquiv_eq_zero (m : Mono n) :
    monoEquiv m = 0 ↔ m = Mono.zero := by
  rw [← monoEquiv_zero]
  exact monoEquiv.injective.eq_iff

/-- Zero equals a mapped monomial exactly when that monomial is zero. -/
@[simp] theorem zero_eq_monoEquiv (m : Mono n) :
    0 = monoEquiv m ↔ m = Mono.zero := by
  rw [eq_comm, monoEquiv_eq_zero]

/-- Monomial multiplication corresponds to addition of finitely supported
exponent functions. -/
@[simp] theorem monoEquiv_mul (a b : Mono n) :
    monoEquiv (Mono.mul a b) = monoEquiv a + monoEquiv b := by
  apply Finsupp.ext
  intro i
  simp [Mono.mul]

/-- A unit monomial corresponds to Mathlib's single-variable exponent. -/
@[simp] theorem monoEquiv_unit (i : Fin n) :
    monoEquiv (Mono.unit i) = Finsupp.single i 1 := by
  apply Finsupp.ext
  intro j
  by_cases h : j = i <;> simp [Mono.unit, h]

/-- The componentwise exponent equivalence on pairs of monomials. -/
def monoPairEquiv :
    (Mono n × Mono n) ≃
      ((Fin n →₀ Nat) × (Fin n →₀ Nat)) :=
  Equiv.prodCongr monoEquiv monoEquiv

/-- The pair equivalence maps both monomials componentwise. -/
@[simp] theorem monoPairEquiv_apply (ab : Mono n × Mono n) :
    monoPairEquiv ab = (monoEquiv ab.1, monoEquiv ab.2) := by
  rfl

/-- The pair embedding applies the monomial equivalence to each component. -/
@[simp] theorem monoPairEmbedding_apply (ab : Mono n × Mono n) :
    monoPairEquiv.toEmbedding ab =
      (monoEquiv ab.1, monoEquiv ab.2) := by
  rfl

section CoherentEquality

variable [BEq R] [LawfulBEq R]

/-- Interpret an executable sparse polynomial as a Mathlib multivariate
polynomial by summing its canonical support. -/
@[nolint unusedArguments]
def toMvPolynomial [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : MvPolynomial (Fin n) R :=
  p.monomials.toFinset.sum fun m =>
    MvPolynomial.monomial (monoEquiv m) (coeff m p)

end CoherentEquality

/-- The canonical-support sum used by the forward conversion. -/
theorem toMvPolynomial_eq_sum [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    toMvPolynomial p =
      p.monomials.toFinset.sum fun m =>
        MvPolynomial.monomial (monoEquiv m) (coeff m p) := by
  rfl

/-- Forward conversion preserves every coefficient. -/
@[simp] theorem coeff_toMvPolynomial [CommSemiring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) :
    MvPolynomial.coeff (monoEquiv m) (toMvPolynomial p) = coeff m p := by
  rw [toMvPolynomial, MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, monoEquiv.injective.eq_iff,
    mem_monomials_iff, eq_comm]

section CoherentEquality

variable [BEq R] [LawfulBEq R]

/-- Forward conversion preserves a single executable monomial. -/
@[simp] theorem toMvPolynomial_monomial
    [CommSemiring R] [DecidableEq R]
    (m : Mono n) (c : R) :
    toMvPolynomial (monomial m c : MvPoly n R cmp) =
      MvPolynomial.monomial (monoEquiv m) c := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨k, rfl⟩
  rw [coeff_toMvPolynomial, coeff_monomial,
    MvPolynomial.coeff_monomial]
  by_cases h : k = m
  · subst k
    simp
  · have h' : monoEquiv m ≠ monoEquiv k := fun heq =>
      h (monoEquiv.injective heq).symm
    simp [h, h']

/-- Adding one executable term is addition by the corresponding Mathlib
monomial, including coefficient cancellation. -/
@[simp] theorem toMvPolynomial_addMonomial
    [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (m : Mono n) (c : R) :
    toMvPolynomial (addMonomial p m c) =
      toMvPolynomial p + MvPolynomial.monomial (monoEquiv m) c := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨k, rfl⟩
  rw [coeff_toMvPolynomial, coeff_addMonomial,
    MvPolynomial.coeff_add, coeff_toMvPolynomial,
    MvPolynomial.coeff_monomial]
  by_cases h : k = m
  · subst k
    simp
  · have h' : monoEquiv m ≠ monoEquiv k := fun heq =>
      h (monoEquiv.injective heq).symm
    simp [h, h']

/-- Constructing from a term stream agrees with folding the corresponding
Mathlib monomials. Duplicate monomials sum and cancellations disappear on
both sides. -/
theorem toMvPolynomial_ofTerms
    [CommSemiring R] [DecidableEq R]
    (terms : List (Mono n × R)) :
    toMvPolynomial (ofTerms terms : MvPoly n R cmp) =
      terms.foldl
        (fun p term =>
          p + MvPolynomial.monomial (monoEquiv term.1) term.2)
        0 := by
  have fold_eq : ∀ (rest : List (Mono n × R)) (init : MvPoly n R cmp),
      toMvPolynomial
          (rest.foldl
            (fun p term => addMonomial p term.1 term.2)
            init) =
        rest.foldl
          (fun p term =>
            p + MvPolynomial.monomial (monoEquiv term.1) term.2)
          (toMvPolynomial init) := by
    intro rest
    induction rest with
    | nil =>
        intro init
        rfl
    | cons term rest ih =>
        intro init
        rw [List.foldl_cons, List.foldl_cons, ih,
          toMvPolynomial_addMonomial]
  have zero_eq :
      toMvPolynomial (0 : MvPoly n R cmp) = 0 := by
    apply MvPolynomial.ext
    intro d
    rcases monoEquiv.surjective d with ⟨m, rfl⟩
    simp
  simpa [ofTerms, zero_eq] using
    fold_eq terms (0 : MvPoly n R cmp)

/-- Rebuild an executable sparse polynomial from a Mathlib multivariate
polynomial's finite support. -/
@[nolint unusedArguments]
def ofMvPolynomial [CommSemiring R] [DecidableEq R]
    (p : MvPolynomial (Fin n) R) : MvPoly n R cmp :=
  ofTerms <| p.support.toList.map fun d =>
    (monoEquiv.symm d, MvPolynomial.coeff d p)

/-- Backward conversion preserves every coefficient. -/
@[simp] theorem coeff_ofMvPolynomial [CommSemiring R] [DecidableEq R]
    (m : Mono n) (p : MvPolynomial (Fin n) R) :
    coeff m (ofMvPolynomial (cmp := cmp) p) =
      MvPolynomial.coeff (monoEquiv m) p := by
  rw [ofMvPolynomial, coeff_ofTerms]
  rw [List.foldl_filter, List.foldl_map]
  simp only [Equiv.symm_apply_eq]
  have fold_pick (q : Fin n →₀ Nat) (f : (Fin n →₀ Nat) → R) :
      ∀ (xs : List (Fin n →₀ Nat)), xs.Nodup → ∀ z,
        xs.foldl
            (fun acc d => if decide (d = q) = true then acc + f d else acc)
            z =
          if q ∈ xs then z + f q else z := by
    intro xs
    induction xs with
    | nil =>
        intro _ z
        simp
    | cons d ds ih =>
        intro hnodup z
        have hd : d ∉ ds := (List.nodup_cons.mp hnodup).1
        have hds : ds.Nodup := (List.nodup_cons.mp hnodup).2
        simp only [List.foldl_cons]
        by_cases hdq : d = q
        · subst d
          rw [ite_eq_left (by simp), ih hds]
          simp [hd]
        · have hqd : q ≠ d := Ne.symm hdq
          rw [ite_eq_right (by simp [hdq]), ih hds]
          simp [hqd]
  rw [fold_pick (monoEquiv m) (fun d => MvPolynomial.coeff d p)
    p.support.toList p.support.nodup_toList]
  by_cases hcoeff : MvPolynomial.coeff (monoEquiv m) p = 0
  · simp [hcoeff]
  · simp [hcoeff]

/-- Converting a Mathlib polynomial to the executable representation and back
recovers the original polynomial. -/
@[simp] theorem toMvPolynomial_ofMvPolynomial
    [CommSemiring R] [DecidableEq R]
    (p : MvPolynomial (Fin n) R) :
    toMvPolynomial (ofMvPolynomial (cmp := cmp) p) = p := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp

/-- Converting an executable polynomial to Mathlib and back recovers the
canonical executable polynomial. -/
@[simp] theorem ofMvPolynomial_toMvPolynomial
    [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    ofMvPolynomial (cmp := cmp) (toMvPolynomial p) = p := by
  apply Hex.MvPoly.ext
  intro m
  simp

end CoherentEquality

/-- Forward conversion sends the executable zero to Mathlib zero. -/
@[simp] theorem toMvPolynomial_zero [CommSemiring R] [DecidableEq R] :
    toMvPolynomial (0 : MvPoly n R cmp) = 0 := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp

section CoherentEquality

variable [BEq R] [LawfulBEq R]

/-- Forward conversion preserves addition. -/
@[simp] theorem toMvPolynomial_add [CommSemiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) :
    toMvPolynomial (p + q) = toMvPolynomial p + toMvPolynomial q := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [coeff_add]

/-- Forward conversion sends executable constants to Mathlib constants. -/
@[simp] theorem toMvPolynomial_C [CommSemiring R] [DecidableEq R] (c : R) :
    toMvPolynomial (C c : MvPoly n R cmp) = MvPolynomial.C c := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [MvPolynomial.coeff_C, coeff_C]

/-- Forward conversion sends executable variables to Mathlib variables. -/
@[simp] theorem toMvPolynomial_X [CommSemiring R] [DecidableEq R]
    (i : Fin n) :
    toMvPolynomial (X i : MvPoly n R cmp) = MvPolynomial.X i := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, coeff_X, MvPolynomial.coeff_X,
    ← monoEquiv_unit]
  by_cases h : m = Mono.unit i
  · subst m
    simp
  · have h' : monoEquiv (Mono.unit i) ≠ monoEquiv m := by
      intro heq
      exact h (monoEquiv.injective heq).symm
    rw [ite_eq_right h, ite_eq_right h']

/-- Forward conversion preserves the multiplicative identity. -/
@[simp] theorem toMvPolynomial_one [CommSemiring R] [DecidableEq R] :
    toMvPolynomial (1 : MvPoly n R cmp) = 1 := by
  rw [show (1 : MvPoly n R cmp) = C 1 from rfl, toMvPolynomial_C,
    MvPolynomial.C_1]

/-- Forward conversion preserves multiplication. -/
@[simp] theorem toMvPolynomial_mul [CommSemiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) :
    toMvPolynomial (p * q) = toMvPolynomial p * toMvPolynomial q := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, coeff_mul, MvPolynomial.coeff_mul]
  have hanti :
      (Mono.splits m).toFinset.map monoPairEquiv.toEmbedding =
        Finset.antidiagonal (monoEquiv m) := by
    ext ab
    constructor
    · intro hab
      rcases Finset.mem_map.mp hab with ⟨xy, hxy, rfl⟩
      rw [Finset.mem_antidiagonal]
      rw [monoPairEmbedding_apply]
      rw [← monoEquiv_mul]
      exact congrArg monoEquiv ((Mono.splits_mem_iff ..).mp
        (List.mem_toFinset.mp hxy))
    · intro hab
      rw [Finset.mem_antidiagonal] at hab
      let xy : Mono n × Mono n :=
        (monoEquiv.symm ab.1, monoEquiv.symm ab.2)
      apply Finset.mem_map.mpr
      refine ⟨xy, ?_, ?_⟩
      · apply List.mem_toFinset.mpr
        apply (Mono.splits_mem_iff ..).mpr
        apply monoEquiv.injective
        simpa [xy] using hab
      · apply Prod.ext <;> simp [xy]
  rw [← hanti, Finset.sum_map]
  simp_rw [monoPairEmbedding_apply, coeff_toMvPolynomial (cmp := cmp)]
  change
    (Mono.splits m).foldl
        (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 =
      ∑ ab ∈ (Mono.splits m).toFinset,
        coeff ab.1 p * coeff ab.2 q
  rw [List.sum_toFinset _ (Mono.splits_nodup m)]
  rw [List.sum_eq_foldl, List.foldl_map]

/-- Forward conversion is injective. -/
theorem toMvPolynomial_injective [CommSemiring R] [DecidableEq R] :
    Function.Injective
      (toMvPolynomial : MvPoly n R cmp → MvPolynomial (Fin n) R) := by
  intro p q h
  rw [← ofMvPolynomial_toMvPolynomial p,
    ← ofMvPolynomial_toMvPolynomial q, h]

/-- Forward conversion is surjective. -/
theorem toMvPolynomial_surjective [CommSemiring R] [DecidableEq R] :
    Function.Surjective
      (toMvPolynomial : MvPoly n R cmp → MvPolynomial (Fin n) R) :=
  fun p => ⟨ofMvPolynomial p, toMvPolynomial_ofMvPolynomial p⟩

/-- The executable sparse representation is ring-equivalent to Mathlib's
multivariate polynomials. -/
def equiv [CommSemiring R] [DecidableEq R] :
    MvPoly n R cmp ≃+* MvPolynomial (Fin n) R where
  toFun := toMvPolynomial
  invFun := ofMvPolynomial
  left_inv := ofMvPolynomial_toMvPolynomial
  right_inv := toMvPolynomial_ofMvPolynomial
  map_mul' := toMvPolynomial_mul
  map_add' := toMvPolynomial_add

/-- The ring equivalence applies as `toMvPolynomial`. -/
@[simp] theorem equiv_apply [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    equiv p = toMvPolynomial p := by
  rfl

/-- The inverse ring equivalence applies as `ofMvPolynomial`. -/
@[simp] theorem equiv_symm_apply [CommSemiring R] [DecidableEq R]
    (p : MvPolynomial (Fin n) R) :
    (equiv (cmp := cmp)).symm p = ofMvPolynomial (cmp := cmp) p := by
  rfl

end CoherentEquality

end

section CoherentEquality

variable [BEq R] [LawfulBEq R]

/-! # Transported Mathlib algebraic structures -/

/-- Natural casts are executable constant polynomials. -/
@[implicit_reducible, nolint unusedArguments]
instance instNatCastMvPoly [CommSemiring R] :
    NatCast (MvPoly n R cmp) where
  natCast k := C (k : R)

/-- Natural scalar multiplication uses one executable constant product. -/
@[implicit_reducible, nolint unusedArguments]
instance instSMulNatMvPoly [CommSemiring R] :
    SMul Nat (MvPoly n R cmp) where
  smul k p := C (k : R) * p

/-- Conversion to Mathlib preserves natural scalar multiplication. -/
theorem toMvPolynomial_nsmul [CommSemiring R] [DecidableEq R]
    (k : Nat) (p : MvPoly n R cmp) :
    toMvPolynomial (k • p) = k • toMvPolynomial p := by
  change toMvPolynomial (C (k : R) * p) = _
  rw [toMvPolynomial_mul, toMvPolynomial_C]
  simp [nsmul_eq_mul]

/-- Conversion to Mathlib preserves natural powers. -/
@[simp] theorem toMvPolynomial_pow [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (k : Nat) :
    toMvPolynomial (p ^ k) = toMvPolynomial p ^ k := by
  induction k with
  | zero =>
      rw [_root_.pow_zero (toMvPolynomial p)]
      have hp : p ^ 0 = (1 : MvPoly n R cmp) := by
        change Hex.MvPoly.npowBySq p 0 = 1
        rw [Hex.MvPoly.npowBySq]
      rw [hp]
      exact toMvPolynomial_one (n := n) (R := R) (cmp := cmp)
  | succ k ih =>
      rw [Hex.MvPoly.pow_succ p k, toMvPolynomial_mul, ih,
        _root_.pow_succ]

/-- Conversion to Mathlib preserves natural-number casts. -/
@[simp] theorem toMvPolynomial_natCast [CommSemiring R] [DecidableEq R]
    (k : Nat) :
    toMvPolynomial (k : MvPoly n R cmp) =
      (k : MvPolynomial (Fin n) R) := by
  change toMvPolynomial (C (k : R)) = _
  rw [toMvPolynomial_C, map_natCast]

/-- Mathlib's commutative-semiring structure, transported along the exact
representation equivalence while retaining every executable operation. -/
instance instCommSemiringMvPoly [CommSemiring R] :
    CommSemiring (MvPoly n R cmp) := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact {
    add := fun p q => p + q
    add_assoc := Hex.MvPoly.add_assoc
    zero := 0
    zero_add := Hex.MvPoly.zero_add
    add_zero := Hex.MvPoly.add_zero
    nsmul := fun k p => C (k : R) * p
    nsmul_zero := fun p => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_nsmul, toMvPolynomial_zero]
      simp
    nsmul_succ := fun k p => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_nsmul, toMvPolynomial_add,
        toMvPolynomial_nsmul]
      simp [_root_.add_mul]
    add_comm := Hex.MvPoly.add_comm
    mul := fun p q => p * q
    mul_assoc := Hex.MvPoly.mul_assoc
    one := 1
    one_mul := Hex.MvPoly.one_mul
    mul_one := Hex.MvPoly.mul_one
    npow := fun k p => Hex.MvPoly.npowBySq p k
    npow_zero := fun p => by
      change Hex.MvPoly.npowBySq p 0 = 1
      rw [Hex.MvPoly.npowBySq]
    npow_succ := fun k p => Hex.MvPoly.pow_succ p k
    zero_mul := Hex.MvPoly.zero_mul
    mul_zero := Hex.MvPoly.mul_zero
    left_distrib := Hex.MvPoly.mul_add
    right_distrib := Hex.MvPoly.add_mul
    natCast := fun k => C (k : R)
    natCast_zero := by
      apply toMvPolynomial_injective
      simp [toMvPolynomial_zero]
    natCast_succ := fun k => by
      apply toMvPolynomial_injective
      simp [toMvPolynomial_C, toMvPolynomial_add, Nat.cast_succ]
    mul_comm := Hex.MvPoly.mul_comm }

/-- Forward conversion preserves coefficientwise negation. -/
@[simp] theorem toMvPolynomial_neg [CommRing R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    toMvPolynomial (-p) = -toMvPolynomial p := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [coeff_neg]

/-- Forward conversion preserves subtraction. -/
@[simp] theorem toMvPolynomial_sub [CommRing R] [DecidableEq R]
    (p q : MvPoly n R cmp) :
    toMvPolynomial (p - q) = toMvPolynomial p - toMvPolynomial q := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [coeff_sub]

/-- Integer casts are executable constant polynomials. -/
@[implicit_reducible, nolint unusedArguments]
instance instIntCastMvPoly [CommRing R] :
    IntCast (MvPoly n R cmp) where
  intCast z := C (z : R)

/-- Integer scalar multiplication uses one executable constant product. -/
@[implicit_reducible, nolint unusedArguments]
instance instSMulIntMvPoly [CommRing R] :
    SMul Int (MvPoly n R cmp) where
  smul z p := C (z : R) * p

/-- Conversion to Mathlib preserves integer scalar multiplication. -/
theorem toMvPolynomial_zsmul [CommRing R] [DecidableEq R]
    (z : Int) (p : MvPoly n R cmp) :
    toMvPolynomial (z • p) = z • toMvPolynomial p := by
  change toMvPolynomial (C (z : R) * p) = _
  rw [toMvPolynomial_mul, toMvPolynomial_C]
  simp [zsmul_eq_mul]

/-- Conversion to Mathlib preserves integer casts. -/
@[simp] theorem toMvPolynomial_intCast [CommRing R] [DecidableEq R]
    (z : Int) :
    toMvPolynomial (z : MvPoly n R cmp) =
      (z : MvPolynomial (Fin n) R) := by
  change toMvPolynomial (C (z : R)) = _
  rw [toMvPolynomial_C, map_intCast]

/-- Mathlib's commutative-ring structure, transported along the exact
representation equivalence while retaining every executable operation. -/
instance instCommRingMvPoly [CommRing R] :
    CommRing (MvPoly n R cmp) := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact {
    __ := instCommSemiringMvPoly
    neg := fun p => -p
    sub := fun p q => p - q
    zsmul := fun z p => C (z : R) * p
    sub_eq_add_neg := fun p q => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_sub, toMvPolynomial_add, toMvPolynomial_neg]
      exact sub_eq_add_neg _ _
    zsmul_zero' := fun p => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_zsmul, toMvPolynomial_zero]
      simp
    zsmul_succ' := fun k p => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_zsmul, toMvPolynomial_add,
        toMvPolynomial_zsmul]
      simp [_root_.add_mul]
    zsmul_neg' := fun k p => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_zsmul, toMvPolynomial_neg,
        toMvPolynomial_zsmul]
      simp [_root_.add_mul, neg_mul, neg_add_rev, _root_.add_comm]
    neg_add_cancel := fun p => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_add, toMvPolynomial_neg, toMvPolynomial_zero]
      simp
    intCast := fun z => C (z : R)
    intCast_ofNat := fun k => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_C, toMvPolynomial_natCast]
      simp
    intCast_negSucc := fun k => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_C, toMvPolynomial_neg,
        toMvPolynomial_natCast]
      simp }

/-- Executable constant polynomials packaged as a ring homomorphism. -/
def constantHom [CommSemiring R] :
    R →+* MvPoly n R cmp := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact {
    toFun := C
    map_one' := by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_C, toMvPolynomial_one, MvPolynomial.C_1]
    map_mul' := fun a b => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_C, toMvPolynomial_mul, toMvPolynomial_C,
        toMvPolynomial_C, MvPolynomial.C_mul]
    map_zero' := by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_C, toMvPolynomial_zero, MvPolynomial.C_0]
    map_add' := fun a b => by
      apply toMvPolynomial_injective
      rw [toMvPolynomial_C, toMvPolynomial_add, toMvPolynomial_C,
        toMvPolynomial_C, MvPolynomial.C_add] }

/-- The constant homomorphism builds the executable constant polynomial. -/
@[simp] theorem constantHom_apply [CommSemiring R]
    (r : R) :
    constantHom (n := n) (cmp := cmp) r = C r := by
  rfl

/-- The coefficient ring acts through executable constant polynomials. -/
@[implicit_reducible]
instance instAlgebraMvPoly [CommSemiring R] :
    Algebra R (MvPoly n R cmp) := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  exact {
    smul := fun r p => C r * p
    algebraMap := constantHom
    commutes' := fun r p => by
      rw [constantHom_apply]
      exact Hex.MvPoly.mul_comm (C r) p
    smul_def' := fun r p => by
      rw [constantHom_apply]
      change C r * p = C r * p
      rfl }

/-- The transported algebra map is executable constant-polynomial
construction. -/
@[simp] theorem algebraMap_apply [CommSemiring R]
    (r : R) :
    algebraMap R (MvPoly n R cmp) r = C r := by
  change constantHom (n := n) (cmp := cmp) r = C r
  exact constantHom_apply r

/-- Conversion to Mathlib preserves algebra scalar multiplication. -/
@[simp] theorem toMvPolynomial_smul [CommSemiring R] [DecidableEq R]
    (r : R) (p : MvPoly n R cmp) :
    toMvPolynomial (r • p) = r • toMvPolynomial p := by
  rw [Algebra.smul_def, Algebra.smul_def, algebraMap_apply,
    MvPolynomial.algebraMap_eq, toMvPolynomial_mul, toMvPolynomial_C]

/-- The exact representation equivalence as an equivalence of
`R`-algebras. -/
noncomputable def algEquiv [CommSemiring R] [DecidableEq R] :
    MvPoly n R cmp ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofRingEquiv (f := equiv) fun r => by
    rw [algebraMap_apply, MvPolynomial.algebraMap_eq,
      equiv_apply, toMvPolynomial_C]

/-- The algebra equivalence applies as `toMvPolynomial`. -/
@[simp] theorem algEquiv_apply [CommSemiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    algEquiv p = toMvPolynomial p := by
  rfl

/-- The inverse algebra equivalence applies as `ofMvPolynomial`. -/
@[simp] theorem algEquiv_symm_apply [CommSemiring R] [DecidableEq R]
    (p : MvPolynomial (Fin n) R) :
    (algEquiv (cmp := cmp)).symm p = ofMvPolynomial (cmp := cmp) p := by
  rfl

end CoherentEquality

section InstanceCoherence

example (p q : MvPoly n Int Mono.lex) :
    toMvPolynomial (p * q) = toMvPolynomial p * toMvPolynomial q := by
  simp

example (p q : MvPoly n Rat Mono.lex) :
    toMvPolynomial (p * q) = toMvPolynomial p * toMvPolynomial q := by
  simp

end InstanceCoherence

end HexMvPolyMathlib
