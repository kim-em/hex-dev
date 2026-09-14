/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Reify
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

namespace HexGenericRankMathlib.Modular

open Hex HexMatrixMathlib PolyLists
open Hex.MvPoly.Kernel
open Hex.Matrix.Lists (all all_iff entry)
open scoped HexMvPolyMathlib BigOperators

/-- Coefficient reduction for the residue check uses only integer arithmetic. -/
def reduce (p : Nat) (a : Poly Int) : Poly Int := mapCoeffs (fun c => c % (p : Int)) a

/-- Equality of polynomial coefficients modulo the characteristic. -/
def equal (p : Nat) (a b : Poly Int) : Bool := beq (reduce p a) (reduce p b)

/-- The leading coefficient of the quoted denominator survives reduction. -/
def nonzero (p : Nat) : Poly Int → Bool
  | [] => false
  | t :: _ => !(t.2 % (p : Int) == 0)

/-- The pivot identity with primitive modular coefficient comparison. -/
def pivotCheck (p : Nat) (A : Rows Int) (c : PolyWitness Int) : Bool :=
  all (fun i => all (fun j => equal p (product c.rank (block A c) (get c.adj) i j)
    (if Nat.beq i j then c.denom else [])) c.rank) c.rank

/-- The all-column identity with primitive modular coefficient comparison. -/
def upperCheck (p n m : Nat) (A : Rows Int) (c : PolyWitness Int) : Bool :=
  let middle := table c.rank m (product c.rank (get c.adj) (rows A c))
  all (fun i => all (fun j => equal p (mul c.denom (get A i j))
    (product c.rank (columns A c) (get middle) i j)) m) n

/-- Shape, canonical data and denominator checks for a residue certificate. -/
def checkRankPolyHeader (p k n m : Nat) (A : Rows Int) (c : PolyWitness Int) : Bool :=
  indices n m c && valid k n m A && valid k c.rank c.rank c.adj &&
    isCanonical k c.denom && nonzero p c.denom

/-- Residue certificates use integer lists throughout the kernel computation. -/
def checkRankPolyList (p k n m : Nat) (A : Rows Int) (c : PolyWitness Int) : Bool :=
  checkRankPolyHeader p k n m A c && pivotCheck p A c && upperCheck p n m A c

/-- Combine the three independently checked parts. -/
theorem checkRankPolyList_parts {p k n m : Nat} {A : Rows Int} {c : PolyWitness Int}
    (hh : checkRankPolyHeader p k n m A c = true)
    (hp : pivotCheck p A c = true) (hu : upperCheck p n m A c = true) :
    checkRankPolyList p k n m A c = true := by
  simp only [checkRankPolyList, hh, hp, hu, Bool.and_self]

variable {C : Type} [CommRing C] [DecidableEq C] [BEq C] [LawfulBEq C] {k : Nat}

/-- Interpret integer coefficient representatives; this is semantic data,
never a coefficient operation on the modular checker's reduction path. -/
def cast (a : Poly Int) : Poly C := a.map fun t => (t.1, (t.2 : C))

/-- Change coefficients on the reference polynomial ring. -/
noncomputable def hom : MvPoly k Int Mono.grevlex →+* MvPoly k C Mono.grevlex :=
  HexMvPolyMathlib.equiv.symm.toRingHom.comp
    ((MvPolynomial.map (Int.castRingHom C)).comp HexMvPolyMathlib.equiv.toRingHom)

theorem hom_monomial (e : Mono k) (a : Int) :
    hom (C := C) (MvPoly.monomial e a) = MvPoly.monomial e (a : C) := by
  apply (HexMvPolyMathlib.equiv (cmp := Mono.grevlex)).injective
  simp [hom, HexMvPolyMathlib.equiv_apply, HexMvPolyMathlib.toMvPolynomial_monomial]

theorem denote_cast (a : Poly Int) :
    PolyLists.denote (k := k) (cast (C := C) a) = hom (PolyLists.denote a) := by
  induction a with
  | nil => simp [cast, PolyLists.denote_nil]
  | cons t ts ih =>
    change MvPoly.monomial (mono k t.1) (t.2 : C) + PolyLists.denote (cast ts) =
      hom (MvPoly.monomial (mono k t.1) t.2 + PolyLists.denote ts)
    rw [map_add, hom_monomial, ih]

theorem hom_coeff (e : Mono k) (a : MvPoly k Int Mono.grevlex) :
    MvPoly.coeff e (hom (C := C) a) = ((MvPoly.coeff e a : Int) : C) := by
  rw [← HexMvPolyMathlib.coeff_toMvPolynomial, ← HexMvPolyMathlib.equiv_apply]
  simp only [hom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, RingEquiv.apply_symm_apply,
    MvPolynomial.coeff_map, Int.coe_castRingHom]
  rw [HexMvPolyMathlib.equiv_apply, HexMvPolyMathlib.coeff_toMvPolynomial]

variable (p : Nat) [CharP C p]

theorem hom_reduce (a : Poly Int) :
    hom (C := C) (PolyLists.denote (k := k) (reduce p a)) = hom (PolyLists.denote a) := by
  induction a with
  | nil => rfl
  | cons t ts ih =>
    unfold reduce mapCoeffs
    dsimp only
    split
    · next hz =>
        change hom (PolyLists.denote (reduce p ts)) =
          hom (MvPoly.monomial (mono k t.1) t.2 + PolyLists.denote ts)
        rw [map_add, hom_monomial, ← ih]
        have hc : (t.2 : C) = 0 := by
          rw [CharP.intCast_eq_intCast_mod C p, hz, Int.cast_zero]
        have hm : MvPoly.monomial (cmp := Mono.grevlex) (mono k t.1) (0 : C) = 0 := by
          apply MvPoly.ext
          intro e
          simp [MvPoly.coeff_monomial, MvPoly.coeff_zero]
        rw [hc, hm, zero_add]
    · change hom (MvPoly.monomial (mono k t.1) (t.2 % (p : Int)) +
          PolyLists.denote (reduce p ts)) =
        hom (MvPoly.monomial (mono k t.1) t.2 + PolyLists.denote ts)
      rw [map_add, map_add, hom_monomial, hom_monomial, ih,
        ← CharP.intCast_eq_intCast_mod C p]

theorem equal_sound {a b : Poly Int} (h : equal p a b = true) :
    hom (C := C) (PolyLists.denote (k := k) a) = hom (PolyLists.denote b) := by
  have h := congrArg (fun a => hom (C := C) (PolyLists.denote (k := k) a))
    (beq_eq_true_iff.mp h)
  simpa only [hom_reduce] using h

theorem nonzero_sound {a : Poly Int} (ha : Canonical k a) (hn : nonzero p a = true) :
    hom (C := C) (PolyLists.denote (k := k) a) ≠ 0 := by
  cases a with
  | nil => simp [nonzero] at hn
  | cons t ts =>
    intro h
    have hc := congrArg (MvPoly.coeff (mono k t.1)) h
    rw [hom_coeff, MvPoly.coeff_zero] at hc
    rw [PolyLists.denote, coeff_denote t.1 (t :: ts) (ha.1 _ (by simp)) ha] at hc
    simp only [coeffAt, ↓reduceIte] at hc
    have hz := (CharP.intCast_eq_zero_iff C p t.2).mp hc
    simp [nonzero, Int.emod_eq_zero_of_dvd hz] at hn

/-- Interpret row lists coefficientwise. -/
def castRows (A : Rows Int) : Rows C := A.map (List.map cast)

/-- Interpret a certificate without changing its rank or selected indices. -/
abbrev castWitness (c : PolyWitness Int) : PolyWitness C := {
  rank := c.rank
  rows := c.rows
  cols := c.cols
  denom := cast c.denom
  adj := castRows c.adj }

omit [CharP C p] [DecidableEq C] [BEq C] [LawfulBEq C] in
theorem get_cast (A : Rows Int) (i j : Nat) :
    get (castRows (C := C) A) i j = cast (get A i j) := by
  change entry (cast []) (entry (List.map (cast (C := C)) [])
    (A.map (List.map (cast (C := C)))) i) j = _
  rw [entry_map, entry_map]
  rfl

theorem pivot_sound {n m : Nat} {A : Rows Int} {c : PolyWitness Int}
    (hA : valid k n m A = true) (hc : valid k c.rank c.rank c.adj = true)
    (h : pivotCheck p A c = true) (i j : Fin c.rank) :
    (∑ t : Fin c.rank, hom (C := C) (PolyLists.denote (k := k) (block A c i t)) *
      hom (PolyLists.denote (get c.adj t j))) =
      if i = j then hom (PolyLists.denote c.denom) else 0 := by
  have h := (all_iff _ _).mp ((all_iff _ _).mp h i i.isLt) j j.isLt
  have he := equal_sound (C := C) (k := k) p h
  rw [denote_product c.rank (block A c) (get c.adj) i j (fun _ _ => canonical_get hA _ _)
    (fun _ _ => canonical_get hc _ _)] at he
  simpa [map_sum, map_mul, Nat.beq_eq, Fin.ext_iff, apply_ite, denote_nil] using he

theorem upper_sound {n m : Nat} {A : Rows Int} {c : PolyWitness Int}
    (hA : valid k n m A = true) (hc : valid k c.rank c.rank c.adj = true)
    (hd : Canonical k c.denom) (h : upperCheck p n m A c = true)
    (i : Fin n) (j : Fin m) :
    hom (C := C) (PolyLists.denote (k := k) c.denom) *
      hom (PolyLists.denote (get A i j)) =
      ∑ t : Fin c.rank, hom (PolyLists.denote (columns A c i t)) *
        (∑ s : Fin c.rank, hom (PolyLists.denote (get c.adj t s)) *
          hom (PolyLists.denote (rows A c s j))) := by
  let middle := table c.rank m (product c.rank (get c.adj) (rows A c))
  have hm (t : Nat) (ht : t < c.rank) : Canonical k (get middle t j) := by
    rw [get_table _ _ _ _ _ ht j.isLt]
    exact product_canonical _ _ _ _ _ (fun _ _ => canonical_get hc _ _)
      (fun _ _ => canonical_get hA _ _)
  have he := equal_sound (C := C) (k := k) p
    ((all_iff _ _).mp ((all_iff _ _).mp h i i.isLt) j j.isLt)
  change hom (PolyLists.denote (mul c.denom (get A i j))) =
    hom (PolyLists.denote (product c.rank (columns A c) (get middle) i j)) at he
  rw [denote_mul _ _ hd (canonical_get hA _ _),
    denote_product c.rank (columns A c) (get middle) i j (fun _ _ => canonical_get hA _ _) hm] at he
  simp only [map_mul, map_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro t _
  rw [get_table _ _ _ _ _ t.isLt j.isLt,
    denote_product c.rank (get c.adj) (rows A c) t j (fun _ _ => canonical_get hc _ _)
      (fun _ _ => canonical_get hA _ _)]
  simp only [map_sum, map_mul]

/-- A modular list check establishes all three reference certificate
identities over the residue coefficient carrier. -/
theorem checkRankPolyList_sound {k n m : Nat} {A : Rows Int} {c : PolyWitness Int}
    (h : checkRankPolyList p k n m A c = true) :
    Hex.Matrix.checkRank (PolyLists.matrix (k := k) n m (castRows (C := C) A))
      ((castWitness (C := C) c).decode k (by
        simp only [checkRankPolyList, checkRankPolyHeader, Bool.and_eq_true] at h
        exact h.1.1.1.1.1.1)) = true := by
  simp only [checkRankPolyList, checkRankPolyHeader, Bool.and_assoc, Bool.and_eq_true] at h
  rcases h with ⟨hi, hA, hc, hd, hn, hp, hu⟩
  have hd := isCanonical_iff.mp hd
  apply (checkRank_iff_matrixEquiv _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change PolyLists.denote (cast c.denom) ≠ 0
    rw [denote_cast]
    exact nonzero_sound p hd hn
  · apply Matrix.ext
    intro i j
    dsimp only [PolyWitness.decode, castWitness]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, PolyLists.matrix_apply,
      PolyWitness.get_ofFn, PolyWitness.row, PolyWitness.col,
      castWitness, get_cast, denote_cast]
    simpa [PolyLists.block, mul_ite] using
      pivot_sound (C := C) p hA hc hp i j
  · apply Matrix.ext
    intro i j
    dsimp only [PolyWitness.decode, castWitness]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      smul_eq_mul, PolyLists.matrix_apply, PolyWitness.get_ofFn,
      PolyWitness.row, PolyWitness.col, get_cast, denote_cast, id_eq]
    simpa [PolyLists.rows, PolyLists.columns] using upper_sound (C := C) p hA hc hd hu i j

omit [CharP C p] in
theorem denote_raw_terms (f : Int → C) (ts : List (Mono k × Int)) :
    PolyLists.denote (termLists f ts) = Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) f ts := by
  simpa only [PolyLists.denote, Hex.MvPoly.Kernel.denote_normalize] using
    denote_terms f ts (normalize (termLists f ts)) rfl

omit [CharP C p] in
theorem hom_terms (ts : List (Mono k × Int)) :
    hom (C := C) (Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) id ts) =
      Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) (Int.cast : Int → C) ts := by
  rw [← denote_raw_terms id ts, ← denote_cast, ← denote_raw_terms]
  congr 1
  simp [cast, termLists, List.map_map]

/-- Reflection's residue interpretation transfers to integer coefficient
representatives using a separate primitive modular equality check. -/
theorem interpret_entry {F : Type*} [CommRing F] (ι : C →+* F) (v : Fin k → F)
    (ts : List (Mono k × Int)) (L : Poly Int)
    (h : equal p (normalize (termLists id ts)) L = true) (a : F)
    (ha : MvPoly.eval₂ ι v
      (Hex.Reflect.ofIntTerms (cmp := Mono.grevlex) (Int.cast : Int → C) ts) = a) :
    HexMvPolyMathlib.eval₂MathlibHom ι v (PolyLists.denote (cast L)) = a := by
  rw [denote_cast]
  have he := equal_sound (C := C) (k := k) p h
  rw [PolyLists.denote, Hex.MvPoly.Kernel.denote_normalize] at he
  change hom (PolyLists.denote (termLists id ts)) = hom (PolyLists.denote L) at he
  rw [← he, denote_raw_terms, hom_terms, HexMvPolyMathlib.eval₂MathlibHom_apply]
  exact ha

open scoped HexModArithMathlib.ZMod64

/-- The residue provider's ring is a domain at its supplied prime modulus. -/
scoped instance residueDomain {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p] :
    IsDomain (Hex.ZMod64 p) := by
  let : Nontrivial (Hex.ZMod64 p) := ⟨⟨1, 0, Hex.ZMod64.one_ne_zero⟩⟩
  let : NoZeroDivisors (Hex.ZMod64 p) :=
    ⟨fun h => Hex.ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero_of_prime_modulus h⟩
  exact NoZeroDivisors.to_isDomain _

/-- Machine residues have the characteristic supplied by their provider. -/
scoped instance residueChar {p : Nat} [Hex.ZMod64.Bounds p] : CharP (Hex.ZMod64 p) p :=
  charP_of_injective_ringHom (f := HexModArithMathlib.ZMod64.equiv.symm.toRingHom)
    HexModArithMathlib.ZMod64.equiv.symm.injective p

/-- The residue interpretation into a polynomial ring has constant image. -/
theorem residue_C (p : Nat) [Hex.ZMod64.Bounds p] {D : Type*}
    [CommRing D] [CharP D p] {σ : Type*} :
    HexReflectMathlib.residueHom p (MvPolynomial σ D) =
      MvPolynomial.C.comp (HexReflectMathlib.residueHom p D) := by
  ext a
  have ha : (a.toNat : Hex.ZMod64 p) = a :=
    (Hex.ZMod64.natCast_op_eq_ofNat _).trans (Hex.ZMod64.ofNat_toNat a)
  rw [← ha]
  simp

/-- The residue provider's injective coefficient map and literal variables
justify generic rank over a prime-characteristic polynomial ring. -/
theorem rank_variables_residue (p : Nat) [Hex.ZMod64.Bounds p]
    {D : Type*} [CommRing D] [IsDomain D] [CharP D p]
    {σ : Type*} (v : Fin k → MvPolynomial σ D) (f : Fin k → σ)
    (hf : Function.Injective f) (hv : v = MvPolynomial.X ∘ f)
    {P : Hex.Matrix (MvPoly k (Hex.ZMod64 p) Mono.grevlex) n m}
    {c : Hex.Matrix.RankCert (MvPoly k (Hex.ZMod64 p) Mono.grevlex) n m}
    (h : Hex.Matrix.checkRank P c = true)
    (A : Matrix (Fin n) (Fin m) (MvPolynomial σ D))
    (hA : A = (symbolic P).map (MvPolynomial.eval₂Hom (HexReflectMathlib.residueHom p _) v)) :
    A.rank = c.rank :=
  rank_variables (HexReflectMathlib.residueHom p _) (HexReflectMathlib.residueHom p D)
    (HexReflectMathlib.residueHom_injective p D) (residue_C p) v f hf hv h A hA

end HexGenericRankMathlib.Modular
