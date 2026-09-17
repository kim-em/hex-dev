/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Reify
public import HexReflectMathlib.KernelResidue

@[expose] public section

namespace HexGenericRankMathlib.Modular

open Hex HexMatrixMathlib PolyLists
open Hex.MvPoly.Kernel
open Hex.Matrix.Lists (all all_iff entry entry_eq_getD)
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64 BigOperators

/-! The structural checks mirror `PolyLists`, but arithmetic is explicitly
modulus-parametrised. This keeps the kernel term on the shared residue operations
without introducing local arithmetic instances on `Nat`. -/

section
/-- Sum residue polynomials using the shared modular merge. -/
def sum (p : Nat) (f : Nat → Poly Nat) : Nat → Poly Nat
  | 0 => []
  | t + 1 => addMod p (sum p f t) (f t)

/-- One entry of a product over canonical natural residues. -/
def product (p r : Nat) (A B : Nat → Nat → Poly Nat) (i j : Nat) : Poly Nat :=
  sum p (fun t => mulMod p (A i t) (B t j)) r

/-- Exact dimensions and modulus-parametrised canonicality. -/
def valid (p k n m : Nat) (A : Rows Nat) : Bool :=
  Nat.beq A.length n && A.all (fun row => Nat.beq row.length m && row.all (isCanonicalMod p k))

/-- The pivot identity over the shared natural-residue representation. -/
def pivotCheck (p : Nat) (A : Rows Nat) (c : PolyWitness Nat) : Bool :=
  all (fun i => all (fun j => beq (product p c.rank (block A c) (get c.adj) i j)
    (if Nat.beq i j then c.denom else [])) c.rank) c.rank

/-- The all-column identity with shared modular arithmetic. -/
def upperCheck (p n m : Nat) (A : Rows Nat) (c : PolyWitness Nat) : Bool :=
  let middle := table c.rank m (product p c.rank (get c.adj) (rows A c))
  all (fun i => all (fun j => beq (mulMod p c.denom (get A i j))
    (product p c.rank (columns A c) (get middle) i j)) m) n

/-- Shape, canonical residues, and a nonzero polynomial denominator. -/
def checkRankPolyHeader (p k n m : Nat) (A : Rows Nat) (c : PolyWitness Nat) : Bool :=
  indices n m c && valid p k n m A && valid p k c.rank c.rank c.adj &&
    isCanonicalMod p k c.denom && !isZero c.denom

/-- Rank certificate checking with no coefficient-carrier arithmetic in the kernel. -/
def checkRankPolyList (p k n m : Nat) (A : Rows Nat) (c : PolyWitness Nat) : Bool :=
  checkRankPolyHeader p k n m A c && pivotCheck p A c && upperCheck p n m A c

/-- Combine the independently checked header and identities. -/
theorem checkRankPolyList_parts {p k n m : Nat} {A : Rows Nat} {c : PolyWitness Nat}
    (hh : checkRankPolyHeader p k n m A c = true)
    (hp : pivotCheck p A c = true) (hu : upperCheck p n m A c = true) :
    checkRankPolyList p k n m A c = true := by
  simp only [checkRankPolyList, hh, hp, hu, Bool.and_self]

variable (p : Nat) [Hex.ZMod64.Bounds p] {k : Nat}

/-- Read residue rows only on the semantic side of the checker. -/
def castRows (A : Rows Nat) : Rows (Hex.ZMod64 p) := A.map (List.map (toResidues p))

/-- Decode a certificate without changing its selected indices. -/
abbrev castWitness (c : PolyWitness Nat) : PolyWitness (Hex.ZMod64 p) := {
  rank := c.rank
  rows := c.rows
  cols := c.cols
  denom := toResidues p c.denom
  adj := castRows p c.adj }

theorem get_cast (A : Rows Nat) (i j : Nat) :
    get (castRows p A) i j = toResidues p (get A i j) := by
  change entry (toResidues p []) (entry (List.map (toResidues p) [])
    (A.map (List.map (toResidues p))) i) j = _
  rw [entry_map, entry_map]
  rfl

/-- The Mathlib ring instance and native residue instance give the same denotation. -/
theorem denote_cast (a : Poly Nat) :
    PolyLists.denote (k := k) (toResidues p a) = denoteMod p (cmp := Mono.grevlex) a := by
  induction a with
  | nil => rfl
  | cons t ts ih =>
    change MvPoly.monomial (mono k t.1) (Hex.ZMod64.ofNat p t.2) +
      PolyLists.denote (toResidues p ts) =
      MvPoly.monomial (mono k t.1) (Hex.ZMod64.ofNat p t.2) + denoteMod p ts
    rw [ih]
    rfl

omit [Hex.ZMod64.Bounds p] in
theorem canonical_nil : CanonicalMod p k [] := by simp [CanonicalMod, Canonical]

omit [Hex.ZMod64.Bounds p] in
theorem sum_canonical (f : Nat → Poly Nat) (r : Nat)
    (hf : ∀ i, i < r → CanonicalMod p k (f i)) : CanonicalMod p k (sum p f r) := by
  induction r with
  | zero => exact canonical_nil p
  | succ r ih => exact addMod_canonical p (ih fun i hi => hf i (by omega)) (hf r (by omega))

theorem denote_sum (f : Nat → Poly Nat) (r : Nat) (hf : ∀ i, i < r → CanonicalMod p k (f i)) :
    denoteMod p (n := k) (cmp := Mono.grevlex) (sum p f r) = ∑ i : Fin r, denoteMod p (cmp := Mono.grevlex) (f i) := by
  induction r with
  | zero => simp [sum, denoteMod_nil]
  | succ r ih => rw [sum, denoteMod_addMod p (sum_canonical p f r (fun i hi => hf i (by omega))) (hf r (by omega)), ih (fun i hi => hf i (by omega)), Fin.sum_univ_castSucc]; rfl

omit [Hex.ZMod64.Bounds p] in
theorem product_canonical (r : Nat) (A B : Nat → Nat → Poly Nat) (i j : Nat)
    (hA : ∀ t, t < r → CanonicalMod p k (A i t))
    (hB : ∀ t, t < r → CanonicalMod p k (B t j)) : CanonicalMod p k (product p r A B i j) :=
  sum_canonical p _ _ fun t ht => mulMod_canonical p (hA t ht) (hB t ht)

theorem denote_product (r : Nat) (A B : Nat → Nat → Poly Nat) (i j : Nat)
    (hA : ∀ t, t < r → CanonicalMod p k (A i t))
    (hB : ∀ t, t < r → CanonicalMod p k (B t j)) :
    denoteMod p (n := k) (cmp := Mono.grevlex) (product p r A B i j) =
      ∑ t : Fin r, denoteMod p (cmp := Mono.grevlex) (A i t) * denoteMod p (cmp := Mono.grevlex) (B t j) := by
  rw [product, denote_sum p _ _ (fun t ht => mulMod_canonical p (hA t ht) (hB t ht))]
  apply Finset.sum_congr rfl
  intro t _
  exact denoteMod_mulMod p (hA t t.isLt) (hB t t.isLt)

omit [Hex.ZMod64.Bounds p] in
theorem canonical_get {n m : Nat} {A : Rows Nat} (h : valid p k n m A = true)
    (i j : Nat) : CanonicalMod p k (get A i j) := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true] at h
  rw [PolyLists.get, entry_eq_getD, entry_eq_getD]
  by_cases hi : i < A.length
  · rw [getD_eq_getElem' A i [] hi]
    have hr := (h.2 _ (List.getElem_mem hi)).2
    by_cases hj : j < A[i].length
    · rw [getD_eq_getElem' _ _ _ hj]
      exact isCanonicalMod_iff.mp (hr _ (List.getElem_mem hj))
    · rw [getD_eq_default' _ _ _ (by omega)]
      exact canonical_nil p
  · rw [getD_eq_default' A i [] (by omega)]
    exact canonical_nil p

theorem pivot_sound {n m : Nat} {A : Rows Nat} {c : PolyWitness Nat}
    (hA : valid p k n m A = true) (hc : valid p k c.rank c.rank c.adj = true)
    (h : pivotCheck p A c = true) (i j : Fin c.rank) :
    (∑ t : Fin c.rank, denoteMod p (n := k) (cmp := Mono.grevlex) (block A c i t) * denoteMod p (cmp := Mono.grevlex) (get c.adj t j)) =
      if i = j then denoteMod p (cmp := Mono.grevlex) c.denom else 0 := by
  have h := (all_iff _ _).mp ((all_iff _ _).mp h i i.isLt) j j.isLt
  have he := congrArg (denoteMod p (n := k) (cmp := Mono.grevlex)) (beq_eq_true_iff.mp h)
  rw [denote_product p c.rank (block A c) (get c.adj) i j (fun _ _ => canonical_get p hA _ _)
    (fun _ _ => canonical_get p hc _ _)] at he
  simpa [Nat.beq_eq, Fin.ext_iff, apply_ite, denoteMod_nil] using he

theorem upper_sound {n m : Nat} {A : Rows Nat} {c : PolyWitness Nat}
    (hA : valid p k n m A = true) (hc : valid p k c.rank c.rank c.adj = true)
    (hd : CanonicalMod p k c.denom) (h : upperCheck p n m A c = true)
    (i : Fin n) (j : Fin m) :
    denoteMod p (n := k) (cmp := Mono.grevlex) c.denom * denoteMod p (cmp := Mono.grevlex) (get A i j) =
      ∑ t : Fin c.rank, denoteMod p (cmp := Mono.grevlex) (columns A c i t) *
        (∑ s : Fin c.rank, denoteMod p (cmp := Mono.grevlex) (get c.adj t s) * denoteMod p (cmp := Mono.grevlex) (rows A c s j)) := by
  let middle := table c.rank m (product p c.rank (get c.adj) (rows A c))
  have hm (t : Nat) (ht : t < c.rank) : CanonicalMod p k (get middle t j) := by
    rw [get_table _ _ _ _ _ ht j.isLt]
    exact product_canonical p _ _ _ _ _ (fun _ _ => canonical_get p hc _ _)
      (fun _ _ => canonical_get p hA _ _)
  have he := congrArg (denoteMod p (n := k) (cmp := Mono.grevlex)) (beq_eq_true_iff.mp
    ((all_iff _ _).mp ((all_iff _ _).mp h i i.isLt) j j.isLt))
  change denoteMod p (cmp := Mono.grevlex) (mulMod p c.denom (get A i j)) =
    denoteMod p (cmp := Mono.grevlex) (product p c.rank (columns A c) (get middle) i j) at he
  rw [denoteMod_mulMod p hd (canonical_get p hA _ _),
    denote_product p c.rank (columns A c) (get middle) i j (fun _ _ => canonical_get p hA _ _) hm] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro t _
  rw [get_table _ _ _ _ _ t.isLt j.isLt,
    denote_product p c.rank (get c.adj) (rows A c) t j (fun _ _ => canonical_get p hc _ _)
      (fun _ _ => canonical_get p hA _ _)]

/-- The residue checker establishes the reference rank certificate through `denoteMod`. -/
theorem checkRankPolyList_sound {k n m : Nat} {A : Rows Nat} {c : PolyWitness Nat}
    (h : checkRankPolyList p k n m A c = true) :
    Hex.Matrix.checkRank (PolyLists.matrix (k := k) n m (castRows p A))
      ((castWitness p c).decode k (by
        simp only [checkRankPolyList, checkRankPolyHeader, Bool.and_eq_true] at h
        exact h.1.1.1.1.1.1)) = true := by
  simp only [checkRankPolyList, checkRankPolyHeader, Bool.and_assoc, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  rcases h with ⟨hi, hA, hc, hd, hn, hp, hu⟩
  have hd := isCanonicalMod_iff.mp hd
  apply (checkRank_iff_matrixEquiv _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change PolyLists.denote (toResidues p c.denom) ≠ 0
    rw [denote_cast]
    intro hz
    have := (isZero_mod_iff p (cmp := Mono.grevlex) hd).mpr hz
    simp [hn] at this
  · apply Matrix.ext
    intro i j
    dsimp only [PolyWitness.decode, castWitness]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, PolyLists.matrix_apply,
      PolyWitness.get_ofFn, PolyWitness.row, PolyWitness.col,
      castWitness, get_cast, denote_cast]
    simpa [PolyLists.block, mul_ite] using
      pivot_sound p hA hc hp i j
  · apply Matrix.ext
    intro i j
    dsimp only [PolyWitness.decode, castWitness]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      smul_eq_mul, PolyLists.matrix_apply, PolyWitness.get_ofFn,
      PolyWitness.row, PolyWitness.col, get_cast, denote_cast, id_eq]
    simpa [PolyLists.rows, PolyLists.columns] using
      upper_sound p hA hc hd hu i j

end

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
    (HexReflectMathlib.residueHom_injective p D) (HexReflectMathlib.residueHom_mvPolynomial p σ D) v f hf hv h A hA

end HexGenericRankMathlib.Modular
