/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Mixed
public import HexKroneckerMathlib.Kernel

public section

/-! Soundness of mixed list/tree certificates through the integer polynomial
model. Tree models require checked atom bounds; malformed atoms get no value. -/

namespace Hex.Kronecker

/-- The polynomial model of a row whose atoms have been validated. -/
noncomputable def rowPolynomial (k : Nat) : (a : List Expr) →
    a.all (Expr.wellFormed k) = true → List (MvPolynomial (Fin k) Int)
  | [], _ => []
  | e :: es, h => e.toMvPolynomial (Bool.and_eq_true_iff.mp h).1 ::
      rowPolynomial k es (Bool.and_eq_true_iff.mp h).2

/-- All atom bounds are supplied by validation, including in empty rows. -/
noncomputable def treePolynomial (k : Nat) : (a : TreeMatrix) →
    treeValid k a = true → List (List (MvPolynomial (Fin k) Int))
  | [], _ => []
  | row :: rows, h => rowPolynomial k row (Bool.and_eq_true_iff.mp h).1 ::
      treePolynomial k rows (Bool.and_eq_true_iff.mp h).2

theorem rowPolynomial_length (k : Nat) (a : List Expr) (h : a.all (Expr.wellFormed k) = true) :
    (rowPolynomial k a h).length = a.length := by
  induction a with
  | nil => rfl
  | cons e es ih => simp only [rowPolynomial, List.length_cons, ih]

theorem treePolynomial_length (k : Nat) (a : TreeMatrix) (h : treeValid k a = true) :
    (treePolynomial k a h).length = a.length := by
  induction a with
  | nil => rfl
  | cons row rows ih =>
    exact congrArg Nat.succ (ih (Bool.and_eq_true_iff.mp h).2)

theorem rowPolynomial_eval {R : Type u} [CommRing R] (k : Nat) (a : List Expr)
    (h : a.all (Expr.wellFormed k) = true) (v : Nat → R) :
    a.map (Expr.denote v) = (rowPolynomial k a h).map
      (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin k => v i.val)) := by
  induction a with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, rowPolynomial]
    rw [← denote_eq_eval₂, Expr.denoteFin_eq, ih]

theorem treePolynomial_eval {R : Type u} [CommRing R] (k : Nat) (a : TreeMatrix)
    (h : treeValid k a = true) (v : Nat → R) :
    a.map (List.map (Expr.denote v)) = (treePolynomial k a h).map
      (List.map (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin k => v i.val))) := by
  induction a with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, treePolynomial]
    rw [rowPolynomial_eval k row (Bool.and_eq_true_iff.mp h).1 v,
      ih (Bool.and_eq_true_iff.mp h).2]

theorem evalTreeMatrix_eval {k : Nat} (s : SizeBound) (a : TreeMatrix)
    (h : treeValid k a = true) :
    evalTreeMatrix s a = (treePolynomial k a h).map
      (List.map (MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2 ^ s.digitBits : Nat) : Int) ^ s.strides.getD i.val 0))) := by
  unfold evalTreeMatrix
  have he : evalKron (2 ^ s.digitBits) s.strides =
      Expr.denote (fun i => ((2 ^ s.digitBits : Nat) : Int) ^ s.strides.getD i 0) := by
    funext e
    exact evalKron_eq_denote _ _ e
  rw [he]
  exact treePolynomial_eval k a h _

/-- Tree evaluation is total on natural-number assignments. Atom validation is
needed only when constructing the finite polynomial model. -/
@[expose] def denoteTreeMatrix (n m : Nat) {R : Type u} [CommRing R]
    (v : Nat → R) (a : TreeMatrix) : _root_.Matrix (Fin n) (Fin m) R :=
  fun i j => ((a.getD i.val []).getD j.val (.int 0)).denote v

theorem treePolynomial_entry {R : Type u} [CommRing R] (k : Nat) (a : TreeMatrix)
    (h : treeValid k a = true) (v : Nat → R) (i j : Nat) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin k => v i.val)
      (((treePolynomial k a h).getD i []).getD j 0) =
      ((a.getD i []).getD j (.int 0)).denote v := by
  have he := congrArg (fun rows : List (List R) => (rows.getD i []).getD j 0)
    (treePolynomial_eval k a h v)
  let E := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin k => v i.val)
  have hleft : ((a.map (List.map (Expr.denote v))).getD i []).getD j 0 =
      ((a.getD i []).getD j (.int 0)).denote v := by
    rw [show ([] : List R) = List.map (Expr.denote v) [] from rfl, List.getD_map]
    rw [show (0 : R) = Expr.denote v (.int 0) from (Int.cast_zero).symm, List.getD_map]
  have hright : (((treePolynomial k a h).map (List.map E)).getD i []).getD j 0 =
      E (((treePolynomial k a h).getD i []).getD j 0) := by
    rw [show ([] : List R) = List.map E [] from rfl, List.getD_map]
    rw [← map_zero E, List.getD_map]
  exact hright.symm.trans (he.symm.trans hleft)

theorem polyProduct_entry {k n r m : Nat} {a b : List (List (MvPolynomial (Fin k) Int))}
    (ha : a.length = n) (har : ∀ row ∈ a, row.length = r) (hb : b.length = r)
    (i : Fin n) (j : Fin m) :
    ((polyProduct (columnsWith 0 m b) a).getD i.val []).getD j.val 0 =
      ∑ t : Fin r, (a.getD i.val []).getD t.val 0 * (b.getD t.val []).getD j.val 0 := by
  have hi : i.val < a.length := by simpa only [ha] using i.isLt
  have hj : j.val < (columnsWith (0 : MvPolynomial (Fin k) Int) m b).length := by
    simpa only [columnsWith_length] using j.isLt
  rw [polyProduct, map_getD_of_lt _ _ [] [] i.val hi,
    map_getD_of_lt _ _ [] 0 j.val hj, columnsWith_getD _ _ _ _ j.isLt]
  have hal : (a.getD i.val []).length = r := by
    apply har
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  rw [polyDot_sum r _ _ hal (by simpa using hb)]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_getD_of_lt _ _ [] 0 t.val (by simpa only [hb] using t.isLt)]

namespace Kernel

theorem treeRow_bound (k : Nat) (a : List Expr) (h : a.all (Expr.wellFormed k) = true) :
    List.Forall₂ Exact (a.map (fun e => ⟨e.degrees k, e.height⟩)) (rowPolynomial k a h) := by
  induction a with
  | nil => exact .nil
  | cons e es ih =>
    exact .cons (expr_bound e (Bool.and_eq_true_iff.mp h).1) (ih _)

theorem treeMatrix_bound (k : Nat) (a : TreeMatrix) (h : treeValid k a = true) :
    List.Forall₂ (List.Forall₂ Exact) (treeMatrix k a) (treePolynomial k a h) := by
  induction a with
  | nil => exact .nil
  | cons row rows ih =>
    exact .cons (treeRow_bound k row (Bool.and_eq_true_iff.mp h).1) (ih _)

theorem treeColumns_bound (k m : Nat) (a : TreeMatrix) (h : treeValid k a = true) :
    List.Forall₂ (List.Forall₂ Exact) (boundColumns k m (treeMatrix k a))
      (columnsWith 0 m (treePolynomial k a h)) := by
  rw [boundColumns_eq]
  exact columnsWith_rel _ _ (Exact.zero k) m (treeMatrix_bound k a h)

theorem mulTree_polynomial {mode : MulMode} {k n r m ib sb : Nat}
    {a c : TermMatrix} {b : TreeMatrix} (hbv : treeValid k b = true) (h : mulTree mode k n r m a b c ib sb = true) :
    polyProduct (columnsWith 0 m (treePolynomial k b hbv)) (matrixPolynomial k a) = matrixPolynomial k c := by
  obtain ⟨hw, he⟩ := Bool.and_eq_true_iff.mp h
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  have hc := (Bool.and_eq_true_iff.mp hw).2
  let products := product k (boundColumns k m (treeMatrix k b)) (matrix k a)
  let s := plan (common k products.flatten (matrix k c).flatten) ib sb
  have hprod := product_bound (treeColumns_bound k m b hbv) (matrix_bound k n r a ha)
  have hcb := matrix_bound k n m c hc
  have hpf := List.rel_flatten hprod
  have hcf := List.rel_flatten hcb
  have hlen := common_length k _ _ (lengths hpf) (lengths hcf)
  have hs : s.strides.length = k := by simpa only [s, plan, length_makeStrides] using hlen
  change checkRows mode s r (Hex.Matrix.Packed.columns m (evalTreeMatrix s b))
    (packMatrix s a) (packMatrix s c) = true at he
  rw [packMatrix_eval s hs a ha, evalTreeMatrix_eval s b hbv, packMatrix_eval s hs c hc,
    ← columnsWith_int] at he
  let v := fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0
  let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
  have hm : columnsWith (0 : Int) m ((treePolynomial k b hbv).map (List.map E)) =
      (columnsWith 0 m (treePolynomial k b hbv)).map (List.map E) := by
    simpa only [map_zero] using columnsWith_map E 0 m (treePolynomial k b hbv)
  change checkRows mode s r (columnsWith 0 m ((treePolynomial k b hbv).map (List.map E)))
    ((matrixPolynomial k a).map (List.map E)) ((matrixPolynomial k c).map (List.map E)) = true at he
  rw [hm] at he
  have he := checkRows_polynomial mode s r v _ _ _ he
  apply flatten_injective he
  exact lists hpf hcf (List.rel_flatten he)


theorem mulTreeMod_polynomial {mode : MulMode} {k n r m p ib sb : Nat}
    {a c q : TermMatrix} {b : TreeMatrix} (hbv : treeValid k b = true) (h : mulTreeMod mode k n r m p a b c q ib sb = true) :
    List.Forall₂ (fun a b => a.length = b.length)
      (polyProduct (columnsWith 0 m (treePolynomial k b hbv)) (matrixPolynomial k a)) (matrixPolynomial k c) ∧
    List.zipWith (List.zipWith (·-·))
      (polyProduct (columnsWith 0 m (treePolynomial k b hbv)) (matrixPolynomial k a)) (matrixPolynomial k c) =
      (matrixPolynomial k q).map (List.map (MvPolynomial.C (p:Int)*·)) := by
  obtain ⟨hv, he⟩ := Bool.and_eq_true_iff.mp h
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1).2
  have hw₁ := (Bool.and_eq_true_iff.mp hw).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw₁).1).2
  have hc := (Bool.and_eq_true_iff.mp hw₁).2
  have hq := (Bool.and_eq_true_iff.mp hw).2
  let products := product k (boundColumns k m (treeMatrix k b)) (matrix k a)
  let differences := difference products.flatten (matrix k c).flatten
  let scaled := (matrix k q).flatten.map (mul ⟨zeroDegrees k, p⟩)
  let s := plan (common k differences scaled) ib sb
  have hprod := product_bound (treeColumns_bound k m b hbv) (matrix_bound k n r a ha)
  have hcb := matrix_bound k n m c hc
  have hqb := matrix_bound k n m q hq
  have hdb := difference_bound (List.rel_flatten hprod) (List.rel_flatten hcb)
  have hsb := scaled_bound p (List.rel_flatten hqb)
  have hlen := common_length k _ _ (lengths hdb) (lengths hsb)
  have hs : s.strides.length = k := by simpa only [s, plan, length_makeStrides] using hlen
  change checkRowsMod mode s r p (Hex.Matrix.Packed.columns m (evalTreeMatrix s b))
    (packMatrix s a) (packMatrix s c) (packMatrix s q) = true at he
  rw [packMatrix_eval s hs a ha, evalTreeMatrix_eval s b hbv, packMatrix_eval s hs c hc,
    packMatrix_eval s hs q hq, ← columnsWith_int] at he
  let v := fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0
  let E := MvPolynomial.eval₂Hom (RingHom.id Int) v
  have hm : columnsWith (0 : Int) m ((treePolynomial k b hbv).map (List.map E)) =
      (columnsWith 0 m (treePolynomial k b hbv)).map (List.map E) := by
    simpa only [map_zero] using columnsWith_map E 0 m (treePolynomial k b hbv)
  change checkRowsMod mode s r p (columnsWith 0 m ((treePolynomial k b hbv).map (List.map E)))
    ((matrixPolynomial k a).map (List.map E)) ((matrixPolynomial k c).map (List.map E))
    ((matrixPolynomial k q).map (List.map E)) = true at he
  rw [hm] at he
  have he := checkRowsMod_polynomial mode s r p v _ _ _ _ he
  refine ⟨he.1, ?_⟩
  apply flatten_injective he.2
  rw [flatten_zipWith _ he.1, ← List.map_flatten]
  apply lists hdb hsb
  have hef := List.rel_flatten he.2
  rw [flatten_zipWith _ he.1, ← List.map_flatten] at hef
  exact hef

theorem packNat_eq (base : Nat) (ss : List Nat) (ts : Hex.MvPoly.Kernel.PolyList Int) :
    packNat base ss ts = Hex.Kronecker.packTerms base ss ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨e,c⟩ := t
    change Int.add (Int.mul c (Int.ofNat (Nat.pow base (code ss e)))) (packNat base ss ts) = _
    rw [ih, packTerms_cons, power_eq]
    rfl

theorem treeTermsEq_polynomial {k : Nat} {lhs : Expr} {rhs : Hex.MvPoly.Kernel.PolyList Int}
    (hl : lhs.WellFormed k) (h : treeTermsEq k lhs rhs = true) : lhs.toMvPolynomial hl = termsPolynomial k rhs := by
  obtain ⟨hw, he⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hw
  let s := plan (add (⟨lhs.degrees k, lhs.height⟩) (terms k rhs))
  have hbl := expr_bound lhs hl
  have hbr := terms_bound k rhs hr
  have hs : s.strides.length = k := by simp [s, plan, add, hbl.length, hbr.length]
  have he := (Int.beq'_eq _ _).mp he
  change evalKron (2^s.digitBits) s.strides lhs = packNat (2^s.digitBits) s.strides rhs at he
  simp only [packNat_eq] at he
  apply pair hbl hbr
  rw [evalKron_eq_eval₂ _ _ lhs hl, packTerms_eq_eval₂ _ _ hs rhs hr] at he
  exact he

theorem treeTermsEqMod_polynomial {k p : Nat} {lhs : Expr} {rhs q : Hex.MvPoly.Kernel.PolyList Int}
    (hl : lhs.WellFormed k) (h : treeTermsEqMod k p lhs rhs q = true) :
    lhs.toMvPolynomial hl - termsPolynomial k rhs = MvPolynomial.C (p : Int) * termsPolynomial k q := by
  simp only [treeTermsEqMod, Bool.and_eq_true] at h
  have hl := h.1.1.1.1.1.2
  have hr := h.1.1.1.1.2
  have hq := canonical_termShape h.1.2
  have hd := (expr_bound lhs hl).sub (terms_bound k rhs hr)
  have ht : Exact (mul ⟨zeroDegrees k, p⟩ (terms k q))
      (MvPolynomial.C (p:Int)*termsPolynomial k q) := by
    simpa only [Int.natAbs_natCast] using (Exact.int k (p:Int)).mul (terms_bound k q hq)
  let s := plan (add (add (⟨lhs.degrees k, lhs.height⟩) (terms k rhs)) (mul ⟨zeroDegrees k, p⟩ (terms k q)))
  have hs : s.strides.length = k := by
    change (makeStrides 1 (maxDegrees _ _)).length = k
    rw [length_makeStrides, length_maxDegrees, hd.length, ht.length, Nat.max_self]
  have he := (Int.beq'_eq _ _).mp h.2
  change evalKron (2^s.digitBits) s.strides lhs - packNat (2^s.digitBits) s.strides rhs =
    (p:Int)*packNat (2^s.digitBits) s.strides q at he
  simp only [packNat_eq] at he
  apply pair hd ht
  rw [evalKron_eq_eval₂ _ _ lhs hl, packTerms_eq_eval₂ _ _ hs rhs hr,
    packTerms_eq_eval₂ _ _ hs q hq] at he
  simpa only [map_sub, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using he


theorem mulTree_sound {mode : MulMode} {k n r m ib sb : Nat}
    {a c : TermMatrix} {b : TreeMatrix} (h : mulTree mode k n r m a b c ib sb = true) :
    ∀ {R : Type u} [CommRing R] (v : Nat → R),
      denoteMatrix n r R (fun i : Fin k => v i.val) a * denoteTreeMatrix r m v b =
        denoteMatrix n m R (fun i : Fin k => v i.val) c := by
  intro R _ v
  have hw := (Bool.and_eq_true_iff.mp h).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  have hbv := (Bool.and_eq_true_iff.mp hb).2
  have hbl : b.length = r := eq_of_beq (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hb).1).1
  have hal : (matrixPolynomial k a).length = n := by
    simpa only [matrixPolynomial, List.length_map] using matrixShape_rows ha
  have har : ∀ row ∈ matrixPolynomial k a, row.length = r := by
    intro row hr
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hr
    have hx := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ha).2 xs hxs
    simpa only [List.length_map] using eq_of_beq (Bool.and_eq_true_iff.mp hx).1
  funext i j
  have he := congrArg (fun rows => (rows.getD i.val []).getD j.val 0) (mulTree_polynomial hbv h)
  rw [polyProduct_entry hal har (by rw [treePolynomial_length, hbl]), matrixPolynomial_getD] at he
  have he := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i : Fin k => v i.val)) he
  simpa only [map_sum, map_mul, matrixPolynomial_getD, treePolynomial_entry,
    denoteEntry, _root_.Matrix.mul_apply, denoteMatrix, denoteTreeMatrix] using he

theorem mulTreeMod_sound {mode : MulMode} {k n r m p ib sb : Nat}
    {a c q : TermMatrix} {b : TreeMatrix} (h : mulTreeMod mode k n r m p a b c q ib sb = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Nat → R),
      denoteMatrix n r R (fun i : Fin k => v i.val) a * denoteTreeMatrix r m v b =
        denoteMatrix n m R (fun i : Fin k => v i.val) c := by
  intro R _ _ v
  have hv := (Bool.and_eq_true_iff.mp h).1
  have hw₀ := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1).2
  have hw := (Bool.and_eq_true_iff.mp hw₀).1
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  have hbv := (Bool.and_eq_true_iff.mp hb).2
  have hbl : b.length = r := eq_of_beq (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hb).1).1
  have hal : (matrixPolynomial k a).length = n := by
    simpa only [matrixPolynomial, List.length_map] using matrixShape_rows ha
  have har : ∀ row ∈ matrixPolynomial k a, row.length = r := by
    intro row hr
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hr
    have hx := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ha).2 xs hxs
    simpa only [List.length_map] using eq_of_beq (Bool.and_eq_true_iff.mp hx).1
  funext i j
  obtain ⟨hl,he⟩ := mulTreeMod_polynomial hbv h
  have he := congrArg (fun rows => (rows.getD i.val []).getD j.val 0) he
  rw [matrixSub_entry hl, matrixScale_entry,
    polyProduct_entry hal har (by rw [treePolynomial_length, hbl]),
    matrixPolynomial_getD, matrixPolynomial_getD] at he
  have he := quotient_sound he (fun i : Fin k => v i.val)
  simpa only [map_sum, map_mul, matrixPolynomial_getD, treePolynomial_entry,
    denoteEntry, _root_.Matrix.mul_apply, denoteMatrix, denoteTreeMatrix] using he

theorem treeTermsEq_sound {k : Nat} {lhs : Expr} {rhs : Hex.MvPoly.Kernel.PolyList Int}
    (h : treeTermsEq k lhs rhs = true) :
    ∀ {R : Type u} [CommRing R] (v : Nat → R),
      lhs.denote v = denoteTerms R (fun i : Fin k => v i.val) rhs := by
  intro R _ v
  have hl := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  rw [← lhs.denoteFin_eq hl v, denote_eq_eval₂, denoteTerms, treeTermsEq_polynomial hl h]

theorem treeTermsEqMod_sound {k p : Nat} {lhs : Expr} {rhs q : Hex.MvPoly.Kernel.PolyList Int}
    (h : treeTermsEqMod k p lhs rhs q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Nat → R),
      lhs.denote v = denoteTerms R (fun i : Fin k => v i.val) rhs := by
  intro R _ _ v
  have hw := h
  simp only [treeTermsEqMod, Bool.and_eq_true] at hw
  have hl := hw.1.1.1.1.1.2
  rw [← lhs.denoteFin_eq hl v, denote_eq_eval₂]
  exact quotient_sound (treeTermsEqMod_polynomial hl h) _

end Kernel
theorem checkMulTree_sound {budget : Budget} {mode : MulMode} {k n r m : Nat} {a c : TermMatrix} {b : TreeMatrix}
    (h : checkMulTree budget mode k n r m a b c = true) :
    ∀ {R : Type u} [CommRing R]  (v : Nat → R),
      denoteMatrix n r R (fun i : Fin k => v i.val) a * denoteTreeMatrix r m v b =
        denoteMatrix n m R (fun i : Fin k => v i.val) c := by
  unfold checkMulTree at h
  split at h
  · contradiction
  · exact Kernel.mulTree_sound (Bool.and_eq_true_iff.mp h).2

theorem checkMulTreeMod_sound {budget : Budget} {mode : MulMode} {k n r m p : Nat} {a c q : TermMatrix} {b : TreeMatrix}
    (h : checkMulTreeMod budget mode k n r m p a b c q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Nat → R),
      denoteMatrix n r R (fun i : Fin k => v i.val) a * denoteTreeMatrix r m v b =
        denoteMatrix n m R (fun i : Fin k => v i.val) c := by
  unfold checkMulTreeMod at h
  split at h
  · contradiction
  · exact Kernel.mulTreeMod_sound (Bool.and_eq_true_iff.mp h).2

theorem checkTreeTermsEq_sound {budget : Budget} {k : Nat} {lhs : Expr} {rhs : Hex.MvPoly.Kernel.PolyList Int}
    (h : checkTreeTermsEq budget k lhs rhs = true) :
    ∀ {R : Type u} [CommRing R]  (v : Nat → R),
      lhs.denote v = denoteTerms R (fun i : Fin k => v i.val) rhs := by
  unfold checkTreeTermsEq at h
  split at h
  · contradiction
  · exact Kernel.treeTermsEq_sound (Bool.and_eq_true_iff.mp h).2

theorem checkTreeTermsEqMod_sound {budget : Budget} {k p : Nat} {lhs : Expr} {rhs q : Hex.MvPoly.Kernel.PolyList Int}
    (h : checkTreeTermsEqMod budget k p lhs rhs q = true) :
    ∀ {R : Type u} [CommRing R] [CharP R p] (v : Nat → R),
      lhs.denote v = denoteTerms R (fun i : Fin k => v i.val) rhs := by
  unfold checkTreeTermsEqMod at h
  split at h
  · contradiction
  · exact Kernel.treeTermsEqMod_sound (Bool.and_eq_true_iff.mp h).2

end Hex.Kronecker
