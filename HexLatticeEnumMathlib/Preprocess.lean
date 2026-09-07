/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Preprocess
public import HexLatticeEnumMathlib.OptimizationBudget
public import HexLLLMathlib.Reduction
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat} {b : Basis n m} {t : Vector Rat m}

/-- Retargeting preserves valid orthogonalization and recomputes the exact projection and residual. -/
theorem retarget_valid (p : Prepared b t) (hp : p.Valid) (target : Vector Rat m) :
    (retarget p target).Valid := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_, ?_⟩
  · intro i
    simp [retarget]
  · simp [retarget]

/-- A target equal to a lattice point has exactly integral nearest-plane centres. -/
theorem centre_lattice (z : Vector Int n) (p : Prepared b (castVector (vector b z)))
    (hp : p.Valid) (i : Fin n) : p.centre z i = (z[i] : Rat) := by
  have hd := distance_decomposition p.toData b.rows (castVector (vector b z)) hp z
  have hz : distance (vector b z) (castVector (vector b z)) = 0 := by
    simp [distance, subtract_eq, Vector.normSq, HexMatrixMathlib.dotProduct_eq, dotProduct,
      HexMatrixMathlib.vectorEquiv_apply]
  change distance (vector b z) _ = _ at hd
  rw [hz] at hd
  change 0 = p.residual.normSq + ∑ i : Fin n, p.norms[i] * ((z[i] : Rat) - p.centre z i) ^ 2 at hd
  have hr : 0 ≤ p.residual.normSq := by
    rw [Vector.normSq, HexMatrixMathlib.dotProduct_eq]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hi := Finset.single_le_sum
    (fun (j : Fin n) (_ : j ∈ Finset.univ) => mul_nonneg (hp.1 j).1.le (sq_nonneg ((z[j] : Rat) - p.centre z j)))
    (Finset.mem_univ i)
  have hn := (hp.1 i).1
  simp only [Fin.getElem_fin] at hd hi hn ⊢
  have hprod : p.norms[i.val] * ((z[i.val] : Rat) - p.centre z i) ^ 2 ≤ 0 :=
    hi.trans (by linarith)
  have hsq : ((z[i.val] : Rat) - p.centre z i) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ((z[i.val] : Rat) - p.centre z i)]
  have he := le_antisymm hsq (sq_nonneg ((z[i.val] : Rat) - p.centre z i))
  exact (sub_eq_zero.mp (sq_eq_zero_iff.mp he)).symm

/-- Nearest plane recovers exact integer coefficients when the target is a lattice point. -/
theorem nearestPlane_lattice (z : Vector Int n) (p : Prepared b (castVector (vector b z)))
    (hp : p.Valid) (k : Nat) (hk : k ≤ n) (w : Vector Int n)
    (hw : ∀ j : Fin n, k ≤ j.val → w[j] = z[j]) : nearestPlane p k hk w = z := by
  induction k generalizing w with
  | zero =>
    apply Vector.ext
    intro i hi
    exact hw ⟨i, hi⟩ (Nat.zero_le i)
  | succ k ih =>
    rw [nearestPlane]
    apply ih
    intro j hj
    by_cases he : j.val = k
    · have hc : p.centre w ⟨k, by omega⟩ = (z[k] : Rat) := by
        exact (centre_congr p.toData w z ⟨k, by omega⟩ (by
          intro l hl
          apply hw l
          change k < l.val at hl
          omega)).trans (centre_lattice z p hp ⟨k, by omega⟩)
      simp [Fin.getElem_fin, he, hc, nearest_int]
    · simp only [Fin.getElem_fin, Vector.getElem_set, ite_eq_right (Ne.symm he)]
      exact hw j (by omega)

/-- Coordinate recovery reconstructs every row already belonging to the original lattice. -/
theorem rowCoordinates_mul (p : Prepared b t) (hp : p.Valid) (rows : Hex.Matrix Int n m)
    (hrows : ∀ i : Fin n, b.rows.memLattice (rows.getRow i)) : rowCoordinates p rows * b.rows = rows := by
  apply Hex.Matrix.ext_getElem
  intro i j
  obtain ⟨z, hz⟩ := hrows i
  have he : nearestPlane (retarget p (castVector (rows.getRow i))) n (Nat.le_refl n) 0 = z := by
    rw [← hz]
    exact nearestPlane_lattice z _ (retarget_valid p hp _) n (Nat.le_refl n) 0
      (fun j hj => False.elim (by omega))
  have hr : (rowCoordinates p rows).getRow i = z := by
    simpa only [rowCoordinates, Hex.Matrix.getRow_ofRows, Hex.Vector.getElem_ofFn', Fin.getElem_fin] using he
  rw [Hex.Matrix.getElem_mul]
  have hv := congrArg (fun v : Vector Int m => v[j]) hz
  change (b.rows.transpose * z)[j] = (rows.getRow i)[j] at hv
  rw [Hex.Matrix.getElem_mulVec, Hex.Matrix.row_transpose] at hv
  simpa [Hex.Matrix.row, hr, Vector.dotProduct_comm] using hv

/-- LLL preprocessing accepts its recovered transformations for every positive-rank input.
The computational rejection branches are unreachable on the certified reducer's output. -/
theorem lllPreprocess_rows (b : Basis n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) :
    (lllPreprocess b δ hδ hδ').working.rows = Hex.lll b.rows δ hδ hδ' hn := by
  let rows := Hex.lll b.rows δ hδ hδ' hn
  have hind : rows.independent := Hex.lll_independent b.rows δ hδ hδ' hn b.independent
  let working : Basis n m := ⟨rows, hind⟩
  have hforward := rowCoordinates_mul (prepare b 0) (prepare_valid b 0) rows (by
    intro i
    apply (Hex.lll_memLattice_iff b.rows δ hδ hδ' hn _).mp
    exact Hex.Matrix.row_memLattice rows i)
  have hreverse := rowCoordinates_mul (prepare working 0) (prepare_valid working 0) b.rows (by
    intro i
    apply (Hex.lll_memLattice_iff b.rows δ hδ hδ' hn _).mpr
    exact Hex.Matrix.row_memLattice b.rows i)
  have hc : Hex.Matrix.sameLatticeCert b.rows rows
      (rowCoordinates (prepare b 0) rows) (rowCoordinates (prepare working 0) b.rows) = true := by
    simp only [Hex.Matrix.sameLatticeCert, Bool.and_eq_true, Hex.Matrix.mulEqCert_iff]
    exact ⟨hforward, hreverse⟩
  dsimp only [rows] at hind
  simp only [lllPreprocess, dite_eq_left hn, ofMatrix?, dite_eq_left hind]
  change (if h : Hex.Matrix.sameLatticeCert b.rows rows
      (rowCoordinates (prepare b 0) rows) (rowCoordinates (prepare working 0) b.rows) = true then
      (⟨working, _, _, h⟩ : BasisChange b) else BasisChange.identity b).working.rows = rows
  simp only [dite_eq_left hc]
  rfl

/-- The optional preprocessor actually returns an LLL-reduced working basis. -/
theorem lllPreprocess_reduced (b : Basis n m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) :
    Hex.isLLLReduced (lllPreprocess b δ hδ hδ').working.rows δ (11 / 20) := by
  rw [lllPreprocess_rows b δ hδ hδ' hn]
  exact Hex.lll_isLLLReduced b.rows δ hδ hδ' hn b.independent

/-- Rank-zero preprocessing is exactly the checked identity change. -/
@[simp] theorem lllPreprocess_zero (b : Basis 0 m) (δ : Rat)
    (hδ : (121 / 400 : Rat) < δ) (hδ' : δ ≤ 1) :
    lllPreprocess b δ hδ hδ' = BasisChange.identity b := by
  simp [lllPreprocess]

/-- Checked basis changes carry both exact integer matrix identities. -/
theorem change_identities (change : BasisChange b) :
    change.forward * b.rows = change.working.rows ∧ change.reverse * change.working.rows = b.rows := by
  have h := change.checked
  simpa only [Hex.Matrix.sameLatticeCert, Bool.and_eq_true, Hex.Matrix.mulEqCert_iff] using h

/-- Checked preprocessing preserves precisely the integer row lattice. -/
theorem change_lattice (change : BasisChange b) (v : Vector Int m) :
    b.rows.memLattice v ↔ change.working.rows.memLattice v :=
  Hex.Matrix.sameLatticeCert_sound change.checked v

/-- Original coefficients reconstructed with the forward transpose preserve the ambient vector. -/
theorem change_vector (change : BasisChange b) (z : Vector Int n) :
    vector b (change.forward.transpose * z) = vector change.working z :=
  transport_vector b.rows change.working.rows change.forward (change_identities change).1 z

/-- Independence makes the forward transpose injective on working coefficients. -/
theorem change_injective (change : BasisChange b) :
    Function.Injective (fun z : Vector Int n => change.forward.transpose * z) := by
  intro z w he
  apply vector_injective change.working
  rw [← change_vector change z, ← change_vector change w]
  exact congrArg (vector b) he

/-- Checked forward and reverse transforms are inverse on original coefficient vectors. -/
theorem change_inverse (change : BasisChange b) (z : Vector Int n) :
    change.forward.transpose * (change.reverse.transpose * z) = z :=
  transport_inverse b change.working.rows change.forward change.reverse
    (change_identities change).1 (change_identities change).2 z

/-- A transported point has exactly the same ambient vector and exact distance. -/
theorem change_point (change : BasisChange b) (t : Vector Rat m) (q : Point n m)
    (hq : q = point change.working t q.coefficients) :
    (change.point t q).ambient = q.ambient ∧ (change.point t q).distanceSq = q.distanceSq := by
  have ha := congrArg Point.ambient hq
  have hd := congrArg Point.distanceSq hq
  constructor
  · change vector b (change.forward.transpose * q.coefficients) = q.ambient
    exact (change_vector change q.coefficients).trans ha.symm
  · change distanceSq b t (change.forward.transpose * q.coefficients) = q.distanceSq
    change distance (vector b (change.forward.transpose * q.coefficients)) t = q.distanceSq
    rw [change_vector]
    exact hd.symm

/-- Preprocessed enumeration returns the same complete original-basis point records. -/
theorem change_enumerate (change : BasisChange b) (t : Vector Rat m) (r : Rat) :
    change.enumerate t r = enumerate b t r := by
  let ps := enumerate change.working t r
  have hmap : ∀ q, q ∈ ps → (change.point t q).ambient = q.ambient ∧
      (change.point t q).distanceSq = q.distanceSq := by
    intro q hq
    exact change_point change t q ((enumerate_point_spec change.working t r q).mp hq).1
  have hmem : ∀ q, q ∈ change.enumerate t r ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
    intro q
    simp only [BasisChange.enumerate, BasisChange.points, sortPoints, Hex.List.sort_eq, List.mem_mergeSort,
      List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨rfl, ?_⟩
      rw [(hmap v hv).2]
      exact ((enumerate_point_spec change.working t r v).mp hv).2
    · rintro ⟨hq, hd⟩
      let z := change.reverse.transpose * q.coefficients
      let v := point change.working t z
      have he : change.point t v = q := by
        change point b t (change.forward.transpose * (change.reverse.transpose * q.coefficients)) = q
        rw [change_inverse]
        exact hq.symm
      refine ⟨v, ?_, he⟩
      apply (enumerate_point_spec change.working t r v).mpr
      refine ⟨rfl, ?_⟩
      have hv := (change_point change t v rfl).2
      rw [he] at hv
      rwa [← hv]
  have hn : (change.enumerate t r).Nodup := by
    unfold BasisChange.enumerate BasisChange.points sortPoints
    rw [Hex.List.sort_eq]
    apply (List.mergeSort_perm _ _).symm.nodup
    apply List.Nodup.map_on ?_ (enumerate_nodup change.working t r)
    intro p hp q hq he
    have hz := change_injective change (congrArg Point.coefficients he)
    have hp' := ((enumerate_point_spec change.working t r p).mp hp).1
    have hq' := ((enumerate_point_spec change.working t r q).mp hq).1
    rw [hp', hq', hz]
  exact sorted_points_eq b t _ _ hn (enumerate_nodup b t r)
    (fun q => (hmem q).trans (enumerate_point_spec b t r q).symm)
    (fun q hq => ((hmem q).mp hq).1) (sortPoints_sorted _) (enumerate_sorted b t r)

/-- Transporting reconstructed points preserves their ambient membership exactly. -/
theorem change_ambient (change : BasisChange b) (t : Vector Rat m) (ps : List (Point n m))
    (hp : ∀ q, q ∈ ps → q = point change.working t q.coefficients) (v : Vector Int m) :
    v ∈ (change.points t ps).map Point.ambient ↔ v ∈ ps.map Point.ambient := by
  simp only [BasisChange.points, sortPoints, Hex.List.sort_eq, List.mem_map, List.mem_mergeSort]
  constructor
  · rintro ⟨q, ⟨p, hps, rfl⟩, hv⟩
    exact ⟨p, hps, (change_point change t p (hp p hps)).1.symm.trans hv⟩
  · rintro ⟨p, hps, hv⟩
    exact ⟨change.point t p, ⟨p, hps, rfl⟩, (change_point change t p (hp p hps)).1.trans hv⟩

/-- Checked preprocessing leaves the complete global closest-vector answer unchanged in ambient space. -/
theorem change_closest_spec (change : BasisChange b) (t : Vector Rat m) (v : Vector Int m) :
    v ∈ (change.closest t).points.map Point.ambient ↔
      b.rows.memLattice v ∧ ∀ w, b.rows.memLattice w → distance v t ≤ distance w t := by
  change v ∈ (change.points t (closest change.working t).points).map Point.ambient ↔ _
  rw [change_ambient change t _ (fun q hq => ((closest_point_spec change.working t q).mp hq).1), closest_spec]
  simp_rw [change_lattice change]

/-- Checked preprocessing leaves every shortest nonzero vector and both signs in the answer. -/
theorem change_shortest_spec (change : BasisChange b) (answer : Minimum n m)
    (h : change.shortest = some answer) (v : Vector Int m) :
    v ∈ answer.points.map Point.ambient ↔ b.rows.memLattice v ∧ v ≠ 0 ∧
      ∀ w, b.rows.memLattice w → w ≠ 0 → distance v 0 ≤ distance w 0 := by
  obtain ⟨original, ho, he⟩ := Option.map_eq_some_iff.mp h
  subst answer
  change v ∈ (change.points 0 original.points).map Point.ambient ↔ _
  rw [change_ambient change 0 original.points
    (fun q hq => ((shortest_point_spec change.working original ho q).mp hq).1),
    shortest_spec change.working original ho]
  simp_rw [change_lattice change]

/-- A transformed complete enumeration certificate passes replay with its original-basis points. -/
theorem change_certificate_check (change : BasisChange b) (t : Vector Rat m) (r : Rat) :
    checkEnumeration b.rows t r (change.certificate t r) = true := by
  let p := prepare change.working t
  let run := traverse change.working t p {} .ball n (Nat.le_refl n) 0 0 { radius := r }
  have hball := ball_complete change.working t r
  obtain ⟨tree, ht⟩ := Option.isSome_iff_exists.mp hball.2.1
  have htree := traverse_exhaustive change.working t p {} n (Nat.le_refl n) 0 { radius := r }
  rw [suffix_rank] at htree
  have hv := htree.2.2 tree ht
  have hz : (Vector.replicate n (0 : Int)) = 0 := by ext i hi; simp
  rw [← hz] at hv
  obtain ⟨result, hr, _⟩ := replay_accepts b.rows change.working.rows change.forward (change_identities change).1
    p.toData t r n (Nat.le_refl n) (Vector.replicate n 0) tree hv tree.nodes (Nat.le_refl _)
  rw [suffix_rank] at hr
  have hspec := replay_spec b.rows change.working.rows change.forward p.toData t (prepare_valid change.working t)
    (change_identities change).1 r n (Nat.le_refl n) (Vector.replicate n 0) tree tree.nodes result
  rw [suffix_rank] at hspec
  obtain ⟨hn, hm⟩ := hspec hr
  have hmem : ∀ q, q ∈ sortPoints result.points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
    intro q
    simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort, hm]
    exact replay_root b change.working.rows change.forward change.reverse
      (change_identities change).1 (change_identities change).2 t r _ q
  have heq : sortPoints result.points = enumerate b t r := by
    apply sorted_points_eq b t _ _ ?_ (enumerate_nodup b t r)
      (fun q => (hmem q).trans (enumerate_point_spec b t r q).symm)
      (fun q hq => ((hmem q).mp hq).1) (sortPoints_sorted _) (enumerate_sorted b t r)
    unfold sortPoints
    rw [Hex.List.sort_eq]
    exact (List.mergeSort_perm _ _).symm.nodup hn
  have hd : p.toData.check change.working.rows t = true := (Data.check_iff _ _ _).mpr (prepare_valid change.working t)
  have hpoints : change.points t (enumerationCertificate change.working t r).points = enumerate b t r :=
    change_enumerate change t r
  dsimp only [p] at hd hr
  simp only [BasisChange.certificate, checkEnumeration, checkEnumerationWith, change.checked,
    enumerationCertificate, ht, Option.getD_some, hd, Bool.true_and, replay, hr, heq]
  apply decide_eq_true_eq.mpr
  exact hpoints.symm

end HexLatticeEnumMathlib
