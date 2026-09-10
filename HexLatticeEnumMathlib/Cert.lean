/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Cert
public import HexLatticeEnumMathlib.Shortest
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

/-- Integer labels listed by the checker cover the exact closed interval. -/
theorem interval_labels (interval : Interval) (a : Int) :
    a ∈ (List.range interval.size).map (fun (i : Nat) => interval.lo + (i : Int)) ↔
      interval.lo ≤ a ∧ a ≤ interval.hi := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold Interval.size at hi
    omega
  · rintro ⟨hl, hh⟩
    refine ⟨(a - interval.lo).toNat, ?_, ?_⟩
    · unfold Interval.size
      omega
    · omega

/-- Accepted labels are unique and exhaust the recomputed interval, in any supplied order. -/
theorem checkLabels_spec (interval : Interval) (children : List (Int × Tree))
    (h : checkLabels interval children = true) :
    (children.map Prod.fst).Nodup ∧
      ∀ a, a ∈ children.map Prod.fst ↔ interval.lo ≤ a ∧ a ≤ interval.hi := by
  simp only [checkLabels, Bool.and_eq_true, beq_iff_eq, Hex.List.sort_eq] at h
  have hperm := (List.mergeSort_perm (children.map Prod.fst) (fun x y => x ≤ y)).symm.trans
    (List.Perm.of_eq h.2)
  constructor
  · apply hperm.nodup_iff.mpr
    apply List.Nodup.map_on ?_ List.nodup_range
    intro i _ j _ he
    omega
  · intro a
    exact hperm.mem_iff.trans (interval_labels interval a)

/-- Replay combines successful disjoint children while preserving their exact point coverage. -/
theorem replay_children (visit : Int → Tree → Nat → Option (Replay n m))
    (P : Int → Point n m → Prop)
    (hvisit : ∀ a tree fuel result, visit a tree fuel = some result →
      result.points.Nodup ∧ ∀ q, q ∈ result.points ↔ P a q)
    (hdisjoint : ∀ a b q, P a q → P b q → a = b)
    (children : List (Int × Tree)) (fuel : Nat) (points : List (Point n m)) (result : Replay n m)
    (hn : (children.map Prod.fst).Nodup)
    (hr : replayAux.loop visit children fuel points = some result) :
    ∃ fresh, result.points = points.reverse ++ fresh ∧ fresh.Nodup ∧
      ∀ q, q ∈ fresh ↔ ∃ a ∈ children.map Prod.fst, P a q := by
  induction children generalizing fuel points result with
  | nil =>
    simp only [replayAux.loop, Option.some.injEq] at hr
    subst result
    refine ⟨[], by simp, by simp, ?_⟩
    simp
  | cons child children ih =>
    rcases child with ⟨a, tree⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [replayAux.loop] at hr
    cases hc : visit a tree fuel with
    | none => simp [hc] at hr
    | some child =>
      simp only [hc] at hr
      obtain ⟨hcn, hcm⟩ := hvisit a tree fuel child hc
      obtain ⟨rest, he, hrest, hm⟩ := ih child.remaining (child.points.reverse ++ points) result hn.2 hr
      refine ⟨child.points ++ rest, ?_, ?_, ?_⟩
      · simpa only [List.reverse_append, List.reverse_reverse, List.append_assoc] using he
      · apply List.nodup_append.mpr
        refine ⟨hcn, hrest, ?_⟩
        intro q hq q' hq' heq
        subst q'
        obtain ⟨b, hb, hbp⟩ := (hm q).mp hq'
        exact hn.1 ((hdisjoint a b q ((hcm q).mp hq) hbp) ▸ hb)
      · intro q
        simp only [List.mem_append, hcm, hm, List.map_cons, List.mem_cons]
        constructor
        · rintro (ha | ⟨b, hb, hp⟩)
          · exact ⟨a, Or.inl rfl, ha⟩
          · exact ⟨b, Or.inr hb, hp⟩
        · rintro ⟨b, hb, hp⟩
          rcases hb with rfl | hb
          · exact Or.inl hp
          · exact Or.inr ⟨b, hb, hp⟩

/-- A checked forward transform reconstructs the same ambient vector in original coordinates. -/
theorem transport_vector (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (h : forward * rows = working) (z : Vector Int n) :
    Hex.Matrix.vecMul (forward.transpose * z) rows = Hex.Matrix.vecMul z working := by
  rw [Hex.Matrix.vecMul_transpose_mul, h]

/-- Feasible suffix completions, with every reported coefficient expressed in the original basis. -/
@[expose] def ReplayFeasible (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (t : Vector Rat m) (r : Rat) (k : Nat) (z : Vector Int n) (q : Point n m) : Prop :=
  ∃ w, Matches k z w ∧ q = pointRows rows t (forward.transpose * w) ∧
    distance (Hex.Matrix.vecMul w working) t ≤ r

/-- At a leaf there is exactly one coefficient completion, checked using its direct distance. -/
theorem replay_zero (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (h : forward * rows = working) (t : Vector Rat m) (r : Rat) (z : Vector Int n) (q : Point n m) :
    ReplayFeasible rows working forward t r 0 z q ↔
      q = pointRows rows t (forward.transpose * z) ∧
        (pointRows rows t (forward.transpose * z)).distanceSq ≤ r := by
  have hd : (pointRows rows t (forward.transpose * z)).distanceSq =
      distance (Hex.Matrix.vecMul z working) t := by
    simp only [pointRows, transport_vector rows working forward h]
  rw [hd]
  constructor
  · rintro ⟨w, hm, hq, hr⟩
    have hw : w = z := by
      apply Vector.ext
      intro i hi
      exact hm ⟨i, hi⟩ (Nat.zero_le i)
    subst w
    exact ⟨hq, hr⟩
  · rintro ⟨hq, hr⟩
    exact ⟨z, fun _ _ => rfl, hq, hr⟩

/-- Exact interval bounds characterize the next coefficient of every replay completion. -/
theorem replay_branches (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (p : Data n m) (t : Vector Rat m) (hp : p.Valid working t) (r : Rat)
    (k : Nat) (hk : k < n) (z : Vector Int n) (q : Point n m) :
    let interval := bounds (p.centre z ⟨k, hk⟩) p.norms[k]
      (r - p.residual.normSq - suffix p z (k + 1))
    (∃ a, (interval.lo ≤ a ∧ a ≤ interval.hi) ∧
      ReplayFeasible rows working forward t r k (z.set k a hk) q) ↔
        ReplayFeasible rows working forward t r (k + 1) z q := by
  dsimp only
  constructor
  · rintro ⟨a, _, w, hm, hq, hr⟩
    exact ⟨w, ((matches_set k hk z w a).mp hm).1, hq, hr⟩
  · rintro ⟨w, hm, hq, hr⟩
    refine ⟨w[k], completion_bound p working t hp z w k hk r (fun j hj => hm j (by omega)) hr,
      w, (matches_set k hk z w _).mpr ⟨hm, rfl⟩, hq, hr⟩

/-- Distinct child labels cannot report the same original-basis point. -/
theorem replay_disjoint (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (p : Data n m) (t : Vector Rat m) (hp : p.Valid working t) (hU : forward * rows = working)
    (r : Rat) (k : Nat) (hk : k < n) (z : Vector Int n) (a b : Int) (q : Point n m)
    (ha : ReplayFeasible rows working forward t r k (z.set k a hk) q)
    (hb : ReplayFeasible rows working forward t r k (z.set k b hk) q) : a = b := by
  obtain ⟨v, hv, hqv, _⟩ := ha
  obtain ⟨w, hw, hqw, _⟩ := hb
  have he := congrArg Point.ambient (hqv.symm.trans hqw)
  change Hex.Matrix.vecMul (forward.transpose * v) rows =
    Hex.Matrix.vecMul (forward.transpose * w) rows at he
  rw [transport_vector rows working forward hU, transport_vector rows working forward hU] at he
  have hz := data_injective p working t hp he
  subst w
  have hav := ((matches_set k hk z v a).mp hv).2
  have hbv := ((matches_set k hk z v b).mp hw).2
  exact hav.symm.trans hbv

/-- Any successful replay exhausts precisely the feasible completions of its fixed suffix. -/
theorem replay_spec (rows working : Hex.Matrix Int n m) (forward : Hex.Matrix Int n n)
    (p : Data n m) (t : Vector Rat m) (hp : p.Valid working t) (hU : forward * rows = working)
    (r : Rat) (k : Nat) (hk : k ≤ n) (z : Vector Int n) (tree : Tree) (fuel : Nat)
    (result : Replay n m)
    (hr : replayAux rows t r forward p p.residual.normSq k hk z (suffix p z k) tree fuel = some result) :
    result.points.Nodup ∧ ∀ q, q ∈ result.points ↔ ReplayFeasible rows working forward t r k z q := by
  induction k generalizing z tree fuel result with
  | zero =>
    cases fuel with
    | zero => simp [replayAux] at hr
    | succ fuel =>
      cases tree with
      | node interval children => simp [replayAux] at hr
      | leaf =>
        simp only [replayAux] at hr
        split_ifs at hr with hdist
        · cases Option.some.inj hr
          refine ⟨by simp, ?_⟩
          intro q
          rw [replay_zero rows working forward hU]
          simp [hdist]
      | empty =>
        simp only [replayAux] at hr
        split_ifs at hr with hdist
        · cases Option.some.inj hr
          refine ⟨by simp, ?_⟩
          intro q
          rw [replay_zero rows working forward hU]
          simp [not_le.mpr hdist]
  | succ k ih =>
    cases fuel with
    | zero => simp [replayAux] at hr
    | succ fuel =>
      let interval := bounds (p.centre z ⟨k, by omega⟩) p.norms[k]
        (r - p.residual.normSq - suffix p z (k + 1))
      cases tree with
      | leaf => simp [replayAux] at hr
      | empty =>
        simp only [replayAux] at hr
        split_ifs at hr with hempty
        · cases Option.some.inj hr
          have hsize : interval.size = 0 := by simpa only [interval, beq_iff_eq, Fin.getElem_fin] using hempty
          refine ⟨by simp, ?_⟩
          intro q
          simp only [List.not_mem_nil, false_iff]
          intro hq
          obtain ⟨a, ha, _⟩ := (replay_branches rows working forward p t hp r k (by omega) z q).mpr hq
          have hm := (interval_labels interval a).mpr ha
          simp [hsize] at hm
      | node claimed children =>
        simp only [replayAux] at hr
        split_ifs at hr with hbad
        · have hlabels : checkLabels interval children = true := by
            simp only [Bool.or_eq_true, Bool.not_eq_true, bne_iff_ne, decide_eq_true_eq,
              not_or, not_not] at hbad
            have hh : (!checkLabels interval children) = false := hbad.2
            exact Bool.eq_true_of_not_eq_false (fun he => by rw [he] at hh; cases hh)
          obtain ⟨hn, hm⟩ := checkLabels_spec interval children hlabels
          let visit := fun (a : Int) (tree : Tree) (fuel : Nat) =>
            replayAux rows t r forward p p.residual.normSq k (by omega) (z.set k a (by omega))
              (suffix p z (k + 1) + p.norms[k] * ((a : Rat) - p.centre z ⟨k, by omega⟩) *
                ((a : Rat) - p.centre z ⟨k, by omega⟩)) tree fuel
          have hv : ∀ a tree fuel result, visit a tree fuel = some result →
              result.points.Nodup ∧ ∀ q, q ∈ result.points ↔
                ReplayFeasible rows working forward t r k (z.set k a (by omega)) q := by
            intro a tree fuel result h
            apply ih (by omega) (z.set k a (by omega)) tree fuel result
            rwa [suffix_step]
          obtain ⟨fresh, he, hfn, hfm⟩ := replay_children visit
            (fun a => ReplayFeasible rows working forward t r k (z.set k a (by omega))) hv
            (replay_disjoint rows working forward p t hp hU r k (by omega) z)
            children fuel [] result hn hr
          simp only [List.reverse_nil, List.nil_append] at he
          rw [he]
          refine ⟨hfn, ?_⟩
          intro q
          rw [hfm]
          simp_rw [hm]
          exact replay_branches rows working forward p t hp r k (by omega) z q

/-- Checked reverse and forward transforms recover the original coefficients exactly. -/
theorem transport_inverse (b : Basis n m) (working : Hex.Matrix Int n m)
    (forward reverse : Hex.Matrix Int n n) (hU : forward * b.rows = working)
    (hV : reverse * working = b.rows) (z : Vector Int n) :
    forward.transpose * (reverse.transpose * z) = z := by
  apply vector_injective b
  change Hex.Matrix.vecMul (forward.transpose * (reverse.transpose * z)) b.rows =
    Hex.Matrix.vecMul z b.rows
  rw [transport_vector b.rows working forward hU, transport_vector working b.rows reverse hV]

/-- At the root, replay completeness is the original-basis point and radius contract. -/
theorem replay_root (b : Basis n m) (working : Hex.Matrix Int n m)
    (forward reverse : Hex.Matrix Int n n) (hU : forward * b.rows = working)
    (hV : reverse * working = b.rows) (t : Vector Rat m) (r : Rat) (z : Vector Int n)
    (q : Point n m) : ReplayFeasible b.rows working forward t r n z q ↔
      q = point b t q.coefficients ∧ q.distanceSq ≤ r := by
  constructor
  · rintro ⟨w, _, hq, hr⟩
    subst q
    refine ⟨rfl, ?_⟩
    change distance (Hex.Matrix.vecMul (forward.transpose * w) b.rows) t ≤ r
    rwa [transport_vector b.rows working forward hU]
  · rintro ⟨hq, hr⟩
    refine ⟨reverse.transpose * q.coefficients, fun i hi => by omega, ?_, ?_⟩
    · rw [transport_inverse b working forward reverse hU hV]
      exact hq
    · rw [transport_vector working b.rows reverse hV]
      have hd := congrArg Point.distanceSq hq
      change q.distanceSq = distance (Hex.Matrix.vecMul q.coefficients b.rows) t at hd
      rwa [← hd]

/-- Successful bounded replay proves exact original-basis point coverage and uniqueness. -/
theorem checkEnumerationWith_spec (b : Basis n m) (t : Vector Rat m) (r : Rat)
    (cert : Certificate n m) (maxNodes : Nat)
    (h : checkEnumerationWith maxNodes b.rows t r cert = true) :
    cert.points.Nodup ∧
      (∀ q, q ∈ cert.points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r) ∧
      cert.points.Pairwise (fun p q => compare p.ambient.toList q.ambient.toList ≠ .gt) := by
  simp only [checkEnumerationWith, Bool.and_eq_true] at h
  have hdata := (Data.check_iff cert.data cert.rows t).mp h.1.2
  have htrans := h.1.1
  simp only [Hex.Matrix.sameLatticeCert, Bool.and_eq_true, Hex.Matrix.mulEqCert_iff] at htrans
  cases hr : replay b.rows t r cert.forward cert.data n (Nat.le_refl n)
      (Vector.replicate n 0) 0 cert.tree maxNodes with
  | none => simp [hr] at h
  | some result =>
    have he : sortPoints result.points = cert.points := by simpa only [hr, decide_eq_true_eq] using h.2
    have hs := replay_spec b.rows cert.rows cert.forward cert.data t hdata htrans.1 r n
      (Nat.le_refl n) (Vector.replicate n 0) cert.tree maxNodes result
    rw [suffix_rank] at hs
    obtain ⟨hn, hm⟩ := hs hr
    rw [← he]
    refine ⟨?_, ?_, sortPoints_sorted _⟩
    · unfold sortPoints
      rw [Hex.List.sort_eq]
      exact (List.mergeSort_perm _ _).symm.nodup hn
    · intro q
      simp only [sortPoints, Hex.List.sort_eq, List.mem_mergeSort, hm]
      exact replay_root b cert.rows cert.forward cert.reverse htrans.1 htrans.2 t r _ q

/-- Any accepted exhaustive certificate has the same complete point contract as native enumeration. -/
theorem checkEnumeration_point_spec (b : Basis n m) (t : Vector Rat m) (r : Rat)
    (cert : Certificate n m) (h : checkEnumeration b.rows t r cert = true) (q : Point n m) :
    q ∈ cert.points ↔ q = point b t q.coefficients ∧ q.distanceSq ≤ r :=
  (checkEnumerationWith_spec b t r cert cert.tree.nodes h).2.1 q

/-- Soundness of arbitrary supplied certificates: all and only lattice points in the closed ball. -/
theorem checkEnumeration_sound (b : Basis n m) (t : Vector Rat m) (r : Rat)
    (cert : Certificate n m) (h : checkEnumeration b.rows t r cert = true) (v : Vector Int m) :
    v ∈ cert.points.map Point.ambient ↔ b.rows.memLattice v ∧ distance v t ≤ r := by
  rw [← enumerate_spec b t r v]
  simp only [List.mem_map, checkEnumeration_point_spec b t r cert h, enumerate_point_spec]

/-- Accepted certificates never repeat an ambient lattice vector. -/
theorem checkEnumeration_nodup (b : Basis n m) (t : Vector Rat m) (r : Rat)
    (cert : Certificate n m) (h : checkEnumeration b.rows t r cert = true) :
    (cert.points.map Point.ambient).Nodup := by
  apply List.Nodup.map_on ?_ (checkEnumerationWith_spec b t r cert cert.tree.nodes h).1
  intro q hq q' hq' he
  have hr := ((checkEnumeration_point_spec b t r cert h q).mp hq).1
  have hr' := ((checkEnumeration_point_spec b t r cert h q').mp hq').1
  have ha := congrArg Point.ambient hr
  have ha' := congrArg Point.ambient hr'
  have hz : q.coefficients = q'.coefficients := vector_injective b (ha.symm.trans (he.trans ha'))
  rw [hr, hr', hz]

/-- A bounded checked closest certificate attains a global minimum and includes every tie. -/
theorem checkClosestWith_sound (maxNodes : Nat) (b : Basis n m) (t : Vector Rat m) (cert : OptimumCertificate n m)
    (h : checkClosestWith maxNodes b.rows t cert = true) :
    Optimal b t .closest cert.candidate ∧
      ∀ q, q ∈ cert.enumeration.points ↔
        q = point b t q.coefficients ∧ q.distanceSq = cert.candidate.distanceSq := by
  simp only [checkClosestWith, Bool.and_eq_true, checkPoint, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  have hpoint : cert.candidate = point b t cert.candidate.coefficients := h.1.1
  have hoptimal : Optimal b t .closest cert.candidate := by
    refine ⟨hpoint, Or.inl rfl, ?_⟩
    intro q hq _
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hmem := ((checkEnumerationWith_spec b t cert.candidate.distanceSq cert.enumeration maxNodes h.1.2).2.1 q).mpr
      ⟨hq, le_of_lt hlt⟩
    have he := h.2 q hmem
    linarith
  refine ⟨hoptimal, ?_⟩
  intro q
  constructor
  · intro hq
    exact ⟨(((checkEnumerationWith_spec b t cert.candidate.distanceSq cert.enumeration maxNodes h.1.2).2.1 q).mp hq).1,
      h.2 q hq⟩
  · rintro ⟨hq, hd⟩
    exact ((checkEnumerationWith_spec b t cert.candidate.distanceSq cert.enumeration maxNodes h.1.2).2.1 q).mpr
      ⟨hq, le_of_eq hd⟩

/-- A checked closest certificate attains a global minimum and includes every tie. -/
theorem checkClosest_sound (b : Basis n m) (t : Vector Rat m) (cert : OptimumCertificate n m)
    (h : checkClosest b.rows t cert = true) :
    Optimal b t .closest cert.candidate ∧
      ∀ q, q ∈ cert.enumeration.points ↔
        q = point b t q.coefficients ∧ q.distanceSq = cert.candidate.distanceSq :=
  checkClosestWith_sound cert.enumeration.tree.nodes b t cert h

/-- A bounded checked shortest certificate attains the global nonzero minimum and retains every nonzero tie. -/
theorem checkShortestWith_sound (maxNodes : Nat) (b : Basis n m) (cert : OptimumCertificate n m)
    (h : checkShortestWith maxNodes b.rows cert = true) :
    Optimal b 0 .shortest cert.candidate ∧
      ∀ q, q ∈ minimumPoints .shortest cert.enumeration.points ↔
        q = point b 0 q.coefficients ∧ q.ambient ≠ 0 ∧ q.distanceSq = cert.candidate.distanceSq := by
  have hz : (Vector.replicate m (0 : Int)) = 0 := by ext i hi; simp
  have ht : (Vector.replicate m (0 : Rat)) = 0 := by ext i hi; simp
  simp only [checkShortestWith, hz, ht, Bool.and_eq_true, checkPoint, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  have hpoint : cert.candidate = point b 0 cert.candidate.coefficients := h.1.1.2
  have hoptimal : Optimal b 0 .shortest cert.candidate := by
    refine ⟨hpoint, Or.inr h.1.1.1, ?_⟩
    intro q hq he
    have hnonzero : q.ambient ≠ 0 := by simpa [Eligible] using he
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hmem := ((checkEnumerationWith_spec b 0 cert.candidate.distanceSq cert.enumeration maxNodes h.1.2).2.1 q).mpr
      ⟨hq, le_of_lt hlt⟩
    rcases h.2 q hmem with hzero | heq
    · exact hnonzero hzero
    · linarith
  refine ⟨hoptimal, ?_⟩
  intro q
  simp only [minimumPoints, sortPoints, Hex.List.sort_eq, List.mem_mergeSort, List.mem_filter,
    bne_self_eq_false, Bool.false_or, bne_iff_ne]
  constructor
  · rintro ⟨hq, hn⟩
    have he := (((checkEnumerationWith_spec b 0 cert.candidate.distanceSq cert.enumeration maxNodes h.1.2).2.1 q).mp hq).1
    exact ⟨he, hn, (h.2 q hq).resolve_left hn⟩
  · rintro ⟨hq, hn, hd⟩
    exact ⟨((checkEnumerationWith_spec b 0 cert.candidate.distanceSq cert.enumeration maxNodes h.1.2).2.1 q).mpr
      ⟨hq, le_of_eq hd⟩, hn⟩
/-- A checked shortest certificate attains the global nonzero minimum and retains every nonzero tie. -/
theorem checkShortest_sound (b : Basis n m) (cert : OptimumCertificate n m)
    (h : checkShortest b.rows cert = true) :
    Optimal b 0 .shortest cert.candidate ∧
      ∀ q, q ∈ minimumPoints .shortest cert.enumeration.points ↔
        q = point b 0 q.coefficients ∧ q.ambient ≠ 0 ∧ q.distanceSq = cert.candidate.distanceSq :=
  checkShortestWith_sound cert.enumeration.tree.nodes b cert h

end HexLatticeEnumMathlib
