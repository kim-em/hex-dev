/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Build
public import HexPermGroup.Search.NormalizerPredicate

public section

namespace Hex.PermGroup.Search.Normalizer

theorem orbit_image (H : Group n) (p : Perm n) (hp : (Predicate.normalizer H).test p = true)
    (x y : Fin n) : y ∈ H.orbit x ↔ p.get y ∈ H.orbit (p.get x) := by
  rw [H.mem_orbit, H.mem_orbit]
  constructor
  · rintro ⟨q, hq, he⟩
    refine ⟨p.conj q, ((Predicate.normalizer_iff H p).mp hp q).mp hq, ?_⟩
    simp [Perm.conj, he]
  · rintro ⟨q, hq, he⟩
    refine ⟨p.inv.conj q, ?_, ?_⟩
    · apply ((Predicate.normalizer_iff H p).mp hp _).mpr
      simpa only [Perm.conj_inv_conj] using hq
    · have hi := congrArg p.inv.get he
      simpa [Perm.conj] using hi

theorem orbit_size (H : Group n) (p : Perm n) (hp : (Predicate.normalizer H).test p = true)
    (x : Fin n) : (H.orbit x).size = (H.orbit (p.get x)).size := by
  have hn : ((H.orbit x).toList.map p.get).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply (H.orbit_nodup x).imp
    intro a b hab he
    exact hab (p.get_inj he)
  have he : ((H.orbit x).toList.map p.get).Perm (H.orbit (p.get x)).toList := by
    apply (List.perm_ext_iff_of_nodup hn (H.orbit_nodup _)).mpr
    intro y
    simp only [List.mem_map, Array.mem_toList_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (orbit_image H p hp x z).mp hz
    · intro hy
      refine ⟨p.inv.get y, ?_, by simp⟩
      apply (orbit_image H p hp x _).mpr
      simpa only [Perm.get_inv_get] using hy
  simpa only [List.length_map, Array.length_toList] using he.length_eq

/-- Orbit cardinalities and the equivalence relation are invariants, while
individual orbits are allowed to be permuted. -/
inductive Reason (n : Nat) where
  | size (x : Fin n)
  | relation (x y : Fin n)

variable {G : Group n}

@[expose] def reject (H : Group n) (t : Node G) : Reason n → Bool
  | .size x => decide (x.val < t.base) &&
      decide ((H.orbit x).size ≠ (H.orbit (t.rep.val.get x)).size)
  | .relation x y => decide (x.val < t.base ∧ y.val < t.base) &&
      decide (decide (y ∈ H.orbit x) ≠ decide (t.rep.val.get y ∈ H.orbit (t.rep.val.get x)))

theorem reject_sound (H : Group n) (t : Node G) (r : Reason n) (hr : reject H t r = true)
    (p : Perm n) (hp : t.Contains p) : (Predicate.normalizer H).test p = false := by
  apply Bool.eq_false_iff.mpr
  intro hP
  cases r with
  | size x =>
    simp only [reject, Bool.and_eq_true, decide_eq_true_eq] at hr
    apply hr.2
    simpa only [t.agrees hp x hr.1] using orbit_size H p hP x
  | relation x y =>
    simp only [reject, Bool.and_eq_true, decide_eq_true_eq] at hr
    apply hr.2
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simpa only [t.agrees hp x hr.1.1, t.agrees hp y hr.1.2] using orbit_image H p hP x y

@[expose] def constraint (G H : Group n) : Constraint G (Predicate.normalizer H) where
  Reason := Reason n
  reject := reject H
  sound := reject_sound H
  trials _ := ((Trials.range n).map Reason.size).append
    (((Trials.range n).product (Trials.range n)).map fun (x, y) => Reason.relation x y)

end Hex.PermGroup.Search.Normalizer

namespace Hex.PermGroup.Group

@[expose] def normalizerSearch (G H : Group n) : Search.Solution (Search.Normalizer.constraint G H) :=
  Search.solve (Search.Normalizer.constraint G H)

/-- Exact normalization requires the leaf conjugation test as well as the
sound orbit refinements used to exclude partial prefixes. -/
@[expose] def normalizer (G H : Group n) : Group n := (G.normalizerSearch H).group

theorem mem_normalizer (G H : Group n) (p : Perm n) :
    Generated (G.normalizer H).generators p ↔ Generated G.generators p ∧
      ∀ q : Perm n, Generated H.generators q ↔ Generated H.generators (p.conj q) := by
  rw [normalizer, Search.Solution.spec, Search.Predicate.normalizer_iff]

end Hex.PermGroup.Group
