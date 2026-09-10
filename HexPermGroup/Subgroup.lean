/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Build

public section

namespace Hex.PermGroup.Group

/-- Inclusion of the represented permutation subgroups. -/
@[expose] def IsSubgroup (H G : Group n) : Prop :=
  ∀ p : Perm n, Generated H.generators p → Generated G.generators p

/-- Containment needs only the original generators of the smaller group. -/
@[expose] def isSubgroup (H G : Group n) : Bool :=
  decide (∀ i : Fin H.generators.size, G.contains H.generators[i.val] = true)

theorem isSubgroup_iff (H G : Group n) : H.isSubgroup G = true ↔ H.IsSubgroup G := by
  constructor
  · intro h p hp
    apply hp.mono
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hq
    exact (G.contains_iff _).mp ((of_decide_eq_true h) ⟨i, hi⟩)
  · intro h
    apply decide_eq_true
    intro i
    exact (G.contains_iff _).mpr (h _ (.generator (Array.getElem_mem i.isLt)))

/-- The first original generator whose complete sift disproves containment. -/
@[expose] def subgroupFailure? (H G : Group n) : Option (Fin H.generators.size) :=
  (List.finRange H.generators.size).find? fun i => !G.contains H.generators[i.val]

theorem subgroupFailure_none (H G : Group n) : H.subgroupFailure? G = none ↔ H.isSubgroup G = true := by
  simp [subgroupFailure?, isSubgroup]

theorem subgroupFailure_sound (H G : Group n) (i : Fin H.generators.size)
    (h : H.subgroupFailure? G = some i) : ¬ Generated G.generators H.generators[i.val] := by
  have hf := List.find?_some h
  intro hi
  have hp := (G.contains_iff _).mpr hi
  simp [hp] at hf

/-- Equality of subgroups, independent of their presentations. -/
@[expose] def sameGroup (G H : Group n) : Bool := G.isSubgroup H && H.isSubgroup G

theorem sameGroup_iff (G H : Group n) : G.sameGroup H = true ↔ SameGroup G H := by
  simp only [sameGroup, Bool.and_eq_true, isSubgroup_iff]
  unfold SameGroup
  exact ⟨fun ⟨hgh, hhg⟩ p => ⟨hgh p, hhg p⟩,
    fun h => ⟨fun p => (h p).mp, fun p => (h p).mpr⟩⟩

/-- Concatenate the original generators and rebuild a complete chain. -/
@[expose] def join (G H : Group n) : Group n := ofGenerators (G.generators ++ H.generators)

theorem left_subgroup_join (G H : Group n) : G.IsSubgroup (G.join H) := by
  intro p hp
  exact hp.mono fun q hq => .generator (by simp [join, hq])

theorem right_subgroup_join (G H : Group n) : H.IsSubgroup (G.join H) := by
  intro p hp
  exact hp.mono fun q hq => .generator (by simp [join, hq])

theorem join_le (G H K : Group n) : (G.join H).IsSubgroup K ↔ G.IsSubgroup K ∧ H.IsSubgroup K := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (G.left_subgroup_join H p hp),
      fun p hp => h p (G.right_subgroup_join H p hp)⟩
  · rintro ⟨hg, hh⟩ p hp
    apply hp.mono
    intro q hq
    simp only [join, generators_ofGenerators, Array.mem_append] at hq
    rcases hq with hq | hq
    · exact hg q (.generator hq)
    · exact hh q (.generator hq)

/-- Normalize once for orbit operations; signed input references retain the
connection to the group's original generator array. -/
@[expose] def working (G : Group n) : Normalized G.generators := normalize G.generators

/-- The top working array already has checked symmetry and original-generator
provenance; point-orbit replay need not normalize the input again. -/
theorem chain_symmetric (G : Group n) (p : Perm n) (hp : p ∈ G.chain.generators) :
    p.inv ∈ G.chain.generators := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
  exact ((of_decide_eq_true G.valid).1.1.2.2 ⟨i, hi⟩).2

theorem chain_generated (G : Group n) (p : Perm n) :
    Generated G.chain.generators p ↔ Generated G.generators p :=
  (Chain.checkFrom_sound (of_decide_eq_true G.valid).2.2 p).symm.trans (G.contains_iff p)

@[expose] def orbitData (G : Group n) (a : Fin n) :
    {c : Orbit n // c.Valid G.chain.generators a} :=
  Orbit.ofSymmetric G.chain.generators a G.chain_symmetric

/-- Sorted point orbit, retaining fixed points. The discovery order remains in
the certificate and is independent of this public serialization. -/
@[expose] def orbit (G : Group n) (a : Fin n) : Array (Fin n) :=
  let data := G.orbitData a
  ((List.finRange n).filter fun x => data.val.lookup[x.val].isSome).toArray

theorem mem_orbit (G : Group n) (a x : Fin n) :
    x ∈ G.orbit a ↔ ∃ p : Perm n, Generated G.generators p ∧ p.get a = x := by
  let data := G.orbitData a
  have hm : data.val.lookup[x.val].isSome = true ↔ x ∈ data.val.points := by
    rw [Option.isSome_iff_ne_none]
    have he := (data.property.2.2.2.1 x).1
    by_cases hx : x ∈ data.val.points <;> simp_all
  simp only [orbit, List.mem_toArray, List.mem_filter, List.mem_finRange, true_and]
  rw [hm, data.property.mem_iff]
  simp only [G.chain_generated]

theorem orbit_sorted (G : Group n) (a : Fin n) :
    (G.orbit a).toList.Pairwise (fun x y => x.val < y.val) := by
  simp only [orbit, List.toList_toArray]
  exact (List.pairwise_lt_finRange n).filter _

theorem orbit_nodup (G : Group n) (a : Fin n) : (G.orbit a).toList.Nodup := by
  apply (G.orbit_sorted a).imp
  intro x y h he
  simp [he] at h

theorem self_mem_orbit (G : Group n) (a : Fin n) : a ∈ G.orbit a :=
  (G.mem_orbit a a).mpr ⟨Perm.id n, .id, Perm.get_id a⟩

theorem orbit_eq (G : Group n) (a b : Fin n) (hb : b ∈ G.orbit a) : G.orbit a = G.orbit b := by
  obtain ⟨p, hp, he⟩ := (G.mem_orbit a b).mp hb
  have hm (x : Fin n) : x ∈ G.orbit a ↔ x ∈ G.orbit b := by
    rw [G.mem_orbit, G.mem_orbit]
    constructor
    · rintro ⟨q, hq, hx⟩
      refine ⟨q.comp p.inv, .comp hq (.inv hp), ?_⟩
      have hi := congrArg p.inv.get he
      simp only [Perm.inv_get_get] at hi
      simp [← hi, hx]
    · rintro ⟨q, hq, hx⟩
      exact ⟨q.comp p, .comp hq hp, by simp [he, hx]⟩
  unfold orbit
  apply congrArg List.toArray
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simpa only [orbit, List.mem_toArray, List.mem_filter, List.mem_finRange, true_and] using hm x

/-- Retain an orbit at its least point. This gives a deterministic partition with
both point arrays and the list of orbits sorted. -/
@[expose] def orbitAt? (G : Group n) (a : Fin n) : Option (Array (Fin n)) :=
  let points := G.orbit a
  if points[0]? = some a then some points else none

@[expose] def orbits (G : Group n) : Array (Array (Fin n)) :=
  ((List.finRange n).filterMap G.orbitAt?).toArray

theorem orbit_mem_orbits (G : Group n) (a : Fin n) : G.orbit a ∈ G.orbits := by
  have hpos := Array.size_pos_of_mem (G.self_mem_orbit a)
  let b := (G.orbit a)[0]'hpos
  have hb : b ∈ G.orbit a := Array.getElem_mem hpos
  have he := G.orbit_eq a b hb
  apply List.mem_toArray.mpr
  apply List.mem_filterMap.mpr
  refine ⟨b, List.mem_finRange b, ?_⟩
  simp only [orbitAt?, ← he]
  simp [b]

theorem mem_orbits (G : Group n) (points : Array (Fin n)) :
    points ∈ G.orbits ↔ ∃ a : Fin n, points = G.orbit a := by
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp (List.mem_toArray.mp h)
    unfold orbitAt? at ha
    dsimp only at ha
    split at ha
    · exact ⟨a, (Option.some.inj ha).symm⟩
    · simp at ha
  · rintro ⟨a, rfl⟩
    exact G.orbit_mem_orbits a

theorem orbits_disjoint (G : Group n) {xs ys : Array (Fin n)}
    (hx : xs ∈ G.orbits) (hy : ys ∈ G.orbits) (hne : xs ≠ ys) :
    ∀ x ∈ xs, x ∉ ys := by
  obtain ⟨a, rfl⟩ := (G.mem_orbits xs).mp hx
  obtain ⟨b, rfl⟩ := (G.mem_orbits ys).mp hy
  intro x hx hy
  exact hne ((G.orbit_eq a x hx).trans (G.orbit_eq b x hy).symm)

theorem orbits_sorted (G : Group n) : G.orbits.toList.Pairwise
    (fun xs ys => ∃ a b : Fin n, xs[0]? = some a ∧ ys[0]? = some b ∧ a.val < b.val) := by
  simp only [orbits, List.toList_toArray]
  apply List.pairwise_filterMap.mpr
  apply (List.pairwise_lt_finRange n).imp
  intro a b hab xs hx ys hy
  unfold orbitAt? at hx hy
  dsimp only at hx hy
  split at hx <;> split at hy
  · rename_i ha hb
    exact ⟨a, b, (Option.some.inj hx) ▸ ha, (Option.some.inj hy) ▸ hb, hab⟩
  all_goals simp_all

theorem orbits_cover (G : Group n) (a : Fin n) : ∃ points ∈ G.orbits, a ∈ points :=
  ⟨G.orbit a, G.orbit_mem_orbits a, G.self_mem_orbit a⟩

theorem orbits_nodup (G : Group n) : G.orbits.toList.Nodup := by
  apply G.orbits_sorted.imp
  intro xs ys h he
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hh : a = b := Option.some.inj (ha.symm.trans (he ▸ hb))
  simp [hh] at hab

/-- A transporter is returned exactly when the target is in the point orbit. -/
@[expose] def transporter? (G : Group n) (a b : Fin n) : Option (Element G) :=
  let data := G.orbitData a
  match data.val.lookup[b.val] with
  | none => none
  | some j => some ⟨data.val.reps[j.val],
      (G.chain_generated _).mp (Orbit.rep_generated data.property j)⟩

theorem transporter_image (G : Group n) (a b : Fin n) (p : Element G)
    (h : G.transporter? a b = some p) : p.val.get a = b := by
  unfold transporter? at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i j hj
    have he := congrArg (fun p : Element G => p.val) (Option.some.inj h)
    rw [← he, Orbit.rep_apply (G.orbitData a).property]
    exact ((G.orbitData a).property.2.2.2.1 b).2 j hj

theorem transporter_isSome (G : Group n) (a b : Fin n) :
    (G.transporter? a b).isSome = true ↔ b ∈ G.orbit a := by
  simp only [orbit, List.mem_toArray, List.mem_filter, List.mem_finRange, true_and]
  unfold transporter?
  dsimp only
  split <;> simp_all

theorem transporter_none (G : Group n) (a b : Fin n) :
    G.transporter? a b = none ↔ ¬ ∃ p : Element G, p.val.get a = b := by
  have he : G.transporter? a b = none ↔ ¬ (G.transporter? a b).isSome = true := by
    cases G.transporter? a b <;> simp
  rw [he, transporter_isSome, mem_orbit]
  constructor
  · rintro h ⟨p, hp⟩
    exact h ⟨p.val, p.property, hp⟩
  · rintro h ⟨p, hp, he⟩
    exact h ⟨⟨p, hp⟩, he⟩

/-- The full point stabilizer, using every Schreier generator of the point orbit. -/
@[expose] def stabilizer (G : Group n) (a : Fin n) : Group n :=
  ofGenerators (Orbit.stabilizerGens (G.orbitData a).property)

theorem mem_stabilizer (G : Group n) (a : Fin n) (p : Perm n) :
    Generated (G.stabilizer a).generators p ↔ Generated G.generators p ∧ p.get a = a := by
  rw [stabilizer, generators_ofGenerators, Orbit.stabilizerGens_spec,
    G.chain_generated]

/-- Iterate full point stabilizers in the supplied order. -/
@[expose] def pointwise (G : Group n) : List (Fin n) → Group n
  | [] => G
  | a :: points => (G.stabilizer a).pointwise points

theorem mem_pointwise (G : Group n) (points : List (Fin n)) (p : Perm n) :
    Generated (G.pointwise points).generators p ↔
      Generated G.generators p ∧ ∀ a ∈ points, p.get a = a := by
  induction points generalizing G with
  | nil => simp [pointwise]
  | cons a points ih =>
    simp only [pointwise, ih, mem_stabilizer, List.forall_mem_cons, and_assoc]

/-- Pointwise stabilizers depend on the listed point set, so reordering or
repeating points leaves the represented subgroup unchanged. -/
theorem pointwise_same (G : Group n) (xs ys : List (Fin n))
    (h : ∀ a, a ∈ xs ↔ a ∈ ys) : SameGroup (G.pointwise xs) (G.pointwise ys) := by
  intro p
  rw [mem_pointwise, mem_pointwise]
  constructor
  · rintro ⟨hp, hf⟩
    exact ⟨hp, fun a ha => hf a ((h a).mpr ha)⟩
  · rintro ⟨hp, hf⟩
    exact ⟨hp, fun a ha => hf a ((h a).mp ha)⟩

end Hex.PermGroup.Group
