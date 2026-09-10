/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Build
public import HexPermGroup.Search.Image
public import HexPermGroup.Predicates

public section

namespace Hex.PermGroup.Search

/-- Commutation is tested on the original generators of the second group. -/
@[expose] def Predicate.centralizer (H : Group n) : Predicate n where
  test p := decide (∀ i : Fin H.generators.size,
    p.comp H.generators[i.val] = H.generators[i.val].comp p)
  id := by simp
  comp p q hp hq := by
    apply decide_eq_true
    intro i
    have hp := (of_decide_eq_true hp) i
    have hq := (of_decide_eq_true hq) i
    calc
      (p.comp q).comp H.generators[i.val] = p.comp (q.comp H.generators[i.val]) := Perm.comp_assoc ..
      _ = p.comp (H.generators[i.val].comp q) := congrArg p.comp hq
      _ = (p.comp H.generators[i.val]).comp q := (Perm.comp_assoc ..).symm
      _ = (H.generators[i.val].comp p).comp q := congrArg (fun r => r.comp q) hp
      _ = H.generators[i.val].comp (p.comp q) := Perm.comp_assoc ..
  inv p hp := by
    apply decide_eq_true
    intro i
    apply Perm.ext
    intro x
    apply p.get_inj
    have he := congrArg (fun r : Perm n => r.get (p.inv.get x)) ((of_decide_eq_true hp) i)
    simpa using he.symm

theorem Predicate.centralizer_iff (H : Group n) (p : Perm n) :
    (centralizer H).test p = true ↔
      ∀ q : Perm n, Generated H.generators q → p.comp q = q.comp p := by
  constructor
  · intro h q hq
    apply hq.commutes
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact (of_decide_eq_true h) ⟨i, hi⟩
  · intro h
    apply decide_eq_true
    intro i
    exact h _ (.generator (Array.getElem_mem i.isLt))

namespace Centralizer

variable {G : Group n}

/-- Once `x` is assigned, commutation forces the image of `h(x)`. Reject if
that image is outside its remaining suffix orbit. This includes conflicts
with an already assigned image, whose suffix orbit is a singleton. -/
@[expose] def reject (H : Group n) (t : Node G) (r : Fin H.generators.size × Fin n) : Bool :=
  decide (r.2.val < t.base) &&
    !t.imagePossible (H.generators[r.1.val].get r.2) (H.generators[r.1.val].get (t.rep.val.get r.2))

theorem reject_sound (H : Group n) (t : Node G) (r : Fin H.generators.size × Fin n)
    (hr : reject H t r = true) (p : Perm n) (hp : t.Contains p) :
    (Predicate.centralizer H).test p = false := by
  apply Bool.eq_false_iff.mpr
  intro hP
  simp only [reject, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
  have he := congrArg (fun q : Perm n => q.get r.2) ((of_decide_eq_true hP) r.1)
  have hi := t.imagePossible_of_contains hp (H.generators[r.1.val].get r.2)
  have ha := t.agrees hp r.2 hr.1
  simp only [Perm.get_comp, ha] at he
  rw [he, hr.2] at hi
  cases hi

/-- Replay identifies the original generator and assigned source point that
forced an impossible image. Discovery follows generator then point order. -/
@[expose] def constraint (G H : Group n) : Constraint G (Predicate.centralizer H) where
  Reason := Fin H.generators.size × Fin n
  reject := reject H
  sound := reject_sound H
  trials _ := (Trials.range H.generators.size).product (Trials.range n)

end Centralizer

end Hex.PermGroup.Search

namespace Hex.PermGroup.Group

/-- Exact centralizer search, with replay of forced-image pruning and complete
coverage of every remaining chain branch. `H` need not be a subgroup of `G`. -/
@[expose] def centralizerSearch (G H : Group n) : Search.Solution (Search.Centralizer.constraint G H) :=
  Search.solve (Search.Centralizer.constraint G H)

@[expose] def centralizer (G H : Group n) : Group n := (G.centralizerSearch H).group

theorem mem_centralizer (G H : Group n) (p : Perm n) :
    Generated (G.centralizer H).generators p ↔ Generated G.generators p ∧
      ∀ q : Perm n, Generated H.generators q → p.comp q = q.comp p := by
  rw [centralizer, Search.Solution.spec, Search.Predicate.centralizer_iff]

/-- The center is the centralizer of the group in itself. -/
@[expose] def center (G : Group n) : Group n := G.centralizer G

theorem mem_center (G : Group n) (p : Perm n) :
    Generated G.center.generators p ↔ Generated G.generators p ∧
      ∀ q : Perm n, Generated G.generators q → p.comp q = q.comp p :=
  mem_centralizer G G p

/-- Centralizing one permutation is centralizing the cyclic group it generates;
the permutation itself need not belong to the ambient group. -/
@[expose] def centralizerPerm (G : Group n) (q : Perm n) : Group n :=
  G.centralizer (ofGenerators #[q])

theorem mem_centralizerPerm (G : Group n) (q p : Perm n) :
    Generated (G.centralizerPerm q).generators p ↔ Generated G.generators p ∧ p.comp q = q.comp p := by
  rw [centralizerPerm, mem_centralizer]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact h q (.generator (by simp))
  · intro h r hr
    apply hr.commutes
    intro s hs
    simp only [generators_ofGenerators, Array.mem_singleton] at hs
    simpa only [hs] using h

end Hex.PermGroup.Group
