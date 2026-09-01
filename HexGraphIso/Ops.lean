/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Complete

public section

/-!
Public canonical-form operations, backed by the certificate-checked
nauty-semantic canonicalization: the branch-and-bound producer first,
validated by the trusted replay, with the provably total exhaustive
fallback. Every theorem stated here descends from the Lean-proved
`specCanon` equivalence.

`canonicalize` is total. `findIso` composes the two canonical labels
into a forward transporter when the canonical forms agree. The bounded
surface separates search limits from replay limits and returns `none`
on exhaustion; exhaustion is never evidence of non-isomorphism.
-/

namespace Hex.GraphIso

variable {n k : Nat}

/-- Compute the canonical form of a coloured graph together with the label
producing it. Total; worst-case cost is factorial. -/
@[expose] def canonicalize (G : Colored n k) : CanonResult n k :=
  Nauty.canonicalizeSpec G

/-- The canonical form of a coloured graph. -/
@[expose] def canon (G : Colored n k) : Colored n k :=
  (canonicalize G).form

/-- The label producing the canonical form. -/
@[expose] def label (G : Colored n k) : Label n :=
  (canonicalize G).label

/-- Relabelling by the canonical label produces the canonical form. -/
theorem relabel_label (G : Colored n k) : G.relabel (label G) = canon G :=
  Nauty.canonicalizeSpec_relabel G

/-- The canonical form has contiguous colour cells in their original
order. -/
theorem colorSorted_canon (G : Colored n k) : ColorSorted (canon G) := by
  rw [ColorSorted]
  intro i j hij
  rw [show canon G = Nauty.specCanon G from
    Nauty.canonicalizeSpec_form G]
  have hkv : ∀ (x : Fin n),
      ((Nauty.specCanon G).coloring.cells[x]).val =
        (Nauty.sortedColorSeq G)[x.val]! := by
    intro x
    rw [Nauty.specCanon]
    simp only [Nauty.formOfKey, Fin.getElem_fin,
      Hex.Vector.getElem_ofFn']
  rw [Fin.le_def, hkv i, hkv j]
  rcases Nat.eq_or_lt_of_le (Fin.le_def.mp hij) with he | hlt
  · rw [he]
    exact Nat.le_refl _
  · have hp := Nauty.pairwise_sortedColorSeq G
    rw [List.pairwise_iff_getElem] at hp
    have hlen := Nauty.length_sortedColorSeq G
    have := hp i.val j.val (by omega) (by
      have := j.isLt
      omega) hlt
    rw [getElem!_pos _ _ (by
        have := i.isLt
        omega),
      getElem!_pos _ _ (by
        have := j.isLt
        omega)]
    exact this

/-- Every coloured graph is isomorphic to its canonical form. -/
theorem canon_iso (G : Colored n k) : Isomorphic G (canon G) :=
  Nauty.canonicalizeSpec_iso G

/-- Isomorphic coloured graphs have equal canonical forms. -/
theorem canon_invariant {G H : Colored n k} (h : Isomorphic G H) :
    canon G = canon H :=
  Nauty.canonicalizeSpec_invariant h

/-- Two coloured graphs are isomorphic exactly when their canonical forms
are equal. The biconditional compares canonical coloured graphs, not the
labels: label arrays refer to different input vertex names and generally
differ for isomorphic inputs. -/
theorem iso_iff_canon_eq (G : Colored n k) (H : Colored n k) :
    Isomorphic G H ↔ canon G = canon H :=
  Nauty.iso_iff_canonicalizeSpec_eq

/-! # Isomorphism search -/

/-- Find one isomorphism from `G` to `H` when one exists: the forward
transporter through the two canonical forms, the canonical label of `H`
composed with the inverse of the canonical label of `G` (in forward
permutation convention). -/
@[expose] def findIso (G H : Colored n k) : Option (Perm n) :=
  if canon G = canon H then
    some (((label H).toPerm.inv).comp ((label G).toPerm))
  else
    none

/-- Boolean isomorphism decision. -/
@[expose] def isIso (G H : Colored n k) : Bool :=
  (findIso G H).isSome

theorem findIso_sound {G H : Colored n k} {p : Perm n}
    (h : findIso G H = some p) : IsIso G H p := by
  rw [findIso] at h
  split at h
  · rename_i hc
    injection h with h
    subst h
    have h1 : IsIso G (canon G) (label G).toPerm := by
      rw [← relabel_label G]
      exact isIso_relabel ..
    have h2 : IsIso H (canon G) (label H).toPerm := by
      rw [hc, ← relabel_label H]
      exact isIso_relabel ..
    exact h1.trans h2.symm
  · simp at h

theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true ↔ Isomorphic G H := by
  rw [findIso]
  split
  · simpa using (iso_iff_canon_eq G H).mpr (by assumption)
  · rename_i hc
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun h => hc ((iso_iff_canon_eq G H).mp h)

theorem isIso_eq_true_iff (G H : Colored n k) :
    isIso G H = true ↔ Isomorphic G H :=
  findIso_isSome_iff G H

theorem isIso_eq_false_iff (G H : Colored n k) :
    isIso G H = false ↔ ¬Isomorphic G H := by
  rw [← isIso_eq_true_iff]
  rcases h : isIso G H <;> simp

/-! # Bounded operations -/

/-- Bounded isomorphism search. Outer `none` is exhaustion; `some none` is
a completed non-isomorphism result; `some (some p)` is a found
transporter. Exhaustion is not evidence of non-isomorphism. -/
@[expose] def findIso? (search : SearchLimits) (G H : Colored n k) :
    Option (Option (Perm n)) :=
  if searchCost n ≤ search.maxNodes then some (findIso G H) else none

set_option linter.unusedVariables false in
/-- Bounded canonicalization. `none` is exhaustion. The replay limit is
part of the public signature: the production backing replays its
certificate before returning; the conservative pre-check charges the
worst case. -/
@[expose] def canon? (search : SearchLimits) (replay : ReplayLimits)
    (G : Colored n k) : Option (CanonResult n k) :=
  if searchCost n ≤ search.maxNodes then some (canonicalize G) else none

namespace FindIso

theorem some_sound (search : SearchLimits) (G H : Colored n k) (p : Perm n)
    (h : findIso? search G H = some (some p)) : IsIso G H p := by
  rw [findIso?] at h
  split at h
  · exact findIso_sound (Option.some.inj h)
  · simp at h

theorem none_sound (search : SearchLimits) (G H : Colored n k)
    (h : findIso? search G H = some none) : ¬Isomorphic G H := by
  rw [findIso?] at h
  split at h
  · intro hiso
    have := (findIso_isSome_iff G H).mpr hiso
    rw [Option.some.inj h] at this
    simp at this
  · simp at h

end FindIso

theorem canon?_eq_some {search : SearchLimits} {replay : ReplayLimits}
    {G : Colored n k} {result : CanonResult n k}
    (h : canon? search replay G = some result) :
    result.form = canon G ∧ G.relabel result.label = result.form := by
  rw [canon?] at h
  split at h
  · rw [← Option.some.inj h]
    exact ⟨rfl, relabel_label G⟩
  · simp at h

/-! # Canonical certificates -/

/-- A canonical certificate: the replayed tree shape, the claimed best
key, and the achieving labelling. Plain data; the checker recomputes
partitions, codes, and comparisons from the graph. -/
structure CanonCert (n k : Nat) where
  /-- The pruned tree the producer visited. -/
  tree : Nauty.CertNode
  /-- The claimed canonical key. -/
  key : Nauty.Key
  /-- The labelling achieving the key. -/
  lab : Array Nat

set_option linter.unusedVariables false in
/-- Produce a canonical certificate from the branch-and-bound search.
`none` on exhaustion of the conservative precharge or when the
untrusted search fails its own validation. -/
@[expose] def certify? (limits : SearchLimits) (G : Colored n k) :
    Option (CanonCert n k) :=
  if searchCost n ≤ limits.maxNodes then
    match Nauty.certifyKey? G with
    | none => none
    | some (cert, B) =>
      match Nauty.bestLab? { n := n, g := Nauty.rowsOf G } 100 B.rows
          n 1 (Nauty.initialPartition G).1
          (Nauty.initPtn n (n + 2) (Nauty.initialPartition G).2)
          (Nauty.initActive (Nauty.initialPartition G).2)
          (Nauty.initialPartition G).2.length B.codes with
      | none => none
      | some lab => some ⟨cert, B, lab⟩
  else
    none

/-- Replay a canonical certificate against the graph. -/
@[expose] def checkCanon (limits : ReplayLimits) (G : Colored n k)
    (cert : CanonCert n k) : Option (CanonResult n k) :=
  if searchCost n ≤ limits.maxCheckerSteps then
    Nauty.checkCanon G cert.tree cert.key cert.lab
  else
    none

theorem checkCanon_sound {limits : ReplayLimits} {G : Colored n k}
    {cert : CanonCert n k} {result : CanonResult n k}
    (h : checkCanon limits G cert = some result) :
    result.form = canon G ∧ G.relabel result.label = result.form := by
  rw [checkCanon] at h
  split at h
  · refine ⟨?_, (Nauty.checkCanon_sound h).2.1.symm⟩
    rw [Nauty.checkCanon_form h,
      show canon G = Nauty.specCanon G from
        Nauty.canonicalizeSpec_form G]
  · simp at h

/-- A checked certificate's key is the spec key. -/
theorem checkCanon_key {limits : ReplayLimits} {G : Colored n k}
    {cert : CanonCert n k} {result : CanonResult n k}
    (h : checkCanon limits G cert = some result) :
    Nauty.canonSpecKey G = cert.key := by
  rw [checkCanon] at h
  split at h
  · exact (Nauty.checkCanon_sound h).1
  · simp at h

/-! # Difference certificates -/

/-- A difference certificate: two canonical certificates whose keys
differ at some position. -/
structure DiffCert (n k : Nat) where
  /-- The certificate for the left graph. -/
  left : CanonCert n k
  /-- The certificate for the right graph. -/
  right : CanonCert n k

/-- Verify the two canonical keys differ: the lexicographic comparison
finds the first differing entry. -/
@[expose] def checkDiff (d : DiffCert n k) : Bool :=
  Nauty.checkDiff d.left.key d.right.key

/-- Two checked certificates and a verified difference prove
non-isomorphism. -/
theorem checkDiff_not_isomorphic {l1 l2 : ReplayLimits}
    {G H : Colored n k} {d : DiffCert n k} {r1 r2 : CanonResult n k}
    (h1 : checkCanon l1 G d.left = some r1)
    (h2 : checkCanon l2 H d.right = some r2)
    (hd : checkDiff d = true) : ¬Isomorphic G H :=
  Nauty.not_isomorphic_of_key_ne (checkCanon_key h1)
    (checkCanon_key h2) (Nauty.checkDiff_sound hd)

end Hex.GraphIso
