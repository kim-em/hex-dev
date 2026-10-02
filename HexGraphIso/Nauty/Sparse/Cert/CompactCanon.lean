/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.CompactRoot
public import HexGraphIso.Nauty.Sparse.Cert.Canon

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

variable {n k : Nat}

/-- Package a compact canonical certificate with a checked attaining label.
One replay validates the key; graph and ordered-colour checks validate the label. -/
@[expose] def checkCanon (G : GraphIso.Sparse.Colored n k) (c : CertCandidate n) :
    Option (GraphIso.Sparse.CanonResult n k) :=
  match Label.ofArray? n c.lab with
  | none => none
  | some l =>
    if checkKey G c.tree c.key &&
        (graphCmp c.key.graph (G.graph.relabel l.perm) == .eq) &&
        (labelColors G l == colorSeq G) then
      some ⟨G.relabel l, l⟩
    else none

theorem checkCanon_sound {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    {r : GraphIso.Sparse.CanonResult n k} (h : checkCanon G c = some r) :
    canonSpecKey G = c.key ∧ r.form = G.relabel r.label ∧
      r.form = GraphIso.Sparse.canon G := by
  rw [checkCanon] at h
  split at h
  · cases h
  · rename_i l hl
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases Option.some.inj h
      have hk := checkKey_sound hc.1.1
      have hg := Std.LawfulEqCmp.eq_of_compare (cmp := graphCmp) hc.1.2
      refine ⟨hk, rfl, ?_⟩
      apply GraphIso.Sparse.Colored.toDense_injective
      apply GraphIso.Colored.ext
      · intro i j
        change (G.graph.relabel l.perm).toDense.adj i j =
          (GraphIso.Sparse.canon G).graph.toDense.adj i j
        rw [canon_graph, hk, hg]
      · intro i
        apply Fin.ext
        change ((G.relabel l).coloring.cells[i]).val =
          ((GraphIso.Sparse.canon G).coloring.cells[i]).val
        rw [← labelColors_get, hc.2, colorSeq_get]
    · cases h

theorem produceCand_canon {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    (h : produceCand G = some c) :
    checkCanon G c = some (GraphIso.Sparse.canonicalize G) := by
  have hp : Label.ofArray? n c.lab = some (GraphIso.Sparse.label G) := by
    rw [produceCand_label h, GraphIso.Sparse.label_parse]
  have hg : graphCmp c.key.graph (G.graph.relabel (GraphIso.Sparse.label G).perm) = .eq := by
    apply Std.LawfulEqCmp.compare_eq_iff_eq.mpr
    rw [produceCand_key h, ← canon_graph]
    exact congrArg GraphIso.Sparse.Colored.graph (GraphIso.Sparse.relabel_label G).symm
  simp only [checkCanon, hp, produceCand_replays h, hg, beq_self_eq_true,
    labelColors_eq, Bool.and_self, ite_true]
  congr 1
  change (⟨G.relabel (GraphIso.Sparse.label G), GraphIso.Sparse.label G⟩ :
    GraphIso.Sparse.CanonResult n k) = GraphIso.Sparse.canonicalize G
  rw [GraphIso.Sparse.relabel_label]
  rfl

/-- Compact certification preserves the production key and literal label
from one optimized search and validates them with one sparse replay. -/
@[expose] def certifyCanon? (G : GraphIso.Sparse.Colored n k) :
    Option (GraphIso.Sparse.CanonResult n k) :=
  (produceCand G).bind (checkCanon G)

theorem certifyCanon?_eq (G : GraphIso.Sparse.Colored n k) :
    certifyCanon? G = some (GraphIso.Sparse.canonicalize G) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (produceCand_isSome G)
  simp only [certifyCanon?, hc, Option.bind_some, produceCand_canon hc]

end Hex.GraphIso.Nauty.Sparse.Compact
