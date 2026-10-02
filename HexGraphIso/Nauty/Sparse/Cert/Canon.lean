/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Candidate
public import HexGraphIso.Nauty.Sparse.Cert.Colors

public section

namespace Hex.GraphIso.Nauty.Sparse

variable {n k : Nat}

/-- The graph component of the total production form is the declarative
maximum's graph. -/
theorem canon_graph (G : GraphIso.Sparse.Colored n k) :
    (GraphIso.Sparse.canon G).graph = (canonSpecKey G).graph := by
  rw [GraphIso.Sparse.canon_eq_specCanon, canonSpecLabel_attains]
  rfl

/-- Check an untrusted key, tree and label with one sparse replay. The
label must attain the key's graph and the ordered canonical colours. -/
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

/-- Accepted certificates identify the canonical key, return an actual
relabelling, and give precisely the total sparse canonical form. -/
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

/-- Every produced candidate passes the full result checker with the
literal production label, including its tie order. -/
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

/-- Produce and check the complete native sparse result. The optimized
search runs once; the checker replays the supplied certificate once. -/
@[expose] def certifyCanon? (G : GraphIso.Sparse.Colored n k) :
    Option (GraphIso.Sparse.CanonResult n k) :=
  (produceCand G).bind (checkCanon G)

/-- Unlimited certification succeeds unconditionally and agrees with the
executed direct API in both its canonical form and literal label. -/
theorem certifyCanon?_eq (G : GraphIso.Sparse.Colored n k) :
    certifyCanon? G = some (GraphIso.Sparse.canonicalize G) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (produceCand_isSome G)
  simp only [certifyCanon?, hc, Option.bind_some, produceCand_canon hc]

end Hex.GraphIso.Nauty.Sparse
