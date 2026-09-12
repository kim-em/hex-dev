/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIsoMathlib.Sparse.Encode
public import HexGraphIso.Sparse.Canonical

public section

namespace Hex.GraphIso.Mathlib.Sparse

universe u v

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W] {n k : Nat}
  {G : Mathlib.Colored V k} {H : Mathlib.Colored W k}
  [DecidableRel G.graph.Adj] [DecidableRel H.graph.Adj]

/-- Equality of native sparse canonical forms characterizes Mathlib
coloured graph isomorphism for any two finite enumerations. -/
theorem iso_iff_canon_eq (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H ↔ GraphIso.Sparse.canon (encode eV G) = GraphIso.Sparse.canon (encode eW H) :=
  (encode_iso_iff eV eW).trans (GraphIso.Sparse.iso_iff_canon_eq _ _)

/-- Changing the finite enumeration does not change the canonical form
computed by the actual sparse search. This includes the empty graph. -/
theorem canon_encode_eq (e e' : V ≃ Fin n) :
    GraphIso.Sparse.canon (encode e G) = GraphIso.Sparse.canon (encode e' G) :=
  (iso_iff_canon_eq e e').mp (Mathlib.Colored.Isomorphic.intro
    ⟨SimpleGraph.Iso.refl, fun _ => rfl⟩)

/-- The executable sparse decision is a complete Mathlib isomorphism test. -/
theorem isIso_iff (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    GraphIso.Sparse.isIso (encode eV G) (encode eW H) = true ↔ G.Isomorphic H :=
  (GraphIso.Sparse.isIso_eq_true_iff _ _).trans (encode_iso_iff eV eW).symm

theorem findIso_eq_none_iff (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    GraphIso.Sparse.findIso (encode eV G) (encode eW H) = none ↔ ¬ G.Isomorphic H :=
  (GraphIso.Sparse.findIso_eq_none_iff _ _).trans (not_congr (encode_iso_iff eV eW).symm)

/-- Decode the transporter returned by the total native sparse search. -/
def isoOfFindIso (eV : V ≃ Fin n) (eW : W ≃ Fin n) {p : Perm n}
    (h : GraphIso.Sparse.findIso (encode eV G) (encode eW H) = some p) :
    Mathlib.Colored.Iso G H := isoOfIsIso eV eW (GraphIso.Sparse.findIso_sound h)

end Hex.GraphIso.Mathlib.Sparse
