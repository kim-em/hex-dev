/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Autos
public import HexGraphIso.Sparse.UncoloredOps
import all HexGraphIso.Sparse.Autos

public section

namespace Hex.SparseGraph

variable {n : Nat}

/-- Native automorphism results for a bare sparse graph, using the
zero-or-one-colour view and a single production traversal. -/
@[expose] def autos (G : SparseGraph n) : GraphIso.AutResult n := GraphIso.Sparse.autos G.toColored

theorem autos_isIso {G : SparseGraph n} {p : Perm n} (hp : p ∈ (autos G).gens) : IsIso G G p :=
  (isIso_toColored_iff G G p).mp (GraphIso.Sparse.autos_isIso hp)

theorem autos_complete (G : SparseGraph n) {p : Perm n} (hp : IsIso G G p) :
    GraphIso.Perm.Generated (autos G).gens p :=
  GraphIso.Sparse.autos_complete G.toColored ((isIso_toColored_iff G G p).mpr hp)

theorem autos_sameOrbit (G : SparseGraph n) (u v : Fin n) :
    (autos G).orbits[u.val]! = (autos G).orbits[v.val]! ↔ ∃ p, IsIso G G p ∧ p.get u = v := by
  rw [autos, GraphIso.Sparse.autos_sameOrbit]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, (isIso_toColored_iff G G p).mp hp, he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, (isIso_toColored_iff G G p).mpr hp, he⟩

end Hex.SparseGraph
