/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Logic.Equiv.Defs

public section

/-!
Mathlib-facing coloured graphs.

`SimpleGraph.Coloring` expresses proper colouring, where adjacent
vertices must have different colours; that is not nauty's input. The
object here is an arbitrary ordered vertex partition: a `SimpleGraph`
together with an onto colour map into `Fin k`. An isomorphism preserves
each ordered colour index and may not permute the cells.

The structure requires every colour to occur. A caller with a
non-surjective map can either restrict `k` and renumber the used colours
explicitly, or use the checked helper `Colored.ofColor?`, which returns
`none` together with nothing rather than silently compressing or
reordering colours — compression would change the canonical labelling
convention.
-/

namespace Hex.GraphIso.Mathlib

universe u v

variable {V : Type u} {W : Type v} {k : Nat}

/-- A finite simple graph with an ordered vertex colouring by `Fin k` in
which every colour is used. -/
structure Colored (V : Type u) (k : Nat) [Fintype V] where
  /-- The underlying Mathlib graph. -/
  graph : SimpleGraph V
  /-- The ordered colour of each vertex. -/
  color : V → Fin k
  /-- Every colour is used. -/
  onto : Function.Surjective color

variable [Fintype V] [Fintype W]

/-- A colour-preserving isomorphism of coloured graphs: a graph
isomorphism carrying each vertex to a vertex of the same ordered
colour. -/
structure Colored.Iso (G : Colored V k) (H : Colored W k) where
  /-- The underlying graph isomorphism. -/
  graphIso : G.graph ≃g H.graph
  /-- Colour indices are preserved. -/
  map_color : ∀ v, H.color (graphIso v) = G.color v

/-- Two coloured graphs are isomorphic when a colour-preserving graph
isomorphism exists. -/
def Colored.Isomorphic (G : Colored V k) (H : Colored W k) : Prop :=
  Nonempty (Colored.Iso G H)

/-- Checked construction from a possibly non-onto colour map: `none`
exactly when some colour below `k` is unused. -/
def Colored.ofColor? [DecidableEq (Fin k)] (graph : SimpleGraph V)
    (color : V → Fin k) [DecidableEq V] : Option (Colored V k) :=
  if h : ∀ c : Fin k, ∃ v, color v = c then
    some { graph, color, onto := h }
  else
    none

/-- The unused colour witnessing a failed `Colored.ofColor?`. -/
theorem Colored.ofColor?_eq_none_iff [DecidableEq (Fin k)] [DecidableEq V]
    {graph : SimpleGraph V} {color : V → Fin k} :
    Colored.ofColor? graph color = none ↔ ∃ c : Fin k, ∀ v, color v ≠ c := by
  rw [Colored.ofColor?]
  split
  · next h =>
      simp only [reduceCtorEq, false_iff, not_exists, not_forall]
      intro c
      rcases h c with ⟨v, hv⟩
      exact ⟨v, fun hne => hne hv⟩
  · next h =>
      simp only [true_iff]
      rcases not_forall.mp h with ⟨c, hc⟩
      exact ⟨c, fun v hv => hc ⟨v, hv⟩⟩

/-- The one-cell coloured graph over a nonempty vertex type, and the
zero-colour empty graph otherwise. The result is independent of any
ordering of the vertices. -/
def Colored.plain (graph : SimpleGraph V) : Sigma fun k => Colored V k :=
  if h : Nonempty V then
    ⟨1, { graph, color := fun _ => 0, onto := fun c => by
      rcases h with ⟨v⟩
      exact ⟨v, Subsingleton.elim _ _⟩ }⟩
  else
    ⟨0, { graph, color := fun v => absurd ⟨v⟩ h, onto := fun c => absurd c.pos (by
      have : (0 : Nat) < 0 → False := by omega
      exact fun hc => this hc) }⟩

end Hex.GraphIso.Mathlib
