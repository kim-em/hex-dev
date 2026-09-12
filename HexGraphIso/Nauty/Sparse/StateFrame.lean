/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecNode
public import HexGraphIso.Nauty.Sparse.SearchBounds
public import HexGraphIso.Nauty.Policy.Generic.Reach
public import HexGraphIso.Nauty.Policy.Effect

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A proof projection exposing shared partition and bookkeeping fields.
Its empty unused storage is never
passed to an executable search or adjacency operation. -/
@[expose] noncomputable def State.frame (st : State n) : Search n :=
  { st with canong := #[] }

/-- Entry to an actual sparse node: valid partition, exact depth/count,
ordered-colour reachability, reference-label frame and bounded scratch. -/
structure NodeInv (G : GraphIso.Sparse.Colored n k) (level numcells : Nat) (st : State n) : Prop where
  spec : SpecNode G.graph level st.lab st.ptn st.active numcells
  ok : SearchOk G.toDense level numcells st.frame
  scratch : Scratch.Bounded n st.canong.scratch

/-- A refined or recovered parent is equitable. Its active set need not
be reused: the next child installs its own singleton active splitter. -/
structure Ready (G : GraphIso.Sparse.Colored n k) (level numcells : Nat) (st : State n) : Prop where
  ok : SearchOk G.toDense level numcells st.frame
  equitable : Equitable (Graph.context G.graph) level st.lab st.ptn
  scratch : Scratch.Valid n st.lab st.ptn level st.canong.scratch

/-- The persistent result of a call, retaining the exact frame effect and
scratch bounds also when the call unwinds past its caller. -/
structure FrameOut (G : GraphIso.Sparse.Colored n k) (base level : Nat) (st out : State n) : Prop where
  effect : SearchOut G.toDense base level st.frame out.frame
  scratch : Scratch.Bounded n out.canong.scratch

namespace FrameOut

theorem refl {G : GraphIso.Sparse.Colored n k} {base level numcells : Nat} {st : State n}
    (h : NodeInv G level numcells st) : FrameOut G base level st st :=
  ⟨SearchOut.refl _ _ _ h.ok.reach, h.scratch⟩

theorem trans {G : GraphIso.Sparse.Colored n k} {level : Nat} {st mid out : State n}
    (h : FrameOut G level level st mid) (h' : FrameOut G level level mid out) :
    FrameOut G level level st out := ⟨h.effect.trans h'.effect, h'.scratch⟩

end FrameOut

end Hex.GraphIso.Nauty.Sparse
