/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeInduction

public section

/-!
The pre-incumbent phase of the outcome-indexed search induction.

Before `firstterminal` installs the first leaf, the comparison, leaf, and
guide ledgers do not yet exist.  `FirstInv` records exactly the state that
the unique first descent must preserve.  The ordinary `RunInv` takes over
at the discrete leaf.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- State carried by the unique descent before the first leaf exists. -/
structure FirstInv (G : Colored n k) (ctx : Ctx) (level : Nat)
    (cs : List Nat) (numcells : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codes : DescentCodes n cs st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  trailOk : TrailOk ctx level st trail
  genEmpty : st.genTrace = #[]
  autosEmpty : st.autos = #[]
  canongSize : st.canong.size = ctx.n
  orbitId : ∀ v, v < ctx.n → st.orbits[v]! = v

/-- A nonempty root starts the first descent with empty stores, identity
orbits, and no active ancestor frame. -/
theorem FirstInv.root {G : Colored n k} (hn0 : 0 < n) :
    FirstInv G { n := n, g := rowsOf G } 1 []
      (initialPartition G).2.length
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      FrameTrail.empty := by
  have hok := root_searchOk G hn0
  refine ⟨hok, DescentCodes.root _ _ hn0, ?_,
    TrailOk.empty _ _ _, ?_, ?_, ?_, ?_⟩
  · exact CheapOk.root rfl hn0 hok (by simp [rootSt])
  · simp [rootSt]
  · simp [rootSt]
  · simp [rootSt]
  · intro v hv
    change (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]

end Hex.GraphIso.Nauty
