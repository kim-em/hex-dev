/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeMutual
import all HexGraphIso.Nauty.Search

public section

/-!
`cosetindex` is a first-path loop cursor.  The first-path loop overwrites
it when it chooses a new sibling, but the whole `otherNode` subtree below
that sibling leaves it unchanged.  These equations isolate that executable
fact; orbit-return coverage may use the cursor only on the off-path side.
-/

namespace Hex.GraphIso.Nauty

private theorem pushAuto_coset (st : SearchSt) (pair : Nat × Nat) :
    (pushAuto st pair).cosetindex = st.cosetindex := by
  rw [pushAuto]
  split <;> rfl

/-- Leaf classification never changes the first-path coset cursor. -/
theorem processnode_coset (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) :
    (processnode ctx level numcells st).2.cosetindex = st.cosetindex := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt => x.2.cosetindex),
    pushAuto_coset, ite_self]

/-- Comparison preparation never changes the first-path coset cursor. -/
theorem otherNodePrep_coset (level code : Nat) (st : SearchSt) :
    (otherNodePrep level code st).cosetindex = st.cosetindex := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.cosetindex, ite_self]

/-- Parent-frame recovery never changes the first-path coset cursor. -/
theorem recover_coset (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).cosetindex = st.cosetindex := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.cosetindex, ite_self]

/-- Completed-leaf cleanup never changes the first-path coset cursor. -/
theorem leafFinish_coset (ctx : Ctx) (level : Nat) (st : SearchSt) :
    (leafFinish ctx level st).cosetindex = st.cosetindex := by
  rw [leafFinish]
  split <;> split <;> rfl

end Hex.GraphIso.Nauty
