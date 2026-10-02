/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StateFrame
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.State

/-- Cache invalidation is invisible to the shared proof frame. -/
theorem invalidate_frame (st : State n) :
    State.frame { st with canong := st.canong.invalidate } = st.frame := rfl

/-- The sparse child performs the shared individualization on its frame. -/
theorem child_frame (first : Bool) (level tc tv : Nat) (st : State n) :
    ((policy (n := n)).child first level tc tv st).frame =
      Nauty.child first level tc tv st.frame := by
  cases first <;> rfl

/-- Recovery changes the shared partition and controls exactly as in the
common engine; invalidating native cache indices adds no frame change. -/
theorem recover_frame (inf level : Nat) (st : State n) :
    ((policy (n := n)).recover inf level st).frame = Nauty.recover inf level st.frame := by
  change State.frame (Nauty.recover inf level st) = Nauty.recover inf level st.frame
  unfold Nauty.recover recoverLevels recoverPtn State.frame
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split <;> first | rfl | skip

end Hex.GraphIso.Nauty.Sparse.State
