/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The bounded workspace does not change the full generator trace. -/
theorem pushAuto_trace (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

/-- Admission appends the completed scratch permutation to the full trace. -/
theorem admit_trace (st : Search n) :
    (admit st).genTrace = st.genTrace.push st.workperm := by
  simp only [admit, Id.run_pure, pushAuto_trace]

/-- Admitting a checked permutation preserves validity of the full trace. -/
theorem admit_checked {ctx : Ctx n} {st : Search n}
    (htrace : ∀ γ ∈ st.genTrace, checkAutom ctx.g γ = true)
    (hwork : checkAutom ctx.g st.workperm = true) :
    ∀ γ ∈ (admit st).genTrace, checkAutom ctx.g γ = true := by
  intro γ hγ
  rw [admit_trace, Array.mem_push] at hγ
  rcases hγ with hγ | rfl
  · exact htrace γ hγ
  · exact hwork

end Hex.GraphIso.Nauty
