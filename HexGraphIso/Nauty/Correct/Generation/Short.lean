/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.OffPath.Loop
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty

namespace Generation

variable {n : Nat}

set_option maxHeartbeats 4000000 in
/-- A fresh short-prune request never returns to the current first-path
guide. The guiding child can subsequently change that guide; an off-path
child cannot. -/
theorem process_short {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    (hclear : st.needshortprune = false)
    (hshort : (processnode ctx level numcells st).2.needshortprune = true) :
    (processnode ctx level numcells st).1 ≠ Int.ofNat st.gcaFirst := by
  by_cases hg : st.eqlevFirst ≠ level ∧ st.compCanon < 0
  · rw [(processnode_fast hg).1]
    rw [processnode_fast_short hg, hclear] at hshort
    split at hshort
    · exact ‹level ≠ st.noncheaplevel ∧ _›.2
    · contradiction
  · by_cases hnc : (numcells == n) = true
    · by_cases hgate :
        (st.eqlevFirst == level && st.firstcode[level + 1]! == codeSentinel) = true
      all_goals by_cases hcomp : (st.compCanon == 0) = true
      all_goals by_cases hdepth : level < st.canonlevel
      all_goals
        unfold processnode at hshort ⊢
        simp only [hg, hnc, hgate, hcomp, hdepth, ↓reduceIte, bind, pure, Id.run] at hshort ⊢
        simp only [apply_ite (fun x : Int × SearchSt n => x.1),
          apply_ite (fun x : Int × SearchSt n => x.2.needshortprune),
          pushAuto_needshortprune, pushAuto_gcaFirst, pushAuto_gcaCanon,
          pushAuto_noncheaplevel, pushAuto_allsamelevel, pushAuto_eqlevCanon,
          Bool.false_eq_true, false_and, true_and, ↓reduceIte] at hshort ⊢
        simp_all (config := { maxSteps := 1000000 })
        repeat' (first | split at hshort | split) <;> simp_all
        all_goals repeat' (first | split at hshort | split) <;> simp_all
        all_goals omega
    · rw [processnode_internal hg hnc, hclear] at hshort
      contradiction

end Generation

end Hex.GraphIso.Nauty
