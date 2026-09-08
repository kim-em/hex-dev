/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Reference
public import HexGraphIso.Nauty.Cert.Translator
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public import HexGraphIso.Nauty.Invariant.TargetCell

public import HexGraphIso.Nauty.Invariant.Trace

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- A matching next refinement code advances the first-reference
comparison, regardless of the canonical-incumbent comparison. -/
theorem match_prep {st : SearchSt n} {level code : Nat}
    (hlevel : st.eqlevFirst = level - 1) (hcode : code = st.firstcode[level]!) :
    (otherNodePrep level code st).eqlevFirst = level := by
  rw [otherNodePrep_eqlevFirst]
  simp only [hlevel, hcode, beq_self_eq_true, and_self, ↓reduceIte]

/-- Recovering a matching ancestor keeps the first-reference comparison
live at precisely that ancestor. -/
theorem match_recover {st : SearchSt n} {level inf : Nat}
    (hlevel : level ≤ st.eqlevFirst) :
    (recover n inf level st).eqlevFirst = level := by
  rw [recover_eqlevFirst]
  split <;> omega

/-- A first-reference target hint equal to the specification's choice
cannot demote the first-reference comparison. -/
theorem match_target {ctx : Ctx n} {lab ptn : Array Nat} {level tcLevel : Nat}
    (heq : Equitable ctx level lab ptn) (hlab : LabOk lab n)
    (hlsz : lab.size = n) (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) {hint : Int}
    (hhint : hint = Int.ofNat (specTargetcell ctx lab ptn level tcLevel)) :
    Int.ofNat (maketargetcell ctx lab ptn level tcLevel hint).1 = hint := by
  change Int.ofNat (targetcell ctx lab ptn level tcLevel hint) = hint
  by_cases hadmit : hint ≥ 0 ∧ ptn[hint.toNat]! > level ∧
      ((hint == 0) = true ∨ ptn[hint.toNat - 1]! ≤ level)
  · rw [targetcell, ite_eq_left hadmit, hhint]
    simp
  · rw [targetcell_eq_spec_of_inadmissible heq hlab hlsz hpsz hend hint hadmit, hhint]

/-- The row checker implies the executable automorphism scan. -/
theorem isautom_of_checked {ctx : Ctx n} {γ : Array Nat}
    (hsize : ctx.g.size = n) (h : checkAutom ctx.g γ = true) :
    isautom ctx γ = true := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hsize h
  apply (isautom_iff ctx γ).mpr
  intro i hi j hj _
  have hm := VSet.mem_toList.mp hj
  have hjn := VSet.mem_lt hm
  rw [← hσ i hi, ← hσ j hjn, hrows.2.2 i hi, VSet.mem_image_apply σ _ hjn]
  exact hm

end Hex.GraphIso.Nauty.Generation
