/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.ThomRoots
public import HexRealRootsTheory.RealClosed

public section

namespace RealClosureConsumer

open Hex Hex.SignDet HexPolyTheory.Interpret HexRealRootsTheory

attribute [local instance 2000] Field.toGrindField

noncomputable section

def rootValue (d : Descriptor ℝ Nat Sturm.orderSign 7) : ℝ :=
  d.root id (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) HexSturmTheory.orderSign_eq

/-- Use complete BKR/Thom production to obtain an actual selected descriptor
for any root in a lawful domain. No successful-output assumption is supplied. -/
theorem selected_root (p : DensePoly ℝ) (a b : Endpoint ℝ)
    (domain : HexSturmTheory.Domain id (fun _ => Iff.rfl) p a b)
    (x : ℝ) (member : x ∈ Tarski.rootsIn (interpret id (fun _ => Iff.rfl) p)
      (a.map id) (b.map id)) :
    ∃ out, Descriptor.buildRoots Sturm.orderSign 7 p a b = .ok (some out) ∧
      (∃ d ∈ out, rootValue d = x) ∧
      (∀ y, y ∈ Tarski.rootsIn (interpret id (fun _ => Iff.rfl) p)
        (a.map id) (b.map id) ↔ y ∈ out.map rootValue) ∧
      (out.map rootValue).Nodup ∧
      (out.map rootValue).Pairwise (· < ·) := by
  obtain ⟨out, produced, coverage, distinct, ordered⟩ := Descriptor.buildRoots_roots
    id (fun _ => Iff.rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) HexSturmTheory.orderSign_eq
    (fun _ => rfl) (fun _ => rfl) 7 p a b domain
  exact ⟨out, produced, List.mem_map.mp ((coverage x).mp member), coverage, distinct, ordered⟩

/-- info: 'RealClosureConsumer.selected_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected_root

end

end RealClosureConsumer
