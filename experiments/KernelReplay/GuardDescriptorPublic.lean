/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorPoint

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPublic
open Hex.SignDet HexRealRootsTheory HexPolyTheory.Interpret

/-- The actual second owner's descriptor uses the same realized first reader. -/
theorem descriptor : Transport.Finite.DescriptorData GuardDescriptorPoint.predecessor
    (Element.sign (context := FrameOwners.first)) (fun x : ℝ => (SignType.sign x : Int))
    FrameOwners.second.root.raw FrameOwners.second.root.evidence :=
  GuardDescriptorPoint.descriptorData

/-- One ordinary real point lies in the original second root interval and has
its full original Thom sign word. -/
theorem selected :
    GuardDescriptorPoint.point ∈ Tarski.rootsIn
      (interpret (fun y : ℝ => y) (fun _ => Iff.rfl)
        (Transport.polynomial GuardDescriptorPoint.predecessor FrameOwners.second.root.raw.head))
      ((Transport.endpoint GuardDescriptorPoint.predecessor FrameOwners.second.root.raw.lower).map
        (fun y : ℝ => y))
      ((Transport.endpoint GuardDescriptorPoint.predecessor FrameOwners.second.root.raw.upper).map
        (fun y : ℝ => y)) ∧
    signsAt (fun y : ℝ => y) (fun _ => Iff.rfl)
      (FrameOwners.second.root.raw.queries.map
        (Transport.polynomial GuardDescriptorPoint.predecessor))
      GuardDescriptorPoint.point = FrameOwners.second.root.raw.signs :=
  GuardDescriptorPoint.spec

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorPublic
