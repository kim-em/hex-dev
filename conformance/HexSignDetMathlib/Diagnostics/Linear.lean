/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Diagnostics.Nested.Inputs
public import HexSignDet.Reencode
public meta import HexSignDet.Reencode
public meta import HexSignDet.Replay
public meta import HexSignDetMathlib.Diagnostics.Nested.Inputs

public section

namespace Hex.SignDetMathlib.Diagnostics.Linear
open Hex Hex.SignDet
open scoped Hex

@[expose] def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
@[expose] def targetHead : DensePoly Rat := DensePoly.ofCoeffs #[0, 2]

/-- Supplied chains for the linear head 2X. -/
@[expose] def positive (c : Rat) : TarskiCertificate Rat Rat Nat :=
  {Nested.query c with
    head := targetHead
    squarefree := {
      Nested.chain 1 with
      chain := #[targetHead, 1]
      initial := ⟨1, 0, 2⟩
      terminal := some (1, targetHead)}
    remainders := {
      Nested.chain c with
      chain := #[targetHead, 1]
      initial := ⟨1, 0, 2 * c⟩
      terminal := some (1, targetHead)}}

/-- X and X² vanish at the root; the initial quotients are 1 and X. -/
@[expose] def vanishing (q quotient : DensePoly Rat) : TarskiCertificate Rat Rat Nat :=
  {positive 1 with
    queryPoly := q
    remainders := {
      chain := #[targetHead]
      degrees := #[1]
      initial := ⟨1, quotient, 1⟩
      steps := #[]
      terminal := none}
    lowerSigns := #[-1]
    upperSigns := #[1]
    lowerVariations := 0
    upperVariations := 0
    value := 0}

@[expose] def countNode : Node Rat Nat :=
  {Nested.parent (1 : Rat) with
    queries := []
    system := {
      (Nested.parent (1 : Rat)).system with
      rows := #v[[]]
      columns := #v[[]]}}

@[expose] def positiveNode : Node Rat Nat :=
  {Nested.leaf (2 : Rat) 4 with
    head := targetHead
    moments := #v[positive 1, positive 2, positive 4]}

@[expose] def zeroNode : Node Rat Nat :=
  {Nested.leaf (0 : Rat) 0 with
    head := targetHead
    queries := [x]
    system := {
      (Nested.leaf (0 : Rat) 0).system with
      counts := #v[0, 1, 0]
      values := #v[1, 0, 0]}
    moments := #v[positive 1, vanishing x 1, vanishing (x * x) x]}

@[expose] def joint : Replay Rat Nat :=
  .split {
    Nested.parent (2 : Rat) with
    head := targetHead
    queries := [2, x]
    system := {(Nested.parent (2 : Rat)).system with columns := #v[[1, 0]]}
    moments := #v[positive 1]} (.leaf positiveNode) (.leaf zeroNode)

@[expose] def sourceRaw : RawDescriptor Rat Nat := ⟨7, x, .negInf, .posInf, [], []⟩
@[expose] def targetRaw : RawDescriptor Rat Nat := ⟨7, targetHead, .negInf, .posInf, [1], [1]⟩

set_option maxRecDepth 32768 in
/-- Count-one evidence for both heads and the joint equation/sign queries. -/
theorem accepted :
    sourceRaw.check Sturm.orderSign 7 (.leaf countNode) = true ∧
    targetRaw.check Sturm.orderSign 7 (.leaf positiveNode) = true ∧
    joint.check Sturm.orderSign 7 targetHead .negInf .posInf [2, x] = true := by
  simp only [RawDescriptor.check, joint, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Construct a validated descriptor from its supplied count-one evidence. -/
def descriptor (raw : RawDescriptor Rat Nat) (tree : Replay Rat Nat)
    (h : raw.check Sturm.orderSign 7 tree = true) : Descriptor Rat Nat Sturm.orderSign 7 := by
  have hs := RawDescriptor.check_eq h
  have hc : tree.check Sturm.orderSign 7 raw.head raw.lower raw.upper raw.queries = true := by
    obtain ⟨hc, _⟩ := hs.2.2
    exact hc
  exact Descriptor.ofTable raw tree hs.1 hs.2.1 hc (by
    obtain ⟨_, hone⟩ := hs.2.2
    exact hone)

theorem descriptor_raw (raw : RawDescriptor Rat Nat) (tree : Replay Rat Nat)
    (h : raw.check Sturm.orderSign 7 tree = true) : (descriptor raw tree h).raw = raw := by
  simp only [descriptor, Descriptor.ofTable_raw]

@[expose] def source := descriptor sourceRaw (.leaf countNode) accepted.1
@[expose] def target := descriptor targetRaw (.leaf positiveNode) accepted.2.1

theorem source_raw : source.raw = sourceRaw := descriptor_raw _ _ _
theorem target_raw : target.raw = targetRaw := descriptor_raw _ _ _

/-- Re-encoding from X to the different head 2X checks both defining equations
at the selected root. No producer or JSON parser is evaluated in this proof. -/
theorem reencoded :
    source.checkReencoding target targetHead .negInf .posInf joint = true := by
  simp only [Descriptor.checkReencoding, source_raw, target_raw, joint, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.Diagnostics.Linear.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted
/-- info: 'Hex.SignDetMathlib.Diagnostics.Linear.reencoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reencoded

end Hex.SignDetMathlib.Diagnostics.Linear
