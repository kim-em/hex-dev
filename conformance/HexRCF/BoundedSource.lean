/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.SourceBuild
import HexRCF.RealCoefficients.SourceIdentity
import HexRealClosure.NumberFieldTower
import HexSignDet.Codec.Bytes
import HexRCF.BoundedSource.Positive
import HexRCF.BoundedSource.Negative
import HexRCF.BoundedSource.Cubic
import HexRCF.SelectedRoot.KernelCheck

/-! Native bounded-source production and exact frozen-byte controls.
Ordinary proof authentication is checked separately in `BoundedSource.Quote`. -/
namespace Hex.RCF.BoundedSourceTests
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients

def registry : BaseContext.Registry := fun _ => none
abbrev base := NumberField.base registry
def poly (values : List Rat) : base.Poly :=
  DensePoly.ofCoeffs (values.toArray.map fun value => ⟨value⟩)
def margin (square : DyadicSquare) : base.Poly :=
  DensePoly.ofCoeffs ((SourceIdentity.margin square).coeffs.map fun value => ⟨value⟩)

def propose (polynomial : base.Poly) (square : DyadicSquare) :=
  let center := square.re.toRat
  let radius := 2 * square.halfWidth.toRat
  SourceBuild.buildOn polynomial (margin square)
    (.finite ⟨center-radius⟩) (.finite ⟨center+radius⟩)

open Lean in
run_meta do
  unless Hex.RCF.SelectedRootTests.KernelCheck.producers.contains ``SourceBuild.buildOn do
    throwError "bounded source producer is missing from the kernel guard"

private def descriptorError (polynomial : base.Poly) (lower upper : Rat)
    (expected : DescriptorError) : IO Unit := do
  match SourceBuild.buildOn polynomial (poly [1]) (.finite ⟨lower⟩) (.finite ⟨upper⟩) with
  | .error (.descriptor error) =>
    unless error == expected do
      throw (IO.userError s!"wrong bounded-source diagnostic: {repr error}, expected {repr expected}")
  | _ => throw (IO.userError "bounded-source failure was swallowed or retried")

private def validate (source : SourceBuild.Result base) (proposal : ScalarPacket.Proposal) : IO Unit := do
  let .ok graph := Codec.readGraph base.codec Tower.Signature.codec base.signature
      source.root.raw.head source.root.raw.lower source.root.raw.upper proposal.evidence
    | throw (IO.userError "bounded scalar graph did not decode")
  unless (graph.validate? base.sign base.signature source.root.raw.head
      source.root.raw.lower source.root.raw.upper).isSome do
    throw (IO.userError "bounded scalar graph did not validate")

#eval (show IO Unit from do
  let quadratic := poly [-2,0,1]
  let square : DyadicSquare := ⟨Dyadic.ofInt 181 >>> (7 : Int),0,8⟩
  let cubic : DyadicSquare := ⟨Dyadic.ofInt 1290 >>> (10 : Int),0,12⟩
  let _ : Hashable base.Value := ⟨fun value => hash (base.codec.encode value)⟩
  let _ : Hashable Tower.Signature := ⟨fun value => hash (Tower.Signature.codec.encode value)⟩
  let mut packets := #[]
  for (polynomial,window) in [(quadratic,square),(quadratic,{square with re := -square.re}),
      (poly [-2,0,0,1],cubic)] do
    let .ok source := propose polynomial window
      | throw (IO.userError "bounded source refused a valid selected root")
    unless source.root.raw.indices.isEmpty && source.root.raw.signs.isEmpty do
      throw (IO.userError "bounded source unexpectedly retained derivative queries")
    validate source source.equation
    validate source source.enclosure
    packets := packets.push <| Codec.Json.arr #[
      Codec.descriptor base.codec Tower.Signature.codec source.root.raw,
      Codec.graph base.codec Tower.Signature.codec (Dag.encode source.root.evidence),
      source.equation.packet,source.enclosure.packet]
  let frozen := Codec.Json.arr #[BoundedSource.Positive.packet,
    BoundedSource.Negative.packet,BoundedSource.Cubic.packet]
  unless (Codec.Json.arr packets).writeBytes == frozen.writeBytes do
    throw (IO.userError "bounded source proposals differ from frozen quotation inputs")
  descriptorError quadratic (-2) 2 .ambiguous
  descriptorError quadratic 2 3 .absent
  descriptorError (poly [0,1]) 0 1 .domain
  descriptorError quadratic 1 1 .domain
  descriptorError quadratic 2 (-2) .domain
  descriptorError (poly [0,0,1]) (-1) 1 .domain
  descriptorError (poly []) (-1) 1 .domain
  descriptorError (poly [1]) (-1) 1 .malformed
  for window in [poly [],margin {square with re := -square.re}] do
    match SourceBuild.buildOn quadratic window (.finite ⟨1⟩) (.finite ⟨2⟩) with
    | .error .unselected => pure ()
    | _ => throw (IO.userError "bounded source erased a zero/wrong-conjugate window")
  if let some path ← IO.getEnv "HEX_RCF_BOUNDED_SOURCE_OUTPUT" then
    IO.FS.writeBinFile path (Codec.Json.arr packets).writeBytes
  IO.println s!"bounded sources: {(Codec.Json.arr packets).writeBytes.size} frozen bytes; six scalar graphs; endpoint/equal/reversed/repeated/zero/constant/absent/ambiguous and wrong-conjugate refusals passed")
end Hex.RCF.BoundedSourceTests
