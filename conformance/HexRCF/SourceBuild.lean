/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.SourceBuild
import HexRCF.RealCoefficients.SourceIdentity
import HexRealClosure.NumberFieldTower
import HexSignDet.Codec.Bytes
import HexRCF.EnumeratedSource.Positive
import HexRCF.EnumeratedSource.Negative
import HexRCF.EnumeratedSource.Cubic
import HexRCF.SelectedRoot.KernelCheck
import KernelReplay.AxiomClosure

/-! Native source proposals from enumerated roots, without a retained selected
root fixture. These are producer/serialization controls, not quoted real proofs. -/
namespace Hex.RCF.SourceBuildTests
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients

def registry : BaseContext.Registry := fun _ => none
abbrev base := Hex.RealClosure.NumberField.base registry
def poly (values : List Rat) : base.Poly :=
  DensePoly.ofCoeffs (values.toArray.map fun value => ⟨value⟩)

def margin (square : DyadicSquare) : base.Poly :=
  DensePoly.ofCoeffs ((SourceIdentity.margin square).coeffs.map fun value => ⟨value⟩)

-- The guard uses literal names to preserve proof-only import boundaries.
-- Check those names against actual declarations here, in the native driver.
open Lean in
run_meta do
  for name in #[``SourceBuild.build, ``SourceBuild.select, ``ScalarPacket.buildParts] do
    unless Hex.RCF.SelectedRootTests.KernelCheck.producers.contains name do
      throwError "source producer is missing from the kernel guard: {name}"
  let roots := #[``ScalarPacket.buildParts_success, ``ScalarPacket.build_success,
    ``SourceBuild.select_success, ``SourceBuild.select_checks,
    ``SourceBuild.build_success, ``SourceBuild.build_checked, ``SourceBuild.build_checks]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (fun name => [``propext, ``Classical.choice, ``Quot.sound].contains name) do
    throwError "enumerated source progress has inadmissible dependencies: {axioms}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  for name in roots do
    let .thmInfo info ← getConstInfo name | throwError "progress declaration is not a theorem: {name}"
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__sourceProgress}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let _ ← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "source progress audit retained copied declarations"
  logInfo m!"enumerated source progress: {roots.size} actual theorem bodies rechecked; full axioms={axioms}"

private def require (polynomial window : base.Poly) : IO (SourceBuild.Result base) := do
  match SourceBuild.build polynomial window with
  | .error error => throw (IO.userError s!"source production refused: {repr error}")
  | .ok result => return result

private def signAt (source : SourceBuild.Result base) (query : base.Poly) : IO Int := do
  let context := Algebraic.Context.adjoin source.root base.isClean
  let some result := ScalarPacket.buildParts context base.codec query
    | throw (IO.userError "source observation production failed")
  return result.sign

private def rejected (polynomial window : base.Poly) (ambiguous : Bool) : IO Unit := do
  match SourceBuild.build polynomial window with
  | .error .ambiguous => unless ambiguous do throw (IO.userError "unexpected ambiguity")
  | .error .unselected => if ambiguous then throw (IO.userError "lost ambiguous roots")
  | _ => throw (IO.userError "source selection did not preserve its refusal")

private def packet (source : SourceBuild.Result base) (proposal : ScalarPacket.Proposal) : IO Unit := do
  let literal := proposal.packet
  let .ok fields := Codec.tuple 3 literal | throw (IO.userError "invalid scalar packet layout")
  unless fields[0] == proposal.polynomial && fields[1] == Codec.Json.of proposal.sign &&
      fields[2] == proposal.evidence do throw (IO.userError "scalar packet fields changed")
  let .ok graph := Codec.readGraph base.codec Tower.Signature.codec base.signature
      source.root.raw.head source.root.raw.lower source.root.raw.upper proposal.evidence
    | throw (IO.userError "source graph did not decode")
  unless (graph.validate? base.sign base.signature source.root.raw.head
      source.root.raw.lower source.root.raw.upper).isSome do
    throw (IO.userError "source graph did not independently validate")

#eval (show IO Unit from do
  let quadratic := poly [-2,0,1]
  let square : DyadicSquare := ⟨Dyadic.ofInt 181 >>> (7 : Int),0,8⟩
  let positive ← require quadratic (margin square)
  let negative ← require quadratic (margin {square with re := -square.re})
  unless (← signAt positive (poly [0,1])) == 1 &&
      (← signAt negative (poly [0,1])) == -1 do
    throw (IO.userError "source selection confused real conjugates")
  let cubicSquare : DyadicSquare := ⟨Dyadic.ofInt 1290 >>> (10 : Int),0,12⟩
  let cubic ← require (poly [-2,0,0,1]) (margin cubicSquare)
  unless (← signAt cubic (poly [-1,1])) == 1 do
    throw (IO.userError "nonquadratic root lost its positive embedding")
  for source in [positive,negative,cubic] do
    packet source source.equation
    packet source source.enclosure
    unless source.equation.sign == 0 && source.enclosure.sign == 1 do
      throw (IO.userError "source proposal changed selected signs")
  rejected quadratic (poly [1]) true
  rejected quadratic (poly [-1]) false
  rejected quadratic (poly []) false
  match SourceBuild.select (poly [1]) (poly [1]) [positive.root] with
  | .error .equation => pure ()
  | _ => throw (IO.userError "source selection ignored a different equation")
  match SourceBuild.select quadratic (poly [1]) [positive.root,positive.root] with
  | .error .ambiguous => pure ()
  | _ => throw (IO.userError "duplicate proposed roots bypassed ambiguity")
  match SourceBuild.build (poly []) (poly [1]) with
  | .error (.roots _) => pure ()
  | _ => throw (IO.userError "invalid root input bypassed root production failure")
  let _ : Hashable base.Value := ⟨fun value => hash (base.codec.encode value)⟩
  let _ : Hashable Tower.Signature := ⟨fun value => hash (Tower.Signature.codec.encode value)⟩
  let packets := [positive,negative,cubic].toArray.map fun source =>
    Codec.Json.arr #[Codec.descriptor base.codec Tower.Signature.codec source.root.raw,
      Codec.graph base.codec Tower.Signature.codec (Dag.encode source.root.evidence),
      source.equation.packet,source.enclosure.packet]
  let frozen := Codec.Json.arr #[EnumeratedSource.Positive.packet,
    EnumeratedSource.Negative.packet,EnumeratedSource.Cubic.packet]
  unless (Codec.Json.arr packets).writeBytes == frozen.writeBytes do
    throw (IO.userError "enumerated-source proposals differ from frozen quotation inputs")
  if let some path ← IO.getEnv "HEX_RCF_ENUMERATED_SOURCE_OUTPUT" then
    IO.FS.writeBinFile path (Codec.Json.arr packets).writeBytes
  IO.println "source enumeration: positive/negative quadratic, cubic, six independent graph replays, ambiguous/empty/zero windows, wrong equation and duplicate-root refusals passed")

end Hex.RCF.SourceBuildTests
