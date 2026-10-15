/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.FiniteBatch
public meta import Lean.Meta.Eval

public meta section

register_option Hex.RealClosure.batchLookups : Bool := {
  defValue := true
  descr := "prepare checked native lookups in bounded batches before dependency discovery"
}

namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData.NativeBatch
open Lean Meta

private def unavailable (environment : Environment) (name : Name) : Bool :=
  if environment.isImportedConst name then false
  else match environment.find? name with
    | some (.defnInfo _) => (IR.findEnvDecl environment name).isNone
    | _ => false

/-- Obtain advisory bits for the original closed lookup computations in one
native call. Native execution supplies no proof object. -/
private unsafe def hints (lookups : Array Lookup) : MetaM (Array Bool) := do
  let inputs := lookups.toList.map fun lookup => lookup.leaf.type.getAppArgs[1]!
  let program ← mkArrayLit (mkConst ``Bool) inputs
  evalExpr (Array Bool) (← inferType program) program (checkMeta := false)

/-- Prepare one discovery frontier, checking all suggested successes with the
ordinary kernel. Missing keys remain available to the original decider and
record supplier. No interpretation or real coordinate is chosen here. -/
unsafe def prepare (leaves : Array Leaf) : MetaM (Array KnownLookup) := do
  let candidates ← batchCandidates leaves
  let environment ← getEnv
  let lookups := candidates.filter fun lookup =>
    !lookup.leaf.type.getAppArgs[1]!.getUsedConstants.any (unavailable environment ·)
  let mut result := #[]
  let mut hintCost := 0
  let mut proofCost := 0
  let mut missed := 0
  let mut chunks := 0
  for group in [: (lookups.size + lookupBatchSize - 1) / lookupBatchSize] do
    let start := group * lookupBatchSize
    let chunk := lookups.extract start (min (start + lookupBatchSize) lookups.size)
    let began ← IO.getNumHeartbeats
    let accepted? ← try
      pure (some (← hints chunk))
    catch error =>
      -- Only unavailable executable code is a missed optimization.
      -- Kernel failures, resource limits and unrelated errors propagate.
      if let .error _ message := error then
        if message.stripNestedTags.kind == kindOfErrorName `lean.dependsOnNoncomputable then
          pure none
        else throw error
      else throw error
    let hinted ← IO.getNumHeartbeats
    hintCost := hintCost + hinted - began
    chunks := chunks + 1
    let some accepted := accepted? | do
      missed := missed + chunk.size
      continue
    let checked ← checkLookupBatch chunk accepted
    result := result ++ checked
    proofCost := proofCost + (← IO.getNumHeartbeats) - hinted
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"lookup batch: leaves={leaves.size} candidates={candidates.size} executable={lookups.size} unavailable={candidates.size-lookups.size} failedHints={missed} chunks={chunks} accepted={result.size} hintHB={hintCost/1000} proofHB={proofCost/1000}"
      handle.flush
  return result

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData.NativeBatch
