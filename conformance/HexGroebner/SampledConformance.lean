/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexGroebner.F4Fixtures
import HexGroebner.SamplingConformance

open Hex.Groebner

namespace Hex.Groebner.SampledConformance

private def canonical (field : PrimeField) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod field.modulus.toNat f [(term.exponents.toList,term.coefficient.toNat)]) []

private def compare (a b : Sampled.Result) : Bool := match a,b with
  | .candidate a sa ra,.candidate b sb rb =>
    a.polynomials == b.polynomials && a.randomState == b.randomState && sa == sb && ra == rb
  | _,_ => false

private def resumed (context : Context) (limits : Limits) (generators : Array RawPolynomial)
    (seed : Nat) : Sampled.Result := Id.run do
  let mut result := Sampled.computeWith context limits generators (Hex.Rand.ofSeed seed) {} 1
  for _ in [:10000] do
    match result with
    | .suspended state => result := Sampled.resumeWith limits state 1
    | _ => break
  return result

private def exhaustion : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  let some c := (F4Fixtures.cases field)[4]? | return false
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let limits : Limits := {}
  let complete := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 0)
  let mut result := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 0) {} 1
  for _ in [:1000] do
    match result with
    | .suspended state =>
      if state.statistics.randomWords > 0 then
        let cap := { limits with work := state.workspace.statistics.work }
        match Sampled.resumeWith cap state with
        | .exhausted .work stopped =>
          if stopped.random != state.random || stopped.statistics.randomWords != state.statistics.randomWords ||
              stopped.workspace.statistics.work > cap.work then return false
          let completed := Sampled.resumeWith limits stopped
          match complete,completed with
          | .candidate a _ ra,.candidate b _ rb =>
            return a.polynomials == b.polynomials && a.randomState == b.randomState && ra == rb
          | _,_ => return false
        | _ => return false
      result := Sampled.resumeWith limits state 1
    | _ => return false
  return false

private def forcedMiss : Bool := Id.run do
  let some field := Fixtures.fields[0]? | return false
  let some c := (F4Fixtures.cases field)[4]? | return false
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let .candidate candidate _ samples := Sampled.computeWith context {} c.generators
      (Hex.Rand.ofSeed 9) { blockRows := 1,zeroTests := 3 } | return false
  let .candidate expected _ := Hex.Groebner.computeWith context {} c.generators | return false
  if candidate.polynomials == expected.polynomials || samples.randomWords == 0 then return false
  match certifyWith context {} (c.generators.map (canonical field))
      (candidate.polynomials.map (canonical field)) with
  | .rejected _ => return true
  | _ => return false

private def corpus : IO Unit := do
  let mut profiles := 0
  let mut accepted := 0
  let mut rejected := 0
  for field in Fixtures.fields do
    for c in F4Fixtures.cases field do
      for order in #[TermOrder.lex,.grlex,.grevlex] do
        for scheduling in #[Scheduling.degree,.sugar] do
          let context : Context := ⟨field,c.variables,order⟩
          let limits : Limits := { scheduling }
          let direct := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 10987)
          let scalar := Sampled.computeWith context { limits with nativeRows := false,nativeMonomials := false }
            c.generators (Hex.Rand.ofSeed 10987)
          if !compare direct scalar then throw (IO.userError s!"{c.name}: native/scalar results differ")
          if !compare direct (resumed context limits c.generators 10987) then
            throw (IO.userError s!"{c.name}: suspended/direct results differ")
          let .candidate candidate stats samples := direct |
            throw (IO.userError s!"{c.name}: sampled computation failed")
          if stats.work > limits.work || stats.matrixRows > limits.matrixRows ||
              stats.matrixEntries > limits.matrixEntries || stats.allocatedBytes > limits.packedBytes then
            throw (IO.userError s!"{c.name}: exceeded parent allowance")
          if candidate.randomState != 10987+samples.randomWords.toUInt64*0x9e3779b97f4a7c15 then
            throw (IO.userError s!"{c.name}: random state did not advance")
          let .candidate reference _ := Hex.Groebner.computeWith context limits c.generators |
            throw (IO.userError s!"{c.name}: deterministic reference failed")
          let equal := candidate.polynomials == reference.polynomials
          match certifyWith context { computation := limits } (c.generators.map (canonical field))
              (candidate.polynomials.map (canonical field)) with
          | .success _ _ =>
            if !equal then throw (IO.userError s!"{c.name}: distinct accepted reduced bases")
            accepted := accepted+1
          | .rejected _ =>
            if equal then throw (IO.userError s!"{c.name}: rejected reference basis")
            rejected := rejected+1
          | _ => throw (IO.userError s!"{c.name}: certification did not finish")
          profiles := profiles+1
  IO.println s!"Sampled F4: {profiles} native/scalar/direct/resumed comparisons, {accepted} certified bases, {rejected} independently rejected misses"

def run : IO Unit := do
  for native in #[false,true] do
    if !(SamplingChecks.miss native && SamplingChecks.totalZeros native &&
        SamplingChecks.resumeCombine native && SamplingChecks.resumeGather native &&
        SamplingChecks.resumeSlice native && SamplingChecks.resumeScan native &&
        SamplingChecks.resumeValidation native && SamplingChecks.resumeRows native) then
      throw (IO.userError "sampled matrix prefix/snapshot checks failed")
  if !SamplingChecks.corpus then throw (IO.userError "sampled row-space checks failed")
  if !exhaustion then throw (IO.userError "advanced-state F4 exhaustion/resumption failed")
  if !forcedMiss then throw (IO.userError "forced rank miss was not independently rejected")
  IO.println "Sampled F4: forced rank miss rejected; exhausted advanced state resumes"
  corpus

end Hex.Groebner.SampledConformance
