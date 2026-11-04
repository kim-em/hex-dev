/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner
import HexGroebner.F4Fixtures
import HexGroebner.SamplingConformance
import HexGroebner.Driver.Sampled

open Hex.Groebner

namespace Hex.Groebner.SampledConformance

private def canonical (field : PrimeField) (raw : RawPolynomial) : Certificate.Polynomial :=
  raw.foldl (fun f term => if term.coefficient == 0 then f else
    Hex.MvPoly.Kernel.addMod field.modulus.toNat f [(term.exponents.toList,term.coefficient.toNat)]) []

private def compare (a b : Sampled.Result) : Bool := match a,b with
  | .candidate a sa ra,.candidate b sb rb =>
    a.polynomials == b.polynomials && a.randomState == b.randomState && sa == sb && ra == rb &&
    a.initialRandom == b.initialRandom && a.config == b.config && a.minimumTargets == b.minimumTargets &&
    a.monomials == b.monomials && a.monomialBytes == b.monomialBytes
  | _,_ => false

private def scheduleBound (limits : Limits) : Nat :=
  64*(limits.work+limits.matrixRows+limits.rounds+1)

private def resumed (context : Context) (limits : Limits) (generators : Array RawPolynomial)
    (seed : Nat) : Sampled.Result := Id.run do
  let mut result := Sampled.computeWith context limits generators (Hex.Rand.ofSeed seed) {} 1
  for _ in [:scheduleBound limits] do
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
  for _ in [:scheduleBound limits] do
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

private def bounded (limits : Limits) (state : Sampled.State) : Bool :=
  let s := state.workspace.statistics
  s.work ≤ limits.work && s.allocatedBytes+state.workspace.table.bytes ≤ limits.packedBytes &&
  s.matrixRows ≤ limits.matrixRows && s.matrixEntries ≤ limits.matrixEntries &&
  s.pairs ≤ limits.pairs && s.rounds ≤ limits.rounds

private def sameValue (a b : Sampled.Result) : Bool := match a,b with
  | .candidate a _ ra,.candidate b _ rb =>
    a.polynomials == b.polynomials && a.randomState == b.randomState && ra == rb &&
    a.initialRandom == b.initialRandom && a.config == b.config && a.minimumTargets == b.minimumTargets
  | _,_ => false

/-- Cold admission covers every parent resource. Atomic F4 stages may repeat
work, so only values/random/sampling counts are equated across those retries. -/
private def coldBudgets (native : Bool) : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  let some c := (F4Fixtures.cases field)[4]? | return false
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let limits : Limits := { nativeRows := native }
  let expected := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 0)
  let cases : Array (F4Resource × Limits) := #[
    (.work,{ limits with work := 0 }),(.packedBytes,{ limits with packedBytes := 0 }),
    (.matrixRows,{ limits with matrixRows := 0 }),(.matrixEntries,{ limits with matrixEntries := 0 }),
    (.pairs,{ limits with pairs := 0 }),(.rounds,{ limits with rounds := 0 }),
    (.monomials,{ limits with monomials := 0 }),(.basis,{ limits with basis := 0 }),
    (.variables,{ limits with variables := 0 })]
  for (resource,cap) in cases do
    match Sampled.computeWith context cap c.generators (Hex.Rand.ofSeed 0) with
    | .exhausted actual stopped =>
      if actual != resource || !bounded cap stopped ||
          !sameValue expected (Sampled.resumeWith limits stopped) then return false
    | _ => return false
  return true

/-- Single-phase scheduling exposes parent translations at row submission,
scan and gather. Exact statistics are required for these resumable phases;
atomic prepare/finish retries instead retain their consumed prefixes. -/
private def warmBudgets (native : Bool) : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  let some c := (F4Fixtures.cases field)[4]? | return false
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let limits : Limits := { nativeRows := native }
  let expected := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 0)
  let mut result := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 0) {} 0
  let mut tested : Array Nat := #[]
  for _ in [:scheduleBound limits] do
    let .suspended state := result | break
    let stats := state.workspace.statistics
    let mut cases : Array (Nat × F4Resource × Limits × Bool) := #[]
    if let some round := state.pending then
      let matrix := round.matrix
      if matrix.phase == .draw && matrix.row == matrix.stop then
        cases := cases.push (0,.matrixRows,{ limits with matrixRows := stats.matrixRows },true)
        cases := cases.push (6,.matrixRows,{ limits with matrixRows := stats.matrixRows+1 },true)
      if matrix.phase == .scan then
        cases := cases.push (1,.work,{ limits with work := stats.work },true)
        cases := cases.push (7,.work,{ limits with work := stats.work+1 },true)
      if matrix.phase == .gather then
        cases := cases.push (2,.matrixEntries,{ limits with matrixEntries := stats.matrixEntries },true)
        cases := cases.push (3,.packedBytes,
          { limits with packedBytes := stats.allocatedBytes+state.workspace.table.bytes },true)
        let remaining := (Array.range (matrix.scan.last+1-matrix.gather.cursor)).foldl
          (fun n i => n+if Packed.read field.width matrix.gather.dense (matrix.gather.cursor+i) != 0 then 1 else 0) 0
        if remaining ≥ 2 then
          cases := cases.push (8,.matrixEntries,{ limits with matrixEntries := stats.matrixEntries+1 },true)
          cases := cases.push (9,.packedBytes,
            { limits with packedBytes := stats.allocatedBytes+state.workspace.table.bytes+4+field.width.bytes },true)
      if matrix.phase == .done && matrix.failure.isNone && !matrix.rows.isEmpty then
        cases := cases.push (4,.work,{ limits with work := stats.work+1 },false)
    else if state.checkpoint.phase == .pairs && !state.checkpoint.queue.heap.isEmpty then
      cases := cases.push (5,.work,{ limits with work := stats.work+1 },false)
    for (key,resource,cap,exact) in cases do
      if tested.contains key then continue
      let mut stopped := Sampled.resumeWith cap state 1 1
      for _ in [:scheduleBound limits] do
        match stopped with
        | .suspended next => stopped := Sampled.resumeWith cap next 1 1
        | _ => break
      match stopped with
      | .exhausted actual saved =>
        if actual != resource || !bounded cap saved then return false
        let completed := Sampled.resumeWith limits saved
        if !(if exact then compare expected completed else sameValue expected completed) then return false
        tested := tested.push key
      | _ => return false
    result := Sampled.resumeWith limits state 1 1
  return tested.size == 10 && compare expected result

private def forcedMiss : Bool := Id.run do
  let some field := Fixtures.fields[0]? | return false
  let some c := (F4Fixtures.cases field)[4]? | return false
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let .candidate candidate _ samples := Sampled.computeWith context {} c.generators
      (Hex.Rand.ofSeed 9) { blockRows := 1,zeroTests := 3 } | return false
  let .candidate expected _ := Hex.Groebner.computeWith context {} c.generators | return false
  if candidate.polynomials == expected.polynomials || samples.randomWords == 0 then return false
  if candidate.initialRandom != Hex.Rand.ofSeed 9 || candidate.config != { blockRows := 1,zeroTests := 3 } then
    return false
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
              stats.matrixEntries > limits.matrixEntries ||
              stats.allocatedBytes+candidate.monomialBytes > limits.packedBytes ||
              candidate.monomials > limits.monomials then
            throw (IO.userError s!"{c.name}: exceeded parent allowance")
          if candidate.randomState != 10987+samples.randomWords.toUInt64*0x9e3779b97f4a7c15 then
            throw (IO.userError s!"{c.name}: random state did not advance")
          if candidate.initialRandom != Hex.Rand.ofSeed 10987 || candidate.config != {} then
            throw (IO.userError s!"{c.name}: sampling policy provenance changed")
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

/-- A fresh complete F4 call for native ownership instrumentation. The digest
observes every output coefficient/exponent before the harness reads counters. -/
def fresh (seed : Nat) : Option UInt64 := do
  let field ← Fixtures.fields[6]?
  let c ← (F4Fixtures.cases field)[4]?
  let .candidate value stats samples := Sampled.computeWith
      ⟨field,c.variables,.grevlex⟩ {} c.generators (Hex.Rand.ofSeed seed) | none
  if samples.calls == 0 || samples.randomWords == 0 then none else
    some (hash (value.polynomials.map (fun p => p.map (fun t => (t.exponents,t.coefficient))),
      stats.work,samples.randomWords,value.randomState))

/-- A high cutoff uses no random words; mixed cutoffs retain the sealed policy
and advanced state across scheduling suspension and parent-work exhaustion. -/
def hybridChecks : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  for c in (F4Fixtures.cases field).extract 0 5 do
    let context : Context := ⟨field,c.variables,.grevlex⟩
    let limits : Limits := {}
    let .candidate expected expectedStats := Hex.Groebner.computeWith context limits c.generators | return false
    for cutoff in [0,1,8,1000000] do
      let direct := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 10987)
        (minimumTargets := cutoff)
      let .candidate candidate stats samples := direct | return false
      if candidate.polynomials != expected.polynomials || candidate.minimumTargets != cutoff then return false
      if cutoff == 1000000 && (samples.calls != 0 || samples.randomWords != 0 ||
          candidate.randomState != 10987 || stats != expectedStats) then return false
      let mut result := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 10987) {} 1 cutoff
      for _ in [:scheduleBound limits] do
        match result with
        | .suspended state =>
          if state.minimumTargets != cutoff then return false
          result := Sampled.resumeWith limits state 1
        | _ => break
      if !compare direct result then return false
      let stopped := Sampled.computeWith context { limits with work := 0 } c.generators
        (Hex.Rand.ofSeed 10987) (minimumTargets := cutoff)
      let .exhausted .work state := stopped | return false
      if state.minimumTargets != cutoff || state.random != Hex.Rand.ofSeed 10987 then return false
      if !sameValue direct (Sampled.resumeWith limits state) then return false
  return true

#guard hybridChecks

/-- Exhaust after symbolic selection, inside a deterministic matrix call.
Atomic retries retain the checkpoint and charge repeated
work, while the random generator and sampling statistics stay unchanged. -/
def hybridBudgets (native : Bool) : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  let some c := (F4Fixtures.cases field)[4]? | return false
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let limits : Limits := { nativeRows := native }
  let cutoff := 1000000
  let expected := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 10987)
    (minimumTargets := cutoff)
  let mut result := Sampled.computeWith context limits c.generators (Hex.Rand.ofSeed 10987) {} 1 cutoff
  for _ in [:1000] do
    let .suspended state := result | break
    if state.checkpoint.phase == .pairs && state.pending.isNone then
      let (prepared,workspace) := (Sampled.prepare context limits state.checkpoint
        state.random state.config cutoff).run state.workspace
      let .ok (_,none) := prepared | return false
      let start := state.workspace.statistics.work
      let stop := workspace.statistics.work
      for offset in [1:stop-start] do
        let cap := { limits with work := start+offset }
        if let .exhausted .work saved := Sampled.resumeWith cap state 1 then
          if saved.workspace.statistics.matrixCalls == state.workspace.statistics.matrixCalls then continue
          if saved.random != state.random || saved.statistics != state.statistics ||
              saved.minimumTargets != cutoff || saved.pending.isSome || !bounded cap saved ||
              saved.workspace.statistics.work <= start ||
              saved.checkpoint.phase != state.checkpoint.phase ||
              saved.checkpoint.basis.size != state.checkpoint.basis.size ||
              saved.checkpoint.queue.heap.size != state.checkpoint.queue.heap.size ||
              !sameValue expected (Sampled.resumeWith limits saved) then return false
          return true
    result := Sampled.resumeWith limits state 1
  return false

#guard hybridBudgets false
#guard hybridBudgets true

/-- Resume both kinds of batch after the other kind has already run. -/
private def mixedResume (context : Context) (generators : Array RawPolynomial)
    (cutoff : Nat) (native : Bool) : Bool := Id.run do
  let limits : Limits := { nativeRows := native }
  let expected := Sampled.computeWith context limits generators (Hex.Rand.ofSeed 10987)
    (minimumTargets := cutoff)
  let mut result := Sampled.computeWith context limits generators (Hex.Rand.ofSeed 10987) {} 1 cutoff
  let mut deterministic := false
  let mut stoppedDeterministic := false
  let mut stoppedSampled := false
  for _ in [:10000] do
    let .suspended state := result | break
    if state.pending.isNone && state.checkpoint.phase == .pairs then
      let (prepared,workspace) := (Sampled.prepare context limits state.checkpoint
        state.random state.config cutoff).run state.workspace
      if let .ok (_,none) := prepared then
        if workspace.statistics.matrixCalls > state.workspace.statistics.matrixCalls then
          deterministic := true
          if state.statistics.randomWords > 0 && !stoppedDeterministic then
            let cap := { limits with work := workspace.statistics.work-1 }
            let .exhausted .work saved := Sampled.resumeWith cap state 1 | return false
            if saved.random != state.random || saved.statistics != state.statistics ||
                saved.workspace.statistics.matrixCalls <= state.workspace.statistics.matrixCalls ||
                saved.checkpoint.phase != state.checkpoint.phase || saved.pending.isSome ||
                !bounded cap saved || !sameValue expected (Sampled.resumeWith limits saved) then return false
            stoppedDeterministic := true
    if let some round := state.pending then
      if deterministic && !stoppedSampled && round.matrix.phase == .scan then
        let cap := { limits with work := state.workspace.statistics.work }
        let mut stopped := Sampled.resumeWith cap state 1 1
        for _ in [:10000] do
          if let .suspended next := stopped then stopped := Sampled.resumeWith cap next 1 1 else break
        let .exhausted .work saved := stopped | return false
        if !bounded cap saved || !compare expected (Sampled.resumeWith limits saved) then return false
        stoppedSampled := true
    result := Sampled.resumeWith limits state 1 1
  return stoppedDeterministic && stoppedSampled && compare expected result

/-- At least one fixture must exercise both paths within the same run. -/
def hybridMixed : Bool := Id.run do
  let some field := Fixtures.fields[6]? | return false
  for c in (F4Fixtures.cases field).extract 9 27 do
    let context : Context := ⟨field,c.variables,.grevlex⟩
    let .candidate baseline _ allSamples := Sampled.computeWith context {} c.generators
      (Hex.Rand.ofSeed 10987) | return false
    for cutoff in [2,4,8] do
      let .candidate mixed _ samples := Sampled.computeWith context {} c.generators
        (Hex.Rand.ofSeed 10987) (minimumTargets := cutoff) | return false
      if samples.calls > 0 && samples.calls < allSamples.calls &&
          mixed.polynomials == baseline.polynomials &&
          mixedResume context c.generators cutoff false &&
          mixedResume context c.generators cutoff true then return true
  return false

#guard hybridMixed

def run : IO Unit := do
  if !hybridChecks then throw (IO.userError "hybrid sampling policy/resumption mismatch")
  if !(hybridBudgets false && hybridBudgets true && hybridMixed) then
    throw (IO.userError "hybrid deterministic-batch budgets/mixed policy mismatch")
  let some field := Fixtures.fields[6]? | throw (IO.userError "missing field")
  let some c := (F4Fixtures.cases field)[4]? | throw (IO.userError "missing system")
  let context : Context := ⟨field,c.variables,.grevlex⟩
  let completed ← Driver.Sampled.complete {}
    (Sampled.computeWith context {} c.generators (Hex.Rand.ofSeed 0) {} 0)
  if !compare completed (Sampled.computeWith context {} c.generators (Hex.Rand.ofSeed 0)) then
    throw (IO.userError "candidate driver did not continue a scheduling suspension")
  for native in #[false,true] do
    if !(SamplingChecks.miss native && SamplingChecks.totalZeros native &&
        SamplingChecks.resumeCombine native && SamplingChecks.resumeGather native &&
        SamplingChecks.resumeInverse native &&
        SamplingChecks.extendRange native &&
        SamplingChecks.resumeSlice native && SamplingChecks.resumeScan native &&
        SamplingChecks.resumeValidation native && SamplingChecks.resumeRows native) then
      throw (IO.userError "sampled matrix prefix/snapshot checks failed")
  if !SamplingChecks.corpus then throw (IO.userError "sampled row-space checks failed")
  if !SamplingChecks.inverseCounts then throw (IO.userError "inverse cost schedule disagrees")
  if !exhaustion then throw (IO.userError "advanced-state F4 exhaustion/resumption failed")
  for native in #[false,true] do
    if !(coldBudgets native && warmBudgets native) then
      throw (IO.userError "sampled parent budget translation/resumption failed")
  IO.println "sampled parent budgets: 9 initial resources, 10 partial cuts, native+scalar"
  if !forcedMiss then throw (IO.userError "forced rank miss was not independently rejected")
  IO.println "Sampled F4: forced rank miss rejected; exhausted advanced state resumes"
  corpus

end Hex.Groebner.SampledConformance
