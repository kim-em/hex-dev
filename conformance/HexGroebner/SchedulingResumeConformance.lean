/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner

namespace Hex.Groebner.SchedulingResumeConformance

private def context : Context := ⟨⟨2, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩,3,.lex⟩
private def generators : Array RawPolynomial := #[
  #[⟨#[2,0,0],1⟩,⟨#[0,0,1],1⟩],
  #[⟨#[2,0,0],1⟩,⟨#[1,0,1],1⟩,⟨#[0,2,0],1⟩,⟨#[0,1,1],1⟩,
    ⟨#[1,0,0],1⟩,⟨#[0,1,0],1⟩,⟨#[0,0,1],1⟩],
  #[⟨#[2,0,0],1⟩,⟨#[1,0,1],1⟩,⟨#[0,1,1],1⟩]]
private def other : Scheduling → Scheduling
  | .degree => .sugar
  | .sugar => .degree

/-- Every work boundary compares actual resumed work and matrix counters, not
just the common reduced basis or a label copied from the original state. -/
private def checkpoints : Bool := Id.run do
  let .candidate _ degree := computeWith context { scheduling := .degree } generators | return false
  let .candidate _ sugar := computeWith context { scheduling := .sugar } generators | return false
  if degree == sugar then return false
  for scheduling in [Scheduling.degree,.sugar] do
    let limits : Limits := { scheduling }
    let .candidate _ total := computeWith context limits generators 42 | return false
    let mut queued := false
    let mut attempted := false
    for work in [:total.work+1] do
      match computeWith context { limits with work } generators 42 with
      | .candidate _ statistics => if statistics != total then return false
      | .exhausted .work state =>
        queued := queued || (state.checkpoint.phase == .pairs && !state.checkpoint.queue.heap.isEmpty)
        attempted := attempted || state.workspace.statistics.rounds > 0
        let .candidate control previous := resumeWith limits state | return false
        let .candidate actual statistics := resumeWith { limits with scheduling := other scheduling } state
          | return false
        if actual.polynomials != control.polynomials || statistics != previous ||
            actual.randomState != control.randomState || actual.scheduling != scheduling then return false
      | _ => return false
    if !queued || !attempted then return false
  return true

#guard checkpoints

/-- Traced resumption also preserves exact counters and shared derivations.
Both strategies must differ on the fresh run, and retain a queued checkpoint. -/
private def traced : Bool := Id.run do
  let .candidate _ degree := Producer.computeWith context { scheduling := .degree } 1000000 generators
    | return false
  let .candidate _ sugar := Producer.computeWith context { scheduling := .sugar } 1000000 generators
    | return false
  if degree == sugar then return false
  for scheduling in [Scheduling.degree,.sugar] do
    let limits : Limits := { scheduling }
    let .candidate _ total := Producer.computeWith context limits 1000000 generators | return false
    let mut queued := false
    let mut attempted := false
    for work in [:total.work+1] do
      match Producer.computeWith context { limits with work } 1000000 generators with
      | .candidate _ statistics => if statistics != total then return false
      | .exhausted .work state =>
        queued := queued || (state.checkpoint.phase == .pairs && !state.checkpoint.queue.heap.isEmpty)
        attempted := attempted || state.workspace.statistics.rounds > 0
        let .candidate control previous := Producer.resumeWith limits 1000000 state | return false
        let .candidate actual statistics := Producer.resumeWith
          { limits with scheduling := other scheduling } 1000000 state | return false
        if actual.polynomials != control.polynomials || actual.generators != control.generators ||
            actual.forward != control.forward || statistics != previous ||
            actual.history.scheduling != scheduling then return false
      | _ => return false
    if !queued || !attempted then return false
  return true

#guard traced

end Hex.Groebner.SchedulingResumeConformance
