/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner

namespace Hex.Groebner.SchedulingConformance
open Computation

private def field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩
private def context : Context := ⟨field,2,.grevlex⟩
private def generators : Array RawPolynomial := #[
  #[⟨#[2,0],1⟩,⟨#[0,1],6⟩], #[⟨#[1,1],1⟩,⟨#[0,0],6⟩]]
private def other : Scheduling → Scheduling
  | .degree => .sugar
  | .sugar => .degree

/-- Actual LCM degrees coincide while propagated sugars differ. Degree batching
retains both pairs, sugar batching separates them, and neither overwrites sugar. -/
private def batches : Bool := Id.run do
  for scheduling in [Scheduling.degree,.sugar] do
    let limits : Limits := { scheduling, gebauerMoller := false }
    let trial : Computation Bool := do
      let mut basis : Array BasisElement := #[]
      for (powers,sugar) in [(#[2,0],20),(#[1,1],2),(#[0,2],30)] do
        let polynomial ← Polynomial.normalize context limits 0 #[⟨powers,1⟩]
        basis := basis.push ⟨polynomial,sugar⟩
      let mut queue : PairQueue := {}
      for i in [:basis.size] do queue ← queue.install context limits basis i
      let index ← ReducerIndex.build context limits basis
      let (pairs,remaining) ← queue.select context limits index basis
      let expected := if scheduling == .degree then 2 else 1
      if pairs.size != expected || remaining.heap.size != 2-expected then return false
      if pairs[0]!.sugar != 21 then return false
      if scheduling == .degree && pairs[1]!.sugar != 31 then return false
      for pair in pairs do
        let degree := (← get).table.degree pair.lcm
        if degree != 3 || pair.priority != (if scheduling == .degree then degree else pair.sugar) then
          return false
      return true
    match trial.run ⟨{ arity := 2 },{}⟩ with
    | (.ok true,_) => pure ()
    | _ => return false
  return true

#guard batches

/-- Heap keys use arbitrary natural priorities and stable endpoint ties,
independently of sugar; saved queues keep their original contents. -/
private def heap : Bool := Id.run do
  let trial : Computation Bool := do
    let mut queue : PairQueue := {}
    queue ← queue.push {} ⟨0,2,0,1,2^80⟩
    queue ← queue.push {} ⟨1,2,0,0,2^81⟩
    queue ← queue.push {} ⟨0,1,0,100,2^80⟩
    let saved := queue
    for endpoints in [(0,1),(0,2),(1,2)] do
      let (some pair,next) ← queue.pop {} | return false
      if (pair.left,pair.right) != endpoints then return false
      queue := next
    return queue.heap.isEmpty && saved.heap.size == 3
  match trial.run ⟨{ arity := 0 },{}⟩ with
  | (.ok true,_) => return true
  | _ => return false

#guard heap

private def canonical (p : RawPolynomial) : Certificate.Polynomial :=
  p.foldl (fun result term => Hex.MvPoly.Kernel.addMod 7 result
    [(term.exponents.toList,term.coefficient.toNat)]) []

/-- Zero allowance exposes continuations before computation and certificate
preparation. Supplying a different policy on resume must retain the original. -/
private def resume : Bool := Id.run do
  for scheduling in [Scheduling.degree,.sugar] do
    let limits : Limits := { scheduling }
    let changed := { limits with scheduling := other scheduling }
    let .candidate expected _ := computeWith context limits generators 42 | return false
    let .exhausted .work state := computeWith context { limits with work := 0 } generators 42
      | return false
    if state.scheduling != scheduling then return false
    let .candidate actual _ := resumeWith changed state | return false
    if actual.scheduling != scheduling || actual.randomState != 42 ||
        actual.polynomials != expected.polynomials then return false
    let .exhausted .work traced := Producer.computeWith context { limits with work := 0 }
      1000000 generators | return false
    let .candidate produced _ := Producer.resumeWith changed 1000000 traced | return false
    if produced.history.scheduling != scheduling ||
        produced.polynomials != expected.polynomials.map canonical then return false
    if !Certificate.checkContainment 7 2 produced.generators produced.polynomials produced.forward then
      return false
    let budget : Producer.Budget := { computation := limits }
    let resumed : Producer.Budget := { computation := changed }
    let exhausted : Producer.Budget := { budget with computation := { limits with work := 0 } }
    let original := generators.map canonical
    let .certificateExhausted _ checked := basisWith context exhausted original | return false
    let .success accepted _ := Checked.resumeWith resumed checked | return false
    if accepted.history.scheduling != scheduling ||
        accepted.value.polynomials != produced.polynomials then return false
    let .certificateExhausted _ validation := Producer.certifyWith context exhausted generators
      produced.polynomials | return false
    let .success certified _ history := Producer.resumeBasisWith resumed validation | return false
    if history.scheduling != scheduling || certified.polynomials != produced.polynomials then return false
    let .certificateExhausted _ preparation := certifyWith context exhausted original
      produced.polynomials | return false
    let .success certified _ := Checked.resumeWith resumed preparation | return false
    if certified.history.scheduling != scheduling then return false
  return true

#guard resume

end Hex.Groebner.SchedulingConformance
