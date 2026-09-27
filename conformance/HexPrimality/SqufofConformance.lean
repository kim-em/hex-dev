/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.Squfof

open Hex.Nat.Squfof

private def tiny : Limits := { multipliers := 1, steps := 25, queueCapacity := 128 }

private structure Trace where
  form : Form
  queue : List Pair

-- Test-only transition inspection uses the exported exact arithmetic helpers;
-- it records the queue before a square-form match and carries its retired tail.
private def forwardStep (k S L : Nat) (state : Trace) : Option (Trace × Trace) := do
  let f := state.form
  if f.q = 0 then none else
  let b := (S + f.p) / f.q
  let g := f.q / Nat.gcd f.q (2 * k)
  let queue := if g ≤ L then state.queue ++ [(g, f.p % g)] else state.queue
  let next ← nextForm f b ((b : Int) * (f.q : Int) - (f.p : Int))
  let before := ⟨next, queue⟩
  let r := Nat.sqrt next.q
  let after := if r * r = next.q && r > 1 then
    ⟨next, (afterMatch queue r next.p).getD queue⟩ else before
  return (before, after)

private def forwardView (n k count : Nat) : Option (Trace × Trace) := Id.run do
  let M := k * n
  let D := if M % 4 = 1 then 2 * M else M
  let S := Nat.sqrt D
  let L := Nat.sqrt (Nat.sqrt (4 * D))
  let mut state : Trace := ⟨⟨1, S, D - S * S⟩, []⟩
  for _ in [0:count - 1] do
    match forwardStep k S L state with
    | none => return none
    | some (_, after) => state := after
  return forwardStep k S L state

private def reverseAfter (S count : Nat) (initial : Form) : Option Form := Id.run do
  let mut form := initial
  for _ in [0:count] do
    if form.q = 0 then return none
    let b := (S + form.p) / form.q
    match nextForm form b ((b : Int) * (form.q : Int) - (form.p : Int)) with
    | none => return none
    | some next => form := next
  return some form

private def invariant (D S : Nat) (f : Form) : Bool :=
  f.qprev > 0 && f.q > 0 && f.p ≤ S && D == f.p * f.p + f.qprev * f.q

#guard ([0, 1, 2, 3] : List Nat).all fun n =>
  factor n == ⟨.noFactor, 0, 0, 0⟩
#guard factor 4 { multipliers := 0, steps := 0, queueCapacity := 0 } ==
  ⟨.factor 2, 0, 0, 0⟩
#guard factor 49 { multipliers := 0, steps := 0, queueCapacity := 0 } ==
  ⟨.factor 7, 0, 0, 0⟩
#guard factor (2 ^ 64) == ⟨.unsupported, 0, 0, 0⟩
#guard factor (2 ^ 64 + 1) == ⟨.unsupported, 0, 0, 0⟩
#guard factor (2 ^ 64 + 2) == ⟨.unsupported, 0, 0, 0⟩
#guard (factor (2 ^ 64 - 1) { steps := 0 }).outcome == .exhausted
#guard factor 15 { multipliers := 0 } == ⟨.exhausted, 0, 0, 0⟩
#guard factor 15 { steps := 0 } == ⟨.exhausted, 0, 0, 0⟩

-- Gower--Wagstaff parity and reverse extraction: 17 forward plus 8 reverse.
#guard (runMultiplier 22117019 1 {}).divisor.map (·.val) == some 4451
#guard (runMultiplier 22117019 1 {}).forwardSteps == 17
#guard (runMultiplier 22117019 1 {}).reverseSteps == 8
#guard (runMultiplier 22117019 1 {}).steps == 25
#guard invariant 22117019 4702 ⟨1, 4702, 8215⟩
#guard (forwardView 22117019 1 17).map (·.1.form) == some ⟨6314, 1737, 3025⟩
#guard (forwardView 22117019 1 17).map (invariant 22117019 4702 ∘ (·.1.form)) == some true
#guard reverseForm 22117019 4702 ⟨6314, 1737, 3025⟩ 55 ==
  some ⟨55, 4652, 8653⟩
#guard (reverseAfter 4702 7 ⟨55, 4652, 8653⟩).map (fun f => (f.p, f.q)) ==
  some (4451, 4451)
#guard (reverseAfter 4702 7 ⟨55, 4652, 8653⟩).map (invariant 22117019 4702) == some true
#guard (List.range 17).all fun i =>
  ((forwardView 22117019 1 (i + 1)).map (fun x =>
    invariant 22117019 4702 x.1.form && x.1.queue.length ≤ 128)).getD false
#guard (List.range 8).all fun i =>
  ((reverseAfter 4702 i ⟨55, 4652, 8653⟩).map (invariant 22117019 4702)).getD false
#guard (runMultiplier 22117019 1 { steps := 17 }).stop == .exhausted
#guard (runMultiplier 22117019 1 { steps := 17 }).steps == 17
#guard (runMultiplier 22117019 1 { steps := 24 }).stop == .exhausted
#guard (runMultiplier 22117019 1 { steps := 24 }).reverseSteps == 7
#guard factor 22117019 tiny == ⟨.factor 4451, 1, 25, 0⟩

-- FIFO prefix removal, including a match behind another queued form.
#guard (afterMatch [(3, 2), (23, 17)] 3 305) == some [(23, 17)]
#guard (afterMatch [(23, 17), (9, 8)] 9 242) == some []
#guard (forwardView 247 385 3).map (fun x => (x.1.form, x.1.queue, x.2.queue)) ==
  some (⟨230, 305, 9⟩, [(3, 2), (23, 17)], [(23, 17)])
#guard (forwardView 247 385 9).map (fun x => (x.1.form, x.1.queue, x.2.queue)) ==
  some (⟨451, 242, 81⟩, [(23, 17), (9, 8)], [])
#guard (runMultiplier 247 385 {}).divisor.map (·.val) == some 13
#guard (runMultiplier 247 385 {}).forwardSteps == 13
#guard (runMultiplier 247 385 {}).reverseSteps == 8
#guard (runMultiplier 247 385 {}).peakQueue == 2
#guard (runMultiplier 247 385 { steps := 5, queueCapacity := 0 }).stop == .queueFull
#guard (runMultiplier 247 385 { steps := 5, queueCapacity := 0 }).steps == 1
#guard (runMultiplier 247 385 { steps := 5, queueCapacity := 1 }).stop == .queueFull
#guard (runMultiplier 247 385 { steps := 5, queueCapacity := 1 }).peakQueue == 1

-- Rejected whole-input reverse gcd resumes the saved forward form.
#guard (forwardView 5 7 1).map (·.1.form) == some ⟨10, 5, 1⟩
#guard reverseForm 35 5 ⟨10, 5, 1⟩ 1 == some ⟨1, 5, 10⟩
#guard Nat.gcd 10 5 == 5
#guard (runMultiplier 5 7 {}).divisor.isNone
#guard (runMultiplier 5 7 {}).stop == .repeated
#guard (runMultiplier 5 7 {}).steps == 4

-- A one-step repeated cycle still permits progress by the next multiplier.
#guard (forwardView 633003781 1 1).map (·.1.queue) == some [(1, 0)]
#guard (runMultiplier 633003781 1 {}).stop == .repeated
#guard (runMultiplier 633003781 1 {}).steps == 1
#guard (runMultiplier 633003781 3 {}).divisor.map (·.val) == some 8821
#guard (runMultiplier 633003781 3 {}).forwardSteps == 181
#guard (runMultiplier 633003781 3 {}).reverseSteps == 96
#guard (factor 633003781 { multipliers := 2, steps := 277 }).outcome == .factor 8821
#guard (factor 633003781 { multipliers := 2, steps := 277 }).steps == 278
#guard factor 633003781 { multipliers := 1 } == ⟨.exhausted, 1, 1, 1⟩

#guard (runMultiplier 21 3 {}).divisor.map (·.val) == some 3
#guard (runMultiplier 3 3 {}).stop == .skipped
#guard (runMultiplier 231 21 {}).divisor.map (·.val) == some 21
#guard (runMultiplier 18446744073709551557 1155 { steps := 1 }).steps == 1

-- Negative signed differences and inexact reverse divisions fail explicitly.
#guard nextForm ⟨1, 10, 3⟩ 1 (-7) == none
#guard nextForm ⟨1, 10, 3⟩ 2 20 == none
#guard reverseForm 20 4 ⟨1, 3, 2⟩ 3 == none

-- Public result bounds, deterministic replay, and the independent divisor gate.
private def sound (n : Nat) (l : Limits) : Bool :=
  let r := factor n l
  r == factor n l && r.attempts ≤ min l.multipliers 16 &&
  r.steps ≤ r.attempts * l.steps && r.peakQueue ≤ l.queueCapacity &&
  match r.outcome with
  | .factor d => 1 < d && d < n && n % d == 0
  | _ => true

#guard ([5, 7, 9, 15, 27, 81, 247, 22117019, 633003781,
    2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1] : List Nat).all fun n =>
  ([{ multipliers := 0 }, { steps := 0 }, tiny] : List Limits).all (sound n)
