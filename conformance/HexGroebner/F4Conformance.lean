/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGroebner

/-!
Oracle: none (core); independent basis oracles consume the fixture emitter.
Mode: always.
Covered operations: raw normalization, packed polynomial arithmetic, symbolic
preprocessing, deterministic F4, normal forms, and cumulative-state resumption.
Covered properties: canonical zero/unit conventions, completed S-pair work,
monic sorted reduced output, scalar-preserving remainders and exhaustion.
Covered edge cases: zero variables, duplicate/zero generators, nonmonic inputs,
characteristic two, inhomogeneous and positive-dimensional systems, lex order,
and missing final S-pairs.
-/

namespace Hex.Groebner.F4Conformance

local instance : BEq (Except String (Array RawPolynomial)) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

private def field : PrimeField := ⟨7, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩
private def context : Context := ⟨field, 2, .grevlex⟩

private def input : Array RawPolynomial := #[
  #[⟨#[2, 0], 1⟩, ⟨#[0, 1], 6⟩],
  #[⟨#[1, 1], 1⟩, ⟨#[0, 0], 6⟩]]

private def result (context : Context) (input : Array RawPolynomial) :
    Except String (Array RawPolynomial) :=
  match computeWith context {} input with
  | .candidate candidate _ => .ok candidate.polynomials
  | .internal error _ => .error (reprStr error)
  | .invalid error _ => .error (reprStr error)
  | .exhausted resource _ => .error (reprStr resource)
  | .representation error _ => .error (reprStr error)

/-- info: Except.ok #[#[{ exponents := #[2, 0], coefficient := 1 }, { exponents := #[0, 1], coefficient := 6 }], #[{ exponents := #[1, 1], coefficient := 1 }, { exponents := #[0, 0], coefficient := 6 }], #[{ exponents := #[0, 2], coefficient := 1 }, { exponents := #[1, 0], coefficient := 6 }]] -/
#guard_msgs (whitespace := lax) in #eval result context input

#guard result context #[] == .ok #[]
#guard result context #[#[], #[]] == .ok #[]
#guard result ⟨field, 0, .lex⟩ #[#[⟨#[], 3⟩]] == .ok #[#[⟨#[], 1⟩]]
#guard result ⟨field, 0, .grevlex⟩ #[#[], #[]] == .ok #[]
#guard result context #[#[⟨#[0, 0], 2⟩], input[0]!] == .ok #[#[⟨#[0, 0], 1⟩]]
#guard result context (input ++ input ++ #[#[]]) == result context input
#guard result ⟨field, 2, .lex⟩ input == .ok #[
  #[⟨#[1, 0], 1⟩, ⟨#[0, 2], 6⟩],
  #[⟨#[0, 3], 1⟩, ⟨#[0, 0], 6⟩]]

#guard match computeWith context { rounds := 0 } input with
  | .exhausted .rounds state =>
    match resumeWith {} state with
    | .candidate candidate statistics =>
      .ok candidate.polynomials == result context input &&
        statistics.work ≥ state.workspace.statistics.work && statistics.rounds > 0
    | _ => false
  | _ => false

#guard match computeWith context { work := 50 } input with
  | .exhausted .work state =>
    match resumeWith {} state with
    | .candidate candidate statistics =>
      .ok candidate.polynomials == result context input && statistics.work > state.workspace.statistics.work
    | _ => false
  | _ => false

#guard match computeWith context { packedBytes := 0 } input with
  | .exhausted .packedBytes state =>
    state.workspace.statistics.work > 0 && state.workspace.statistics.work < 100000000 &&
    match resumeWith {} state with
    | .candidate candidate _ => .ok candidate.polynomials == result context input
    | _ => false
  | _ => false

#guard match computeWith context { monomials := 1 } input with
  | .exhausted .monomials state =>
    match resumeWith {} state with
    | .candidate candidate _ => .ok candidate.polynomials == result context input
    | _ => false
  | _ => false

#guard match computeWith context {} #[#[⟨#[1], 0⟩]] with
  | .invalid (.arity 0 0) _ => true
  | _ => false
#guard match computeWith context {} #[#[⟨#[1, 0], 7⟩]] with
  | .invalid (.coefficient 0 0) _ => true
  | _ => false

-- Matrix extraction must undo monic normalization for ordinary remainders.
#guard let calculation : Computation RawPolynomial := do
    let divisor ← Polynomial.normalize context {} 0 #[⟨#[1, 0], 1⟩, ⟨#[0, 0], 6⟩]
    let p ← Polynomial.normalize context {} 1 #[⟨#[2, 0], 3⟩, ⟨#[0, 1], 2⟩]
    let r ← Polynomial.remainder context {} #[⟨divisor, 1⟩] p
    return r.toRaw field (← get).table
  match calculation.run ⟨{ arity := 2 }, {}⟩ with
  | (.ok r, _) => r == #[⟨#[0, 1], 2⟩, ⟨#[0, 0], 3⟩]
  | _ => false

private def budgets : Bool := Id.run do
  let expected := result context input
  let agrees := fun candidate => .ok candidate.polynomials == expected && candidate.randomState == 37
  let resume := fun state => match resumeWith {} state with
    | .candidate candidate _ => agrees candidate
    | _ => false
  let boundaries : Array (Limits × F4Resource) := #[
    ({ work := 0 }, .work), ({ packedBytes := 0 }, .packedBytes),
    ({ monomials := 0 }, .monomials), ({ pairs := 0 }, .pairs),
    ({ rounds := 0 }, .rounds), ({ matrixEntries := 0 }, .matrixEntries),
    ({ matrixRows := 0 }, .matrixRows), ({ basis := 0 }, .basis),
    ({ variables := 0 }, .variables)]
  for (limits, resource) in boundaries do
    match computeWith context limits input 37 with
    | .exhausted r state => if r != resource || !resume state then return false
    | _ => return false
  let statistics := match computeWith context {} input 37 with
    | .candidate _ statistics => statistics
    | _ => {}
  let total := statistics.work
  if total == 0 then return false
  let mut failedRound := false
  -- Every work boundary includes failures after selection has popped pairs.
  for work in [:total + 1] do
    match computeWith context { work } input 37 with
    | .candidate candidate _ => if !agrees candidate then return false
    | .exhausted .work state =>
      failedRound := failedRound || (state.workspace.statistics.rounds > 0 &&
        state.checkpoint.phase == .pairs)
      if !resume state then return false
    | _ => return false
  for bytes in [:2000:23] do
    match computeWith context { packedBytes := bytes } input 37 with
    | .candidate candidate _ => if !agrees candidate then return false
    | .exhausted .packedBytes state => if !resume state then return false
    | _ => return false
  let campaigns : Array (F4Resource × Nat) := #[
    (.pairs, statistics.pairs), (.matrixRows, statistics.matrixRows),
    (.matrixEntries, statistics.matrixEntries), (.basis, 5), (.monomials, 12),
    (.rounds, statistics.rounds)]
  for (resource, maximum) in campaigns do
    let mut later := false
    for value in [:maximum + 1] do
      let limits : Limits := match resource with
        | .pairs => { pairs := value }
        | .matrixRows => { matrixRows := value }
        | .matrixEntries => { matrixEntries := value }
        | .basis => { basis := value }
        | .monomials => { monomials := value }
        | .rounds => { rounds := value }
        | _ => {}
      match computeWith context limits input 37 with
      | .candidate candidate _ => if !agrees candidate then return false
      | .exhausted r state =>
        if r != resource || !resume state then return false
        later := later || state.workspace.statistics.rounds > 0
      | _ => return false
    if !later then return false
  return failedRound

#guard budgets

-- Empty generators still consume work proportional to the outer input size.
#guard match computeWith context { work := 20 } (Array.replicate 100 #[]) with
  | .exhausted .work _ => true
  | _ => false

-- An ordinary importing client cannot replace the identity of a checkpoint.
#check_failure fun (s : ResumeState) => ({ s with context := context } : ResumeState)
#check_failure ResumeState.mk

-- Check ordering, multiplicity and structural persistence against an
-- independently sorted array, including equal sugars with different indices.
private def queueAgreement : Bool := Id.run do
  let calculation : Computation Bool := do
    let mut queue : PairQueue := {}
    let mut expected : Array (Nat × Nat × Nat) := #[]
    for i in [:300] do
      let pair : CriticalPair := ⟨i % 17, i, 0, (i * 37) % 23⟩
      queue ← queue.push {} pair
      expected := expected.push (pair.sugar, pair.left, pair.right)
    let saved := queue
    expected := expected.qsort (fun a b =>
      a.1 < b.1 || (a.1 == b.1 &&
        (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2))))
    for key in expected do
      let (pair, next) ← queue.pop {}
      queue := next
      match pair with
      | none => return false
      | some pair =>
        if (pair.sugar, pair.left, pair.right) != key then return false
    return queue.heap.isEmpty && saved.heap.size == 300 &&
      saved.heap.first?.any (fun p => (p.sugar, p.left, p.right) == expected[0]!)
  match calculation.run ⟨{ arity := 0 }, {}⟩ with
  | (.ok ok, _) => ok
  | _ => false

#guard queueAgreement

end Hex.Groebner.F4Conformance
