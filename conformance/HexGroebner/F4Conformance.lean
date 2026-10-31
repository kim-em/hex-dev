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

#guard match computeWith context { work := 150 } input 37 with
  | .exhausted .work state =>
    match resumeWith { nativeRows := false } state with
    | .candidate candidate _ => .ok candidate.polynomials == result context input && candidate.randomState == 37
    | _ => false
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

private def budgets (context : Context) (input : Array RawPolynomial) : Bool := Id.run do
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

#guard budgets context input

#guard match computeWith { context with order := .lex } {} input with
  | .candidate _ stats => stats.gmPairs > 0
  | _ => false

#guard budgets { context with order := .lex } input

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

-- A flat exhaustive scan is independent of trie paths, masks and degree filters.
private def reducerLookup : Bool := Id.run do
  for variables in [0, 1, 3, 7] do
    let context : Context := ⟨field, variables, .grevlex⟩
    let limits : Limits := { work := 1000000000 }
    let trial : Computation Bool := do
      let boundaries : Array Nat := #[0, 1, 2, 3, 255, 256, 65535, 65536, 4294967295]
      let mut basis : Array BasisElement := #[⟨{}, 0⟩]
      for k in [:72] do
        let powers := (Array.range variables).map fun i => boundaries[((k % 18) / (i + 1) + i) % boundaries.size]!
        let mut raw : RawPolynomial := #[⟨powers, 1⟩]
        if k % 3 == 0 then raw := raw.push ⟨Array.replicate variables 0, 1⟩
        let p ← Polynomial.normalize context limits k raw
        basis := basis.push ⟨p, 0⟩
      let index ← ReducerIndex.build context limits basis
      for k in [:100] do
        let powers := (Array.range variables).map fun i => boundaries[(k / (i + 1) + 2 * i) % boundaries.size]!
        let monomial ← Computation.intern limits (powers.map Nat.toUInt64)
        let table := (← get).table
        let mut expected : Array Nat := #[]
        for i in [:basis.size] do
          let p := basis[i]!.polynomial
          if p.size == 0 then continue
          let leading := p.monomial 0
          let divides := (Array.range variables).all fun j => table.exponent leading j ≤ powers[j]!.toUInt64
          if !divides then continue
          let mut representative := true
          for j in [:basis.size] do
            let q := basis[j]!.polynomial
            if q.size != 0 && q.monomial 0 == leading &&
                (q.size < p.size || (q.size == p.size && j < i)) then
              representative := false
          if representative then expected := expected.push i
        let divisors ← index.divisors context limits monomial
        if divisors.size != expected.size || !expected.all divisors.contains then return false
        match ← index.find context limits basis monomial with
        | none => if !expected.isEmpty then return false
        | some i =>
          if !expected.contains i then return false
          let p := basis[i]!.polynomial
          for j in expected do
            let q := basis[j]!.polynomial
            if q.size < p.size || (q.size == p.size && table.degree (q.monomial 0) > table.degree (p.monomial 0)) then
              return false
      return true
    match trial.run ⟨{ arity := variables }, {}⟩ with
    | (.ok true, _) => pure ()
    | _ => return false
  return true

#guard reducerLookup

-- Pair-set regressions distinguish proper LCM dependencies from equality and
-- from completed zero reductions. They test the queue state itself, not just
-- monomial systems whose S-polynomials happen to vanish.
private def pairCriteria : Bool := Id.run do
  let context : Context := ⟨field, 2, .grevlex⟩
  let limits : Limits := {}
  let setup (powers : Array (Array Nat)) : Computation (Array BasisElement) := do
    let mut basis := #[]
    for i in [:powers.size] do
      let p ← Polynomial.normalize context limits i #[⟨powers[i]!, 1⟩]
      basis := basis.push ⟨p, 0⟩
    return basis
  let proper : Computation Bool := do
    let basis ← setup #[#[2, 1], #[1, 2], #[1, 1]]
    let index ← ReducerIndex.build context limits basis
    let lcm ← Computation.combine limits .lcm (basis[0]!.polynomial.monomial 0)
      (basis[1]!.polynomial.monomial 0)
    let pair : CriticalPair := ⟨0, 1, lcm, 0⟩
    let queue ← ({} : PairQueue).push limits pair
    if (← queue.chain context limits index basis pair) != .proper then return false
    if (← queue.chain context { limits with gebauerMoller := false } index basis pair) != .keep then return false
    let (selected, queue) ← queue.select context limits index basis
    return selected.isEmpty && queue.heap.isEmpty && !queue.resolved.contains (PairQueue.key 0 1)
  let equal : Computation Bool := do
    let basis ← setup #[#[2, 0], #[1, 1], #[0, 1]]
    let index ← ReducerIndex.build context limits basis
    let lcm ← Computation.combine limits .lcm (basis[0]!.polynomial.monomial 0)
      (basis[1]!.polynomial.monomial 0)
    let pair : CriticalPair := ⟨0, 1, lcm, 0⟩
    let queue ← ({} : PairQueue).install context limits basis 2
    if (← queue.chain context limits index basis pair) != .keep then return false
    let queue ← queue.resolve limits 1 2
    return (← queue.chain context limits index basis pair) == .resolved
  let product : Computation Bool := do
    let basis ← setup #[#[1, 1], #[0, 1], #[1, 0]]
    let queue ← ({} : PairQueue).install context limits basis 2
    let statistics := (← get).statistics
    return queue.heap.isEmpty && queue.resolved.contains (PairQueue.key 1 2) &&
      !queue.resolved.contains (PairQueue.key 0 2) && statistics.gmPairs == 1 && statistics.productPairs == 1
  let dominated : Computation Bool := do
    let basis ← setup #[#[2, 1], #[2, 0], #[1, 0], #[1, 1]]
    let queue ← ({} : PairQueue).install context limits basis 3
    return queue.heap.size == 1 && queue.heap.first?.any (fun p => p.left == 2 && p.right == 3) &&
      queue.resolved.isEmpty && (← get).statistics.gmPairs == 2
  let multiple : Computation Bool := do
    let basis ← setup #[#[2, 1], #[1, 2], #[1, 1], #[1, 0]]
    let mut queue : PairQueue := {}
    for new in [:basis.size] do queue ← queue.install context limits basis new
    if queue.heap.size != 4 then return false
    let index ← ReducerIndex.build context limits basis
    let (selected, remainder) ← queue.select context limits index basis
    return selected.size == 3 && remainder.heap.isEmpty && remainder.resolved.isEmpty &&
      (← get).statistics.gmPairs == 3
  for trial in [proper, equal, product, dominated, multiple] do
    match trial.run ⟨{ arity := 2 }, {}⟩ with
    | (.ok true, _) => pure ()
    | _ => return false
  return true

#guard pairCriteria

private def strategyResume : Bool := Id.run do
  let context := { context with order := TermOrder.lex }
  let expected := result context input
  let mut prunedCheckpoint := false
  for (strategy, batchInterreduce) in [(false, false), (false, true), (true, false), (true, true)] do
    let total := match computeWith context { gebauerMoller := strategy, batchInterreduce } input with
      | .candidate _ statistics => statistics.work
      | _ => 0
    if total == 0 then return false
    for work in [:total] do
      match computeWith context { work, gebauerMoller := strategy, batchInterreduce } input 37 with
      | .candidate candidate _ => if .ok candidate.polynomials != expected then return false
      | .exhausted .work state =>
        prunedCheckpoint := prunedCheckpoint || state.workspace.statistics.gmPairs > 0
        match resumeWith { gebauerMoller := !strategy, batchInterreduce := !batchInterreduce } state with
        | .candidate candidate statistics =>
          if .ok candidate.polynomials != expected || candidate.randomState != 37 ||
              statistics.work < state.workspace.statistics.work then return false
        | _ => return false
      | _ => return false
  return prunedCheckpoint

#guard strategyResume

private def monomialResume : Bool := Id.run do
  let expected := result context input
  for nativeMonomials in [false, true] do
    let total := match computeWith context { nativeMonomials } input with
      | .candidate _ statistics => statistics.work
      | _ => 0
    if total == 0 then return false
    for work in [:total] do
      match computeWith context { work, nativeMonomials } input 37 with
      | .candidate candidate _ => if .ok candidate.polynomials != expected then return false
      | .exhausted .work state =>
        match resumeWith { nativeMonomials := !nativeMonomials } state with
        | .candidate candidate statistics =>
          if .ok candidate.polynomials != expected || candidate.randomState != 37 ||
              statistics.work < state.workspace.statistics.work then return false
        | _ => return false
      | _ => return false
  return true

#guard monomialResume

private def sameOutcome (a b : ComputeResult) : Bool :=
  match a, b with
  | .candidate a sa, .candidate b sb => a.polynomials == b.polynomials && sa == sb
  | .exhausted a sa, .exhausted b sb => a == b &&
      sa.workspace.statistics == sb.workspace.statistics && sa.workspace.table.bytes == sb.workspace.table.bytes
  | .representation a sa, .representation b sb => a == b &&
      sa.workspace.statistics == sb.workspace.statistics && sa.workspace.table.bytes == sb.workspace.table.bytes
  | .invalid a sa, .invalid b sb => a == b && sa == sb
  | .internal a sa, .internal b sb => a == b && sa == sb
  | _, _ => false

private def monomialBudgets : Bool := Id.run do
  let expected := result context input
  let .candidate _ statistics := computeWith context {} input | return false
  let mut completedBytes := false
  let mut cachedCheckpoint := false
  for bytes in [:statistics.allocatedBytes + 4096] do
    let native := computeWith context { packedBytes := bytes } input 37
    let portable := computeWith context { packedBytes := bytes, nativeMonomials := false } input 37
    if !sameOutcome native portable then return false
    match native with
    | .candidate candidate _ =>
      if .ok candidate.polynomials != expected then return false
      completedBytes := true
      break
    | .exhausted .packedBytes state =>
      cachedCheckpoint := cachedCheckpoint || state.workspace.table.workspace.size > 0
    | _ => return false
    for (outcome, nativeMonomials) in [(native, false), (portable, true)] do
      let .exhausted .packedBytes state := outcome | return false
      match resumeWith { nativeMonomials } state with
      | .candidate candidate statistics =>
        if .ok candidate.polynomials != expected || candidate.randomState != 37 ||
            statistics.work < state.workspace.statistics.work then return false
      | _ => return false
  let mut completedCount := false
  for count in [:64] do
    let native := computeWith context { monomials := count } input 37
    let portable := computeWith context { monomials := count, nativeMonomials := false } input 37
    if !sameOutcome native portable then return false
    match native with
    | .candidate _ _ => completedCount := true; break
    | .exhausted .monomials _ => pure ()
    | _ => return false
    for (outcome, nativeMonomials) in [(native, false), (portable, true)] do
      let .exhausted .monomials state := outcome | return false
      match resumeWith { nativeMonomials } state with
      | .candidate candidate statistics =>
        if .ok candidate.polynomials != expected || candidate.randomState != 37 ||
            statistics.work < state.workspace.statistics.work then return false
      | _ => return false
  return completedBytes && completedCount && cachedCheckpoint

#guard monomialBudgets

private def largeBatch : Bool := Id.run do
  let field : PrimeField := ⟨65537, Hex.Nat.isPrimeTrial_isPrime (by decide), by decide⟩
  let context : Context := ⟨field, 5, .grevlex⟩
  let mut generators : Array RawPolynomial := #[]
  for degree in [2:7] do
    let mut polynomial : RawPolynomial := #[]
    for i in [:5] do
      polynomial := polynomial.push ⟨(Array.replicate 5 0).set! i degree,
        if i % 2 == 0 then 2 else field.modulus - 2⟩
    polynomial := polynomial.push ⟨Array.replicate 5 0, field.modulus - 1⟩
    generators := generators.push polynomial
  let .candidate actual statistics := computeWith context { work := 1000000000 } generators
    | return false
  let .candidate reference previous := computeWith context { work := 1000000000, batchSize := 64 } generators
    | return false
  return actual.polynomials == reference.polynomials && actual.polynomials.size == 38 &&
    statistics.rounds < previous.rounds && statistics.matrixEntries < previous.matrixEntries

#guard largeBatch

end Hex.Groebner.F4Conformance
