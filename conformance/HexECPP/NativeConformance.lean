/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Search

/-! Arithmetic proposals, exceptional twist families, shared allocation
exhaustion and native subject binding. Composite failures carry no verdict. -/

open Hex.ECPP

#guard CM.symbol 2 13 == -1
#guard CM.symbol 2 17 == 1
#guard CM.symbol 5 25 == 0
#guard CM.rootValid 35 1 34
#guard !CM.rootValid 35 2 6
#guard !CM.normValid 13 3 1 1
#guard CM.normValid 13 3 7 1
#guard CM.sqrt? 13 2 10 == some 7 || CM.sqrt? 13 2 10 == some 6
#guard CM.norm? 13 3 6 == some (5, 3)
#guard CM.norm? 11 7 2 == some (4, 2)
#guard CM.norm? 47 11 6 == some (12, 2)
#guard (CM.curves 13 ⟨3, 0⟩ 2).length == 6
#guard (CM.curves 17 ⟨4, 1728⟩ 3).length == 4
#guard (CM.curves 101 ⟨7, -3375⟩ 2).length == 2
#guard (CM.traces 3 7 1).length == 6
#guard (CM.traces 4 4 3).length == 4
#guard (inverse? 35 15).isNone
#guard CM.curves 35 ⟨7, -3375⟩ 2 == []

private def cardinality (n a b : Nat) : Nat :=
  1 + ((List.range n).map fun x =>
    ((List.range n).filter (onCurve n a b x)).length).sum

private def orders (n d : Nat) (j : Int) (g : Nat) : List Nat :=
  ((CM.curves n ⟨d, j⟩ g).map fun (a, b) => cardinality n a b).mergeSort (· ≤ ·)

private def expected (n d t v : Nat) : List Nat :=
  ((CM.traces d t v).map fun t => ((n : Int) + 1 - t).toNat).mergeSort (· ≤ ·)

#guard orders 13 3 0 2 == expected 13 3 5 3
#guard orders 17 4 1728 3 == expected 17 4 8 1
#guard orders 11 7 (-3375) 2 == expected 11 7 4 2

-- Every successful root is checked, even for nonsquarefree inputs.
#guard ([9, 25, 35, 49, 101, 113].all fun n => (List.range n).all fun a =>
  (CM.sqrt? n 2 a).all (CM.rootValid n a))

private def exhausted (n : Nat) (b : SearchBudget) (r : Resource) : Bool :=
  match (produce n 0 b).result with
  | .error e => e.resource == r
  | .ok _ => false

#guard exhausted 2 { maxBits := 0 } .inputBits
#guard exhausted 2 { maxDepth := 0 } .depth
#guard exhausted 2 { maxFactorWork := 0 } .factorWork
#guard exhausted 2 { maxOutputBits := 0 } .outputBits
#guard exhausted 2 { maxMemo := 0 } .memo

private def hard : Nat := 177080666831933235355717939809840315427
#guard exhausted hard { maxCandidates := 0 } .candidates
#guard exhausted hard { maxRoots := 0 } .roots
#guard exhausted hard { maxNonresidues := 0 } .nonresidues
#guard exhausted hard { maxPoints := 0 } .points
#guard exhausted hard { maxScalarWork := 0 } .scalarWork
#guard exhausted hard { maxDepth := 1 } .depth
#guard exhausted hard { nonresidueRetries := 0 } .nonresidueRetries
#guard exhausted hard { pointRetries := 0 } .portfolio
-- No local point allowance still traverses later orders and twists.
#guard (produce hard 0 { pointRetries := 0 }).state.stats.candidates > 9
#guard exhausted hard { pointRetries := 0, maxCandidates := 9 } .candidates
#guard exhausted 9 {} .screening

#guard ([0, 1, 4, 9, 25, 35, 49, 121, 100003 * 100003].all fun n =>
  (produce n 0).result.toOption.isNone)
#guard (produce 17 0).result.toOption.any (checkAt 17)
#guard (produce hard 0).result.toOption.any (checkAt hard)
#guard !(produce hard 0).result.toOption.any (checkAt (hard + 2))
#guard (produce hard 0).state.rand == (produce hard 0).state.rand
#guard (produce hard 0).state.stats.scalarWork > 0

-- A failed recursive branch is charged and later candidates can still succeed.
private def shallow := produce hard 0 { maxDepth := 3 }
#guard shallow.result.toOption.any (checkAt hard)
#guard shallow.state.stats.backtracks > 0

-- Positive point work can reject every twist without exhausting a shared cap.
-- The completed portfolio, rather than an earlier rejected twist, is the cause.
private def rejected := produce hard 17 { pointRetries := 1 }
#guard rejected.state.stats.points > 0
#guard match rejected.result with
  | .error e => e.resource == .portfolio
  | .ok _ => false

-- A child's local nonresidue failure supersedes the parent's local retry and
-- survives a later ancestor failure. All calls share the same state.
private def childRetry : Option SearchError :=
  let b : SearchBudget := { nonresidueRetries := 0 }
  let action : SearchM (Option Cert) := do
    let _ ← search b b.maxDepth hard
    search b 0 (hard + 2)
  let (_, state) := action.run.run {
    rand := Hex.Rand.ofSeed 0,
    stats := { unresolved := some ⟨hard + 2, .pointRetries⟩ } }
  state.stats.unresolved
#guard childRetry.any fun e => e.subject == hard && e.resource == .nonresidueRetries

-- The exposed stateful search can reuse a success without any new work.
private def memoReplay : Bool :=
  let action : SearchM Bool := do
    let first ← search {} 32 17
    let before ← get
    let second ← search {} 32 17
    let after ← get
    pure (first.any (checkAt 17) && second.any (checkAt 17) &&
      before.stats.factorWork == after.stats.factorWork && before.rand == after.rand)
  let (result, _) := action.run.run { rand := Hex.Rand.ofSeed 0 }
  result.toOption.getD false
#guard memoReplay
#guard primeBits 0 (.small 2) == none
#guard primeBits 1 (.small 2) == some 3
#guard primeBits 1 (.pock 13 [(2, 0, .small 2)]) == none

-- Complete portfolio exhaustion retains the distinct local retry diagnostic.
#guard let result := Hex.ECPP.produce hard 0 { pointRetries := 0 }
  result.state.stats.lastRetry.any (fun e => e.resource == .pointRetries)

-- Stop after the first failed twist, before any child call. This proves the
-- parent retry precedes the child, exercising diagnostic replacement.
private def beforeChild := produce hard 0
  { maxDepth := 1, maxCandidates := 2, maxPoints := 8 }
#guard beforeChild.state.stats.backtracks == 0
#guard beforeChild.state.stats.unresolved.any fun e =>
  e.subject == hard && e.resource == .pointRetries

-- The first real CM order rejects a twist before its first recursive child
-- fails at depth zero. Capping at two candidates stops before the next order.
-- The fresh state has no planted diagnosis; the child supersedes that retry.
private def firstChild := produce hard 0 { maxDepth := 1, maxCandidates := 2 }
#guard firstChild.state.stats.backtracks == 1
#guard firstChild.state.stats.points > 8
#guard firstChild.state.stats.lastRetry.any fun e =>
  e.subject == hard && e.resource == .pointRetries
#guard firstChild.state.stats.unresolved.any fun e =>
  e.subject < hard && e.resource == .depth
-- Completing the parent's portfolio retains that unresolved child.
#guard match (produce hard 0 { maxDepth := 1 }).result with
  | .error e => e.subject < hard && e.resource == .depth
  | .ok _ => false

-- The added root portfolio agrees with exhaustive roots on small prime fields.
private def rootOracle (n : Nat) : Bool :=
  let z := ((List.range n).find? fun z => CM.symbol z n == -1).getD 0
  CM.classPolynomials.all fun p =>
    (CM.roots? n z p).mergeSort (· ≤ ·) ==
      ((List.range n).filter fun x => CM.evaluate n x p.coefficients == 0)
#guard [17, 31, 41, 101, 113].all rootOracle
-- Composite root proposals still satisfy the actual polynomial equation.
#guard [9, 25, 35, 49, 121].all fun n => CM.classPolynomials.all fun p =>
  (CM.roots? n 2 p).all fun x => x < n && CM.evaluate n x p.coefficients == 0
#guard CM.roots? 31 3 ⟨15, [-121287375, 191025, 1]⟩ == [11, 17]
#guard [11, 17].all fun j => orders 31 15 j 3 == expected 31 15 8 2
#guard CM.roots? 35 2 ⟨15, [1, 1, 2]⟩ == []
#guard CM.classPolynomials.length == 33
#guard CM.classPolynomials.all fun p => p.coefficients.length ≤ 3
#guard certShape 1 (.base (.small 17)) == some (0, 2, 1)
#guard certShape 0 (.base (.small 17)) == none
#guard certBitsAt 1 (.base (.pock 13 [(2, 0, .small 2)])) == none
#guard (certBitsAt 2 (.base (.pock 13 [(2, 0, .small 2)]))).isSome

-- Rejection of an oversized terminal retains charged work and permits search.
private def tinyOutput := produce 17 0 { public512Budget with maxNodes := some 1 }
#guard tinyOutput.result.toOption.isNone
#guard tinyOutput.state.stats.outputRejects > 0
#guard tinyOutput.state.stats.factorWork ≥ leafBudget.maxAttempts
#guard exhausted 17 { maxNodes := some 1 } .nodes
#guard (produce 17 0 { public512Budget with maxRows := some 0 }).result.toOption.any (checkAt 17)
#guard exhausted hard { native512Budget with maxPolynomialWork := 0 } .polynomialWork
#guard exhausted hard { native512Budget with maxRootWork := 0 } .rootWork
#guard exhausted hard { order := some { orderBudget with attemptLimit := none } } .factorPolicy

-- A checked memo cannot bypass tighter remaining output or recursion limits.
private def limitedMemo (depth : Nat) (rows nodes : Option Nat) : Bool :=
  match (produce hard 0).result with
  | .error _ => false
  | .ok c =>
      let budget := { public512Budget with
        maxDepth := depth, maxRows := rows, maxNodes := nodes, maxFactorWork := 0 }
      let (result, _) := (search budget depth hard).run.run {
        rand := Hex.Rand.ofSeed 0, memo := [c] }
      match result with
      | .error e => e.resource == .factorWork
      | .ok _ => false
#guard limitedMemo 21 (some 0) (some 32)
#guard limitedMemo 21 (some 20) (some 1)
#guard limitedMemo 1 (some 20) (some 32)
