/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality

open Hex.Nat

private def event (name : String) : FactorEvent := .route name []

private def previous (attempts : Nat) : Construction.Failure :=
  { stop := .exhausted, attempts := attempts, rand := Hex.Rand.ofSeed 19, events := [event "first"] }

private def provider : FactorSearch := fun allocation n r =>
  if allocation.attemptLimit.getD 0 == 0 then ⟨⟨[], n⟩, r, 0, []⟩ else
    ⟨⟨[(2, 1), (3, 1), (166667, 1)], 1⟩, r.next.2, 1,
      [.route "retry" [("allowance", toString allocation.attemptLimit.get!),
        ("seed", toString r.state)]]⟩

-- Exactly three attempts remain: one factor call and two recursive witnesses.
#guard (match Construction.retry 1000003 constructionBudget (previous 1021) provider with
  | .ok s => s.attempts == 1024 && s.rand == (Hex.Rand.ofSeed 19).next.2 &&
      s.events == [event "first", .route "retry" [("allowance", "3"), ("seed", "19")]] &&
      s.cert.raw.subject == 1000003 && checkPrime s.cert.raw
  | .error _ => false)

-- With two attempts left the child can succeed, but its parent's witness cannot.
#guard (match Construction.retry 1000003 constructionBudget (previous 1022) provider with
  | .error f => f.attempts == 1024 && f.obligation == some 1000003 &&
      f.rand == (Hex.Rand.ofSeed 19).next.2 && f.events.length == 2
  | .ok _ => false)

#guard ([1024, 1025].all fun work =>
  match Construction.retry 1000003 constructionBudget (previous work) provider with
  | .error f => f.attempts == work && f.rand == (previous work).rand &&
      f.events == [event "first"]
  | .ok _ => false)

#guard (match Construction.retry 1000003 { constructionBudget with maxAttempts := 0 }
    (previous 0) provider with
  | .error f => f.attempts == 0 && f.events == [event "first"]
  | .ok _ => false)

#guard (match Construction.retry 15 constructionBudget
    { previous 3 with stop := .composite } provider with
  | .error f => f.stop == .composite && f.attempts == 3 && f.events == [event "first"]
  | .ok _ => false)

-- Depth remains shared policy. The returned factors cannot certify this child
-- with a depth-one allowance, even though the root factor product is complete.
#guard (match Construction.retry 1000003 { constructionBudget with maxDepth := 1 }
    (previous 8) provider with
  | .error f => f.obligation == some 166667 && f.attempts > 8 &&
      f.attempts ≤ 1024 && f.events.head? == some (event "first")
  | .ok _ => false)

private def rejects (raw : PartialFactors) : Bool :=
  match Construction.retry 1000003 constructionBudget (previous 11)
      (fun _ _ r => ⟨raw, r, 1, [event "invalid"]⟩) with
  | .error f => f.stop == .exhausted && f.attempts == 12 &&
      f.events == [event "first", event "invalid"] && f.obligation == some 1000003
  | .ok _ => false

#guard rejects ⟨[(0, 1)], 1⟩
#guard rejects ⟨[(2, 100000000000000000000)], 1⟩
#guard rejects ⟨[(2, 1), (2, 1)], 1⟩
#guard rejects ⟨[(2, 1), (3, 1)], 0⟩
#guard rejects ⟨[(2, 1)], 1⟩

-- An over-reported count is rejected, and must not be truncated in diagnostics.
#guard (match Construction.retry 1000003 constructionBudget (previous 1023)
    (fun _ n r => ⟨⟨[], n⟩, r, 2, []⟩) with
  | .error f => f.attempts == 1025
  | .ok _ => false)

-- A child can fail under one random state and be certified in a later subset.
-- Exhaustion must then identify the still-unresolved child, not that old failure.
private def changingProvider : FactorSearch := fun _ n r =>
  let raw : PartialFactors :=
    if n == 42949832319110410 then ⟨[(2, 1), (1000003, 1), (4294970347, 1)], 5⟩
    else if n == 1000002 && r.state > 0 then ⟨[(2, 1), (3, 1), (166667, 1)], 1⟩
    else ⟨[], n⟩
  let rand := if n == 42949832319110410 then r else { state := r.state + 1 }
  ⟨raw, rand, 1, [.route "factor" [("subject", toString (n + 1)), ("seed", toString r.state)]]⟩

#guard (match Construction.runTraced 42949832319110411 (Hex.Rand.ofSeed 0)
    (factor := changingProvider) with
  | .error f => f.obligation == some 4294970347 && f.attempts == 14 && f.rand.state == 6 &&
      f.events.contains (.route "factor" [("subject", "1000003"), ("seed", "3")]) &&
      f.events.getLast? == some (.route "factor" [("subject", "4294970347"), ("seed", "5")])
  | .ok _ => false)
