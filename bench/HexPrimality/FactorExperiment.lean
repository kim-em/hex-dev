/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexIntFactor.Construction
meta import HexIntFactor.EcmStage2
import all HexPrimality.Construction
import Lean.Data.Json

/-! Offline comparison of bounded factor-search policies for Pocklington
certificate construction. These policies do not change the public tactic.
Every proposed factorization is checked for exact reconstruction, and every
successful construction is checked against its original subject. -/

open Hex.Nat

private def insert (q e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(q, e)]
  | (p, k) :: rest =>
      if p = q then (p, k + e) :: rest else (p, k) :: insert q e rest

-- Finite approximation to SymPy's first two ECM rounds. The second-stage
-- endpoint stays within Hex's existing bound of 4194304.
private def rounds : List (Nat × Nat × Nat) :=
  [(10000, 1000000, 50), (50000, 4000000, 200)]

#guard rounds.all fun (b₁, b₂, _) => Ecm.validBounds b₁ b₂
#guard Ecm.validBounds 32768 524288

private def staged (randomCurves trace : Bool) (mixed : Bool := false)
    (early : Bool := false) (interleave : Bool := false) :
    FactorSearch := fun allocation n r => Id.run do
  if n == 0 then return ⟨⟨[], 0⟩, r, 0, []⟩
  let limit := allocation.attemptLimit.getD 1024
  let coreAllocation := { allocation with attemptLimit := some limit }
  let initial := Construction.factorSearch coreAllocation n r
  if initial.raw.residual > 0 && (n / initial.raw.residual)^2 > n + 1 then
    return initial
  let mut work := initial.attempts
  let mut rand := initial.rand
  let mut events := initial.events
  let mut factors := initial.raw.factors
  let mut residual := 1
  let mut stack := [initial.raw.residual]
  let schedule := if interleave then
    [(10000, 1000000, 8, true), (10000, 1000000, 42, true),
      (32768, 524288, 64, false), (50000, 4000000, 200, true)]
    else if mixed then
    [(10000, 1000000, 50, true), (32768, 524288, 64, false),
      (50000, 4000000, 200, true)]
    else rounds.map fun (b₁, b₂, curves) => (b₁, b₂, curves, randomCurves)
  let mut tables := schedule.toArray.map fun (b₁, b₂, _, _) => Ecm.prepare b₁ b₂
  for _ in [:allocation.factorFuel] do
    let unfactored := stack.foldl (· * ·) residual
    if early && unfactored > 0 &&
        Construction.sufficient constructionBudget (n + 1) (n / unfactored) then break
    let m :: rest := stack | break
    stack := rest
    if m ≤ 1 then continue
    if isProbablePrime m then
      factors := insert m 1 factors
      continue
    -- Recover cheap smooth factors before ECM on smaller residuals. On larger
    -- residuals give eight curves a chance before paying for the long p-1 ladder.
    let small := m.log2 + 1 ≤ 192
    if interleave && small then
      let found := Construction.factorSearch
        { coreAllocation with
          smoothBounds := [262144, 524288]
          primeBudget := { coreAllocation.primeBudget with rhoRestarts := 0 }
          attemptLimit := some (limit - work) } m rand
      work := work + found.attempts
      rand := found.rand
      events := events ++ found.events
      if !found.raw.factors.isEmpty then
        for (p, e) in found.raw.factors do factors := insert p e factors
        stack := found.raw.residual :: stack
        continue
    let mut divisor := 0
    for idx in [:schedule.length] do
      if interleave && idx == 1 then tables := tables.set! 1 tables[0]!
      if interleave && !small && idx == 1 then
        let found := Construction.factorSearch
          { coreAllocation with
            smoothBounds := [262144, 524288]
            primeBudget := { coreAllocation.primeBudget with rhoRestarts := 0 }
            attemptLimit := some (limit - work) } m rand
        work := work + found.attempts
        rand := found.rand
        events := events ++ found.events
        if !found.raw.factors.isEmpty then
          -- Preserve all returned components; the normal worklist validates
          -- and processes them using the same remaining allowance.
          divisor := found.raw.factors.head!.1
          if 1 < divisor && divisor < m && m % divisor == 0 then break
          divisor := 0
      let (b₁, b₂, curves, randomCurves) := schedule[idx]!
      for curve in [:curves] do
        if work ≥ limit then break
        let some t := tables[idx]! | break
        let (sigma, next) := if randomCurves then Id.run do
          let (value, next) := rand.words (m.log2 / 64 + 1)
          return (6 + value % (m - 6), next)
        else (6 + curve, rand)
        rand := next
        let ((result, used), t) := Ecm.Internal.searchPrepared m sigma (limit - work) t
        tables := tables.set! idx (some t)
        work := work + used
        if trace then
          dbg_trace "ecm {m}: sigma {sigma}; bounds {b₁}/{b₂}; {repr result}; attempts {used}"
        if let .factor d := result then
          if 1 < d && d < m && m % d == 0 then
            divisor := d
            break
      if divisor > 0 then break
    if divisor == 0 then residual := residual * m
    else
      for part in [divisor, m / divisor] do
        let found := Construction.factorSearch
          { coreAllocation with attemptLimit := some (limit - work) } part rand
        work := work + found.attempts
        rand := found.rand
        events := events ++ found.events
        for (p, e) in found.raw.factors do factors := insert p e factors
        stack := found.raw.residual :: stack
  return ⟨⟨factors, stack.foldl (· * ·) residual⟩, rand, work, events⟩

private def profile (name : String) (trace : Bool) :
    Option (ConstructionBudget × FactorSearch) := do
  let short := { constructionBudget with factor := { constructionBudget.factor with
    smoothBounds := [64, 512, 4096]
    primeBudget := { constructionBudget.factor.primeBudget with rhoSteps := 8192 } } }
  let balanced := { short with factor := { short.factor with
    smoothBounds := [64, 512, 4096, 32768] } }
  match name with
  | "baseline" => some (constructionBudget, ecmConstructionFactor)
  | "baseline-single" => some (constructionBudget, ecmConstructionFactor)
  | "fixed" => some (constructionBudget, ecmFactorSearch 10000 1000000 64 trace)
  | "short" => some (short, ecmFactorSearch 10000 1000000 64 trace)
  | "staged" => some (short, staged false trace)
  | "random" => some (short, staged true trace)
  | "mixed" => some (short, staged true trace true)
  | "efficient" => some (short, staged true trace true true)
  | "balanced" => some (balanced, staged true trace true true)
  | "interleaved" => some (balanced, staged true trace true true true)
  | "random-retry" => some (constructionBudget, staged true trace)
  | _ => none

public def main (args : List String) : IO UInt32 := do
  if args == ["selftest"] then
    let some (budget, provider) := profile "interleaved" false | return 2
    for n in [0, 1, 2, 35, 49, 1000036000099] do
      for limit in [0, 1, 2, 3, 8, 32] do
        let result := provider { budget.factor with attemptLimit := some limit }
          n (Hex.Rand.ofSeed 1)
        unless result.attempts ≤ limit &&
            result.raw.factors.foldl (fun acc (q, e) => acc * q^e)
              result.raw.residual == n do
          throw <| IO.userError "interleaved allowance or reconstruction failure"
    IO.println "Interleaved resource and reconstruction checks passed"
    return 0
  let (args, seedArg) := if args.length == 4 then (args.take 3, args[3]!) else (args, "")
  let [mode, name, subject] := args |
    throw <| IO.userError
      "usage: hexprimality_factor_experiment (factor|construct|trace) PROFILE SUBJECT [SEED]"
  let some n := subject.toNat? | throw <| IO.userError "invalid subject"
  let some seed := if seedArg == "" then some n else seedArg.toNat? |
    throw <| IO.userError "invalid seed"
  let some (budget, provider) := profile name (mode == "trace") |
    throw <| IO.userError "unknown profile"
  let start ← IO.monoNanosNow
  let rand := Hex.Rand.ofSeed seed
  let fields ← if mode == "factor" then do
    let allocation := { budget.factor with attemptLimit := some budget.maxAttempts }
    let input ← IO.mkRef (provider allocation n rand)
    let result ← input.get
    let stop ← IO.monoNanosNow
    let reconstructed := result.raw.factors.foldl (fun acc (q, e) => acc * q^e)
      result.raw.residual
    unless reconstructed == n && result.attempts ≤ budget.maxAttempts do
      throw <| IO.userError "invalid factor-search result"
    pure [("nanos", Lean.toJson (stop - start)),
      ("factors", Lean.toJson result.raw.factors),
      ("residual", Lean.toJson result.raw.residual),
      ("attempts", Lean.toJson result.attempts)]
  else if mode == "construct" || mode == "trace" then do
    let result := if name == "baseline" || name == "random-retry" then
        match Construction.runTraced n rand budget with
        | .ok s => .ok s
        | .error f => Construction.retry n budget f provider
      else Construction.runTraced n rand budget provider
    let input ← IO.mkRef result
    let result ← input.get
    let stop ← IO.monoNanosNow
    match result with
    | .error f => pure [("nanos", Lean.toJson (stop - start)),
        ("status", Lean.toJson (reprStr f.stop)),
        ("attempts", Lean.toJson f.attempts),
        ("unresolved", Lean.toJson (f.obligation.getD n))]
    | .ok s =>
        unless s.cert.raw.subject == n && checkPrime s.cert.raw do
          throw <| IO.userError "invalid certificate"
        pure [("nanos", Lean.toJson (stop - start)), ("status", Lean.toJson "success"),
          ("attempts", Lean.toJson s.attempts),
          ("certificate", Lean.toJson (reprStr s.cert.raw))]
  else throw <| IO.userError "unknown mode"
  IO.println <| (Lean.Json.mkObj <| [("subject", Lean.toJson n),
    ("seed", Lean.toJson seed), ("profile", Lean.toJson name),
    ("budget", Lean.toJson (reprStr budget))] ++ fields).compress
  return 0
