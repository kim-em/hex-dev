/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.EcmStage2
public import HexPrimality.Construction

public section

/-! Bounded ECM factor provider for certificate construction.
The standard HexIntFactor import selects the interleaved provider for
`primality?`. Ordinary integer factorization and `primality` use their
separate search portfolios. -/

namespace Hex.Nat

private def insert (q e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(q, e)]
  | (p, k) :: rest =>
      if p = q then (p, k + e) :: rest else (p, k) :: insert q e rest

/-- Core partial factoring followed by a bounded two-stage ECM schedule.
Each residual uses consecutive Suyama parameters from 6, with at most 64 curves.
The callback honors the remaining total attempt limit and never accepts an
externally asserted prime. The constructor recursively certifies candidates. -/
def ecmFactorSearch (b₁ : Nat := 32768) (b₂ : Nat := 524288)
    (curves : Nat := 64) (trace : Bool := false) : FactorSearch := fun allocation n r => Id.run do
  if n == 0 then return ⟨⟨[], 0⟩, r, 0, []⟩
  let limit := allocation.attemptLimit.getD 1024
  let allocation := { allocation with attemptLimit := some limit }
  -- Rescue belongs after this producer's ECM routes, rather than after the
  -- core provider's shorter smooth/rho portfolio.
  let coreAllocation := { allocation with squfof := match allocation.squfof with
    | .rescue _ => .off
    | policy => policy }
  let initial := Construction.factorSearch coreAllocation n r
  -- Do not factor a residual already unnecessary for the square-root criterion.
  if initial.raw.residual > 0 && (n / initial.raw.residual)^2 > n + 1 then
    return initial
  let mut work := initial.attempts
  let mut rand := initial.rand
  let mut events := initial.events
  let mut factors := initial.raw.factors
  let mut residual := 1
  let mut stack := [initial.raw.residual]
  let mut tables := Ecm.prepare b₁ b₂
  for _ in [:allocation.factorFuel] do
    let m :: rest := stack | break
    stack := rest
    if m ≤ 1 then continue
    let mut divisor := 0
    for curve in [:min curves 64] do
      if work ≥ limit then break
      let some t := tables | break
      let ((result, used), t) := Ecm.Internal.searchPrepared m (6 + curve) (limit - work) t
      tables := some t
      work := work + used
      if trace then
        dbg_trace "ecm {m}: sigma {6+curve}; bounds {b₁}/{b₂}; {repr result}; attempts {used}"
      if let .factor d := result then
        if 1 < d && d < m && m % d == 0 then
          divisor := d
          break
    if divisor == 0 && !isProbablePrime m then
      let rescue := Internal.squfofSearch allocation.squfof false m rand (limit - work)
      work := work + rescue.attempts
      events := events ++ rescue.events
      if let some d := rescue.divisor then divisor := d.val
    if divisor == 0 then residual := residual * m
    else
      for part in [divisor, m / divisor] do
        let found := Construction.factorSearch { coreAllocation with attemptLimit := some (limit - work) } part rand
        work := work + found.attempts
        rand := found.rand
        events := events ++ found.events
        for (p, e) in found.raw.factors do
          factors := insert p e factors
        stack := found.raw.residual :: stack
  return ⟨⟨factors, stack.foldl (· * ·) residual⟩, rand, work, events⟩

/-- The original fixed-curve ECM closure, retained for explicit selection. -/
def ecmConstructionFactor : FactorSearch := ecmFactorSearch

-- Return one proper divisor; the shared worklist handles both parts.
-- The fixed exponent depends only on the bound and base.
private def longSplit (allocation : FactorSearchBudget) (n limit : Nat) :
    Option Nat × Nat := Id.run do
  let mut work := 0
  for bound in [262144, 524288] do
    for base in allocation.smoothBases do
      if work ≥ limit then return (none, work)
      let result := PMinusOne.start n base bound
      work := work + 1
      if let .factor d := result.result then
        if 1 < d && d < n && n % d == 0 then return (some d, work)
  return (none, work)

/-- Interleave bounded Pollard p-minus-one and ECM while retaining each split.
The preliminary search uses smooth bounds through 32768 and caps rho at
8192 steps. Long p-minus-one searches use 262144 and 524288 at the supplied bases.
Small residuals try them before ECM; larger residuals try eight random curves
first. All work shares the supplied attempt limit. Candidate primes are
recursively certified by the caller, and exhaustion makes no primality claim.
Set `early := false` to factor beyond the default Pocklington size criterion. -/
def interleavedFactorSearch (trace : Bool := false) (early : Bool := true) :
    FactorSearch := fun allocation n r => Id.run do
  if n == 0 then return ⟨⟨[], 0⟩, r, 0, []⟩
  let limit := allocation.attemptLimit.getD 1024
  let coreAllocation := { allocation with
    attemptLimit := some limit
    smoothBounds := [64, 512, 4096, 32768]
    primeBudget := { allocation.primeBudget with rhoSteps := min allocation.primeBudget.rhoSteps 8192 }
    squfof := match allocation.squfof with
      | .rescue _ => .off
      | policy => policy }
  let initial := Construction.factorSearch coreAllocation n r
  if early && initial.raw.residual > 0 && (n / initial.raw.residual)^2 > n + 1 then
    return initial
  let mut work := initial.attempts
  let mut rand := initial.rand
  let mut events := initial.events
  let mut factors := initial.raw.factors
  let mut residual := 1
  -- A failed long p-1 search cannot split any divisor of the same subject:
  -- gcd(a^E - 1, d) is 1 or d when the ancestor gcd was 1 or the ancestor.
  -- Descendants inherit this flag. After a success the policy
  -- restarts the ladder; reusing its failed prefix is a remaining optimization.
  let mut stack := [(initial.raw.residual, false)]
  let schedule :=
    [(10000, 1000000, 8, true), (10000, 1000000, 42, true),
      (32768, 524288, 64, false), (50000, 4000000, 200, true)]
  let mut tables := schedule.toArray.map fun (b₁, b₂, _, _) => Ecm.prepare b₁ b₂
  for _ in [:allocation.factorFuel] do
    let unfactored := stack.foldl (fun acc (m, _) => acc * m) residual
    if early && unfactored > 0 &&
        Construction.sufficient constructionBudget (n + 1) (n / unfactored) then break
    let (m, tried) :: rest := stack | break
    stack := rest
    if m ≤ 1 then continue
    if isProbablePrime m then
      factors := insert m 1 factors
      continue
    let small := m.log2 + 1 ≤ 192
    let mut tried := tried
    let mut divisor := 0
    if small && !tried then
      let (found, used) := longSplit coreAllocation m (limit - work)
      work := work + used
      divisor := found.getD 0
      tried := found.isNone
      events := events ++ [.route "long-pminus-one"
        [("subject", toString m), ("attempts", toString used), ("factor", toString divisor)]]
    if divisor == 0 then
      for idx in [:schedule.length] do
        -- Both halves of the first round share the bound-dependent schedules.
        if idx == 1 then tables := tables.set! 1 tables[0]!
        if !small && !tried && idx == 1 then
          let (found, used) := longSplit coreAllocation m (limit - work)
          work := work + used
          divisor := found.getD 0
          tried := found.isNone
          events := events ++ [.route "long-pminus-one"
            [("subject", toString m), ("attempts", toString used), ("factor", toString divisor)]]
          if divisor > 0 then break
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
    if divisor == 0 && !isProbablePrime m then
      let rescue := Internal.squfofSearch allocation.squfof false m rand (limit - work)
      work := work + rescue.attempts
      events := events ++ rescue.events
      if let some d := rescue.divisor then divisor := d.val
    if divisor == 0 then residual := residual * m
    else
      for part in [divisor, m / divisor] do
        let found := Construction.factorSearch
          { coreAllocation with attemptLimit := some (limit - work) } part rand
        work := work + found.attempts
        rand := found.rand
        events := events ++ found.events
        for (p, e) in found.raw.factors do factors := insert p e factors
        stack := (found.raw.residual, tried) :: stack
  return ⟨⟨factors, stack.foldl (fun acc (m, _) => acc * m) residual⟩, rand, work, events⟩

/-- The default interleaved closure selected by the construction registration. -/
def interleavedConstructionFactor : FactorSearch := interleavedFactorSearch

end Hex.Nat
