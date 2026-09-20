/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.EcmStage2
public import HexPrimality.Construction

public section

/-! Explicit bounded ECM factor provider for certificate construction.
It is not registered in the ordinary factorization or primality portfolio. -/

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
  if n == 0 then return ⟨⟨[], 0⟩, r, 0⟩
  let limit := allocation.attemptLimit.getD 1024
  let allocation := { allocation with attemptLimit := some limit }
  let initial := Construction.factorSearch allocation n r
  -- Do not factor a residual already unnecessary for the square-root criterion.
  if initial.raw.residual > 0 && (n / initial.raw.residual)^2 > n + 1 then
    return initial
  let mut work := initial.attempts
  let mut rand := initial.rand
  let mut factors := initial.raw.factors
  let mut residual := 1
  let mut stack := [initial.raw.residual]
  for _ in [:allocation.factorFuel] do
    let m :: rest := stack | break
    stack := rest
    if m ≤ 1 then continue
    let mut divisor := 0
    for curve in [:min curves 64] do
      if work ≥ limit then break
      let (result, used) := Ecm.search m (6 + curve) b₁ b₂ (limit - work)
      work := work + used
      if trace then
        dbg_trace "ecm {m}: sigma {6+curve}; bounds {b₁}/{b₂}; {repr result}; attempts {used}"
      if let .factor d := result then
        if 1 < d && d < m && m % d == 0 then
          divisor := d
          break
    if divisor == 0 then residual := residual * m
    else
      for part in [divisor, m / divisor] do
        let found := Construction.factorSearch { allocation with attemptLimit := some (limit - work) } part rand
        work := work + found.attempts
        rand := found.rand
        for (p, e) in found.raw.factors do
          factors := insert p e factors
        stack := found.raw.residual :: stack
  return ⟨⟨factors, stack.foldl (· * ·) residual⟩, rand, work⟩

end Hex.Nat
