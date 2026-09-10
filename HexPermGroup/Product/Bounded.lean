/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Build.Bounded
public import HexPermGroup.Product.Direct
public import HexPermGroup.Product.Wreath

public section

/-! Product limits check the declared action dimensions before materialization. -/

namespace Hex.PermGroup

/-- Product dimensions and cumulative producer allowances are independent.
Declared fixed points contribute to the degree even when all generators fix them. -/
structure ProductLimits where
  /-- Largest permitted output permutation degree. -/
  degree : Nat
  /-- Largest permitted number of materialized input generators. -/
  generators : Nat
  /-- Shared materialization and recursive chain-construction budget. -/
  work : Execution.Budget

/-- A dimension limit reports the actual dimension required by the operation. -/
inductive ProductLimit where
  | degree (required cap : Nat)
  | generators (required cap : Nat)
  deriving DecidableEq, Repr

namespace Group

open Execution

/-- Direct products check `n+m` and `rG+rH` before either generator map runs.
Image reservations include the degree-sized output arrays and factor identities.
Chain construction then continues with the same meter. -/
@[expose] def directProductWith (limits : ProductLimits) (G : Group n) (H : Group m) :
    Except ProductLimit (Measured limits.work {K : Group (n + m) // K = G.directProduct H}) :=
  if n + m ≤ limits.degree then
    if G.generators.size + H.generators.size ≤ limits.generators then
      .ok (Execution.run limits.work do
        reserve .storage (2 * (G.generators.size + H.generators.size))
        reserve .images ((n + m) * (G.generators.size + H.generators.size) +
          m * G.generators.size + n * H.generators.size)
        construct ((G.generators.map fun p => p.sum (Perm.id m)) ++
          (H.generators.map fun q => (Perm.id n).sum q)))
    else .error (.generators (G.generators.size + H.generators.size) limits.generators)
  else .error (.degree (n + m) limits.degree)

/-- The imprimitive product checks `n*m` and `m*rG+rH`, including fixed blocks.
The native wreath action caches one base permutation per block before building
its point images. Empty blocks remain excluded by the positive-degree hypothesis. -/
@[expose] def wreathProductWith (limits : ProductLimits) (G : Group n) (H : Group m) (hn : 0 < n) :
    Except ProductLimit (Measured limits.work {K : Group (n * m) // K = G.wreathProduct H hn}) :=
  if n * m ≤ limits.degree then
    if m * G.generators.size + H.generators.size ≤ limits.generators then
      .ok (Execution.run limits.work do
        let count := m * G.generators.size + H.generators.size
        reserve .storage ((m + 3) * count + m)
        reserve .images ((2 * (n * m) + m) * count)
        construct (((List.finRange m).flatMap fun i =>
          G.generators.toList.map (Perm.Wreath.copy hn i)).toArray ++
          H.generators.map (Perm.Wreath.lift hn)))
    else .error (.generators (m * G.generators.size + H.generators.size) limits.generators)
  else .error (.degree (n * m) limits.degree)

/-- Degree rejection happens before any direct-product allocation or chain work. -/
theorem directProductWith_degree (limits : ProductLimits) (G : Group n) (H : Group m)
    (h : limits.degree < n + m) :
    G.directProductWith limits H = .error (.degree (n + m) limits.degree) := by
  simp [directProductWith, Nat.not_le.mpr h]

/-- Wreath degree rejection retains the full declared product degree. -/
theorem wreathProductWith_degree (limits : ProductLimits) (G : Group n) (H : Group m) (hn : 0 < n)
    (h : limits.degree < n * m) :
    G.wreathProductWith limits H hn = .error (.degree (n * m) limits.degree) := by
  simp [wreathProductWith, Nat.not_le.mpr h]

end Group
end Hex.PermGroup
