/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDet.Packed

@[expose] public section

namespace Hex.PolyDet.Packed

open Hex.Matrix Hex.MvPoly.Kernel Hex.Kronecker

/-- One product determined entirely by the original determinant witness. -/
structure Product (R : Type) where
  row : Nat
  inner : Nat
  width : Nat
  left : List R
  right : List (List R)
  result : List R
  deriving Repr

/-- The same prefix products consumed by the kernel checker. -/
def products (ops : DetOps R) (n : Nat) (a : List (List R)) :
    DetWitness R → List (Product R)
  | .triangular swaps ts d =>
      (ts.zipIdx).map fun (t, i) =>
        { row := i, inner := i + 1, width := i + 1, left := t
          right := leading (i + 1) (DetWitness.permute swaps a)
          result := List.replicate i ops.zero ++ [next ops swaps d i (ts.drop (i + 1))] }
  | .singular v =>
      [{ row := 0, inner := n, width := n, left := v, right := a,
         result := List.replicate n ops.zero }]

def Product.map (f : R → S) (a : Product R) : Product S :=
  { a with left := a.left.map f, right := a.right.map (List.map f), result := a.result.map f }

/-- Exact crossover coordinates; uncovered products always use term lists. -/
structure Key where
  packedBits : Nat
  leftSupport : Nat
  rightSupport : Nat
  resultSupport : Nat
  inner : Nat
  deriving Repr, BEq, Inhabited

def support (a : List (PolyList C)) : Nat := a.foldl (fun s p => s + p.length) 0

def Product.key (a : Product (PolyList Int)) (s : SizeBound) : Key :=
  ⟨s.packedBits, support a.left, support a.right.flatten, support a.result, a.inner⟩

/-- Measured eligible product keys. An empty table is the sparse control. -/
def crossover : List Key := []

/-- Explicit comparison overrides do not waive either hard packing limit. -/
inductive Arm where
  | automatic
  | lists
  | packed
  | signedPacked
  deriving Repr, BEq, Inhabited

structure Report where
  row : Nat
  size : SizeBound
  key : Key
  deriving Repr

structure Selection where
  mode : MulMode := .plain
  packed : Bool := false
  reports : List Report := []
  reason : Option String := none
  quotientSupport : Nat := 0
  deriving Repr

def Selection.route (s : Selection) : String :=
  if !s.packed then "term-list" else
    match s.mode with | .plain => "packed/plain" | .signedPacked => "packed/signedPacked"

def limitText (n limit : Nat) : String :=
  if n > limit then s!"at least {limit + 1}" else toString n

def declineMessage (budget : Budget) (r : Report) : String :=
  s!"det: packed certificate declined: dense box requires {limitText r.size.digits budget.maxDenseDigits} digits and {limitText r.size.packedBits budget.maxPackedBits} packed bits (limits {budget.maxDenseDigits} digits, {budget.maxPackedBits} bits); using term lists; product row {r.row}, per-atom degrees {r.size.degrees}, limitingStage {reprStr r.size.limitingStage}"

/-- One arm and one multiplication mode for the entire witness. -/
def select (budget : Budget) (arm : Arm) (k : Nat)
    (ps : List (Product (PolyList Int))) (modulus : Option Nat := none)
    (quotients : Option (List (List (PolyList Int))) := none)
    (table : List Key := crossover) : Except String Selection := do
  let mode := if arm == .signedPacked then MulMode.signedPacked else .plain
  let mut reports := []
  for a in ps do
    let sized := match modulus, quotients with
      | some p, some qs => sizeMulTermsMod budget mode k 1 a.inner a.width p
          [a.left] a.right [a.result] [qs.getD a.row []]
      | _, _ => sizeMulTerms budget mode k 1 a.inner a.width [a.left] a.right [a.result]
    let s ← sized.mapError (fun e => s!"malformed packed product at row {a.row}: {reprStr e}")
    reports := reports ++ [⟨a.row, s, a.key s⟩]
  let base : Selection := { mode, reports, quotientSupport := quotients.map (support ∘ List.flatten) |>.getD 0 }
  if let some r := reports.find? (fun r => !r.size.accepts budget) then
    return { base with reason := some (declineMessage budget r) }
  if modulus.isSome && quotients.isNone then
    return { base with reason := some "residue quotient payload unavailable" }
  if arm == .lists then return { base with reason := some "forced term lists" }
  if arm == .automatic && !reports.all (fun r => table.contains r.key) then
    return { base with reason := some "no measured packed regime" }
  return { base with packed := true }

/-- Optional quotient work is bounded by the existing certificate and producer limits. -/
structure QuotientBudget where
  terms : Nat := 100000
  coefficientBits : Nat := 4096
  certificateTerms : Nat := 65536
  deriving Repr

inductive QuotientError where
  | unavailable
  | indivisible (row column : Nat)
  deriving Repr, BEq

def coefficientBits (a : PolyList Int) : Nat :=
  a.foldl (fun b (_, c) => max b (c.natAbs.log2 + 1)) 0

def within (budget : QuotientBudget) (a : PolyList Int) : Bool :=
  a.length ≤ budget.terms && coefficientBits a ≤ budget.coefficientBits

/-- Compute each integer quotient coefficient exactly in compiled code. -/
def prepareQuotients (budget : QuotientBudget) (p : Nat)
    (ps : List (Product (PolyList Int))) : Except QuotientError (List (List (PolyList Int))) := do
  if p == 0 then throw (.indivisible 0 0)
  let mut qs := []
  let mut count := 0
  for a in ps do
    let mut row := []
    for j in [:a.width] do
      let mut acc : PolyList Int := []
      for t in [:a.inner] do
        let l := a.left.getD t []
        let r := (a.right.getD t []).getD j []
        -- Reject unaffordable products before allocating their term cross product.
        if l.length * r.length + acc.length > budget.terms ||
            coefficientBits l + coefficientBits r + (l.length * r.length).log2 + 1 > budget.coefficientBits then
          throw .unavailable
        acc := add acc (mul l r)
        unless within budget acc do throw .unavailable
      let c := a.result.getD j []
      if acc.length + c.length > budget.terms then throw .unavailable
      acc := sub acc c
      unless within budget acc do throw .unavailable
      unless acc.all (fun (_, z) => z % (p : Int) == 0) do throw (.indivisible a.row j)
      let q := acc.map fun (e,z) => (e, z / (p : Int))
      count := count + q.length
      if count > budget.certificateTerms then throw .unavailable
      row := row ++ [q]
    qs := qs ++ [row]
  return qs

end Hex.PolyDet.Packed
