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

/-- Product keys from six paired comparisons with a smaller packed median.
The retained measurements and selection rule are in `reports/bench-results/hex-det-packed/`.
Uncovered witnesses continue to use term lists. -/
def crossover : List Key := [
  ⟨34, 1, 4, 4, 1⟩,
  ⟨35, 1, 1, 1, 1⟩,
  ⟨41, 1, 4, 4, 1⟩,
  ⟨62, 1, 4, 4, 1⟩,
  ⟨83, 1, 4, 4, 1⟩,
  ⟨98, 8, 16, 8, 2⟩,
  ⟨104, 1, 4, 4, 1⟩,
  ⟨111, 1, 4, 4, 1⟩,
  ⟨118, 1, 4, 4, 1⟩,
  ⟨139, 1, 4, 4, 1⟩,
  ⟨175, 8, 16, 11, 2⟩,
  ⟨186, 8, 16, 11, 2⟩,
  ⟨188, 1, 4, 4, 1⟩,
  ⟨208, 25, 36, 12, 3⟩,
  ⟨340, 49, 64, 16, 4⟩,
  ⟨362, 8, 16, 12, 2⟩,
  ⟨400, 36, 36, 21, 3⟩,
  ⟨485, 2, 4, 1, 2⟩,
  ⟨527, 8, 16, 13, 2⟩,
  ⟨538, 8, 16, 15, 2⟩,
  ⟨576, 33, 36, 22, 3⟩,
  ⟨660, 87, 64, 30, 4⟩,
  ⟨784, 41, 36, 34, 3⟩,
  ⟨791, 8, 16, 15, 2⟩,
  ⟨890, 8, 16, 10, 2⟩,
  ⟨1187, 8, 16, 13, 2⟩,
  ⟨1280, 86, 64, 36, 4⟩,
  ⟨1300, 135, 64, 54, 4⟩,
  ⟨1408, 42, 36, 41, 3⟩,
  ⟨1451, 8, 16, 15, 2⟩,
  ⟨1529, 3, 9, 1, 3⟩,
  ⟨1546, 1, 4, 4, 1⟩,
  ⟨1979, 8, 16, 15, 2⟩,
  ⟨2000, 39, 36, 35, 3⟩,
  ⟨3179, 4, 16, 1, 4⟩,
  ⟨3600, 151, 64, 88, 4⟩,
  ⟨3840, 45, 36, 50, 3⟩,
  ⟨4096, 30, 36, 20, 3⟩,
  ⟨5040, 126, 64, 66, 4⟩,
  ⟨5488, 39, 36, 38, 3⟩,
  ⟨5760, 43, 36, 45, 3⟩,
  ⟨7655, 8, 16, 15, 2⟩,
  ⟨11960, 184, 64, 130, 4⟩,
  ⟨12096, 45, 36, 51, 3⟩,
  ⟨12500, 80, 64, 35, 4⟩,
  ⟨12500, 200, 64, 140, 4⟩,
  ⟨14080, 134, 64, 79, 4⟩,
  ⟨19840, 43, 36, 47, 3⟩,
  ⟨47940, 188, 64, 143, 4⟩,
  ⟨48020, 204, 64, 160, 4⟩
]

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
    -- Without a quotient payload these are preliminary integer-product bounds.
    -- They can reject packing, but never establish modular packing eligibility.
    let sized := match modulus, quotients with
      | some p, some qs => sizeMulTermsMod budget mode k 1 a.inner a.width p
          [a.left] a.right [a.result] [qs.getD a.row []]
      | _, _ => sizeMulTerms budget mode k 1 a.inner a.width [a.left] a.right [a.result]
    let s ← sized.mapError (fun e => s!"malformed packed product at row {a.row}: {reprStr e}")
    reports := reports ++ [⟨a.row, s, a.key s⟩]
  let base : Selection := { mode, reports, quotientSupport := quotients.map (support ∘ List.flatten) |>.getD 0 }
  if let some r := reports.find? (fun r => !r.size.accepts budget) then
    return { base with reason := some (declineMessage budget r) }
  if arm == .lists then return { base with reason := some "forced term lists" }
  if modulus.isSome && quotients.isNone then
    return { base with reason := some "residue quotient payload unavailable" }
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
  | invalidModulus
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
  if p == 0 then throw .invalidModulus
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
