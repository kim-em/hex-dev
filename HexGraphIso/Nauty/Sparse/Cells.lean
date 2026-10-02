/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Sort

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Numeric ordering of distinct touched-cell starts. -/
def sortCells (xs : Array Nat) : Array Nat :=
  (Hex.List.sort xs.toList (· ≤ ·)).toArray

/-- Tiny touched sets need only direct comparisons; larger sets retain the
existing verified merge sort. -/
@[inline] def sortCellsFast (xs : Array Nat) : Array Nat :=
  match xs.size with
  | 0 | 1 => xs
  | 2 =>
    let a := xs[0]!
    let b := xs[1]!
    if a ≤ b then xs else #[b, a]
  | 3 =>
    let a := xs[0]!
    let b := xs[1]!
    let c := xs[2]!
    if a ≤ b then
      if b ≤ c then xs else if a ≤ c then #[a, c, b] else #[c, a, b]
    else
      if a ≤ c then #[b, a, c] else if b ≤ c then #[b, c, a] else #[c, b, a]
  | _ => (Hex.List.sort xs.toList (· ≤ ·)).toArray

@[csimp] theorem sortCells_eq_fast : sortCells = sortCellsFast := by
  funext xs
  cases xs with
  | mk xs =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        cases xs with
        | nil =>
          simp [sortCells, sortCellsFast, Hex.List.sort, Hex.List.sort.go, Hex.List.merge]
          split <;> simp_all
        | cons c xs =>
          cases xs with
          | nil =>
            by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;> by_cases hac : a ≤ c <;>
              simp [sortCells, sortCellsFast, Hex.List.sort, Hex.List.sort.go,
                Hex.List.merge, hab, hbc, hac] <;> omega
          | cons d xs => rfl

end Hex.GraphIso.Nauty.Sparse
