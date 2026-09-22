/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Replay
public import HexRank.Int
public import HexRowReduce.Inverse

public section

/-! Construction of recursive BKR certificates from prepared Tarski queries.
The diagnostic result exposes unproved producer obligations; it is not the
domain-only `Option` API of sign determination. In particular, singularity and
nonintegral counts must eventually be excluded by the completeness proof. -/
namespace Hex.SignDet

open scoped Hex

/-- Internal construction diagnostics, distinct from mathematical domain failure. -/
inductive BuildError where
  | dimensions
  | singular
  | nonintegral
  | negative
  | system
  | replay
  deriving DecidableEq, Repr

/-- Solve in the rationals and retain integers only after checking exact
integrality and nonnegativity. The scaled inverse uses a common denominator;
its integer identity is checked in the original row and column orders. -/
def solveSystem {r : Nat} (arity : Nat) (rows : Vector (List Nat) r)
    (columns : Vector (List Int) r) (values : Vector Int r) :
    Except BuildError (System r) := do
  let m : Matrix Rat r r := Matrix.ofFn fun i j => (entry rows[i] columns[j] : Rat)
  let inv ← match Matrix.inverse? m with
    | some inv => .ok inv
    | none => .error .singular
  let counts : Vector Rat r := inv * values.map (fun (z : Int) => (z : Rat))
  if !counts.toList.all (fun q => q.den == 1) then throw .nonintegral
  if !counts.toList.all (fun q => q.num ≥ 0) then throw .negative
  let den := ((List.finRange r).flatMap fun i =>
    (List.finRange r).map fun j => inv[(i, j)].den).foldl Nat.lcm 1
  let s : System r := {
    rows, columns, values
    counts := counts.map (·.num)
    inverse := Matrix.ofFn fun i j => inv[(i, j)].num * (den / inv[(i, j)].den : Nat)
    denominator := den }
  if s.check arity then return s else throw .system

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]

/-- Assemble one node using the same prepared domain for every moment.
No roots, root counts or guessed sign conditions are supplied by a caller. -/
def buildNode (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int)) :
    Except BuildError (Node E Ctx) := do
  if h : rows.length = columns.length then
    let es := rows.toArray.toVector
    let cs : Vector (List Int) rows.length := h ▸ columns.toArray.toVector
    let moments := es.map fun e => Sturm.certifyPrepared context domain (moment qs e)
    match solveSystem qs.length es cs (moments.map (·.value)) with
    | .error err => throw err
    | .ok s => return {
        context, head := domain.head, lower := domain.lower, upper := domain.upper
        queries := qs, size := rows.length, system := s, moments
        basis := Matrix.rankCert s.retainedMatrix }
  else throw .dimensions

/-- Balanced support reduction. Recursion decreases the actual query length;
there is no fuel limit and no full-ternary fallback at internal nodes. -/
def buildTree (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) : Except BuildError (Replay E Ctx) := do
  if h : qs.length ≤ 1 then
    return .leaf (← buildNode context domain qs (leafRows qs.length) (leafColumns qs.length))
  else
    let l ← buildTree context domain (qs.take (qs.length / 2))
    let r ← buildTree context domain (qs.drop (qs.length / 2))
    let n ← buildNode context domain qs (product l.node.rows r.node.rows)
      (product l.node.system.support r.node.system.support)
    return .split n l r
termination_by qs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

/-- A returned construction has passed the independent literal replay.
This is an executable acceptance guarantee, not root-sum soundness. -/
def buildPrepared [DecidableEq Ctx] (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) :
    Except BuildError {t : Replay E Ctx //
      t.check domain.sign context domain.head domain.lower domain.upper qs = true} := do
  let t ← buildTree context domain qs
  if h : t.check domain.sign context domain.head domain.lower domain.upper qs = true then
    return ⟨t, h⟩
  else throw .replay

end Hex.SignDet
