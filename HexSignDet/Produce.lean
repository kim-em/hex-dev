/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Replay
public import HexSignDet.Tensor
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
@[expose] def solveSystem {r : Nat} (arity : Nat) (rows : Vector (List Nat) r)
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

/-- Solve using a supplied scaled integer inverse. This is the parent-node
path when child inverse witnesses have already been combined by a tensor
product. Exact divisibility is checked before extracting counts. -/
@[expose] def solveScaled {r : Nat} (arity : Nat) (rows : Vector (List Nat) r)
    (columns : Vector (List Int) r) (values : Vector Int r)
    (denominator : Int) (inverse : Matrix Int r r) : Except BuildError (System r) := do
  if denominator = 0 then throw .singular
  let numerators := inverse * values
  if !numerators.toList.all (fun z => z % denominator == 0) then throw .nonintegral
  let counts := numerators.map (· / denominator)
  if !counts.toList.all (· ≥ 0) then throw .negative
  let s : System r := {rows, columns, values, counts, inverse, denominator}
  if s.check arity then return s else throw .system

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
  [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]

/-- The shared positive-degree reduction guard, also used at the tree root. -/
@[expose] def useReduction (reduced : Bool) (domain : Sturm.PreparedDomain E) : Bool :=
  reduced && decide (0 < domain.head.natDegree)

/-- Retain supplied preprocessing or build it on a positive-degree reduced
path. Node construction and its companion statements use this same decision. -/
@[expose] def nodePreparation (reduced : Bool) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (preparation : Option (QueryReduction E)) :
    Option (QueryReduction E) :=
  if useReduction reduced domain then
    match preparation with
    | some r => some r
    | none => some (QueryReduction.build domain.sign domain.head qs)
  else none

/-- The actual per-row reduction, shared by construction and correspondence. -/
@[expose] def nodeReduction (reduced : Bool) (domain : Sturm.PreparedDomain E)
    (operands : List (DensePoly E)) (row : List Nat) : Option (Reduction E) :=
  if useReduction reduced domain then
    some (Reduction.build domain.sign domain.head operands row)
  else none

/-- Assemble one node using the same prepared domain for every moment.
No roots, root counts or guessed sign conditions are supplied by a caller. -/
@[expose] def buildNode (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool := true)
    (inverse : Option (Int × Matrix Int rows.length rows.length) := none)
    (preparation : Option (QueryReduction E) := none) :
    Except BuildError (Node E Ctx) := do
  if h : rows.length = columns.length then
    if !rows.all (fun e => decide (e.length = qs.length) && e.all (· ≤ 2)) then
      throw .system
    if !columns.all (fun c => decide (c.length = qs.length) &&
        c.all (fun x => decide (x = -1 ∨ x = 0 ∨ x = 1))) || !decide columns.Nodup then
      throw .system
    let es := rows.toArray.toVector
    let cs : Vector (List Int) rows.length := h ▸ columns.toArray.toVector
    let preparation := nodePreparation reduced domain qs preparation
    let operands := QueryReduction.operands qs preparation
    let reductions := es.map (nodeReduction reduced domain operands)
    let moments : Vector (TarskiCertificate E E Ctx) rows.length := Vector.ofFn fun i =>
      Sturm.certifyPrepared context domain (queryPoly operands es[i] reductions[i])
    let values := moments.map (fun (c : TarskiCertificate E E Ctx) => c.value)
    let solved := match inverse with
      | none => solveSystem qs.length es cs values
      | some (d, a) => solveScaled qs.length es cs values d a
    match solved with
    | .error err => throw err
    | .ok s => return {
        context, head := domain.head, lower := domain.lower, upper := domain.upper
        queries := qs, size := rows.length, system := s, moments, reductions, preparation
        basis := Matrix.rankCert s.retainedMatrix }
  else throw .dimensions

/-- The exact transported tensor inverse used when combining child supports. -/
@[expose] def parentInverse (l r : Node E Ctx) :
    Matrix Int (product l.rows r.rows).length (product l.rows r.rows).length :=
  have hd : (product l.rows r.rows).length = l.basis.rank * r.basis.rank := by
    rw [length_product]
    simp [Node.rows]
  hd.symm ▸ tensor l.basis.adj r.basis.adj

/-- Balanced support reduction. Recursion decreases the actual query length;
there is no fuel limit and no full-ternary fallback at internal nodes.
Call `buildTree` to preprocess each query once; a direct call with no supplied
preparation lets individual nodes construct their own reductions. -/
@[expose] def buildTreeFrom (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E)) :
    Except BuildError (Replay E Ctx) := do
  if h : qs.length ≤ 1 then
    return .leaf (← buildNode context domain qs (leafRows qs.length) (leafColumns qs.length)
      reduced none preparation)
  else
    let l ← buildTreeFrom context domain (qs.take (qs.length / 2)) reduced
      (preparation.map fun r => r.slice 0 (qs.length / 2))
    let r ← buildTreeFrom context domain (qs.drop (qs.length / 2)) reduced
      (preparation.map fun r => r.slice (qs.length / 2) (qs.length - qs.length / 2))
    let n ← buildNode context domain qs (product l.node.rows r.node.rows)
      (product l.node.system.support r.node.system.support) reduced
      (some (l.node.basis.denom * r.node.basis.denom, parentInverse l.node r.node)) preparation
    return .split n l r
termination_by qs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

/-- Prepare every original query once, then reuse its evidence throughout
the balanced support tree and across all moment rows. -/
@[expose] def buildTree (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool := true) : Except BuildError (Replay E Ctx) :=
  let preparation := nodePreparation reduced domain qs none
  buildTreeFrom context domain qs reduced preparation

/-- A returned construction has passed the independent literal replay.
This is an executable acceptance guarantee, not root-sum soundness. -/
@[expose] def buildPrepared [DecidableEq Ctx] (context : Ctx) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (reduced : Bool := true) :
    Except BuildError {t : Replay E Ctx //
      t.check domain.sign context domain.head domain.lower domain.upper qs = true} := do
  let t ← buildTree context domain qs reduced
  if h : t.check domain.sign context domain.head domain.lower domain.upper qs = true then
    return ⟨t, h⟩
  else throw .replay

end Hex.SignDet
