/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexRealFormulaMathlib.Reify.Arithmetic
public import Mathlib.Order.Interval.Set.Defs

public meta section

/-! Scope-aware proposition collection. All atom numerators share one ring batch. -/

namespace Hex.RealFormula.Reify

open Lean Meta

inductive BooleanOp where
  | and | or | imp | iff
  deriving BEq

/-- Open frontend syntax. Binder expressions remain live until the collector's
continuation has finished reflection and closed every proof binder. -/
inductive Tree where
  | atom (source : Expr) (scope : Array Expr) (cmp : Cmp) (view : Arithmetic) (id : Nat)
  | truth (value : Bool) (scope : Array Expr)
  | not (source : Expr) (p : Tree)
  | binary (source : Expr) (op : BooleanOp) (p q : Tree)
  | quant (source : Expr) (q : Quantifier) (binder : Expr) (id : Nat) (body : Tree)

def Tree.scope : Tree → Array Expr
  | .atom _ scope _ _ _ | .truth _ scope => scope
  | .not _ p | .binary _ _ p _ => p.scope
  | .quant _ _ _ _ body => body.scope.pop

def Tree.source : Tree → Expr
  | .atom e _ _ _ _ | .not e _ | .binary e _ _ _ | .quant e _ _ _ _ => e
  | .truth true _ => mkConst ``True
  | .truth false _ => mkConst ``False

/-- Expanded Boolean tree cost includes both copies introduced by biconditionals. -/
def Tree.nodeCount : Tree → Nat
  | .atom .. | .truth .. => 1
  | .not _ p | .quant _ _ _ _ p => 1 + p.nodeCount
  | .binary _ .iff p q => 5 + 2 * p.nodeCount + 2 * q.nodeCount
  | .binary _ .imp p q => 2 + p.nodeCount + q.nodeCount
  | .binary _ _ p q => 1 + p.nodeCount + q.nodeCount

/-- Source binder identifiers in normalized prefix order; repetitions are
distinct output binders created by biconditional expansion. -/
def Tree.prefix (neg : Bool) : Tree → Array (Nat × Quantifier)
  | .atom .. | .truth .. => #[]
  | .not _ p => p.prefix (!neg)
  | .quant _ q _ id p => #[(id, if neg then q.dual else q)] ++ p.prefix neg
  | .binary _ .imp p q => p.prefix (!neg) ++ q.prefix neg
  | .binary _ .iff p q =>
      p.prefix (!neg) ++ q.prefix neg ++ q.prefix (!neg) ++ p.prefix neg
  | .binary _ _ p q => p.prefix neg ++ q.prefix neg

private def withReal (name : Name) (k : Expr → ReifyM α) : ReifyM α := do
  let state ← get
  let outcome ← liftM <| withLocalDeclD name (mkConst ``Real) fun x =>
    ((k x).run state).run
  match outcome with
  | .error e => abort e
  | .ok (a, state) => set state; return a

private def comparison? (e : Expr) : Option (Cmp × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Eq, #[ty, a, b]) => some (.eq, ty, a, b)
  | (``Ne, #[ty, a, b]) => some (.ne, ty, a, b)
  | (``LT.lt, #[ty, _, a, b]) => some (.lt, ty, a, b)
  | (``LE.le, #[ty, _, a, b]) => some (.le, ty, a, b)
  | (``GT.gt, #[ty, _, a, b]) => some (.gt, ty, a, b)
  | (``GE.ge, #[ty, _, a, b]) => some (.ge, ty, a, b)
  | _ => none

/-- Continuation-based collection keeps sibling binders distinct and in scope
through the single batch call. No local constant is reused across invocations. -/
partial def collect (source : Expr) (scope : Array Expr) (k : Tree → ReifyM α) : ReifyM α := do
  let accept (tree : Tree) : ReifyM α := do
    let size := (← get).formulaSize + 1
    formulaBudget size
    modify fun s => { s with formulaSize := size }
    k tree
  let e := source.consumeMData
  if let some (cmp, ty, a, b) := comparison? e then
    unless ← isDefEq ty (mkConst ``Real) do
      abort (.unsupported source "comparisons must have real operands")
    let view ← arithmetic scope (realSub a b)
    accountProof view.proof
    let id := (← get).inputs.size
    modify fun s => { s with inputs := s.inputs.push view.numerator }
    return ← accept (.atom source scope cmp view id)
  match e.getAppFnArgs with
  | (``True, #[]) => accept (.truth true scope)
  | (``False, #[]) => accept (.truth false scope)
  | (``Not, #[p]) => collect p scope fun p => accept (.not source p)
  | (``And, #[p, q]) => collect p scope fun p => collect q scope fun q => accept (.binary source .and p q)
  | (``Or, #[p, q]) => collect p scope fun p => collect q scope fun q => accept (.binary source .or p q)
  | (``Iff, #[p, q]) => collect p scope fun p => collect q scope fun q => accept (.binary source .iff p q)
  | (``Membership.mem, #[_, _, _, set, _]) =>
    if let some name := set.getAppFn.constName? then
      if [``Set.Icc, ``Set.Ico, ``Set.Ioc, ``Set.Ioo, ``Set.Ici, ``Set.Iic,
          ``Set.Ioi, ``Set.Iio].contains name then
        collect (← whnf e) scope k
      else abort (.unsupported source "only polynomial interval bounds are supported")
    else abort (.unsupported source "only polynomial interval bounds are supported")
  | (``Exists, #[ty, predicate]) =>
    unless ← isDefEq ty (mkConst ``Real) do
      abort (.unsupported source "quantifier domain must be Real")
    let .lam name _ body _ := predicate.consumeMData
      | abort (.unsupported source "higher-order predicates are unsupported")
    withReal name fun x => do
      let id := (← get).binders.size
      modify fun s => { s with binders := s.binders.push x }
      collect (body.instantiate1 x) (scope.push x) fun p => accept (.quant source .existsReal x id p)
  | _ =>
    match e with
    | .forallE name domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          abort (.unsupported source "dependent implication is unsupported")
        collect domain scope fun p => collect (body.instantiate1 (mkConst ``True.intro)) scope
          fun q => accept (.binary source .imp p q)
      else
        unless ← isDefEq domain (mkConst ``Real) do
          abort (.unsupported source "quantifier domain must be Real; dependent types are unsupported")
        withReal name fun x => do
          let id := (← get).binders.size
          modify fun s => { s with binders := s.binders.push x }
          collect (body.instantiate1 x) (scope.push x) fun p => accept (.quant source .forallReal x id p)
    | .letE _ _ value body _ => collect (body.instantiate1 value) scope k
    | _ => abort (.unsupported source "unsupported real proposition")

end Hex.RealFormula.Reify
