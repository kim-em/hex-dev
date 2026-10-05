/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroupMathlib.Kernel
public import HexPermGroup.Kernel.Certify
public meta import HexPermGroup.Kernel.Certify
public meta import HexPermGroupMathlib.Kernel
public import HexPermGroup.Tactic
public meta import HexPermGroup.Tactic
public meta import Lean

public section

/-! The Mathlib extension of the computational `perm_group` tactic. -/

namespace Hex.PermGroup.Mathlib.Tactic

open Lean Elab Tactic Meta
open Hex.PermGroup.Kernel Hex.PermGroup.Kernel.Tactic

/-- The elements of a set literal `{a, b, …}`, or of the coercion of a
`Finset` literal. -/
meta partial def setLitElems (s : Expr) : MetaM (Option (List Expr)) := do
  let s ← instantiateMVars s
  if s.isAppOfArity ``List.cons 3 then
    let some rest ← setLitElems (s.getArg! 2) | return none
    return some (s.getArg! 1 :: rest)
  if s.isAppOfArity ``List.nil 1 then
    return some []
  if s.isAppOfArity ``Insert.insert 5 then
    let some rest ← setLitElems (s.getArg! 4) | return none
    return some (s.getArg! 3 :: rest)
  if s.isAppOfArity ``Singleton.singleton 4 then
    return some [s.getArg! 3]
  if s.isAppOfArity ``EmptyCollection.emptyCollection 2 then
    return some []
  if s.isAppOfArity ``SetLike.coe 4 then
    -- `↑t` for a `Finset` literal `t`
    return ← setLitElems (s.getArg! 3)
  let pred := if s.isAppOfArity ``setOf 2 || s.isAppOfArity ``Set.ofPred 2 then
      s.getArg! 1 else s
  if let .lam _ _ body _ := pred then
    if body.isAppOfArity ``Membership.mem 5 && body.getArg! 4 == .bvar 0 &&
        !(body.getArg! 3).hasLooseBVars then
      return ← setLitElems (body.getArg! 3)
  let s' ← whnfR s
  if s' != s then return ← setLitElems s'
  -- A generating set given by a definition, such as `def gens : Set _ := {a, b}`.
  let some s' ← unfoldDefinition? s | return none
  setLitElems s'

/-- The degree `n` of a type `Equiv.Perm (Fin n)`, as a numeral. -/
meta def permDegree (ty : Expr) : MetaM Nat := do
  let ty ← instantiateMVars ty
  let ty' ← whnfR ty
  let some fin := (if ty.isAppOfArity ``Equiv.Perm 1 then some (ty.getArg! 0)
      else if ty'.isAppOfArity ``Equiv 2 then some (ty'.getArg! 0) else none)
    | throwError "perm_group: expected permutations of `Fin n`, got{indentExpr ty}"
  let fin ← whnfR fin
  unless fin.isAppOfArity ``Fin 1 do
    throwError "perm_group: expected permutations of `Fin n`, got{indentExpr ty}"
  let some n ← evalNat (fin.getArg! 0) |>.run
    | throwError "perm_group: the degree must be a numeral, got{indentExpr (fin.getArg! 0)}"
  return n

/-- The shape of a supported goal. -/
meta inductive GoalKind where
  | card (N : Nat)
  | mem (g : Expr)
  | notMem (g : Expr)
  | top

/-- `H` unfolded until it is `Subgroup.closure s`, so that a subgroup given by a
definition, such as `def M : Subgroup _ := Subgroup.closure {a, b}`, is
recognised. Definitions are unfolded one at a time, and `Subgroup.closure`
itself is never unfolded. -/
meta partial def unfoldToClosure? (H : Expr) (fuel : Nat := 32) : MetaM (Option Expr) := do
  let H ← whnfR (← instantiateMVars H)
  if H.isAppOfArity ``Subgroup.closure 3 then return some H
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let some H' ← unfoldDefinition? H | return none
    unfoldToClosure? H' fuel

/-- The generating set `s` when `H` is `Subgroup.closure s`, possibly behind
definitions. -/
meta def closureArg? (H : Expr) : MetaM (Option Expr) := do
  let some H' ← unfoldToClosure? H | return none
  return some (H'.getArg! 2)

/-- `s` with definitions unfolded until it is a set literal or a coerced
`Finset`, so that a generating set such as `def gens : Set _ := {a, b}` is
recognised. -/
meta partial def unfoldSetDefs (s : Expr) (fuel : Nat := 32) : MetaM Expr := do
  let s ← instantiateMVars s
  if s.isAppOfArity ``Insert.insert 5 || s.isAppOfArity ``Singleton.singleton 4 ||
      s.isAppOfArity ``EmptyCollection.emptyCollection 2 ||
      s.isAppOfArity ``SetLike.coe 4 || s.isAppOfArity ``setOf 2 ||
      s.isAppOfArity ``Set.ofPred 2 || s.isLambda then
    return s
  match fuel with
  | 0 => return s
  | fuel + 1 =>
    let some s' ← unfoldDefinition? s | return s
    unfoldSetDefs s' fuel

/-- The goal with every subgroup that unfolds to `Subgroup.closure s` replaced by
that closure, and `s` unfolded to a literal. It is definitionally equal to the
goal, and later steps rewrite `s` syntactically. -/
meta def unfoldClosures (goal : Expr) : MetaM Expr := do
  Meta.transform goal (pre := fun e => do
    let ty ← whnfR (← inferType e)
    unless ty.isAppOfArity ``Subgroup 2 do return .continue
    match ← unfoldToClosure? e with
    | some H =>
      let s ← unfoldSetDefs (H.getArg! 2)
      return .done (mkAppN H.getAppFn (H.getAppArgs.set! 2 s))
    | none => return .continue)

/-- The subgroup `H` when the type `T` is `↥H`, that is `{x // x ∈ H}`. -/
meta def coeSortArg? (T : Expr) : MetaM (Option Expr) := do
  let T ← whnfR (← instantiateMVars T)
  unless T.isAppOfArity ``Subtype 2 do return none
  let .lam _ _ body _ := T.getArg! 1 | return none
  unless body.isAppOfArity ``Membership.mem 5 do return none
  let H := body.getArg! 3
  if H.hasLooseBVars then return none
  return some H

/-- Match one of the four supported goals exactly, returning the generating set. -/
meta def readGoal? (goal : Expr) : MetaM (Option (Expr × GoalKind)) := do
  let goal ← instantiateMVars goal
  if goal.isAppOfArity ``Eq 3 then
    let lhs := goal.getArg! 1
    let rhs := goal.getArg! 2
    if lhs.isAppOfArity ``Nat.card 1 then
      let some H ← coeSortArg? (lhs.getArg! 0) | return none
      let some s ← closureArg? H | return none
      let some N ← (evalNat rhs).run
        | throwError "perm_group: the claimed order must be a numeral{indentExpr rhs}"
      return some (s, .card N)
    if rhs.isAppOfArity ``Top.top 2 then
      let some s ← closureArg? lhs | return none
      return some (s, .top)
    return none
  if goal.isAppOfArity ``Membership.mem 5 then
    let some s ← closureArg? (goal.getArg! 3) | return none
    return some (s, .mem (goal.getArg! 4))
  if goal.isAppOfArity ``Not 1 && (goal.getArg! 0).isAppOfArity ``Membership.mem 5 then
    let m := goal.getArg! 0
    let some s ← closureArg? (m.getArg! 3) | return none
    return some (s, .notMem (m.getArg! 4))
  return none

/-- A proof of `{x | x ∈ [g₁, …, gₖ]} = {g₁, …, gₖ}` built from the list lemmas,
without traversing the elements. -/
meta partial def setOfListEq (permTy : Expr) : List Expr → MetaM Expr
  | [] => mkAppOptM ``setOf_mem_nil #[permTy]
  | [g] => mkAppM ``setOf_mem_singleton #[g]
  | g :: g' :: rest => do
    let restE ← mkListLit permTy rest
    let step ← mkAppM ``setOf_mem_cons #[g, g', restE]
    let ih ← setOfListEq permTy (g' :: rest)
    let ins ← withLocalDeclD `t (← mkAppOptM ``Set #[permTy]) fun t => do
      mkLambdaFVars #[t] (← mkAppM ``Insert.insert #[g, t])
    mkEqTrans step (← mkCongrArg ins ih)

/-- Replace the generating set `s` in the goal by `{x | x ∈ gs}`. -/
meta def rewriteSet (mvarId : MVarId) (s gsList : Expr) (gens : List Expr) (permTy : Expr) :
    TacticM MVarId := do
  -- `{x | x ∈ gs}` in exactly the form the soundness statements use
  let clTy ← whnfR (← inferType (← mkAppM ``closure_ofEquiv #[gsList]))
  let target := (clTy.getArg! 2).getArg! 2
  if ← isDefEq target s then
    return mvarId
  let direct ← setOfListEq permTy gens
  let pf ← if ← isDefEq (← inferType direct) (← mkEq target s) then
      pure direct
    else
      -- a coerced `Finset` literal: identify it by rewriting
      let pf ← mkFreshExprMVar (← mkEq target s)
      let rem ← Term.withoutErrToSorry <| Tactic.run pf.mvarId! do
        evalTactic (← `(tactic| simp only [Hex.PermGroup.Kernel.setOf_mem_cons,
          Hex.PermGroup.Kernel.setOf_mem_singleton, Hex.PermGroup.Kernel.setOf_mem_nil,
          Finset.coe_insert, Finset.coe_singleton, Finset.coe_empty]))
      unless rem.isEmpty do
        throwError "perm_group: could not identify the generating set with a list"
      instantiateMVars pf
  let r ← mvarId.rewrite (← mvarId.getType) (← mkEqSymm pf)
  mvarId.replaceTargetEq r.eNew r.eqProof

/-- The elements of a set-literal syntax `{a, b, …}`, possibly under a type
ascription. -/
meta partial def setLitStx (stx : Syntax) : Option (Array Syntax) :=
  if stx.getKind == ``Lean.Parser.Term.typeAscription then setLitStx stx[1]
  else if stx.getKind == ``Lean.Parser.Term.paren then setLitStx stx[1]
  else if stx.getKind == `coeNotation then setLitStx stx[1]
  else if stx.getNumArgs == 3 && stx[0].isToken "{" && stx[2].isToken "}" then
    some stx[1].getSepArgs
  else none

/-- Preserve the optimized image-list packing route for Mathlib inputs. -/
meta def packTie (nE g : Expr) (x : Nat) (suffix : String) : TacticM Expr := do
  unless g.isAppOfArity ``Perm.ofEquiv 2 do
    return ← Hex.PermGroup.Kernel.Tactic.packTie nE g x suffix
  let e := g.getArg! 1
  if e.isAppOfArity ``permOfImages 2 then
    let l := e.getArg! 1
    if !(← checkedImages nE l) then
      return ← Hex.PermGroup.Kernel.Tactic.packTie nE g x suffix
    let hok ← addKernelEq (← auxName s!"{suffix}_images") (← mkAppM ``imagesOk #[nE, l])
      (mkConst ``Bool.true)
    let hpk ← addKernelEq (← auxName s!"{suffix}_pack") (← mkAppM ``packList #[nE, l])
      (mkNatLit x)
    return ← mkEqTrans (← mkAppM ``pack_ofEquiv_permOfImages #[hok]) hpk
  Hex.PermGroup.Kernel.Tactic.packTie nE g x suffix

/-- The element type of a set, including a predicate written as a raw lambda. -/
private meta def setElementType (s : Expr) : MetaM Expr := do
  let ty ← inferType s
  if ty.isAppOfArity ``Set 1 || ty.isAppOfArity ``Finset 1 then return ty.getArg! 0
  match ← whnfR ty with
  | .forallE _ dom body _ =>
    unless body == .sort .zero do
      throwError "perm_group: unexpected set type{indentExpr ty}"
    return dom
  | _ => throwError "perm_group: unexpected set type{indentExpr ty}"

/-- Translate Mathlib's goal, run the shared computational tactic and transport
its conclusion through the correspondence theorems. -/
@[perm_group_extension] public meta def extension : Hex.PermGroup.Kernel.Tactic.Extension where
  prove? cfg target := do
    let t ← unfoldClosures target
    let parsed ← readGoal? t
    let some (s, kind) := parsed | return none
    let some gens ← setLitElems s
      | throwError "perm_group: the generating set must be a set literal or a coerced Finset \
          literal{indentExpr s}"
    let permTy ← setElementType s
    let n ← permDegree permTy
    let nE := mkNatLit n
    let gs ← mkListLit permTy gens
    let converted ← gens.mapM fun g => mkAppOptM ``Perm.ofEquiv #[nE, g]
    let coreKind ← match kind with
      | .card N => pure (Hex.PermGroup.Kernel.Tactic.GoalKind.card N)
      | .top => pure (.card n.factorial)
      | .mem g => pure (.mem (← mkAppOptM ``Perm.ofEquiv #[nE, g]))
      | .notMem g => pure (.notMem (← mkAppOptM ``Perm.ofEquiv #[nE, g]))
    let core ← Hex.PermGroup.Kernel.Tactic.prove cfg n converted coreKind packTie
    let pf ← match kind with
      | .card _ => mkAppOptM ``card_of_hasOrder #[nE, gs, none, core]
      | .top => mkAppOptM ``eq_top_of_hasOrder #[nE, gs, core]
      | .mem g => mkAppOptM ``mem_of_generated #[nE, gs, g, core]
      | .notMem g => mkAppOptM ``not_mem_of_neg #[nE, gs, g, core]
    let goal ← mkFreshExprMVar t
    let rewritten ← rewriteSet goal.mvarId! s gs gens permTy
    rewritten.assign pf
    return some (← instantiateMVars goal)
  certificate? name s sStx := do
    let some elemStx := setLitStx sStx | return none
    let some gens ← setLitElems s | return none
    let permTy ← setElementType s
    let n ← permDegree permTy
    let converted ← gens.mapM fun g => mkAppOptM ``Perm.ofEquiv #[mkNatLit n, g]
    let rawSrc := (sStx.reprint.getD "").trimAscii.toString
    let sSrc := s!"({rawSrc} : Set (Equiv.Perm (Fin {n})))"
    let elemSrc := elemStx.toList.map fun e => (e.reprint.getD "").trimAscii.toString
    let gsSrc := "[" ++ ", ".intercalate elemSrc ++ "]"
    let arraySrc := s!"(({gsSrc} : List (Equiv.Perm (Fin {n}))).map Perm.ofEquiv).toArray"
    let out ← certificateSource name n converted
      (elemSrc.map fun g => s!"Perm.ofEquiv ({g} : Equiv.Perm (Fin {n}))") arraySrc
      (fun g => do
        if g.isAppOfArity ``Perm.ofEquiv 2 &&
            (g.getArg! 1).isAppOfArity ``permOfImages 2 then
          if ← checkedImages (mkNatLit n) ((g.getArg! 1).getArg! 1) then
            return some "pack_ofEquiv_permOfImages"
        return none)
    let imageLists ← converted.mapM fun g => Hex.PermGroup.Kernel.Tactic.evalImages n g
    let perms ← imageLists.mapM fun l => (parsePerm n l : MetaM (Perm n))
    let c ← match certify perms.toArray with
      | .ok c => pure c
      | .error msg => throwError "#perm_group_certificate: {msg}"
    let finsetLemmas := if sSrc.contains '↑' then
      match gens.length with
      | 0 => ", Finset.coe_empty"
      | 1 => ", Finset.coe_singleton"
      | _ => ", Finset.coe_insert, Finset.coe_singleton"
      else ""
    let setLemmas := match gens.length with
      | 0 => "setOf_mem_nil"
      | 1 => "setOf_mem_singleton"
      | _ => "setOf_mem_cons, setOf_mem_singleton"
    return some (out ++ s!"\nopen Hex.PermGroup Hex.PermGroup.Kernel in\n" ++
      s!"theorem {name}_card : Nat.card (Subgroup.closure {sSrc}) = {order c} := by\n" ++
      s!"  rw [show {sSrc} = \{x | x ∈ {gsSrc}} by\n" ++
      s!"    symm; simp only [{setLemmas}{finsetLemmas}]]\n" ++
      s!"  exact card_of_hasOrder {name}_hasOrder\n")

end Hex.PermGroup.Mathlib.Tactic
