/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroupMathlib.Generated
public meta import HexPermGroupMathlib.Generated
public import HexPermGroup.Tactic
public meta import HexPermGroup.Tactic
public meta import Lean

public section

/-! The Mathlib extension of the computational `perm_group` tactic. -/

namespace Hex.PermGroup.Mathlib.Tactic

open Lean Elab Meta
open _root_.Lean.Elab.Tactic _root_.Hex.PermGroup.Tactic

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

/-- One normalized presentation, including the equality to the original set. -/
private meta structure Presentation where
  degree : Nat
  elements : List Expr
  list : Expr
  equality : Expr
  finset : Bool

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

/-- Normalize once, producing a proof that the original set equals list membership. -/
private meta def presentation (s : Expr) : TermElabM Presentation := do
  let ty ← inferType s
  let s ← if ty.isAppOfArity ``Finset 1 then mkAppM ``SetLike.coe #[s] else pure s
  let some elements ← setLitElems s
    | throwError "perm_group: the generating set must be a set literal or a coerced Finset \
        literal{indentExpr s}"
  let permTy ← setElementType s
  let degree ← permDegree permTy
  let list ← mkListLit permTy elements
  let clTy ← whnfR (← inferType (← mkAppM ``closure_ofEquiv #[list]))
  let canonical := (clTy.getArg! 2).getArg! 2
  let equality ← if ← isDefEq s canonical then mkEqRefl s else do
    let direct ← setOfListEq permTy elements
    if ← isDefEq (← inferType direct) (← mkEq canonical s) then
      mkEqSymm direct
    else
      let proof ← mkFreshExprMVar (← mkEq canonical s)
      let setLemmas := match elements.length with
        | 0 => #[``Hex.PermGroup.setOf_mem_nil]
        | 1 => #[``Hex.PermGroup.setOf_mem_singleton]
        | _ => #[``Hex.PermGroup.setOf_mem_cons, ``Hex.PermGroup.setOf_mem_singleton]
      let finsetLemmas := match elements.length with
        | 0 => #[``Finset.coe_empty]
        | 1 => #[``Finset.coe_singleton]
        | _ => #[``Finset.coe_insert, ``Finset.coe_singleton]
      let args ← (setLemmas ++ finsetLemmas).mapM fun name =>
        `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
      let rem ← Term.withoutErrToSorry <| Tactic.run proof.mvarId! do
        evalTactic (← `(tactic| simp only [$args,*]))
      unless rem.isEmpty do
        throwError "perm_group: could not identify the generating set with a list{indentExpr (← rem.head!.getType)}"
      mkEqSymm (← instantiateMVars proof)
  let reduced ← whnfR s
  let finset := (s.find? fun e => e.isAppOfArity ``Finset 1).isSome ||
    (reduced.find? fun e => e.isAppOfArity ``Finset 1).isSome
  return { degree, elements, list, equality, finset }

/-- Compatibility normalization entry point for graph automorphism consumers. -/
meta def rewriteSet (mvarId : MVarId) (s _gsList : Expr) (_gens : List Expr) (_permTy : Expr) :
    TacticM MVarId := do
  let p ← presentation s
  let r ← mvarId.rewrite (← mvarId.getType) p.equality
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

/-- Find a converted Hex expression without unfolding the conversion itself. -/
private meta partial def toHex? (e : Expr) (fuel : Nat := 32) : MetaM (Option Expr) := do
  if e.isAppOfArity ``Perm.toEquiv 2 then return some (e.getArg! 1)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let some e' ← unfoldDefinition? e | return none
    toHex? e' fuel

/-- Supply only a round-trip equality; Hex owns the optimized packing proof. -/
private meta def input (n : Nat) (e : Expr) : MetaM Input := do
  let term ← mkAppOptM ``Perm.ofEquiv #[mkNatLit n, e]
  let canonical? ← (← toHex? e).mapM fun canonical => do
    return (canonical, ← mkAppM ``Perm.ofEquiv_toEquiv #[canonical])
  return { term, canonical? }

/-- Translate Mathlib's goal, run the shared computational tactic and transport
its conclusion through the correspondence theorems. -/
@[perm_group_extension] public meta def extension : Extension where
  prove? cfg target := do
    let t ← unfoldClosures target
    let some (s, kind) ← readGoal? t | return none
    let p ← presentation s
    let inputs ← p.elements.mapM fun e => input p.degree e
    let prepared ← prepare cfg p.degree inputs
    let request ← match kind with
      | .card N => pure (Goal.card N)
      | .top => pure Goal.all
      | .mem g => pure (.mem (← input p.degree g))
      | .notMem g => pure (.notMem (← input p.degree g))
    let core ← replay prepared request
    let pf ← match kind with
      | .card _ => mkAppOptM ``card_of_hasOrder #[mkNatLit p.degree, p.list, none, core]
      | .top => mkAppOptM ``eq_top_of_all #[mkNatLit p.degree, p.list, core]
      | .mem g => mkAppOptM ``mem_of_generated #[mkNatLit p.degree, p.list, g, core]
      | .notMem g => mkAppOptM ``not_mem_of_neg #[mkNatLit p.degree, p.list, g, core]
    let predicate := mkLambda `generators .default (← inferType s) (← kabstract t s)
    let goalEq ← mkCongrArg predicate p.equality
    return some (← mkAppM ``Eq.mpr #[goalEq, pf])
  certificate? name s sStx := do
    let some elemStx := setLitStx sStx | return none
    let p ← presentation s
    let prepared ← prepare {} p.degree (← p.elements.mapM fun e => input p.degree e)
    let n := p.degree
    let rawSrc := (sStx.reprint.getD "").trimAscii.toString
    let sSrc := s!"({rawSrc} : Set (Equiv.Perm (Fin {n})))"
    let elemSrc := elemStx.toList.map fun e => (e.reprint.getD "").trimAscii.toString
    let gsSrc := "[" ++ ", ".intercalate elemSrc ++ "]"
    let arraySrc := s!"(({gsSrc} : List (Equiv.Perm (Fin {n}))).map Perm.ofEquiv).toArray"
    let out ← render name prepared
      (elemSrc.map fun g => s!"Perm.ofEquiv ({g} : Equiv.Perm (Fin {n}))") arraySrc
    let finsetLemmas := if p.finset then
      match p.elements.length with
      | 0 => ", Finset.coe_empty"
      | 1 => ", Finset.coe_singleton"
      | _ => ", Finset.coe_insert, Finset.coe_singleton"
      else ""
    let setLemmas := match p.elements.length with
      | 0 => "setOf_mem_nil"
      | 1 => "setOf_mem_singleton"
      | _ => "setOf_mem_cons, setOf_mem_singleton"
    return some (out ++ s!"\nopen Hex.PermGroup in\n" ++
      s!"theorem {name}_card : Nat.card (Subgroup.closure {sSrc}) = {prepared.order} := by\n" ++
      s!"  rw [show {sSrc} = \{x | x ∈ {gsSrc}} by\n" ++
      s!"    symm; simp only [{setLemmas}{finsetLemmas}]]\n" ++
      s!"  exact card_of_hasOrder {name}_hasOrder\n")

end Hex.PermGroup.Mathlib.Tactic
