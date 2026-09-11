/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTactic.Protocol
public import HexMatrixTactic.Protocol

public section

/-!
Entry models: the executable value type behind a closed carrier, its
arithmetic, compiled evaluation of a closed matrix, and quotation of values
back into the carrier.  Lookup is by the exact carrier expression; discovery
and quotation are untrusted, and every emitted proof re-checks the quoted
values in the kernel.

The numeric models are `Int` (exact quotient `HexArith.Int.exactDiv`) and
`Rat` (exact quotient `Hex.exactDiv`, the field division); both offer the
Bareiss determinant and the domain rank of `HexRank`.  Matrices are read
through the public `rows` accessor and quoted through the public `ofRows`
constructor; the private buffer is never touched.
-/

namespace Hex.MatrixTactic

open Lean Meta

private meta unsafe def evalMatrixUnsafe (V : Type) (n m : Nat) (ty e : Expr) :
    MetaM (Except String (Hex.Matrix V n m)) := do
  try
    return .ok (← evalExpr (Hex.Matrix V n m) ty e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalMatrixUnsafe]
private meta opaque evalMatrixCore (V : Type) (n m : Nat) (ty e : Expr) :
    MetaM (Except String (Hex.Matrix V n m))

/-- Evaluate a closed `Hex.Matrix` expression with compiled code and quote the
result through the public constructor.  Returns the value and its literal; the
literal is only discovery data, every check the kernel replays on it is tied
back to the original expression by a kernel-checked step. -/
public meta def evalMatrix (V : Type) (op : String) (carrier : Expr)
    (reify : V → MetaM Expr) (n m : Nat) (e : Expr) :
    MetaM (Hex.Matrix V n m × Expr) := do
  let e ← instantiateMVars e
  checkClosed op "matrix" e
  match ← evalMatrixCore V n m (matrixType carrier n m) e with
  | .error msg =>
      throwError "{op}: failed to evaluate the matrix with compiled code{indentExpr e}\n{msg}"
  | .ok value =>
      let rows ← (entryRows value).mapM (·.mapM reify)
      return (value, ← matrixLit carrier n m rows)

/-- A closed `n × m` matrix evaluated through a model: its literal and the
producers the model offers on it, each run on demand. -/
public meta structure Input (n m : Nat) where
  /-- The original matrix expression. -/
  expr : Expr
  /-- The reified literal, built through `ofRows` from the evaluated entries. -/
  literal : Expr
  /-- The reified Bareiss determinant, when the model has an exact quotient. -/
  bareiss? : Option (n = m → MetaM Expr)
  /-- The domain rank `rankWith quot`, when the model has an exact quotient. -/
  domainRank? : Option (MetaM Nat)
  /-- The field rank `rowReduce_rank`, when the model is a field. -/
  fieldRank? : Option (MetaM Nat)
  /-- The reified two-sided rank certificate `rankCertWith quot`, when the
  model has an exact quotient. -/
  rankCert? : Option (MetaM Expr)

/-- A computation model for one closed carrier. -/
public meta structure Model where
  /-- The carrier name used in diagnostics. -/
  name : String
  /-- The carrier expression. -/
  carrier : Expr
  /-- The exact quotient function, when the carrier has a certified one. -/
  quot? : Option Expr
  /-- Whether the carrier is a field with kernel-evaluable arithmetic. -/
  isField : Bool
  /-- Compiled evaluation of a closed matrix of the given shape. -/
  evalInput : (op : String) → (n m : Nat) → Expr → MetaM (Input n m)

/-- Reify a rank certificate: `⟨rank, rows, cols, denom, adj⟩` with literal
index vectors, a quoted denominator and a matrix literal. -/
private meta def reifyRankCert {V : Type} (carrier : Expr) (reify : V → MetaM Expr)
    {n m : Nat} (c : Hex.Matrix.RankCert V n m) : MetaM Expr := do
  let finType (k : Nat) := mkApp (mkConst ``Fin) (mkNatLit k)
  let rows ← vectorLit (finType n) c.rank (← c.rows.toList.mapM fun i => finLit n i.val)
  let cols ← vectorLit (finType m) c.rank (← c.cols.toList.mapM fun j => finLit m j.val)
  let denom ← reify c.denom
  let adj ← matrixLit carrier c.rank c.rank (← (entryRows c.adj).mapM (·.mapM reify))
  mkAppOptM ``Hex.Matrix.RankCert.mk
    #[some carrier, some (mkNatLit n), some (mkNatLit m), some (mkNatLit c.rank), some rows,
      some cols, some denom, some adj]

/-- Package an executable value type and its arithmetic into a model. -/
public meta def Model.ofType (V : Type) [Zero V] [One V] [Neg V] [Sub V] [Mul V]
    [DecidableEq V] (name : String) (carrier : Expr) (reify : V → MetaM Expr)
    (quot? : Option (Expr × (V → V → V))) (field? : Option (Lean.Grind.Field V)) : Model where
  name := name
  carrier := carrier
  quot? := quot?.map (·.1)
  isField := field?.isSome
  evalInput op n m e := do
    let (value, literal) ← evalMatrix V op carrier reify n m e
    return {
      expr := e
      literal := literal
      bareiss? := quot?.map fun (_, quot) h =>
        reify (Hex.Matrix.bareissWith quot (h ▸ value))
      domainRank? := quot?.map fun (_, quot) => pure (Hex.Matrix.rankWith quot value)
      fieldRank? := field?.map fun field =>
        pure (@Hex.Matrix.rowReduce_rank V n m field _ value)
      rankCert? := quot?.map fun (_, quot) =>
        reifyRankCert carrier reify (Hex.Matrix.rankCertWith quot value) }

/-- The integer model. -/
public meta def intModel : Model :=
  Model.ofType Int "Int" (mkConst ``Int) (fun z => pure (toExpr z))
    (some (mkConst ``HexArith.Int.exactDiv, HexArith.Int.exactDiv)) none

/-- Quote a rational as `num / den`, or as an integer numeral when `den = 1`. -/
private meta def ratLit (q : Rat) : MetaM Expr := do
  let rat := mkConst ``Rat
  let numeral ← mkNumeral rat q.num.natAbs
  let num ← if q.num < 0 then mkAppM ``Neg.neg #[numeral] else pure numeral
  if q.den = 1 then return num
  mkAppM ``HDiv.hDiv #[num, ← mkNumeral rat q.den]

/-- The rational model: a field whose exact quotient is `Hex.exactDiv`, so the
Bareiss determinant and the domain rank replay in the kernel.  The field
row-reduction producer `rowReduce` is offered for `rowReduce_rank` goals, but
its body is not kernel-visible from a `module` file. -/
public meta def ratModel : MetaM Model := do
  let quot ← mkAppOptM ``Hex.exactDiv #[some (mkConst ``Rat), none, none, none]
  return Model.ofType Rat "Rat" (mkConst ``Rat) ratLit (some (quot, Hex.exactDiv))
    (some inferInstance)

/-- Select the model for a carrier expression, or `none` when no numeric model
matches.  Matching is on the exact carrier constant. -/
public meta def modelFor? (R : Expr) : MetaM (Option Model) := do
  let R ← whnfR R
  if R.isConstOf ``Int then return some intModel
  if R.isConstOf ``Rat then return some (← ratModel)
  return none

/-- Elaborate a matrix argument.  A raw `#m[...]` literal is given an integer
coefficient expectation so its numerals do not default to `Nat`; the two
dimensions stay independent. -/
public meta def elabMatrixArgument (t : Syntax) : Elab.Term.TermElabM Expr := do
  let e ←
    if t.getKind == ``Hex.Matrix.matrixLiteral then
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let m ← mkFreshExprMVar (mkConst ``Nat)
      let expected := mkApp3 (mkConst ``Hex.Matrix [Level.zero]) (mkConst ``Int) n m
      Elab.Term.elabTerm t (some expected)
    else
      Elab.Term.elabTerm t none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

end Hex.MatrixTactic
