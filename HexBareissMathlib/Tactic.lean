/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBareissMathlib.Kernel
public import HexBareissMathlib.Kernel
public meta import Mathlib.Tactic.NormDet
public import Mathlib.Tactic.NormDet
public meta import Lean

public meta section

/-!
The `det` tactic on Mathlib matrices: closes `A.det = d` (and `d = A.det`)
for a closed integer or rational matrix literal `A` in one of the four
syntaxes of `HexMatrixMathlib.Literal` (`!![…]`, `Matrix.of ![…]`,
`fun i j => …`, `Matrix.ofArray xs h`), possibly behind definitions; the
term form `det% A` returns the certified value as a `Certified` record; and
the simproc `hex_norm_det` rewrites `Matrix.det A` to its value, falling
back to Mathlib's `norm_det` (symbolic entries, other carriers) when the
Hex frontend declines, so the two are one simp set.

Compiled code evaluates the entries with `norm_num`, runs the fraction-free
elimination `detWitnessOfLists` and builds a `DetWitness`; the proof is
`det_eq_of_checkList'` applied to the identification of the literal with
the row list `L` of its entries' numerals (`rfl` for a vector chain, one
kernel `decide` on `entriesEq` otherwise) and to one kernel `decide` on
`checkDetList`.  A rational matrix is scaled row by row to an integer one
and proved by `det_eq_of_checkRat'`, whose kernel check `checkDetRat` also
confirms the scaling and the value.  The whole proof is added as an
auxiliary theorem, checked synchronously, so the kernel checks it exactly
once and a rejection is reported by the tactic.

Outcomes follow the matrix-tactic protocol: a goal that is not a
determinant equation is not applicable; a matrix that is not a closed
integer or rational literal is declined (and the `det` tactic then runs the
fallback simp set); a false target is reported with the certified value
before any proof is built; a certificate the kernel rejects is a failure.
-/

namespace HexMatrixMathlib.Det

open Lean Meta Elab Hex.Matrix HexMatrixMathlib.Literal

deriving instance ToExpr for Hex.Matrix.DetWitness

/-- The outcome of an attempt, per the matrix-tactic protocol; a failure
throws. -/
inductive Outcome (α : Type) where
  /-- The goal or input is not in the fragment; the next handler may try. -/
  | notApplicable
  /-- In the fragment, but a capability is missing; the message names it. -/
  | declined (msg : MessageData)
  /-- A value and a proof. -/
  | success (a : α)

/-- Recognize a determinant target: the matrix, the other side, and whether
the determinant is on the right. -/
def detTarget? (target : Expr) : Option (Expr × Expr × Bool) :=
  let isDet (e : Expr) := e.getAppFn.isConstOf ``Matrix.det
  match target.getAppFnArgs with
  | (``Eq, #[_, a, b]) =>
      if isDet a then some (a.appArg!, b, false)
      else if isDet b then some (b.appArg!, a, true)
      else none
  | _ => none

/-- The certificate of a square literal: the witness, the row list of the
integer matrix it certifies, and for a rational literal the rational row
list and the row scales. -/
structure Cert where
  /-- The recognized literal. -/
  lit : Recognized
  /-- The witness of the integer matrix. -/
  witness : DetWitness
  /-- The integer rows. -/
  rows : Array (Array Int)
  /-- The rational rows and the positive scale of each, for a rational literal. -/
  rat : Option (Array (Array Rat) × Array Nat)

/-- The certified determinant as a rational. -/
def Cert.value (c : Cert) : Rat :=
  match c.rat with
  | none => c.witness.value
  | some (_, s) => (c.witness.value : Rat) / (s.foldl (· * ·) 1 : Nat)

/-- Recognize a closed square integer or rational literal and certify it. -/
def certify (A : Expr) : MetaM (Outcome Cert) := do
  if A.hasFVar || A.hasExprMVar then
    return .declined m!"the matrix{indentExpr A}\nmust be a closed term"
  let some lit ← literal? A |
    return .declined m!"the matrix is not a closed `!![…]`, `Matrix.of ![…]`, `fun i j => …` or `Matrix.ofArray` literal{indentExpr A}"
  unless lit.n = lit.m do
    return .declined m!"the matrix is {lit.n} × {lit.m}, not square"
  let isInt := lit.carrier.isConstOf ``Int
  unless isInt || lit.carrier.isConstOf ``Rat do
    return .declined m!"only integer and rational matrices are supported; the entry type is{indentExpr lit.carrier}"
  let values ← try evalEntries lit catch e => return .declined e.toMessageData
  let (rows, rat) ←
    if isInt then
      pure (values.map (·.map (·.num)), none)
    else
      -- clear each row's denominators by their least common multiple
      let scales := values.map fun row => row.foldl (fun l q => Nat.lcm l q.den) 1
      let rows := values.zipWith (fun row s => row.map fun q => (q * (s : Rat)).num) scales
      pure (rows, some (values, scales))
  match detWitnessOfLists lit.n (rows.toList.map (·.toList)) with
  | .ok w => return .success ⟨lit, w, rows, rat⟩
  | .error e => return .declined m!"the producer found no witness: {e}"

/-- Prove `Matrix.det A = v` for the certificate's value `v`, returning the
value and the proof.  The proof is checked synchronously as an auxiliary
theorem; a rejection is diagnosed. -/
def prove (A : Expr) (c : Cert) : MetaM (Expr × Expr) := do
  let nE := mkNatLit c.lit.n
  let w := toExpr c.witness
  let int := mkConst ``Int
  let B ← rowList int (c.rows.map (·.map toExpr))
  let (value, ofL, check, proof) ← match c.rat with
    | none =>
        let value := toExpr c.witness.value
        let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[nE, nE, B]
        let hA ← identification c.lit A B
        let check ← mkEq (← mkAppM ``Hex.Matrix.checkDetList #[nE, B, w]) (mkConst ``Bool.true)
        let hcheck ← decideProof check
        let eq ← mkAppM ``HexMatrixMathlib.det_eq_of_checkList' #[A, B, w, hA, hcheck]
        -- `DetWitness.value w` reduces to the numeral
        let hvalue ← mkExpectedTypeHint (← mkEqRefl value)
          (← mkEq (← mkAppM ``Hex.Matrix.DetWitness.value #[w]) value)
        pure (value, ofL, check, ← mkEqTrans eq hvalue)
    | some (rat, scales) =>
        let value := toExpr c.value
        let L ← rowList (mkConst ``Rat) (rat.map (·.map toExpr))
        let s ← mkListLit (mkConst ``Nat) (scales.toList.map toExpr)
        let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[nE, nE, L]
        let hA ← identification c.lit A L
        let check ← mkEq (← mkAppM ``Hex.Matrix.checkDetRat #[nE, L, s, B, w, value])
          (mkConst ``Bool.true)
        let hcheck ← decideProof check
        pure (value, ofL, check,
          ← mkAppM ``HexMatrixMathlib.det_eq_of_checkRat' #[A, L, s, B, w, value, hA, hcheck])
  let target ← mkEq (← mkAppM ``Matrix.det #[A]) value
  -- check synchronously, so that a rejection is reported here, not later
  try
    let proof ← withOptions (Lean.Elab.async.set · false) do mkAuxTheorem target proof
    return (value, proof)
  catch e =>
    throw (← diagnose check A ofL e)
where
  /-- Diagnose a proof the kernel rejected: evaluate the certificate check
  with the kernel and test the identification of the literal with its row
  list, reporting the first that fails. -/
  diagnose (check A ofL : Expr) (e : Exception) : MetaM Exception := do
    let env ← getEnv
    let lctx ← getLCtx
    match Kernel.whnf env lctx (← mkDecide check) with
    | .ok r =>
        if r.isConstOf ``Bool.false then
          return .error e.getRef
            m!"det: the producer's certificate fails the kernel check (a producer bug){indentExpr check}"
        unless r.isConstOf ``Bool.true do
          return .error e.getRef m!"det: the kernel check got stuck{indentExpr check}"
    | .error _ => return .error e.getRef m!"det: the kernel check got stuck{indentExpr check}"
    match Kernel.isDefEq env lctx A ofL with
    | .ok true => pure ()
    | _ =>
        return .error e.getRef
          m!"det: the entries of the matrix do not reduce to their numerals in the kernel{indentExpr A}"
    return .error e.getRef m!"det: the kernel rejected the proof: {e.toMessageData}"

/-- Prove a determinant target in either orientation. -/
def proveGoal (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let some (A, rhs, reverse) := detTarget? target | return .notApplicable
  let c ← match ← certify A with
    | .success c => pure c
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
  if rhs.hasFVar || rhs.hasExprMVar then
    return .declined m!"the value{indentExpr rhs}\nmust be a closed term"
  -- a value that evaluates is compared here, for a clear message on a false target
  if let some v ← (try some <$> evalEntry rhs catch _ => pure none) then
    unless v = c.value do
      throwError "det: the target is false: the determinant is {c.value}"
  let (value, proof) ← prove A c
  -- the equality with the stated value, decided by the kernel as well
  let hbound ← decideProof (← mkEq value rhs)
  let proof ← mkEqTrans proof hbound
  return .success (← if reverse then mkEqSymm proof else pure proof)

/-- The `det% A` record: `Certified Matrix.det A`. -/
def certified (A : Expr) : MetaM (Outcome Expr) := do
  let c ← match ← certify A with
    | .success c => pure c
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
  let (value, proof) ← prove A c
  let some (_, lhs, _) := (← inferType proof).eq? |
    throwError "det: internal error: the proof is not an equality"
  return .success (← mkAppOptM ``HexMatrixMathlib.Certified.mk
    #[none, none, some lhs.appFn!, some A, some value, some proof])

/-- `det% A` computes the determinant of a closed integer or rational matrix
literal `A` and returns a `HexMatrixMathlib.Certified Matrix.det A` record
with its value and proof.  The `!![…]` notations are given an integer entry
expectation. -/
syntax (name := detTerm) "det%" term:max : term

@[term_elab detTerm]
def elabDetTerm : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(det% $t) =>
      let A ← elabArgument t
      match ← certified A with
      | .success r => Term.ensureHasType expectedType? r
      | .notApplicable => throwError "det: not a Mathlib matrix{indentExpr A}"
      | .declined msg => throwError "det: declined: {msg}"
  | _ => throwUnsupportedSyntax

/-- Rewrite `Matrix.det A` to its certified value when the Hex frontend
applies; `none` when it declines. -/
def normDet? (e : Expr) : MetaM (Option Simp.Result) := do
  let e ← instantiateMVars e
  unless e.getAppFn.isConstOf ``Matrix.det do return none
  match ← certify e.appArg! with
  | .success c =>
      let (value, proof) ← prove e.appArg! c
      return some { expr := value, proof? := some proof }
  | .notApplicable | .declined _ => return none

end HexMatrixMathlib.Det

open Lean Meta in
/-- The `hex_norm_det` simproc rewrites the determinant of a closed integer or
rational matrix literal to its value through the Hex certificate, and falls
back to Mathlib's `norm_det` when the Hex frontend declines (symbolic
entries, other carriers); a certificate the kernel rejects is an error, not
a fallback. -/
simproc_decl hex_norm_det (Matrix.det _) := fun e => do
  match ← HexMatrixMathlib.Det.normDet? e with
  | some r => return .done r
  | none => norm_det e

namespace HexMatrixMathlib.Det

open Lean Elab

/-- `det` closes `A.det = d` and `d = A.det` for a closed integer or rational
matrix literal `A`, with the kernel checking a determinant certificate; an
input outside that fragment is handed to the simp set `hex_norm_det`, whose
fallback is Mathlib's `norm_det`.  The keyword is non-reserved, so `det`
stays usable as an identifier. -/
syntax (name := detTac) &"det" : tactic

@[tactic detTac]
def evalDetTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← proveGoal (← Tactic.getMainTarget) with
  | .success proof => Tactic.closeMainGoal `det proof
  | .notApplicable =>
      throwError "det: the goal is not `A.det = d` for a Mathlib matrix `A`"
  | .declined msg =>
      try Tactic.evalTactic (← `(tactic| simp only [hex_norm_det]))
      catch _ => throwError "det: declined: {msg}"

end HexMatrixMathlib.Det
