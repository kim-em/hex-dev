/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBareissMathlib.Kernel
public import HexBareissMathlib.Kernel
public meta import Lean

public meta section

/-!
The `det` tactic on Mathlib matrices: closes `A.det = d` (and `d = A.det`)
for a closed integer or rational matrix literal `A` in one of the four
syntaxes of `HexMatrixMathlib.Literal` (`!![…]`, `Matrix.of ![…]`,
`fun i j => …`, `Matrix.ofArray xs h`), possibly behind definitions; the
term form `det% A` returns the certified value as a `Certified` record; and
the simproc `Hex.norm_det` rewrites `Matrix.det A` using a Hex certificate.
It leaves unsupported inputs unchanged; Mathlib determinant tactics are never
invoked implicitly.

Compiled code evaluates the entries with `norm_num`, runs the fraction-free
elimination `detWitnessOfLists` and builds a `DetWitness`; the proof is
`det_eq_of_checkList'` applied to the identification of the literal with
the row list `L` of its entries' numerals (`rfl` for a vector chain, one
kernel `decide` on `entriesEq` otherwise) and to one kernel `decide` on
`checkDetList`.  A rational matrix is scaled row by row to an integer one
and proved by `det_eq_of_checkRat'`, whose kernel check `checkDetRat` also
confirms the scaling and the value.  The whole proof of the goal is added
as an auxiliary lemma on the closed target (`addClosedProof`), checked
synchronously, so the kernel checks it exactly once, with no elaborator
type check first, and a rejection is reported by the tactic.

Outcomes follow the matrix-tactic protocol: a goal that is not a
determinant equation, a matrix that is not a closed integer or rational
literal, or an open value is not applicable and delegates to the next
handler. The last-resort handler may normalize a closed numeric determinant
using the Hex certificate even when the target value is open. A closed value
that is not evaluable similarly permits this Hex-only normalization; a false
target is reported with the certified value before any proof is built; a
producer whose witness fails its own check, or a certificate the kernel
rejects, is a failure, never a fallback.
-/

namespace HexMatrixMathlib.Det

open Lean Meta Elab Hex.Matrix HexMatrixMathlib.Literal

deriving instance ToExpr for Hex.Matrix.DetWitness

/-- The outcome of an attempt, per the matrix-tactic protocol; a failure
throws. -/
inductive Outcome (α : Type) where
  /-- The goal or input is not in the fragment; the next handler may try. -/
  | notApplicable (msg : MessageData)
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

/-- Recognize the numeric matrix fragment without evaluating its entries. -/
def recognize (A : Expr) : MetaM (Outcome Recognized) := do
  if A.hasFVar || A.hasExprMVar then
    return .notApplicable m!"the matrix{indentExpr A}\nmust be a closed term"
  let some lit ← literal? A |
    return .notApplicable m!"the matrix is not a closed `!![…]`, `Matrix.of ![…]`, `fun i j => …` or `Matrix.ofArray` literal{indentExpr A}"
  unless lit.n = lit.m do
    return .notApplicable m!"the matrix is {lit.n} × {lit.m}, not square"
  unless lit.carrier.isConstOf ``Int || lit.carrier.isConstOf ``Rat do
    return .notApplicable m!"only integer and rational matrices are supported; the entry type is{indentExpr lit.carrier}"
  return .success lit

/-- Classify the target before evaluating entries or running the producer. -/
def classify (target : Expr) : MetaM (Outcome (Expr × Expr × Bool × Recognized)) := do
  let target ← instantiateMVars target
  let some (A, rhs, reverse) := detTarget? target |
    return .notApplicable m!"the goal is not `A.det = d` for a Mathlib matrix `A`"
  let lit ← match ← recognize A with
    | .success lit => pure lit
    | .notApplicable msg => return .notApplicable msg
    | .declined msg => return .declined msg
  if rhs.hasFVar || rhs.hasExprMVar then
    return .notApplicable m!"the value{indentExpr rhs}\nmust be a closed term"
  return .success (A, rhs, reverse, lit)

/-- Certify a square literal over `Int` or `Rat`, as returned by `recognize`.
A producer whose witness fails its own check is a failure, not a decline. -/
def certifyLiteral (lit : Recognized) : MetaM (Outcome Cert) := do
  let isInt := lit.carrier.isConstOf ``Int
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
  | .error e => throwError "det: the producer's witness fails its own check (a producer bug): {e}"

/-- Recognize a closed square integer or rational literal and certify it. -/
def certify (A : Expr) : MetaM (Outcome Cert) := do
  match ← recognize A with
  | .success lit => certifyLiteral lit
  | .notApplicable msg => return .notApplicable msg
  | .declined msg => return .declined msg

/-- The proof of `Matrix.det A = v` for the certificate's value `v`, with the
value, the kernel check it rests on, and the row list of the literal. -/
structure Proof where
  /-- The certified value, as a numeral. -/
  value : Expr
  /-- The proof term of `Matrix.det A = value`. -/
  proof : Expr
  /-- The certificate check the kernel evaluates. -/
  check : Expr
  /-- The row list the literal is identified with. -/
  rowList : Expr

/-- The entry bound and slot width of the packed check: `k` one more than the
largest absolute value among the integer rows and the transform, and `W`
the least positive width with `n · k² < 2^W`. -/
def packedBounds (c : Cert) : Nat × Nat :=
  let rowsMax := c.rows.foldl (fun m r => r.foldl (fun m x => max m x.natAbs) m) 0
  let k := 1 + match c.witness with
    | .triangular _ T _ => T.foldl (fun m t => t.foldl (fun m x => max m x.natAbs) m) rowsMax
    | .singular _ => rowsMax
  (k, Nat.log2 (c.lit.n * (k * k)) + 1)

/-- Build the proof of `Matrix.det A = v` for the certificate's value `v`. -/
def build (cfg : HexMatrixMathlib.KernelConfig) (A : Expr) (c : Cert) : MetaM Proof := do
  let nE := mkNatLit c.lit.n
  let w := toExpr c.witness
  let B ← rowList (mkConst ``Int) (c.rows.map (·.map toExpr))
  let (k, W) := packedBounds c
  let kE := mkNatLit k
  let wE := mkNatLit W
  match c.rat with
  | none =>
      let value := toExpr c.witness.value
      let hA ← identification c.lit A B
      let check ← if cfg.packing then
          mkEq (← mkAppM ``Hex.Matrix.checkDetListPacked #[wE, kE, nE, B, w]) (mkConst ``Bool.true)
        else
          mkEq (← mkAppM ``Hex.Matrix.checkDetList #[nE, B, w]) (mkConst ``Bool.true)
      let hcheck ← decideProof check
      let eq ← if cfg.packing then
          mkAppM ``HexMatrixMathlib.det_eq_of_checkListPacked' #[A, B, w, wE, kE, hA, hcheck]
        else
          mkAppM ``HexMatrixMathlib.det_eq_of_checkList' #[A, B, w, hA, hcheck]
      -- `DetWitness.value w` reduces to the numeral
      let hvalue ← mkExpectedTypeHint (← mkEqRefl value)
        (← mkEq (← mkAppM ``Hex.Matrix.DetWitness.value #[w]) value)
      return ⟨value, ← mkEqTrans eq hvalue, check, B⟩
  | some (rat, scales) =>
      let value := toExpr c.value
      let L ← rowList (mkConst ``Rat) (rat.map (·.map toExpr))
      let s ← mkListLit (mkConst ``Nat) (scales.toList.map toExpr)
      let hA ← identification c.lit A L
      let check ← if cfg.packing then
          mkEq (← mkAppM ``Hex.Matrix.checkDetRatPacked #[wE, kE, nE, L, s, B, w, value])
            (mkConst ``Bool.true)
        else
          mkEq (← mkAppM ``Hex.Matrix.checkDetRat #[nE, L, s, B, w, value]) (mkConst ``Bool.true)
      let hcheck ← decideProof check
      let proof ← if cfg.packing then
          mkAppM ``HexMatrixMathlib.det_eq_of_checkRatPacked'
            #[A, L, s, B, w, value, wE, kE, hA, hcheck]
        else
          mkAppM ``HexMatrixMathlib.det_eq_of_checkRat' #[A, L, s, B, w, value, hA, hcheck]
      return ⟨value, proof, check, L⟩

/-- Diagnose a proof the kernel rejected: evaluate the certificate check with
the kernel and test the identification of the literal with its row list
along its route, reporting the first that fails. -/
def diagnose (A : Expr) (c : Cert) (p : Proof) (e : Exception) : MetaM Exception := do
  let env ← getEnv
  let lctx ← getLCtx
  let evalBool (prop : Expr) : MetaM (Option Bool) := do
    match Kernel.whnf env lctx (← mkDecide prop) with
    | .ok r => return if r.isConstOf ``Bool.true then some true
        else if r.isConstOf ``Bool.false then some false else none
    | .error _ => return none
  match ← evalBool p.check with
  | some false =>
      return .error e.getRef
        m!"det: the producer's certificate fails the kernel check (a producer bug){indentExpr p.check}"
  | none => return .error e.getRef m!"det: the kernel check got stuck{indentExpr p.check}"
  | some true => pure ()
  let nE := mkNatLit c.lit.n
  let identified ← match c.lit.route with
    | .chain =>
        let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[nE, nE, p.rowList]
        pure (match Kernel.isDefEq env lctx A ofL with | .ok true => true | _ => false)
    | .entrywise =>
        let check ← mkEq (← mkAppM ``HexMatrixMathlib.entriesEq #[nE, nE, A, p.rowList])
          (mkConst ``Bool.true)
        pure ((← evalBool check) == some true)
  unless identified do
    return .error e.getRef
      m!"det: the entries of the matrix do not reduce to their numerals in the kernel{indentExpr A}"
  return .error e.getRef m!"det: the kernel rejected the proof: {e.toMessageData}"

/-- Add `proof : target` as an auxiliary lemma checked synchronously, so
that a rejection is reported here, not later, and diagnosed. -/
def checked (A : Expr) (c : Cert) (p : Proof) (target proof : Expr) : MetaM Expr := do
  try
    HexMatrixMathlib.Literal.addClosedProof target proof
  catch e =>
    throw (← diagnose A c p e)

/-- Prove a determinant target in either orientation. -/
def proveGoal (cfg : HexMatrixMathlib.KernelConfig) (target : Expr) : MetaM (Outcome Expr) := do
  let target ← instantiateMVars target
  let (A, rhs, reverse, lit) ← match ← classify target with
    | .success input => pure input
    | .notApplicable msg => return .notApplicable msg
    | .declined msg => return .declined msg
  let c ← match ← certifyLiteral lit with
    | .success c => pure c
    | .notApplicable msg => return .notApplicable msg
    | .declined msg => return .declined msg
  -- the stated value is compared here, for a clear message on a false target
  let some v ← (try some <$> evalEntry rhs catch _ => pure none) |
    return .declined m!"the value{indentExpr rhs}\nmust be a closed numeral"
  unless v = c.value do
    throwError "det: the target is false: the determinant is {c.value}"
  let p ← build cfg A c
  -- the equality with the stated value, decided by the kernel as well
  let hbound ← decideProof (← mkEq p.value rhs)
  let proof ← mkEqTrans p.proof hbound
  let proof ← if reverse then mkEqSymm proof else pure proof
  return .success (← checked A c p target proof)

/-- The proof of `Matrix.det A = v` for the certified value `v`, checked. -/
def certifiedProof (A : Expr) (c : Cert) : MetaM Proof := do
  let p ← build {} A c
  let target ← mkEq (← mkAppM ``Matrix.det #[A]) p.value
  return { p with proof := ← checked A c p target p.proof }

/-- The `det% A` record: `Certified Matrix.det A`. -/
def certified (A : Expr) : MetaM (Outcome Expr) := do
  let c ← match ← certify A with
    | .success c => pure c
    | .notApplicable msg => return .notApplicable msg
    | .declined msg => return .declined msg
  let p ← certifiedProof A c
  let some (_, lhs, _) := (← inferType p.proof).eq? |
    throwError "det: internal error: the proof is not an equality"
  return .success (← mkAppOptM ``HexMatrixMathlib.Certified.mk
    #[none, none, some lhs.appFn!, some A, some p.value, some p.proof])

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
      | .notApplicable msg => throwError "det: not applicable: {msg}"
      | .declined msg => throwError "det: declined: {msg}"
  | _ => throwUnsupportedSyntax

/-- Rewrite `Matrix.det A` to its certified value when the Hex frontend
applies; `none` when it declines. -/
def normDet? (e : Expr) : MetaM (Option Simp.Result) := do
  let e ← instantiateMVars e
  unless e.getAppFn.isConstOf ``Matrix.det do return none
  match ← certify e.appArg! with
  | .success c =>
      let p ← certifiedProof e.appArg! c
      return some { expr := p.value, proof? := some p.proof }
  | .notApplicable _ | .declined _ => return none

end HexMatrixMathlib.Det

open Lean Meta in
/-- The `Hex.norm_det` simproc rewrites the determinant of a closed integer or
rational matrix literal to its value through the Hex certificate. Unsupported
inputs are unchanged; a producer failure or kernel rejection is an error. -/
simproc_decl Hex.norm_det (Matrix.det _) := fun e => do
  match ← HexMatrixMathlib.Det.normDet? e with
  | some r => return .done r
  | none => return .continue

namespace HexMatrixMathlib.Det

open Lean Elab

/-- `det` closes `A.det = d` and `d = A.det` for a closed integer or rational
matrix literal `A`, with the kernel checking a determinant certificate; an
equation outside that fragment delegates to other Hex handlers. A final
Hex-only normalization may leave a residual value equality. Extensions
must use `@[no_fallback]` to preserve their errors and `throwUnsupportedSyntax`
to delegate outside their fragment. The keyword is non-reserved, so `det`
stays usable as an identifier. -/
syntax (name := detTac) &"det" optConfig : tactic

/-- Normalize using only the Hex certificate, reporting the original reason
when it makes no progress. Errors from the simproc propagate unchanged. -/
def simpCertificate (msg : MessageData) : Tactic.TacticM Unit := do
  let goals ← Tactic.getGoals
  Tactic.evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [Hex.norm_det]))
  if (← Tactic.getGoals) == goals then
    throwError "{msg}"

/-- Registered before the numeric handler, so tried after it (Lean reverses
registration order at equal priority). Try Hex certificate normalization for
determinant equations, reporting the classification reason when it makes no
progress. Classification itself produces no certificate. -/
@[tactic detTac, no_fallback]
def detDiagnostic : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let target ← instantiateMVars (← Tactic.getMainTarget)
  match ← classify target with
  | .notApplicable msg =>
      if (detTarget? target).isNone then
        throwError "det: not applicable: {msg}"
      simpCertificate m!"det: not applicable: {msg}"
  | _ => throwUnsupportedSyntax

-- Ordinary errors commit; unsupported syntax still tries the next handler.
@[tactic detTac, no_fallback]
def evalDetTac : Tactic.Tactic := fun stx => Tactic.withMainContext do
  let cfg ← HexMatrixMathlib.Literal.elabKernelConfig stx[1]
  match ← proveGoal cfg (← Tactic.getMainTarget) with
  | .success proof => Tactic.closeMainGoal `det proof
  | .notApplicable _ => throwUnsupportedSyntax
  | .declined msg =>
      simpCertificate m!"det: declined: {msg}"

end HexMatrixMathlib.Det
