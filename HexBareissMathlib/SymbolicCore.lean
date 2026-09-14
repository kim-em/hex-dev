/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareissMathlib.Scaling
public meta import HexBareissMathlib.Scaling
public meta import HexBareissMathlib.Normalize
public meta import HexReflect.Session
public meta import HexMvGcd.Divide
public meta import HexMvGcd.Instances
public meta import HexMatrixMathlib.Literal
public meta import Lean

public meta section

namespace HexMatrixMathlib.DetPoly.Frontend

open Lean Meta Hex Hex.Reflect HexMatrixMathlib.Literal
open Lean.Meta.Sym.Arith (denoteRingExpr)

abbrev Poly := MvPoly.Kernel.PolyList Int

/-- A symbolic attempt either produces a proof or explains its decline. -/
inductive Outcome (α : Type) where
  | success (value : α)
  | notApplicable (reason : MessageData)
  | declined (reason : MessageData)

/-- Independent frontend limits supplement the common reflection budget. -/
def maxDimension : Nat := 16
def maxCertificateTerms : Nat := 65536

def require (o : ProviderOutcome α) : ReflectM α := do
  match o with
  | .success a _ => return a
  | .declined d _ => declineWith d
  | .failure f => failWith f
  | .notApplicable => failWith (.internal "a required polynomial provider is not applicable")

def decline (reason : MessageData) : ReflectM α := do
  declineWith (.providerCondition { name := `det } (← (← addMessageContext reason).toString))

def profile (name : String) (action : ReflectM α) : ReflectM α := do
  profileitM Exception name (← getOptions) action

/-- A capped binomial bound on the number of possible monomials. -/
def monomialBound (k degree cap : Nat) : Nat := Id.run do
  let mut count := 1
  for i in [:min k degree] do
    count := count * (k + degree - i) / (i + 1)
    if count > cap then return cap + 1
  return count

/-- Bound the minors of `[P | I]` before starting polynomial elimination. -/
def preflight (n k : Nat) (rows : Array (Array Poly)) : ReflectM Unit := do
  let entries := rows.flatten
  let degree := entries.foldl (fun d p => p.foldl (fun d (m, _) => max d (m.foldl (· + ·) 0)) d) 0
  let support := entries.foldl (fun s p => max s p.length) 1
  let bits := entries.foldl (fun b p => p.foldl (fun b (_, z) => max b (integerBits z)) b) 1
  let bound := min (n.factorial * support ^ n) (monomialBound k (n * degree) maxCertificateTerms)
  if bound * (n * (n + 1) / 2 + 1) > maxCertificateTerms then
    decline m!"certificate term budget exhausted before elimination (limit {maxCertificateTerms})"
  checkBudget .terms (monomialBound k (2 * n * degree) 100000)
  checkBudget .coefficientBits (2 * n * (bits + support.log2 + n.log2 + 2))

/-- Quotations contain only lists, integers and naturals. -/
def quoteWitness (w : Hex.Matrix.DetWitness Poly) : MetaM Expr := do
  let ty := toTypeExpr Poly
  match w with
  | .triangular s t d =>
    return mkApp4 (mkConst ``Hex.Matrix.DetWitness.triangular) ty (toExpr s) (toExpr t) (toExpr d)
  | .singular v => return mkApp2 (mkConst ``Hex.Matrix.DetWitness.singular) ty (toExpr v)

/-- Close over the local context before the one synchronous kernel check. -/
def checked (target proof : Expr) : MetaM Expr := do
  let all := (← getLCtx).getFVars
  let mut needed := collectFVars (collectFVars {} target) proof
  for e in all.reverse do
    if needed.fvarSet.contains e.fvarId! then
      let decl ← e.fvarId!.getDecl
      needed := collectFVars needed decl.type
      if let some v := decl.value? then needed := collectFVars needed v
  let locals := all.filter fun e => needed.fvarSet.contains e.fvarId!
  let type ← mkForallFVars locals target (usedOnly := false) (usedLetOnly := false)
    (generalizeNondepLet := false)
  let proof ← mkLambdaFVars locals proof (usedOnly := false) (usedLetOnly := false)
    (generalizeNondepLet := false)
  let result ← profileitM Exception "det.symbolic.kernel" (← getOptions) do
    addClosedProof (← instantiateMVars type) (← instantiateMVars proof)
  let args ← locals.filterM fun e => return !(← e.fvarId!.getDecl).isLet
  return mkAppN result args

/-- Replay only structural polynomial lists in an entry identification proof. -/
def entryProof (k : Nat) (ctx : Expr) (r : ReifiedRing) (p : Poly) : ReflectM Expr :=
    profile "det.symbolic.identification" do
    let hbound ← decideProof (← mkAppM ``LE.le #[toExpr (RingExpr.varBound r.expr), toExpr k])
    let equality ← mkEq (← mkAppM ``MvPoly.Kernel.beq
      #[← mkAppM ``Hex.Reflect.Kernel.ringList #[toExpr k, toExpr r.expr], toExpr p])
      (mkConst ``Bool.true)
    let proof ← mkAppM ``HexReflectMathlib.Kernel.eval_checked
      #[toExpr k, ctx, toExpr r.expr, toExpr p, hbound, ← decideProof equality]
    let some (_, lhs, rhs) := (← inferType proof).eq? | throwError "det: malformed entry proof"
    let denoted ← (denoteRingExpr (← atoms) r.expr : ReaderT Nat ReflectM Expr).run r.ringId
    unless ← withTransparency .default (isDefEq rhs denoted) do
      failWith (.illTypedProof (← (m!"entry denotation instance mismatch: {rhs} versus {denoted}").toString))
    unless ← withTransparency .default (isDefEq denoted r.source) do failWith (.illTypedProof "entry source instance mismatch")
    mkExpectedTypeHint proof (← mkEq lhs r.source)

/-- Nested conjunctions identify symbolic entries without decidable equality. -/
def conjunction (proofs : Array Expr) : MetaM Expr :=
  proofs.foldrM (fun h tail => mkAppM ``And.intro #[h, tail]) (mkConst ``True.intro)

/-- The polynomial expression for a value in the batch's existing atoms. -/
def expression (p : Poly) : RingExpr :=
  p.foldr (fun (m, c) tail => .add
    (m.zipIdx.foldl (fun term (e, i) => if e == 0 then term else .mul term (.pow (.var i) e))
      (if c < 0 then .neg (.num c.natAbs) else .num c)) tail) (.num 0)

structure Result where
  value : Expr
  proof : Expr

/-- Reduce closed literal-index conditionals without unfolding ring operations
or the numeral instances returned by their branches. -/
partial def reduceIndices (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  if (e.isAppOf ``ite || e.isAppOf ``dite) && args.size == 5 then
    let decision ← whnfD args[2]!
    if decision.isAppOf ``Decidable.isTrue || decision.isAppOf ``Decidable.isFalse then
      let branch := args[if decision.isAppOf ``Decidable.isTrue then 3 else 4]!
      reduceIndices (if e.isAppOf ``dite then (mkApp branch decision.appArg!).headBeta else branch)
    else pure e
  else pure e

/-- One batch, one elimination and one kernel check for a symbolic determinant.
The optional target is reified before sealing, and may not allocate new atoms. -/
def compute (A : Expr) (rhs? : Option Expr := none) : MetaM (Outcome Result) := do
  if A.hasExprMVar then return .declined m!"unresolved metavariable"
  let sourceSize := sourceNodeCount A 100001 + (rhs?.map (sourceNodeCount · 100001) |>.getD 0)
  if sourceSize > 100000 then return .declined m!"source node budget exhausted (limit 100000)"
  let some (n, m, _) ← shape? (← inferType A) | return .notApplicable m!"matrix is not a supported literal"
  unless n == m do return .notApplicable m!"matrix is not square"
  if n > maxDimension then return .declined m!"dimension budget exhausted (limit {maxDimension})"
  let some lit ← literal? A (allowOpen := true) | return .notApplicable m!"matrix is not a supported literal"
  let .some _ ← trySynthInstance (← mkAppM ``_root_.CommRing #[lit.carrier]) |
    return .declined m!"a commutative ring instance is required"
  let .some _ ← trySynthInstance (← mkAppOptM ``_root_.CharZero #[some lit.carrier, none]) |
    return .declined m!"residue coefficient provider unavailable (#10255, #10257)"
  let lit := { lit with entries := ← lit.entries.mapM (fun row => row.mapM reduceIndices) }
  let rat := lit.carrier.isConstOf ``Rat
  let options ← getOptions
  let normalized ← if rat then
      match ← profileitM Exception "det.symbolic.scaling" options (lit.entries.mapM Normalize.row).run with
      | .ok rs => pure (some rs)
      | .error msg => return .declined msg
    else pure none
  let targetNorm ← if rat then
      match ← profileitM Exception "det.symbolic.scaling" options (rhs?.mapM Normalize.expression).run with
      | .ok r => pure r
      | .error msg => return .declined msg
    else pure none
  let entries ← (normalized.map (·.map fun (_, rs) => rs.map (·.term)) |>.getD lit.entries).mapM
    (fun row => row.mapM reduceIndices)
  let scales := normalized.map (·.map (·.1)) |>.getD #[]
  let D := scales.foldl (· * ·) 1
  let t := targetNorm.map (·.scale) |>.getD 1
  let outcome ← Hex.Reflect.run <| withOutcome do
    let mut reified : Array (Array ReifiedRing) := #[]
    for row in entries do
      reified := reified.push (← row.mapM fun e => do profile "det.symbolic.reify" (do require (← reifyCommRing e)))
    -- An empty matrix still needs a classified carrier to construct its context.
    let seed ← profile "det.symbolic.reify" (do require (← reifyCommRing (← mkNumeral lit.carrier 0)))
    let count := (← atoms).size
    let rhs ← (targetNorm.map (·.term) <|> rhs?).mapM fun e => do profile "det.symbolic.reify" (do require (← reifyCommRing e))
    unless (← atoms).size == count do
      decline m!"target is not a ring expression in the matrix atoms"
    let sealed ← sealAtoms
    let k := sealed.n
    let ring ← ringOf seed
    let ctx ← contextExpr ring sealed
    let mut rows : List (List (MvPoly k Int Mono.grevlex)) := []
    let mut lists : Array (Array Poly) := #[]
    for row in reified do
      let mut polys := []
      let mut serial := #[]
      for r in row do
        let c ← profile "det.symbolic.convert" (do require (← convert r sealed .grevlex))
        unless c.sealed.n == k do failWith (.internal "batch size changed")
        let ts := c.terms.map fun (m, z) => (m.toArray.toList, z)
        -- Conversion and reconstruction here execute in compiled code only.
        let p := MvPoly.ofTerms (cmp := Mono.grevlex)
          (ts.map fun (m, z) => (MvPoly.Kernel.mono k m, z))
        polys := polys ++ [p]
        serial := serial.push (profileit "det.symbolic.lists" options fun _ => MvPoly.Kernel.toList p)
      rows := rows ++ [polys]
      lists := lists.push serial
    preflight lit.n k lists
    let check := fun rows w =>
      let (rows, w) := profileit "det.symbolic.lists" options fun _ =>
        (rows.map (List.map MvPoly.Kernel.toList), w.map MvPoly.Kernel.toList)
      profileit "det.symbolic.selfcheck" options fun _ =>
        Hex.Matrix.checkDetPolyList (Polynomial.ops k) lit.n rows w
    let produced := profileit "det.symbolic.producer" options fun _ =>
      Hex.Matrix.detWitnessWith Hex.exactDiv lit.n check rows
    let w ← match produced with
      | .ok w => pure (profileit "det.symbolic.lists" options fun _ => w.map MvPoly.Kernel.toList)
      | .error e => failWith (.internal s!"determinant producer failed its own check: {e}")
    let d := Polynomial.value w
    let size := match w with
      | .triangular _ ts d => ts.foldl (fun n r => r.foldl (fun n p => n + p.length) n) d.length
      | .singular v => v.foldl (fun n p => n + p.length) 0
    if size > maxCertificateTerms then
      decline m!"certificate term budget exhausted (limit {maxCertificateTerms})"
    checkBudget .proofNodes ((size + lists.flatten.foldl (fun n p => n + p.length) 0) * (4 * k + 24))
    let q ← match rhs with
      | some r =>
        let c ← profile "det.symbolic.convert" (do require (← convert r sealed .grevlex))
        let p := MvPoly.ofTerms (cmp := Mono.grevlex)
          (c.terms.map fun (m, z) => (MvPoly.Kernel.mono k m.toArray.toList, z))
        pure (profileit "det.symbolic.lists" options fun _ => MvPoly.Kernel.toList p)
      | none => pure d
    let left := if rat && rhs?.isSome then MvPoly.Kernel.smul (Int.ofNat t) d else d
    let right := if rat && rhs?.isSome then MvPoly.Kernel.smul (Int.ofNat D) q else q
    unless MvPoly.Kernel.beq left right do
      let value ← (denoteRingExpr sealed.atoms (expression d) : ReaderT Nat ReflectM Expr).run seed.ringId
      decline m!"canonical lists differ; computed value is{indentExpr value}"
    let rowsE := toExpr (lists.toList.map Array.toList)
    let wE ← quoteWitness w
    let ops ← mkAppOptM ``Polynomial.ops
      #[some (mkConst ``Int), none, none, some (toExpr k)]
    let check ← mkEq (← mkAppM ``Hex.Matrix.checkDetPolyList #[ops, toExpr lit.n, rowsE, wE])
      (mkConst ``Bool.true)
    let hcheck ← decideProof check
    let mut hrows := #[]
    for i in [:lit.n] do
      let mut hs := #[]
      for j in [:lit.n] do
        let h ← entryProof k ctx (reified[i]!.getD j seed) (lists[i]!)[j]!
        let h ← match normalized with
          | none => mkEqSymm h
          | some rs => mkEqTrans h (rs[i]!.2[j]!).proof
        hs := hs.push h
      hrows := hrows.push (← conjunction hs)
    let B ← mkAppM ``Polynomial.evaluated #[toExpr k, toExpr lit.n, rowsE, ctx]
    let r ← match rhs with
      | some r => pure r
      | none =>
        let e := expression d
        let source ← (denoteRingExpr sealed.atoms e : ReaderT Nat ReflectM Expr).run seed.ringId
        pure { seed with expr := e, source }
    let he ← entryProof k ctx r q
    let hq ← decideProof (← mkEq (← mkAppM ``MvPoly.Kernel.beq #[toExpr left, toExpr right])
      (mkConst ``Bool.true))
    let (value, proof) ← if rat then do
      let sE := toExpr scales.toList
      let hA ← mkAppM ``Scaling.identify #[toExpr lit.n, A, B, sE, ← conjunction hrows]
      let hs ← decideProof (← mkEq (← mkAppM ``List.length #[sE]) (toExpr lit.n))
      let hdet ← mkAppM ``Polynomial.scaled
        #[toExpr k, toExpr lit.n, rowsE, wE, ctx, A, sE, hcheck, hA, hs]
      let hD ← decideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr D])
      match targetNorm with
      | some qnorm =>
        let he ← mkEqTrans he qnorm.proof
        let ht ← decideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr t])
        let proof ← mkAppM ``Scaling.target
          #[toExpr k, toExpr lit.n, wE, ctx, A, sE, toExpr t, toExpr q, rhs?.get!,
            hdet, ht, hD, he, hq]
        pure (rhs?.get!, proof)
      | none =>
        let h ← mkEqTrans hdet he
        let proof ← mkAppM ``Scaling.value #[toExpr D, ← mkAppM ``Matrix.det #[A], r.source, hD, h]
        pure (← mkAppM ``HDiv.hDiv #[r.source, ← Normalize.natural D], proof)
    else do
      let hA ← mkAppM ``Polynomial.identify #[A, B, ← conjunction hrows]
      let proof ← mkAppM ``Polynomial.target
        #[toExpr k, toExpr lit.n, rowsE, wE, ctx, A, toExpr q, r.source, hcheck, hA, he, hq]
      pure (r.source, proof)
    let proofNodes := sourceNodeCount proof 1000001
    charge .proofNodes proofNodes
    let witnessEntries := match w with
      | .triangular _ rows d => d :: rows.flatten
      | .singular v => v
    if ← isTracingEnabledFor `HexMatrix.certificate then
      reportCertificate "det-symbolic" (reprStr w) (witnessEntries.flatMap (List.map Prod.snd)) []
        [("proof_nodes", toJson proofNodes), ("atoms", toJson k),
         ("max_minor_support", toJson (witnessEntries.foldl (fun n p => max n p.length) 0)),
         ("max_minor_degree", toJson (witnessEntries.foldl (fun n p =>
           p.foldl (fun n (m, _) => max n (m.foldl (· + ·) 0)) n) 0))]
    let target ← mkEq (← mkAppM ``Matrix.det #[A]) value
    return { value, proof := ← checked target proof : Result }
  match outcome with
  | .success r _ => return .success r
  | .declined (.providerCondition _ reason) _ => return .declined m!"{reason}"
  | .declined d _ => return .declined d.toMessageData
  | .notApplicable => return .declined m!"no polynomial provider"
  | .failure f => throwError "det: {f.toMessageData}"

end HexMatrixMathlib.DetPoly.Frontend
