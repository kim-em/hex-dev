/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib.Scaling
public import HexPolyDetMathlib.Residue
public import HexPolyDetMathlib.Packed
public meta import HexPolyDetMathlib.Scaling
public meta import HexPolyDetMathlib.Residue
public meta import HexPolyDetMathlib.Certificate
public meta import HexReflectMathlib.Display
public meta import HexArith.Nat.Prime
public meta import HexPolyDetMathlib.Normalize
public meta import HexReflect.Session
public meta import HexPolyDet.Basic
public meta import HexMvGcd.Instances
public meta import HexMvGcd.Divide
public meta import HexMatrixMathlib.Literal
public meta import Lean

public meta section

namespace HexMatrixMathlib.DetPoly.Frontend

open Lean Meta Hex Hex.Reflect HexMatrixMathlib.Literal
open Lean.Meta.Sym.Arith (denoteRingExpr)
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

abbrev Poly := MvPoly.Kernel.PolyList Int

/-- A symbolic attempt either produces a proof or explains its decline. -/
inductive Outcome (α : Type) where
  | success (value : α)
  | notApplicable (reason : MessageData)
  | declined (reason : MessageData)

/-- Independent frontend limits supplement the common reflection budget. -/
def maxDimension : Nat := 16
def maxCertificateTerms : Nat := 65536
def maxIntermediateTerms : Nat := 100000

def producerBudget : Hex.Matrix.DetWitness.Budget :=
  { maxIntermediate := maxIntermediateTerms, maxCertificate := maxCertificateTerms }

def require (o : ProviderOutcome α) : ReflectM α := do
  match o with
  | .success a _ => return a
  | .declined d _ => declineWith d
  | .failure f => failWith f
  | .notApplicable => failWith (.internal "a required polynomial provider is not applicable")

def decline (reason : MessageData) : ReflectM α := do
  declineWith (.providerCondition { name := `det } (← (← addMessageContext reason).toString))

/-- Resource exhaustion is an ordinary decline; invalid witnesses are failures. -/
def requireWitness (result : Except Hex.Matrix.DetWitness.Error α) : ReflectM α := do
  match result with
  | .ok w => return w
  | .error e =>
    match e with
    | .exhausted .. => decline m!"{e.message}"
    | _ => failWith (.internal s!"determinant producer failed: {e.message}")

def profile (name : String) (action : ReflectM α) : ReflectM α := do
  profileitM Exception name (← getOptions) action

/-- A capped binomial bound on the number of possible monomials. -/
def monomialBound (k degree cap : Nat) : Nat := Id.run do
  let mut count := 1
  for i in [:min k degree] do
    count := count * (k + degree - i) / (i + 1)
    if count > cap then return cap + 1
  return count

/-- Worst-case minor support is diagnostic only. Coefficient bounds remain
independent of the producer's observed support and round admission policy. -/
def preflight (n k : Nat) (rows : Array (Array Poly)) : ReflectM Unit := do
  let entries := rows.flatten
  let degree := entries.foldl (fun d p => p.foldl (fun d (m, _) => max d (m.foldl (· + ·) 0)) d) 0
  let support := entries.foldl (fun s p => max s p.length) 1
  let bits := entries.foldl (fun b p => p.foldl (fun b (_, z) => max b (integerBits z)) b) 1
  let bound := min (n.factorial * support ^ n) (monomialBound k (n * degree) maxCertificateTerms)
  trace[HexMatrix.certificate] "det producer: a-priori minor support bound {bound} (diagnostic only)"
  checkBudget .coefficientBits (2 * n * (bits + support.log2 + n.log2 + 2))

/-- Quotations contain only lists, integers and naturals. -/
def quoteWitness {C : Type} [ToExpr C] (w : Hex.Matrix.DetWitness (MvPoly.Kernel.PolyList C)) : MetaM Expr := do
  let ty := toTypeExpr (MvPoly.Kernel.PolyList C)
  match w with
  | .triangular s t d =>
    return mkApp4 (mkConst ``Hex.Matrix.DetWitness.triangular) ty (toExpr s) (toExpr t) (toExpr d)
  | .singular v => return mkApp2 (mkConst ``Hex.Matrix.DetWitness.singular) ty (toExpr v)

/-- Close over the local context before the one synchronous kernel check. -/
def checked (target proof : Expr) (profileName : String := "det.symbolic.kernel") : MetaM Expr := do
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
  let result ← profileitM Exception profileName (← getOptions) <|
    withOptions (fun o => o.setBool `profiler false) do
      addClosedProof (← instantiateMVars type) (← instantiateMVars proof)
  let args ← locals.filterM fun e => return !(← e.fvarId!.getDecl).isLet
  return mkAppN result args

/-- Replay only structural polynomial lists in an entry identification proof. -/
def entryProof (k : Nat) (ctx : Expr) (r : ReifiedRing) (p : Poly)
    (location : String := "target") : ReflectM Expr :=
    profile "det.symbolic.identification" do
    unless MvPoly.Kernel.beq (Hex.Reflect.Kernel.ringList k r.expr) p do
      decline m!"{location}: conversion does not agree with integer-list replay; residue list replay is unavailable"
    let hbound ← decideProof (← mkAppM ``LE.le #[toExpr (RingExpr.varBound r.expr), toExpr k])
    let equality ← mkEq (← mkAppM ``MvPoly.Kernel.beq
      #[← mkAppM ``Hex.Reflect.Kernel.ringList #[toExpr k, toExpr r.expr], toExpr p])
      (mkConst ``Bool.true)
    let proof ← mkAppM ``HexReflectMathlib.Kernel.eval_checked
      #[toExpr k, ctx, toExpr r.expr, toExpr p, hbound, ← decideProof equality]
    let some (_, lhs, rhs) := (← inferType proof).eq? | throwError "det: malformed entry proof"
    let denoted ← (denoteRingExpr (← atoms) r.expr : ReaderT Nat ReflectM Expr).run r.ringId
    unless ← withTransparency .default (isDefEq rhs denoted) do
      decline m!"entry denotation instance mismatch: {rhs} versus {denoted}"
    unless ← withTransparency .default (isDefEq denoted r.source) do decline m!"entry source instance mismatch"
    mkExpectedTypeHint proof (← mkEq lhs r.source)

/-- Nested conjunctions identify symbolic entries without decidable equality. -/
def conjunction (proofs : Array Expr) : MetaM Expr :=
  proofs.foldrM (fun h tail => mkAppM ``And.intro #[h, tail]) (mkConst ``True.intro)

/-- State the final proof argument's type without unifying through its payload.
The kernel checks the expected-type hint when checking the closed proof. -/
def applyHint (head proof : Expr) : MetaM Expr := do
  let .forallE _ expected _ _ ← inferType head
    | throwError "det: expected a final proof argument"
  return mkAppN head #[mkExpectedPropHint proof expected]

/-- Pair adjacent sums until one balanced expression remains. This bounds
canonical-list replay of a generated T-term value to O(T log T) merges. -/
partial def sumTerms (terms : Array RingExpr) : RingExpr := Id.run do
  if terms.isEmpty then return .num 0
  if terms.size == 1 then return terms[0]!
  let mut next := #[]
  for i in [:terms.size / 2] do
    next := next.push (.add terms[2 * i]! terms[2 * i + 1]!)
  if terms.size % 2 == 1 then next := next.push terms[terms.size - 1]!
  return sumTerms next

/-- The polynomial expression for a value in the batch's existing atoms. -/
def expression (p : Poly) : RingExpr :=
  sumTerms (p.toArray.map fun (m, c) =>
    m.zipIdx.foldl (fun term (e, i) => if e == 0 then term else .mul term (.pow (.var i) e))
      (if c < 0 then .neg (.num c.natAbs) else .num c))

structure Result where
  value : Expr
  proof : Expr

/-- Reduce closed literal-index conditionals without unfolding ring operations
or the numeral instances returned by their branches. -/
def reduceIndices (e : Expr) : MetaM Expr := Meta.transform e (pre := fun e => do
  let args := e.getAppArgs
  if (e.isAppOf ``ite || e.isAppOf ``dite) && args.size == 5 then
    let decision ← whnfD args[2]!
    if decision.isAppOf ``Decidable.isTrue || decision.isAppOf ``Decidable.isFalse then
      let branch := args[if decision.isAppOf ``Decidable.isTrue then 3 else 4]!
      return .visit (if e.isAppOf ``dite then (mkApp branch decision.appArg!).headBeta else branch)
    else return .continue
  else return .continue)

/-- Use the coefficient provider's exact bounds and characteristic evidence. -/
def withEvidence (evidence : List Expr) (action : ReflectM Result) : ReflectM Result := do
  match evidence with
  | [] => action
  | e :: es =>
    withLetDecl `coefficientInstance (← inferType e) e fun x => do
      let r ← withEvidence es action
      return { value := r.value.replaceFVar x e, proof := r.proof.replaceFVar x e }

/-- Convert in compiled code, quoting residues through the shared list encoding. -/
def residuePoly? (p k : Nat) (a : Poly) : Option (MvPoly.Kernel.PolyList Nat) := do
  if hb : 0 < p ∧ p < 2^31 then
    letI : ZMod64.Bounds p := ⟨hb.1, hb.2⟩
    let f := MvPoly.ofTerms (cmp := Mono.grevlex)
      (a.map fun (m, z) => (MvPoly.Kernel.mono k m, (z : ZMod64 p)))
    return MvPoly.Kernel.ofResidues p (Hex.PolyDet.toList f)
  else none

/-- Fraction-free elimination in the selected residue coefficient domain. -/
def residueWitness? (p k n : Nat) (rows : List (List (MvPoly.Kernel.PolyList Nat))) :
    Option (Except Hex.Matrix.DetWitness.Error (Hex.Matrix.DetWitness (MvPoly.Kernel.PolyList Nat))) := do
  if hb : 0 < p ∧ p < 2^31 then
    letI : ZMod64.Bounds p := ⟨hb.1, hb.2⟩
    if hp : Hex.Nat.Prime p then
      letI : ZMod64.PrimeModulus p := ⟨hp⟩
      let decode := MvPoly.Kernel.denoteMod p (n := k) (cmp := Mono.grevlex)
      let quotePoly := fun f => MvPoly.Kernel.ofResidues p (Hex.PolyDet.toList f)
      let check := fun rs w => Hex.Matrix.checkDetPolyList (Hex.PolyDet.opsMod p k) n
        (rs.map (List.map quotePoly)) (w.map quotePoly)
      return (Hex.PolyDet.produce producerBudget n check (rows.map (List.map decode))).map
        (fun w => w.map quotePoly)
    else none
  else none

/-- Identify an entry by replaying only natural-residue list arithmetic. -/
def residueEntry (p k : Nat) (ctx : Expr) (r : ReifiedRing)
    (a : MvPoly.Kernel.PolyList Nat) : ReflectM Expr := profile "det.symbolic.identification" do
  unless MvPoly.Kernel.beq (Hex.Reflect.Kernel.ringListMod p k r.expr) a do
    decline m!"residue conversion does not agree with list replay"
  let hp ← decideProof (← mkAppM ``LT.lt #[toExpr (1 : Nat), toExpr p])
  let hb ← decideProof (← mkAppM ``LE.le #[toExpr r.expr.varBound, toExpr k])
  let replay ← mkAppM ``Hex.Reflect.Kernel.ringListMod #[toExpr p, toExpr k, toExpr r.expr]
  let he ← decideProof (← mkEq (← mkAppM ``MvPoly.Kernel.beq #[replay, toExpr a]) (mkConst ``Bool.true))
  let proof ← mkAppM ``HexReflectMathlib.Kernel.eval_checkedMod
    #[toExpr p, hp, toExpr k, ctx, toExpr r.expr, toExpr a, hb, he]
  let some (_, lhs, rhs) := (← inferType proof).eq? | throwError "det: malformed residue entry proof"
  unless ← withTransparency .default (isDefEq rhs r.source) do
    decline m!"residue entry source instance mismatch"
  mkExpectedTypeHint proof (← mkEq lhs r.source)

/-- One residue batch, one producer, and one kernel-checked determinant certificate. -/
def computeResidue (p : Nat) (provider : CoeffProvider) (A : Expr)
    (lit : Recognized) (reified : Array (Array ReifiedRing)) (seed : ReifiedRing)
    (rhs : Option ReifiedRing) (sealed : Sealed) (ctx : Expr) : ReflectM Result :=
    withEvidence provider.auxInstances.toList do
  let k := sealed.n
  let convertList (r : ReifiedRing) : ReflectM (MvPoly.Kernel.PolyList Nat) := do
    let c ← profile "det.symbolic.convert" (do require (← convert r sealed .grevlex (some provider)))
    unless c.sealed.n == k do failWith (.internal "batch size changed")
    unless c.provider.id == provider.id do decline m!"mixed coefficient providers in residue batch"
    let some a := residuePoly? p k (c.terms.map fun (m, z) => (m.toList, z))
      | decline m!"unsupported residue modulus"
    return a
  let lists ← reified.mapM fun row => row.mapM convertList
  preflight lit.n k (lists.map fun row => row.map fun a => a.map fun (m, c) => (m, (c : Int)))
  let some produced := profileit "det.symbolic.producer" (← getOptions) fun _ =>
      residueWitness? p k lit.n (lists.toList.map Array.toList)
    | failWith (.internal "residue determinant producer failed its own check")
  let w ← requireWitness produced
  let d := Residue.value w
  let witnessEntries := match w with
    | .triangular _ ts d => d :: ts.flatten
    | .singular v => v
  let size := witnessEntries.foldl (fun n a => n + a.length) 0
  checkBudget .proofNodes ((size + lists.flatten.foldl (fun n a => n + a.length) 0) * (4 * k + 24))
  let q ← match rhs with | some r => convertList r | none => pure d
  unless MvPoly.Kernel.beq d q do
    decline m!"target is not a polynomial identity in the sealed atoms modulo {p}"
  let rowsE := toExpr (lists.toList.map Array.toList)
  let wE ← quoteWitness w
  let remaining := (← getThe Hex.Reflect.State).budget.remaining
  let (hcheck, selection) ← Certificate.residue p k lit.n (lists.toList.map Array.toList) w rowsE wE
    { terms := min maxIntermediateTerms remaining.terms
      coefficientBits := remaining.coefficientBits
      certificateTerms := min remaining.terms
        (min (maxCertificateTerms - size) (remaining.proofNodes / (4 * k + 24))) }
  charge .terms selection.quotientSupport
  checkBudget .proofNodes (selection.quotientSupport * (4 * k + 24))
  let mut hrows := #[]
  for i in [:lit.n] do
    let mut hs := #[]
    for j in [:lit.n] do
      hs := hs.push (← mkEqSymm (← residueEntry p k ctx (reified[i]!.getD j seed) (lists[i]!)[j]!))
    hrows := hrows.push (← conjunction hs)
  let hA ← profile "det.symbolic.matrix" <| applyHint
    (← mkAppM ``Residue.identify #[toExpr p, toExpr k, toExpr lit.n, rowsE, ctx, A])
    (← conjunction hrows)
  let r ← match rhs with
    | some r => pure r
    | none =>
      let e := expression (d.map fun (m, c) => (m, HexReflectMathlib.signedResidue p c))
      let source ← (denoteRingExpr sealed.atoms e : ReaderT Nat ReflectM Expr).run seed.ringId
      pure { seed with expr := e, source }
  let he ← residueEntry p k ctx r q
  let proof ← profile "det.symbolic.transport" do
    match rhs with
    | some _ =>
      let hq ← decideProof (← mkEq (← mkAppM ``MvPoly.Kernel.beq #[toExpr d, toExpr q]) (mkConst ``Bool.true))
      return mkAppN (← mkAppM ``Residue.target_det
        #[toExpr p, toExpr k, toExpr lit.n, rowsE, wE, ctx, A, toExpr q, r.source])
        #[hcheck, hA, he, hq]
    | none =>
      return mkAppN (← mkAppM ``Residue.result_det
        #[toExpr p, toExpr k, toExpr lit.n, rowsE, wE, ctx, A, r.source]) #[hcheck, hA, he]
  let proofNodes := (size + q.length + lists.flatten.foldl (fun n a => n + a.length) 0) * (4 * k + 24)
  charge .proofNodes proofNodes
  trace[HexMatrix.certificate] "{(Json.mkObj (Certificate.fields selection "residue" ++ [
    ("modulus", toJson p), ("proof_node_budget", toJson proofNodes), ("atoms", toJson k)])).compress}"
  let target ← mkEq (← mkAppM ``Matrix.det #[A]) r.source
  return { value := r.source, proof := ← checked target proof }

/-- Tree entry identification uses only the retained expression's denotation. -/
def treeEntry (ctx : Expr) (r : ReifiedRing) : MetaM Expr := do
  let h ← mkAppM ``HexKroneckerMathlib.fromGrind_denote #[ctx, toExpr r.expr]
  let some (_, lhs, _) := (← inferType h).eq? | throwError "det: malformed tree denotation proof"
  mkExpectedTypeHint h (← mkEq lhs r.source)

/-- Assemble a tree certificate after its product and target preflights pass. -/
def computeTree? (A ctx : Expr) (lit : Recognized) (k size : Nat)
    (reified : Array (Array ReifiedRing)) (lists : Array (Array Poly))
    (w : Hex.Matrix.DetWitness Poly) (r : ReifiedRing) (rhs? : Option Expr)
    (normalized : Option (Array (Nat × Array Normalize.Result)))
    (targetNorm : Option Normalize.Result) (scales : Array Nat) (D t : Nat) :
    ReflectM (Option Result) := do
  if Certificate.arm (← getOptions) == .lists then return none
  let trees := reified.toList.map (fun row => row.toList.map (fun r => HexKroneckerMathlib.fromGrind r.expr))
  let treeTy := mkConst ``Hex.Kronecker.Expr
  let quoteTree (r : ReifiedRing) : MetaM Expr :=
    mkAppM ``HexKroneckerMathlib.fromGrind #[toExpr r.expr]
  let quoted ← reified.toList.mapM fun row => do
    mkListLit treeTy (← row.toList.mapM (fun r => do quoteTree r))
  let treesE ← mkListLit (mkApp (mkConst ``List [Level.zero]) treeTy) quoted
  let wE ← quoteWitness w
  withLetDecl `detTrees (← inferType treesE) treesE fun treesE => do
    withLetDecl `detWitness (← inferType wE) wE fun wE => do
      withLetDecl `detMatrix (← inferType A) A fun A => do
        let qE ← quoteTree r
        let q := HexKroneckerMathlib.fromGrind r.expr
        let d := Polynomial.value w
        let (target, value, targetE) ← if targetNorm.isSome then do
            pure (Hex.Kronecker.Expr.mul (.int D) q, MvPoly.Kernel.smul (Int.ofNat t) d,
              mkApp2 (mkConst ``Hex.Kronecker.Expr.mul)
                (mkApp (mkConst ``Hex.Kronecker.Expr.int) (toExpr (Int.ofNat D))) qE)
          else pure (q, d, qE)
        let dE ← mkAppM ``Polynomial.value #[wE]
        let valueE ← if targetNorm.isSome then
            mkAppM ``MvPoly.Kernel.smul #[toExpr (Int.ofNat t), dE]
          else pure dE
        let some (hcheck, hq, selection) ← Certificate.tree? k lit.n (lists.toList.map Array.toList)
            trees w target value treesE wE targetE valueE | return none
        let hq ← mkAppM ``Hex.Kronecker.Kernel.treeTermsEq_sound
          #[hq, ← mkAppM ``Lean.RArray.get #[ctx]]
        let mut hrows := #[]
        for i in [:lit.n] do
          let mut hs := #[]
          for j in [:lit.n] do
            let h ← treeEntry ctx ((reified[i]!).getD j r)
            let h ← match normalized with
              | none => mkEqSymm h
              | some rs => mkEqTrans h (rs[i]!.2[j]!).proof
            hs := hs.push h
          hrows := hrows.push (← conjunction hs)
        let B ← mkAppM ``Tree.evaluated #[toExpr lit.n, treesE, ctx]
        let he ← treeEntry ctx r
        let (value, proof) ← if normalized.isSome then do
            let sE := toExpr scales.toList
            let hA ← applyHint (← mkAppM ``Scaling.identify #[toExpr lit.n, A, B, sE])
              (← conjunction hrows)
            let hs ← decideProof (← mkEq (← mkAppM ``List.length #[sE]) (toExpr lit.n))
            let hdet := mkAppN (← mkAppM ``Tree.scaled_det
              #[toExpr k, toExpr lit.n, treesE, wE, ctx, A, sE]) #[hcheck, hA, hs]
            let hD ← decideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr D])
            match targetNorm with
            | some qnorm =>
              let he ← mkEqTrans he qnorm.proof
              let ht ← decideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr t])
              let proof := mkAppN (← mkAppM ``Tree.scaled_target
                #[toExpr k, dE, ctx, toExpr D, toExpr t,
                  ← mkAppM ``Matrix.det #[A], rhs?.get!, qE]) #[hdet, ht, hD, he, hq]
              pure (rhs?.get!, proof)
            | none =>
              let he := mkAppN (← mkAppM ``Tree.value_eq
                #[toExpr k, ctx, qE, dE, r.source]) #[he, hq]
              let h ← mkEqTrans hdet he
              let proof ← mkAppM ``Scaling.value #[toExpr D, ← mkAppM ``Matrix.det #[A], r.source, hD, h]
              if D == 1 then pure (r.source, ← mkEqTrans proof (← mkAppM ``div_one #[r.source]))
              else pure (← mkAppM ``HDiv.hDiv #[r.source, ← Normalize.natural D], proof)
          else do
            let hA ← applyHint (← mkAppM ``Polynomial.identify #[A, B]) (← conjunction hrows)
            let head := if rhs?.isSome then ``Tree.target_det else ``Tree.result_det
            let proof := mkAppN (← mkAppM head
              #[toExpr k, toExpr lit.n, treesE, wE, ctx, A, qE, r.source])
              #[hcheck, hA, he, hq]
            pure (r.source, proof)
        let proofNodes := (size + d.length) * (4 * k + 24)
        charge .proofNodes proofNodes
        trace[HexMatrix.certificate] "{(Json.mkObj (Certificate.fields selection "integer" ++ [
          ("entries", toJson "tree"), ("proof_node_budget", toJson proofNodes), ("atoms", toJson k)])).compress}"
        let target ← mkEq (← mkAppM ``Matrix.det #[A]) value
        return some { value, proof := ← checked target proof }

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
  let entries := normalized.map (·.map fun (_, rs) => rs.map (·.term)) |>.getD lit.entries
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
    let selected ← selectProvider .commRingNormalize ring
    -- Determinants also have universal integer transport. A residue capability
    -- decline does not remove this independently checked certificate route.
    let selected ← match selected with
      | .declined (.providerCondition id _) _ =>
        if id == HexReflectMathlib.residueCoefficientsId then
          pure (.success (.coefficients (← intCoeffProvider ring)) Budget.zero)
        else pure selected
      | _ => pure selected
    let .coefficients coeffs ← require selected
      | failWith (.internal "expected coefficient evidence")
    if coeffs.id == HexReflectMathlib.residueCoefficientsId then
      let_expr Hex.ZMod64 p _ := coeffs.coeffType
        | failWith (.internal "invalid residue coefficient type")
      let some p ← (Meta.evalNat p).run | decline m!"nonliteral residue characteristic"
      return ← computeResidue p coeffs A lit reified seed rhs sealed ctx
    let mut rows : List (List (MvPoly k Int Mono.grevlex)) := []
    let mut lists : Array (Array Poly) := #[]
    for row in reified do
      let mut polys := []
      let mut serial := #[]
      for r in row do
        let c ← profile "det.symbolic.convert" (do require (← convert r sealed .grevlex (some coeffs)))
        unless c.sealed.n == k do failWith (.internal "batch size changed")
        let ts := c.terms.map fun (m, z) => (m.toArray.toList, z)
        -- Conversion and reconstruction here execute in compiled code only.
        let p := MvPoly.ofTerms (cmp := Mono.grevlex)
          (ts.map fun (m, z) => (MvPoly.Kernel.mono k m, z))
        polys := polys ++ [p]
        serial := serial.push (profileit "det.symbolic.lists" options fun _ => Hex.PolyDet.toList p)
      rows := rows ++ [polys]
      lists := lists.push serial
    preflight lit.n k lists
    let check := fun rows w =>
      let (rows, w) := profileit "det.symbolic.lists" options fun _ =>
        (rows.map (List.map Hex.PolyDet.toList), w.map Hex.PolyDet.toList)
      profileit "det.symbolic.selfcheck" options fun _ =>
        Hex.Matrix.checkDetPolyList (Polynomial.ops k) lit.n rows w
    let produced := profileit "det.symbolic.producer" options fun _ =>
      Hex.PolyDet.produce producerBudget lit.n check rows
    let w ← requireWitness produced
    let w := profileit "det.symbolic.lists" options fun _ => w.map Hex.PolyDet.toList
    let d := Polynomial.value w
    let size := match w with
      | .triangular _ ts d => ts.foldl (fun n r => r.foldl (fun n p => n + p.length) n) d.length
      | .singular v => v.foldl (fun n p => n + p.length) 0
    checkBudget .proofNodes ((size + lists.flatten.foldl (fun n p => n + p.length) 0) * (4 * k + 24))
    let q ← match rhs with
      | some r =>
        let c ← profile "det.symbolic.convert" (do require (← convert r sealed .grevlex (some coeffs)))
        let p := MvPoly.ofTerms (cmp := Mono.grevlex)
          (c.terms.map fun (m, z) => (MvPoly.Kernel.mono k m.toArray.toList, z))
        pure (profileit "det.symbolic.lists" options fun _ => Hex.PolyDet.toList p)
      | none => pure d
    let left := if rat && rhs?.isSome then MvPoly.Kernel.smul (Int.ofNat t) d else d
    let right := if rat && rhs?.isSome then MvPoly.Kernel.smul (Int.ofNat D) q else q
    unless MvPoly.Kernel.beq left right do
      let value ← (denoteRingExpr sealed.atoms (expression d) : ReaderT Nat ReflectM Expr).run seed.ringId
      decline m!"target is not a polynomial identity in the sealed atoms; computed value is{indentExpr value}"
    let r ← match rhs with
      | some r => pure r
      | none =>
        let e := expression d
        let source ← (denoteRingExpr sealed.atoms e : ReaderT Nat ReflectM Expr).run seed.ringId
        pure { seed with expr := e, source }
    if let some result ← computeTree? A ctx lit k size reified lists w r rhs?
        normalized targetNorm scales D t then return result
    let rowsE := toExpr (lists.toList.map Array.toList)
    let wE ← quoteWitness w
    let (hcheck, selection) ← Certificate.integer k lit.n (lists.toList.map Array.toList) w rowsE wE
    let mut hrows := #[]
    for i in [:lit.n] do
      let mut hs := #[]
      for j in [:lit.n] do
        let h ← entryProof k ctx (reified[i]!.getD j seed) (lists[i]!)[j]! s!"entry ({i}, {j})"
        let h ← match normalized with
          | none => mkEqSymm h
          | some rs => mkEqTrans h (rs[i]!.2[j]!).proof
        hs := hs.push h
      hrows := hrows.push (← conjunction hs)
    let B ← mkAppM ``Polynomial.evaluated #[toExpr k, toExpr lit.n, rowsE, ctx]
    let he ← entryProof k ctx r q
    let targetCheck : ReflectM Expr := do
      decideProof (← mkEq (← mkAppM ``MvPoly.Kernel.beq #[toExpr left, toExpr right])
        (mkConst ``Bool.true))
    let (value, proof) ← if rat then do
      let sE := toExpr scales.toList
      let hA ← applyHint (← mkAppM ``Scaling.identify #[toExpr lit.n, A, B, sE])
        (← conjunction hrows)
      let hs ← decideProof (← mkEq (← mkAppM ``List.length #[sE]) (toExpr lit.n))
      let hdet := mkAppN (← mkAppM ``Polynomial.scaled_det
        #[toExpr k, toExpr lit.n, rowsE, wE, ctx, A, sE]) #[hcheck, hA, hs]
      let hD ← decideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr D])
      match targetNorm with
      | some qnorm =>
        let he ← mkEqTrans he qnorm.proof
        let ht ← decideProof (← mkAppM ``LT.lt #[toExpr (0 : Nat), toExpr t])
        let proof := mkAppN (← mkAppM ``Scaling.target
          #[toExpr k, toExpr lit.n, wE, ctx, A, sE, toExpr t, toExpr q, rhs?.get!])
          #[hdet, ht, hD, he, ← targetCheck]
        pure (rhs?.get!, proof)
      | none =>
        let h ← mkEqTrans hdet he
        let proof ← mkAppM ``Scaling.value #[toExpr D, ← mkAppM ``Matrix.det #[A], r.source, hD, h]
        if D == 1 then
          pure (r.source, ← mkEqTrans proof (← mkAppM ``div_one #[r.source]))
        else pure (← mkAppM ``HDiv.hDiv #[r.source, ← Normalize.natural D], proof)
    else do
      let hA ← applyHint (← mkAppM ``Polynomial.identify #[A, B]) (← conjunction hrows)
      let proof ← if rhs?.isSome then
        pure <| mkAppN (← mkAppM ``Polynomial.target_det
          #[toExpr k, toExpr lit.n, rowsE, wE, ctx, A, toExpr q, r.source])
          #[hcheck, hA, he, ← targetCheck]
      else
        pure <| mkAppN (← mkAppM ``Polynomial.result_det
          #[toExpr k, toExpr lit.n, rowsE, wE, ctx, A, r.source]) #[hcheck, hA, he]
      pure (r.source, proof)
    let proofNodes := (size + q.length + lists.flatten.foldl (fun n a => n + a.length) 0) * (4 * k + 24)
    charge .proofNodes proofNodes
    let witnessEntries := match w with
      | .triangular _ rows d => d :: rows.flatten
      | .singular v => v
    if ← isTracingEnabledFor `HexMatrix.certificate then
      reportCertificate "det-symbolic" (reprStr w) (witnessEntries.flatMap (List.map Prod.snd)) []
        (Certificate.fields selection "integer" ++ [("proof_node_budget", toJson proofNodes), ("atoms", toJson k),
         ("max_minor_support", toJson (witnessEntries.foldl (fun n p => max n p.length) 0)),
         ("max_minor_degree", toJson (witnessEntries.foldl (fun n p =>
           p.foldl (fun n (m, _) => max n (m.foldl (· + ·) 0)) n) 0))])
    let target ← mkEq (← mkAppM ``Matrix.det #[A]) value
    return { value, proof := ← checked target proof : Result }
  match outcome with
  | .success r _ => return .success r
  | .declined (.providerCondition _ reason) _ => return .declined m!"{reason}"
  | .declined d _ => return .declined d.toMessageData
  | .notApplicable => return .declined m!"no polynomial provider"
  | .failure f => throwError "det: {f.toMessageData}"

end HexMatrixMathlib.DetPoly.Frontend
