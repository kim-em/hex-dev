/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Modular
public meta import HexGenericRankMathlib.Modular
public meta import HexModArithMathlib.Ring
public meta import HexArith.Nat.Prime
public meta import HexGenericRankMathlib.Kernel
public meta import HexMvGcd.Instances
public meta import HexRankMathlib.Tactic
public meta import HexReflectMathlib
public meta import Lean

public meta section

namespace HexGenericRankMathlib.Provider

open Lean Meta Elab Hex Hex.Reflect
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64 HexGenericRankMathlib.Modular

deriving instance ToExpr for PolyWitness

/-- Limits for one symbolic matrix request. Case splitting is reserved and disabled. -/
structure Config where
  reflection : Hex.Reflect.Config := {}
  matrixSize : Nat := 4096
  caseSplits : Nat := 0
  conditions : ConditionPolicy := {}

/-- Static proof statistics; timing is supplied by Lean's profiler and the
external fresh-module runner, never by clocks in the provider. -/
structure Measurements where
  proofNodes : Nat := 0
  deriving ToJson

initialize registerTraceClass `Hex.genericRank

/-- The provider's checked data and both specialised bounds. -/
structure Result where
  rank : Nat
  batch : RingBatch
  polynomial : Expr
  certificate : Expr
  checked : Expr
  genericProof : Expr
  interpretation : Expr
  genericResult : Expr
  conditional : ConditionalResult
  upperProof : Expr
  denominator : Expr
  denominatorEq : Expr
  matrixSize : Nat
  measurements : Measurements

def id : ProviderId := { name := `HexGenericRankMathlib.Provider.rank }

/-- Read a symbolic literal through the numeric frontend's literal parsers. -/
partial def literal? (A : Expr) (n m : Nat) (carrier : Expr)
    (budget : Nat := HexMatrixMathlib.Literal.unfoldBudget) :
    MetaM (Option HexMatrixMathlib.Literal.Recognized) := do
  if A.hasExprMVar then return none
  if let some entries ← HexMatrixMathlib.Literal.matchChain? n m A then
    return some ⟨n, m, carrier, entries, .chain⟩
  if let some entries ← HexMatrixMathlib.Literal.matchFn? n m A then
    return some ⟨n, m, carrier, entries, .entrywise⟩
  if let some entries ← HexMatrixMathlib.Literal.matchOfArray? n m A then
    return some ⟨n, m, carrier, entries, .entrywise⟩
  if budget == 0 then return none
  if let some A' ← unfoldDefinition? A then literal? A' n m carrier (budget - 1)
  else return none

/-- Quote and kernel-check a closed Boolean certificate exactly once. -/
def checkedProof (proposition : Expr) : MetaM Expr := do
  HexMatrixMathlib.Literal.addClosedProof proposition
    (← HexMatrixMathlib.Literal.decideProof proposition)

/-- Give each synchronous declaration check its own Lean profiler category.
Nested profiler categories are disabled so the category includes kernel work;
construction of the Boolean proof remains outside it. -/
def checkedProfiled (category : String) (proposition : Expr) : MetaM Expr := do
  let value ← HexMatrixMathlib.Literal.decideProof proposition
  profileitM Exception category (← getOptions) <|
    withOptions (fun o => o.setBool `profiler false) <|
      HexMatrixMathlib.Literal.addClosedProof proposition value

/-- Build an equality of lists from the individual equality proofs. -/
def listEq (type : Expr) : List Expr → MetaM Expr
  | [] => do mkEqRefl (← mkListLit type [])
  | p :: ps => do mkAppM ``cons_eq #[p, ← listEq type ps]

/-- Run the polynomial certificate producer, then flatten its output for quotation. -/
def integerWitness (k n m : Nat) (L : PolyLists.Rows Int) : PolyWitness Int :=
  let P := PolyLists.matrix (k := k) n m L
  let c := GenericRank.genericCert P
  { rank := c.rank
    rows := c.rows.toList.map Fin.val
    cols := c.cols.toList.map Fin.val
    denom := MvPoly.Kernel.toList c.denom
    adj := c.adj.rows.toList.map fun row => row.toList.map MvPoly.Kernel.toList }

/-- Small signed representatives keep the displayed polynomial readable. -/
def balance (p : Nat) (a : Int) : Int :=
  let b := a % (p : Int)
  if 2 * b > p then b - p else b

/-- Produce over the selected residue carrier and quote only integer lists.
The runtime checks construct erased instances; the proof uses the coefficient
provider's bounds and primality evidence. -/
def residueWitness? (p k n m : Nat) (L : PolyLists.Rows Int) : Option (PolyWitness Int) := do
  if hb : 0 < p ∧ p < 2^31 then
    letI : ZMod64.Bounds p := ⟨hb.1, hb.2⟩
    if hp : Hex.Nat.Prime p then
      letI : ZMod64.PrimeModulus p := ⟨hp⟩
      let P := PolyLists.matrix (k := k) n m (Modular.castRows (C := ZMod64 p) L)
      let c := GenericRank.genericCert P
      -- `toList` omits zero residues; balancing a nonzero residue preserves
      -- nonvanishing modulo p. Thus a nonempty quoted denominator has a
      -- surviving head coefficient, as required by `Modular.nonzero`.
      let quotePoly (a : MvPoly k (ZMod64 p) Mono.grevlex) : PolyLists.Poly Int :=
        (MvPoly.Kernel.toList a).map fun t => (t.1, balance p (t.2.toNat : Int))
      return {
        rank := c.rank
        rows := c.rows.toList.map Fin.val
        cols := c.cols.toList.map Fin.val
        denom := quotePoly c.denom
        adj := c.adj.rows.toList.map fun row => row.toList.map quotePoly }
    else none
  else none

/-- Simplify only the evaluation syntax when displaying a condition. No local
hypothesis or field-specific identity changes the polynomial denominator. -/
def displayDenominator (d : Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for name in #[``interpret_cons, ``interpret_nil, ``Fin.prod_univ_succ,
      ``Fin.prod_univ_zero, ``Int.cast_zero, ``Int.cast_one, ``Int.cast_neg,
      ``Int.cast_ofNat, ``one_mul, ``mul_one, ``zero_mul, ``mul_zero,
      ``zero_add, ``add_zero, ``pow_zero, ``pow_one,
      ``map_intCast, ``map_natCast, ``map_zero, ``map_one, ``map_neg, ``neg_mul, ``neg_one_mul, ``Fin.val_zero, ``Fin.val_succ, ``List.getD_cons_zero, ``List.getD_cons_succ,
      ``Int.coe_castRingHom] do
    thms ← thms.addConst name
  thms ← thms.addDeclToUnfold ``Modular.cast
  thms ← thms.addConst ``List.map_cons
  thms ← thms.addConst ``List.map_nil
  thms ← thms.addDeclToUnfold ``Hex.Reflect.ctxValuation
  thms ← thms.addDeclToUnfold ``Lean.RArray.get
  thms ← thms.addConst ``sub_eq_add_neg (inv := true)
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← simp d ctx).1

/-- Normalize closed numeral conditions, allowing carrier and instance parameters. -/
def closedNormNum (p : Expr) : MetaM (Option Expr) := do
  if p.hasMVar then return none
  -- Type and instance parameters do not make a numeral condition symbolic.
  -- A source value variable still keeps the default normalizer out.
  for fvar in (collectFVars {} p).fvarIds do
    let type ← inferType (mkFVar fvar)
    unless (← whnf type).isSort || (← isClass? type).isSome do return none
  -- `norm_num`'s simplification step knows this even without CharZero.
  try
    let_expr Ne α _ _ := p | return none
    let proof ← mkAppOptM ``one_ne_zero #[α, none, none, none]
    if ← isDefEq (← inferType proof) p then return some proof
  catch _ => pure ()
  try
    let ⟨true, proof⟩ ← Mathlib.Meta.NormNum.deriveBool p | return none
    return some proof
  catch _ => return none

/-- Check rank-specific limits before matrix entries are enumerated. -/
def checkSize (cfg : Config) (n m : Nat) : Option Decline :=
  if n * m > cfg.matrixSize then
    some (.providerCondition id s!"budget exhausted in dimension matrix size: limit {cfg.matrixSize}, requested {n * m}")
  else if cfg.caseSplits != 0 then
    some (.providerCondition id "unsupported caseSplits configuration: piecewise rank is not implemented; the limit must be 0")
  else none

/-- Assemble function equality using only the closed finite indices and
an explicit equality proof for each value. -/
def finiteCongr (n : Nat) (f g : Expr) (prove : Expr → Expr → MetaM Expr) : MetaM Expr := do
  match n with
  | 0 => mkAppM ``fin_ext_nil #[f, g]
  | n + 1 =>
    let z ← HexMatrixMathlib.Literal.finLit (n + 1) 0
    let h ← prove (mkApp f z) (mkApp g z)
    let (ft, gt) ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit n)) fun i => do
      let si ← mkAppM ``Fin.succ #[i]
      return (← mkLambdaFVars #[i] (mkApp f si), ← mkLambdaFVars #[i] (mkApp g si))
    mkAppM ``fin_ext_cons #[f, g, h, ← finiteCongr n ft gt prove]

/-- Finite function equality whose values agree definitionally. -/
def finiteEq (n : Nat) (f g : Expr) : MetaM Expr :=
  finiteCongr n f g (fun a _ => mkEqRefl a)

/-- Identify a symbolic literal with its rows without deciding equality of atoms. -/
def identification (lit : HexMatrixMathlib.Literal.Recognized) (A source : Expr) : MetaM Expr := do
  match lit.route with
  | .chain => HexMatrixMathlib.Literal.identification lit A source
  | .entrywise =>
    let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[mkNatLit lit.n, mkNatLit lit.m, source]
    finiteCongr lit.n A ofL (finiteEq lit.m)

/-- Assemble the provider result from one sealed batch and one checked certificate. -/
def batchResult (A : Expr) (lit : HexMatrixMathlib.Literal.Recognized)
    (batch : RingBatch) (modulus : Option Nat := none) : MetaM Result := do
  let k := batch.sealed.n
  let n := lit.n
  let m := lit.m
  let some first := batch.entries[0]? | throwError "rank: empty reflection batch"
  let kE := mkNatLit k
  let nE := mkNatLit n
  let mE := mkNatLit m
  let C := first.conversion.provider.coeffType
  let mut flat : Array (PolyLists.Poly Int) := #[]
  for e in batch.entries do
    unless e.conversion.provider.id == first.conversion.provider.id do
      throwError "rank: mixed coefficient providers in one batch"
    flat := flat.push (MvPoly.Kernel.normalize
      (e.conversion.terms.map fun t => (t.1.toList,
        match modulus with | none => t.2 | some p => balance p t.2)))
  let L : PolyLists.Rows Int := (List.range n).map fun i =>
    (List.range m).map fun j => flat[i * m + j]!
  let c ← profileitM Exception "generic-rank producer" (← getOptions) do
    match modulus with
    | none => pure (integerWitness k n m L)
    | some p => match residueWitness? p k n m L with
      | some c => pure c
      | none => throwError "rank: invalid residue coefficient evidence"
  let passes := match modulus with
    | none => checkRankPolyList k n m L c
    | some p => Modular.checkRankPolyList p k n m L c
  unless passes do throwError "rank: the polynomial certificate failed its list check"
  let LE := toExpr L
  let cE := toExpr c
  let (header, pivot, upper) ← match modulus with
    | none => do
      pure (← mkAppM ``checkRankPolyHeader #[kE, nE, mE, LE, cE],
        ← mkAppM ``PolyLists.pivotCheck #[LE, cE],
        ← mkAppM ``PolyLists.upperCheck #[nE, mE, LE, cE])
    | some p => do
      pure (← mkAppM ``Modular.checkRankPolyHeader #[mkNatLit p, kE, nE, mE, LE, cE],
        ← mkAppM ``Modular.pivotCheck #[mkNatLit p, LE, cE],
        ← mkAppM ``Modular.upperCheck #[mkNatLit p, nE, mE, LE, cE])
  let hh ← checkedProfiled "generic-rank header kernel" (← mkEq header (mkConst ``Bool.true))
  let hp ← checkedProfiled "generic-rank pivot kernel" (← mkEq pivot (mkConst ``Bool.true))
  let hu ← checkedProfiled "generic-rank upper kernel" (← mkEq upper (mkConst ``Bool.true))
  let h ← match modulus with
    | none => mkAppM ``checkRankPolyList_parts #[hh, hp, hu]
    | some _ => mkAppM ``Modular.checkRankPolyList_parts #[hh, hp, hu]
  let checked ← match modulus with
    | none => mkAppM ``checkRankPolyList_sound #[h]
    | some p =>
      mkAppOptM ``Modular.checkRankPolyList_sound
        #[C, none, none, none, none, mkNatLit p, none, kE, nE, mE, LE, cE, h]
  let some (_, check, _) := (← inferType checked).eq? | throwError "rank: invalid check theorem"
  let args := check.getAppArgs
  let polynomial := args[args.size - 2]!
  let certificate := args[args.size - 1]!
  let genericProof ← mkAppM ``rank_eq #[checked]
  let ι ← match modulus with
    | none => mkAppOptM ``Int.castRingHom #[lit.carrier, none]
    | some p =>
      mkAppOptM ``HexReflectMathlib.residueHom
        #[mkNatLit p, none, lit.carrier, none, none]
  let lhsArgs := first.result.interpretation.getAppArgs
  let v := lhsArgs[lhsArgs.size - 2]!
  let mut entryProofs := #[]
  for idx in [:batch.entries.size] do
    let e := batch.entries[idx]?.getD first
    let ts := Hex.Reflect.quoteTerms e.conversion.sealed.n e.conversion.terms
    let raw := toExpr (e.conversion.terms.map fun t => (t.1.toList, t.2))
    let rawProof ← mkEqRefl raw
    let proof ← match modulus with
      | none => do
        let norm ← mkAppM ``MvPoly.Kernel.normalize #[raw]
        let normProof ← checkedProof (← mkEq norm (toExpr flat[idx]!))
        mkAppM ``interpret_entry
          #[ι, v, e.conversion.provider.ofInt, ts, raw, toExpr flat[idx]!, rawProof, normProof,
            e.input, e.result.proof]
      | some p => do
        let norm ← mkAppM ``MvPoly.Kernel.normalize #[raw]
        let equal ← mkAppM ``Modular.equal #[mkNatLit p, norm, toExpr flat[idx]!]
        let normProof ← checkedProof (← mkEq equal (mkConst ``Bool.true))
        mkAppM ``Modular.interpret_entry
          #[mkNatLit p, ι, v, ts, raw, toExpr flat[idx]!, rawProof, normProof, e.input, e.result.proof]
    entryProofs := entryProofs.push proof
  let rowProofs ← (List.range n).mapM fun i =>
    listEq lit.carrier ((entryProofs.toList.drop (i * m)).take m)
  let hL ← listEq (mkApp (mkConst ``List [← getDecLevel lit.carrier]) lit.carrier) rowProofs
  let rowType := mkApp (mkConst ``List [← getDecLevel lit.carrier]) lit.carrier
  let source ← mkListLit rowType (← lit.entries.toList.mapM fun row => mkListLit lit.carrier row.toList)
  let hA ← identification lit A source
  let coefficientRows ← match modulus with
    | none => pure LE
    | some _ => mkAppOptM ``Modular.castRows #[C, none, LE]
  let interpretation ← mkAppM ``interpret_matrix #[ι, v, coefficientRows, source, A, hL, hA]
  let d ← mkAppM ``Hex.Matrix.RankCert.denom #[certificate]
  let some (_, φ, _) := (← inferType (← mkAppM ``eval₂_comp #[ι, v])).eq?
    | throwError "rank: invalid evaluation transport theorem"
  let rawDenominator := mkApp (← mkAppM ``DFunLike.coe #[φ]) d
  let displayed ← displayDenominator rawDenominator
  let denominator := displayed.expr
  let denominatorEq ← displayed.getProof
  let zero ← mkAppOptM ``OfNat.ofNat #[lit.carrier, mkNatLit 0, none]
  let proposition ← mkAppM ``Ne #[denominator, zero]
  let condition : Condition := {
    proposition, provider := id.name, source := A, operation := "rank"
    reason := s!"the certificate denominator is a nonzero signed {c.rank} × {c.rank} minor of the polynomial matrix" }
  let rankFn := (← mkAppM ``Matrix.rank #[A]).appFn!
  let rankIdentification ← mkCongrArg rankFn interpretation
  let conditionalProof ← withLocalDeclD `denominator_ne_zero proposition fun hd => do
    let hdRaw ← mkAppM ``nonzero_of_display #[denominatorEq, hd]
    let hEq ← mkAppM ``rank_at #[ι, v, checked, hdRaw]
    mkLambdaFVars #[hd] (← mkEqTrans rankIdentification hEq)
  let S ← mkAppM ``symbolic #[polynomial]
  let ψ ← mkAppM ``MvPolynomial.eval₂Hom #[ι, v]
  let upper ← mkAppM ``rank_map_le #[ψ, S]
  let upper ← mkAppM ``Nat.le_trans #[upper, ← mkAppM ``Eq.le #[genericProof]]
  let upperProof ← mkAppM ``Nat.le_trans #[← mkAppM ``Eq.le #[rankIdentification], upper]
  let atoms ← mkArrayLit lit.carrier batch.sealed.atoms.toList
  let coeffType := first.conversion.provider.coeffType
  let coeffRing ← synthInstance (← mkAppM ``CommRing #[coeffType])
  let coeffDecEq ← synthInstance (← mkAppM ``DecidableEq #[coeffType])
  let coeffBEq ← synthInstance (← mkAppM ``BEq #[coeffType])
  let coeffLawfulBEq ← synthInstance (← mkAppOptM ``LawfulBEq #[coeffType, coeffBEq])
  let genericResult ← mkAppM ``GenericResult.mk
    #[mkNatLit c.rank, coeffRing, coeffDecEq, coeffBEq, coeffLawfulBEq,
      atoms, v, ι, polynomial, certificate, checked, genericProof, interpretation]
  return {
    rank := c.rank
    batch := batch
    polynomial := polynomial
    certificate := certificate
    checked := checked
    genericProof := genericProof
    interpretation := interpretation
    genericResult := genericResult
    upperProof := upperProof
    denominator := denominator
    denominatorEq := denominatorEq
    matrixSize := n * m
    measurements := {}
    conditional := {
      value := mkNatLit c.rank
      proof := conditionalProof
      conditions := #[condition]
      atoms := batch.sealed.atoms } }

/-- Substitute auxiliary instance lets out of every quoted result field. -/
def Result.mapExpr (r : Result) (f : Expr → Expr) : Result := { r with
  polynomial := f r.polynomial
  certificate := f r.certificate
  checked := f r.checked
  genericProof := f r.genericProof
  interpretation := f r.interpretation
  genericResult := f r.genericResult
  upperProof := f r.upperProof
  denominator := f r.denominator
  denominatorEq := f r.denominatorEq
  conditional := { r.conditional with
    value := f r.conditional.value
    proof := f r.conditional.proof
    conditions := r.conditional.conditions.map fun c => { c with
      proposition := f c.proposition
      source := f c.source } } }

/-- Use the coefficient provider's evidence locally, retaining its exact
instances in the emitted proof without leaking temporary local declarations. -/
def withEvidence (evidence : List Expr) (action : MetaM Result) : MetaM Result := do
  match evidence with
  | [] => action
  | e :: es =>
    withLetDecl `coefficientInstance (← inferType e) e fun x => do
      let r ← withEvidence es action
      return r.mapExpr (fun p => p.replaceFVar x e)

/-- Count distinct nodes of the shared emitted proof expressions. The batch
has already charged its own reconstruction; shared certificate and instance
subexpressions are counted once across the three outputs. -/
def proofNodeCount (expressions : Array Expr) (cap : Nat) : Nat :=
  ((expressions.forM visit).run ({} : ExprSet)).2.size
where
  visit (e : Expr) : StateM ExprSet Unit := do
    if (← get).size ≥ cap || (← get).contains e then return
    modify (·.insert e)
    match e with
    | .app f a => visit f; visit a
    | .lam _ t b _ | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ b | .proj _ _ b => visit b
    | _ => pure ()

/-- Reflect a whole symbolic matrix and return its checked certificate and
single conditional rank statement, without creating goals. -/
def rank (A : Expr) (cfg : Config := {}) : MetaM (ProviderOutcome Result) := do
  let A ← instantiateMVars A
  let some (n, m, carrier) ← HexMatrixMathlib.Literal.shape? (← inferType A)
    | return .notApplicable
  if let some d := checkSize cfg n m then return .declined d Budget.zero
  let some lit ← literal? A n m carrier | return .notApplicable
  let u ← getDecLevel carrier
  let .some _ ← trySynthInstance (mkApp (mkConst ``CommRing [u]) carrier)
    | return .notApplicable
  let .some _ ← trySynthInstance (← mkAppOptM ``IsDomain #[carrier, none])
    | return .notApplicable
  let mut inputs := lit.entries.flatten
  if inputs.isEmpty then
    inputs := #[← mkAppOptM ``OfNat.ofNat #[carrier, mkNatLit 0, none]]
  let batchOutcome ← profileitM Exception "generic-rank batch" (← getOptions) <|
    withOptions (fun o => o.setBool `profiler false) <|
      reflectRingBatch inputs MonoOrder.grevlex cfg.reflection
  match batchOutcome with
  | .notApplicable => return .notApplicable
  | .declined d u => return .declined d u
  | .failure f => return .failure f
  | .success batch usage =>
    let some first := batch.entries[0]? | return .failure (.internal "empty coefficient batch")
    let provider := first.conversion.provider
    let modulus ← if provider.id == intCoefficientsId then pure none
      else if provider.id == HexReflectMathlib.residueCoefficientsId then do
        let_expr Hex.ZMod64 p _ := provider.coeffType
          | return .failure (.invalidProviderEvidence id "invalid residue coefficient type")
        let some p ← (Meta.evalNat p).run
          | return .failure (.invalidProviderEvidence id "nonliteral characteristic")
        pure (some p)
      else return .declined (.missingCapability .gcd provider.coeffType) usage
    let r ← try
      withEvidence provider.auxInstances.toList do
        match modulus with
        | none => batchResult A lit batch
        | some p =>
          let charInst ← mkAppOptM ``Modular.residueChar #[mkNatLit p, none]
          let domainInst ← mkAppOptM ``Modular.residueDomain #[mkNatLit p, none, none]
          withEvidence [charInst, domainInst] (batchResult A lit batch modulus)
      catch ex =>
        if ex.isInterrupt then throw ex
        return .failure (.internal (← ex.toMessageData.toString))
    let limit := cfg.reflection.budget.proofNodes
    let r := Lean.ShareCommon.shareCommon r
    let nodes := proofNodeCount #[r.genericResult, r.conditional.proof, r.upperProof] (limit + 1)
    if usage.proofNodes + nodes > limit then
      return .declined (.budgetExhausted {
        dimension := .proofNodes
        limit := limit
        consumed := usage.proofNodes
        requested := nodes }) usage
    let r := { r with measurements := { r.measurements with proofNodes := nodes } }
    trace[Hex.genericRank] "{(toJson r.measurements).compress}"
    return .success r { usage with proofNodes := usage.proofNodes + nodes }

/-- Local coefficient evidence for an optional proof. -/
def withProofEvidence (evidence : List Expr) (action : MetaM (Option Expr)) :
    MetaM (Option Expr) := do
  match evidence with
  | [] => action
  | e :: es =>
    withLetDecl `coefficientInstance (← inferType e) e fun x => do
      return (← withProofEvidence es action).map fun proof => proof.replaceFVar x e

/-- Recognize precisely independent literal polynomial variables. The
characteristic-zero hypothesis is synthesized on the coefficient domain,
never assumed from the integer provider's presence. -/
def independent (A : Expr) (r : Result) : MetaM (Option Expr) := do
  let some (_, _, carrier) ← HexMatrixMathlib.Literal.shape? (← inferType A) | return none
  let_expr MvPolynomial σ D _ := carrier | return none
  let some first := r.batch.entries[0]? | return none
  let provider := first.conversion.provider
  let modulus ← if provider.id == intCoefficientsId then do
      let charZero ← mkAppOptM ``CharZero #[D, none]
      let .some _ ← trySynthInstance charZero | return none
      pure none
    else if provider.id == HexReflectMathlib.residueCoefficientsId then do
      let_expr Hex.ZMod64 p _ := provider.coeffType | return none
      let .some _ ← trySynthInstance (← mkAppOptM ``CharP #[D, none, p]) | return none
      pure (some p)
    else return none
  let mut indices := #[]
  for atom in r.batch.sealed.atoms do
    let_expr MvPolynomial.X _ _ _ i := atom | return none
    if i.hasFVar || i.hasMVar then return none
    indices := indices.push i
  let mut f ← mkAppOptM ``Matrix.vecEmpty #[σ]
  for i in indices.reverse do
    f ← mkAppM ``Matrix.vecCons #[i, f]
  let hf ← try
    checkedProof (← mkAppM ``Function.Injective #[f])
  catch _ => return none
  let lhsArgs := first.result.interpretation.getAppArgs
  let v := lhsArgs[lhsArgs.size - 2]!
  let xf ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit r.batch.sealed.n)) fun i => do
    let x ← mkAppOptM ``MvPolynomial.X #[D, σ, none, mkApp f i]
    mkLambdaFVars #[i] x
  let hv ← finiteEq r.batch.sealed.n v xf
  withProofEvidence provider.auxInstances.toList do
    match modulus with
    | none => return some (← mkAppM ``rank_variables_int
        #[v, f, hf, hv, r.checked, A, r.interpretation])
    | some p => return some (← mkAppM ``Modular.rank_variables_residue
        #[p, v, f, hf, hv, r.checked, A, r.interpretation])

/-- Discharge the single condition in the shared condition order. -/
def discharge (r : Result) (cfg : Config := {}) : MetaM (Option Expr) := do
  let policy := { cfg.conditions with
    normalizers := #[closedNormNum] ++ cfg.conditions.normalizers }
  let (resolved, unresolved) ← dischargeConditions r.conditional.conditions policy
  if !unresolved.isEmpty then return none
  return some (mkAppN r.conditional.proof (resolved.map (·.2)))

end HexGenericRankMathlib.Provider
