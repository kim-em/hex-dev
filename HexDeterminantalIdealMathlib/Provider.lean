/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib.Residue
public meta import HexDeterminantalIdeal.Residue
public meta import HexReflectMathlib
public meta import Lean

public meta section

namespace HexDeterminantalIdealMathlib.Provider

open Lean Meta Elab Hex Hex.Reflect
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

structure Config where
  reflection : Hex.Reflect.Config := {}
  matrixSize : Nat := 4096
  minorWork : Nat := 1000000
  conditions : ConditionPolicy := {}

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

/-- Primitive coefficient encodings supported by the minor checker. -/
inductive Encoding where
  | integer (rows : Rows Int)
  | residue (modulus : Nat) (rows : Rows Nat)

def Encoding.quote : Encoding → Expr
  | .integer L => toExpr L
  | .residue _ L => toExpr L

def Encoding.support : Encoding → Nat
  | .integer L => L.flatten.foldl (fun s e => max s e.length) 1
  | .residue _ L => L.flatten.foldl (fun s e => max s e.length) 1

def Encoding.operations (data : Encoding) (k : Nat) : MetaM Expr :=
  match data with
  | .integer _ => mkAppOptM ``Hex.Matrix.MinorArithmetic.poly
      #[mkConst ``Int, none, none, none, none, none, none, mkNatLit k]
  | .residue p _ => mkAppM ``Hex.Matrix.MinorArithmetic.residue #[mkNatLit p, mkNatLit k]

/-- One sealed matrix interpretation, shared by all requested thresholds. -/
structure Reified where
  A : Expr
  lit : HexMatrixMathlib.Literal.Recognized
  batch : RingBatch
  data : Encoding
  polynomial : Expr
  valuation : Expr
  coefficientMap : Expr
  interpretation : Expr
  shapeProof : Expr
  canonicalProof : Expr

def Reified.mapExpr (p : Reified) (f : Expr → Expr) : Reified := { p with
  A := f p.A, polynomial := f p.polynomial, valuation := f p.valuation
  coefficientMap := f p.coefficientMap, interpretation := f p.interpretation
  shapeProof := f p.shapeProof, canonicalProof := f p.canonicalProof }

/-- Use provider evidence locally and substitute every temporary instance out. -/
def withEvidence {α : Type} (map : α → (Expr → Expr) → α)
    (evidence : List Expr) (action : MetaM α) : MetaM α := do
  match evidence with
  | [] => action
  | e :: es => withLetDecl `coefficientInstance (← inferType e) e fun x => do
      let r ← withEvidence map es action
      return map r (fun p => p.replaceFVar x e)

def evidence (batch : RingBatch) : List Expr :=
  match batch.entries[0]? with
  | none => []
  | some e =>
    let provider := e.conversion.provider
    let extra := if provider.coeffType.isAppOfArity ``Hex.ZMod64 2 then
      let args := provider.coeffType.getAppArgs
      [mkApp2 (mkConst ``HexModArithMathlib.ZMod64.commRing) args[0]! args[1]!]
      else []
    provider.auxInstances.toList ++ extra

/-- Quote a previously sealed batch, also used by the default-rank handler. -/
def reifyBatch (A : Expr) (lit : HexMatrixMathlib.Literal.Recognized)
    (batch : RingBatch) : MetaM Reified := withEvidence Reified.mapExpr (evidence batch) do
  let n := lit.n
  let m := lit.m
  let carrier := lit.carrier
  let some first := batch.entries[0]? | throwError "rank_locus: empty batch"
  let provider := first.conversion.provider
  let modulus ← if provider.id == intCoefficientsId then pure none
    else if provider.id == HexReflectMathlib.residueCoefficientsId then do
      let_expr Hex.ZMod64 p _ := provider.coeffType
        | throwError "rank_locus: invalid residue provider"
      let some p ← (Meta.evalNat p).run | throwError "rank_locus: nonliteral characteristic"
      pure (some p)
    else throwError "rank_locus: declined: unsupported coefficient encoding"
  let k := batch.sealed.n
  let raw := batch.entries.map fun e => e.conversion.terms.map fun t => (t.1.toList, t.2)
  let (data, flat) := match modulus with
    | none =>
      let flat := raw.map MvPoly.Kernel.normalize
      (Encoding.integer ((List.range n).map fun i => (List.range m).map fun j => flat[i*m+j]!),
        flat.map toExpr)
    | some p =>
      let flat := raw.map (Hex.Matrix.Residue.reduce p)
      (Encoding.residue p ((List.range n).map fun i => (List.range m).map fun j => flat[i*m+j]!),
        flat.map toExpr)
  let LE := data.quote
  let coefficientRows ← match modulus with
    | none => pure LE
    | some p => mkAppM ``Residue.rows #[mkNatLit p, LE]
  let ι ← match modulus with
    | none => mkAppOptM ``Int.castRingHom #[carrier, none]
    | some p => mkAppOptM ``HexReflectMathlib.residueHom #[mkNatLit p, none, carrier, none, none]
  let args := first.result.interpretation.getAppArgs
  let v := args[args.size - 2]!
  let mut entryProofs := #[]
  for idx in [:n*m] do
    let e := batch.entries[idx]?.getD first
    unless e.conversion.provider.id == provider.id do
      throwError "rank_locus: mixed coefficient providers"
    let ts := Hex.Reflect.quoteTerms e.conversion.sealed.n e.conversion.terms
    let rawE := toExpr raw[idx]!
    let hraw ← mkEqRefl rawE
    let proof ← match modulus with
      | none => do
        let hn ← checkedProof (← mkEq (← mkAppM ``MvPoly.Kernel.normalize #[rawE]) flat[idx]!)
        mkAppM ``interpret_entry
          #[ι, v, provider.ofInt, ts, rawE, flat[idx]!, hraw, hn, e.input, e.result.proof]
      | some p => do
        let he ← checkedProof (← mkEq (← mkAppM ``Residue.exponents #[mkNatLit k, rawE]) (toExpr true))
        let hn ← checkedProof (← mkEq
          (← mkAppM ``Hex.Matrix.Residue.reduce #[mkNatLit p, rawE]) flat[idx]!)
        mkAppM ``Residue.interpret_entry
          #[mkNatLit p, ι, v, ts, rawE, flat[idx]!, hraw, he, hn, e.input, e.result.proof]
    entryProofs := entryProofs.push proof
  let rowProofs ← (List.range n).mapM fun i => listEq carrier ((entryProofs.toList.drop (i*m)).take m)
  let rowType := mkApp (mkConst ``List [← getDecLevel carrier]) carrier
  let hL ← listEq rowType rowProofs
  let source ← mkListLit rowType (← lit.entries.toList.mapM fun row => mkListLit carrier row.toList)
  let hA ← identification lit A source
  let interpretation ← mkAppM ``interpret_matrix #[ι, v, coefficientRows, source, A, hL, hA]
  let polynomial ← mkAppM ``polynomial #[mkNatLit n, mkNatLit m, mkNatLit k, coefficientRows]
  let shapeProof ← checkedProof (← mkEq (← mkAppM ``shape #[mkNatLit n, mkNatLit m, LE]) (toExpr true))
  let valid ← match modulus with
    | none => mkAppM ``canonical #[mkNatLit k, LE]
    | some p => mkAppM ``Residue.canonical #[mkNatLit p, mkNatLit k, LE]
  let canonicalProof ← checkedProof (← mkEq valid (toExpr true))
  if batch.entries.all (fun e => e.conversion.terms.all (fun t => t.1.toList.all (· == 0))) then
    logInfo "rank_locus: the matrix entries are constant polynomials; its generators are constants"
  return {
    A, lit, batch, data, polynomial, valuation := v, coefficientMap := ι
    interpretation, shapeProof, canonicalProof }

/-- Reflect a literal once and quote canonical primitive polynomial entries. -/
def reify (A : Expr) (cfg : Config := {}) : MetaM Reified := do
  let A ← instantiateMVars A
  let some (n, m, carrier) ← HexMatrixMathlib.Literal.shape? (← inferType A)
    | throwError "rank_locus: expected a matrix with closed finite dimensions"
  if n * m > cfg.matrixSize then
    throwError "rank_locus: declined: matrixSize {n * m} exceeds {cfg.matrixSize}"
  let some lit ← literal? A n m carrier
    | throwError "rank_locus: declined: unsupported matrix literal"
  let _ ← synthInstance (← mkAppOptM ``IsDomain #[carrier, none])
  let mut inputs := lit.entries.flatten
  if inputs.isEmpty then inputs := #[← mkAppOptM ``OfNat.ofNat #[carrier, mkNatLit 0, none]]
  let batch ← match ← profileitM Exception "rank-locus batch" (← getOptions) <|
      withOptions (fun o => o.setBool `profiler false) <|
        reflectRingBatch inputs MonoOrder.grevlex cfg.reflection with
    | .success b _ => pure b
    | .notApplicable => throwError "rank_locus: entries are outside the ring fragment"
    | .declined d _ => throwError "rank_locus: declined: {d.toMessageData}"
    | .failure f => throwError "rank_locus: {f.toMessageData}"
  reifyBatch A lit batch

/-- Factorial-weighted support budget, charged before any minor enumeration. -/
def checkWork (p : Reified) (r : Nat) (cfg : Config) : MetaM Unit := do
  if r > min p.lit.n p.lit.m then return
  let support := p.data.support
  let work := p.lit.n.choose r * p.lit.m.choose r * r.factorial * support^r
  if work > cfg.minorWork then
    throwError "rank_locus: declined: minorWork {work} exceeds {cfg.minorWork}"

initialize registerTraceClass `Hex.rankLocus

/-- Account for shared proof expressions as well as the original batch. -/
def checkProofBudget (p : Reified) (proofs : Array Expr) (cfg : Config) : MetaM Nat := do
  let limit := cfg.reflection.budget.proofNodes
  let nodes := Hex.Reflect.proofNodeCount proofs (limit + 1)
  if p.batch.usage.proofNodes + nodes > limit then
    throwError "rank_locus: declined: proofNodes {p.batch.usage.proofNodes + nodes} exceeds {limit}"
  trace[Hex.rankLocus] "proofNodes: {nodes}"
  return nodes

structure Generator where
  encoded : Expr
  value : Expr
  display : Expr
  equality : Expr

/-- Denote a computed polynomial in the original source expressions. -/
def display (p : Reified) (g : Expr) : MetaM Generator := do
  let (value, valueEq) ← match p.data with
    | .integer _ => do
      let v ← mkAppM ``denote #[mkNatLit p.batch.sealed.n, g]
      pure (v, ← mkEqRefl v)
    | .residue q _ => do
      let v ← mkAppM ``Residue.denote #[mkNatLit q, mkNatLit p.batch.sealed.n, g]
      pure (v, ← mkAppM ``Residue.denote_eq #[mkNatLit q, mkNatLit p.batch.sealed.n, g])
  let hom ← mkAppM ``evaluation #[p.coefficientMap, p.valuation]
  let f ← mkAppM ``DFunLike.coe #[hom]
  let some (_, _, semantic) := (← inferType valueEq).eq? | throwError "invalid denotation equality"
  let shown ← HexReflectMathlib.displayPolynomial (mkApp f semantic)
    #[``evaluation, ``denote, ``MvPoly.Kernel.toResidues, ``MvPoly.Kernel.CoeffMap.map]
  let equality ← mkEqTrans (← mkCongrArg f valueEq) (← shown.getProof)
  return { encoded := g, value, display := shown.expr, equality }

def Generator.mapExpr (g : Generator) (f : Expr → Expr) : Generator := {
  encoded := f g.encoded, value := f g.value, display := f g.display, equality := f g.equality }

structure Result where
  matrix : Reified
  threshold : Nat
  generators : Array Generator
  generatorsProof : Expr
  displayProof : Expr
  iffProof : Expr

def Result.mapExpr (r : Result) (f : Expr → Expr) : Result := { r with
  matrix := r.matrix.mapExpr f, generators := r.generators.map (·.mapExpr f)
  generatorsProof := f r.generatorsProof, displayProof := f r.displayProof, iffProof := f r.iffProof }

/-- Certify every generator and return the exact displayed iff. -/
def locus (p : Reified) (r : Nat) (cfg : Config := {}) : MetaM Result :=
    withEvidence Result.mapExpr (evidence p.batch) do
  checkWork p r cfg
  let k := p.batch.sealed.n
  let (GE, encoded) ← profileitM Exception "rank-locus enumeration" (← getOptions) do
    match p.data with
    | .integer L =>
      let G := Hex.Matrix.detIdealGensList (Hex.Matrix.MinorArithmetic.poly (C := Int) k) r L
      pure (toExpr G, G.toArray.map toExpr)
    | .residue q L =>
      let G := Hex.Matrix.detIdealGensList (Hex.Matrix.MinorArithmetic.residue q k) r L
      pure (toExpr G, G.toArray.map toExpr)
  let computation ← mkAppM ``Hex.Matrix.detIdealGensList
    #[← p.data.operations k, mkNatLit r, p.data.quote]
  let checked ← checkedProfiled "rank-locus enumeration kernel" (← mkEq computation GE)
  let args := #[p.data.quote, p.shapeProof, p.canonicalProof, mkNatLit r, GE, checked]
  let generatorsProof ← match p.data with
    | .integer _ => mkAppM ``generators args
    | .residue q _ => mkAppM ``Residue.generators (#[mkNatLit q] ++ args)
  let gs ← encoded.mapM (display p)
  let displayProof ← listEq p.lit.carrier (gs.toList.map (·.equality))
  let some (_, values, _) := (← inferType generatorsProof).eq? | throwError "invalid generator proof"
  let shown ← mkListLit p.lit.carrier (gs.toList.map (·.display))
  let iffProof ← mkAppM ``HexDeterminantalIdealMathlib.locus
    #[p.coefficientMap, p.valuation, p.polynomial, p.A, p.interpretation,
      mkNatLit r, values, generatorsProof, shown, displayProof]
  let _ ← checkProofBudget p #[p.interpretation, iffProof] cfg
  return { matrix := p, threshold := r, generators := gs, generatorsProof, displayProof, iffProof }

/-- The hypothesis type uses the expanded conjunction in source expressions. -/
def Result.proposition (r : Result) : MetaM Expr := do
  let zero ← mkAppOptM ``OfNat.ofNat #[r.matrix.lit.carrier, mkNatLit 0, none]
  let ps ← r.generators.toList.mapM (fun g => mkEq g.display zero)
  let rec conjunction : List Expr → Expr
    | [] => mkConst ``True
    | [p] => p
    | p :: q :: ps => mkApp2 (mkConst ``And) p (conjunction (q :: ps))
  let lhs ← mkAppM ``LT.lt #[← mkAppM ``Matrix.rank #[r.matrix.A], mkNatLit r.threshold]
  mkAppM ``Iff #[lhs, conjunction ps]

/-- The first automatic tier includes reflexive equalities. -/
def reflexive (p : Expr) : MetaM (Option Expr) := do
  let some (_, a, b) := p.eq? | return none
  if ← isDefEq a b then return some (← mkEqRefl a)
  return none

def policy (cfg : Config) : ConditionPolicy := {
  normalizers := #[reflexive, HexReflectMathlib.closedNormNum] ++ cfg.conditions.normalizers }

def condition (p : Reified) (g : Generator) (nonzero : Bool) : MetaM Condition := do
  let zero ← mkAppOptM ``OfNat.ofNat #[p.lit.carrier, mkNatLit 0, none]
  let proposition ← if nonzero then mkAppM ``Ne #[g.display, zero] else mkEq g.display zero
  return {
    proposition, source := p.A, provider := `rank_locus, operation := "rank_locus"
    reason := "vanishing or nonvanishing of a displayed determinantal generator" }

structure LowerResult where
  generator : Generator
  rows : List Nat
  cols : List Nat
  condition : Condition
  proof : Expr
  resolved : Option Expr

def LowerResult.mapExpr (r : LowerResult) (f : Expr → Expr) : LowerResult := { r with
  generator := r.generator.mapExpr f, proof := f r.proof, resolved := r.resolved.map f
  condition := { r.condition with proposition := f r.condition.proposition, source := f r.condition.source } }

/-- Producer-side candidate enumeration; no proof evaluates all minor values. -/
def candidates {α : Type} (ops : Hex.Matrix.MinorArithmetic α) (L : List (List α))
    (n m r : Nat) : List (List Nat × List Nat × α) := Id.run do
  let mut result := []
  let mut seen := []
  for rows in Hex.Matrix.indexTuples r n do
    for cols in Hex.Matrix.indexTuples r m do
      let g := Hex.Matrix.minorList ops rows cols L
      if !ops.isZero g && !seen.any (ops.beq g) then
        seen := g :: seen
        result := (rows, cols, g) :: result
  return result.reverse

/-- Try all generators automatically before selecting an unresolved one.
Only the selected minor's memberships and value are checked in the kernel. -/
def lower (p : Reified) (r : Nat) (cfg : Config := {}) : MetaM LowerResult :=
    withEvidence LowerResult.mapExpr (evidence p.batch) do
  checkWork p r cfg
  let k := p.batch.sealed.n
  let encoded : List (List Nat × List Nat × Expr) := match p.data with
    | .integer L => (candidates (Hex.Matrix.MinorArithmetic.poly (C := Int) k) L p.lit.n p.lit.m r).map
        (fun t => (t.1, t.2.1, toExpr t.2.2))
    | .residue q L => (candidates (Hex.Matrix.MinorArithmetic.residue q k) L p.lit.n p.lit.m r).map
        (fun t => (t.1, t.2.1, toExpr t.2.2))
  let mut choices : Array (List Nat × List Nat × Generator × Condition) := #[]
  for (rows, cols, g) in encoded do
    let shown ← display p g
    choices := choices.push (rows, cols, shown, ← condition p shown true)
  let some first := choices[0]?
    | throwError "rank_locus: declined: no nonzero polynomial minor at threshold {r}"
  let (resolved, _) ← dischargeConditions (choices.map (·.2.2.2)) (policy cfg)
  let chosen ← match resolved[0]? with
    | none => pure first
    | some (c, _) =>
      let some found := choices.find? (fun a => a.2.2.2.proposition == c.proposition)
        | throwError "rank_locus: invalid condition selection"
      pure found
  let (rows, cols, g, c) := chosen
  let hr ← checkedProof (← mkAppM ``Membership.mem
    #[← mkAppM ``Hex.Matrix.indexTuples #[mkNatLit r, mkNatLit p.lit.n], toExpr rows])
  let hc ← checkedProof (← mkAppM ``Membership.mem
    #[← mkAppM ``Hex.Matrix.indexTuples #[mkNatLit r, mkNatLit p.lit.m], toExpr cols])
  let comp ← mkAppM ``Hex.Matrix.minorList
    #[← p.data.operations k, toExpr rows, toExpr cols, p.data.quote]
  let hg ← checkedProfiled "rank-locus selected minor kernel" (← mkEq comp g.encoded)
  let args := #[p.data.quote, p.shapeProof, p.canonicalProof, mkNatLit r,
      toExpr rows, toExpr cols, hr, hc, g.encoded, hg]
  let membership ← match p.data with
    | .integer _ => mkAppM ``selected args
    | .residue q _ => mkAppM ``Residue.selected (#[mkNatLit q] ++ args)
  let proof ← withLocalDeclD `minor_ne_zero c.proposition fun h => do
    mkLambdaFVars #[h] (← mkAppM ``minor_lower
      #[p.coefficientMap, p.valuation, p.polynomial, p.A, p.interpretation,
        mkNatLit r, g.value, membership, g.display, g.equality, h])
  let _ ← checkProofBudget p #[p.interpretation, proof] cfg
  return { generator := g, rows, cols, condition := c, proof, resolved := resolved[0]?.map (·.2) }

/-- Detect the symbolic-matrix case using the same atom and coefficient
conditions as generic rank. Return the coefficient and variable types too. -/
def ideal? (r : Result) (fieldLevel : Level) : MetaM (Option (Expr × Expr × Expr)) := do
  let p := r.matrix
  let_expr MvPolynomial σ D _ := p.lit.carrier | return none
  match p.data with
  | .integer _ =>
    let .some _ ← trySynthInstance (← mkAppOptM ``CharZero #[D, none]) | return none
  | .residue q _ =>
    let .some _ ← trySynthInstance (← mkAppOptM ``CharP #[D, none, mkNatLit q]) | return none
  let mut indices := #[]
  for atom in p.batch.sealed.atoms do
    let_expr MvPolynomial.X _ _ _ i := atom | return none
    if i.hasFVar || i.hasMVar then return none
    indices := indices.push i
  let mut f ← mkAppOptM ``Matrix.vecEmpty #[σ]
  for i in indices.reverse do f ← mkAppM ``Matrix.vecCons #[i, f]
  let hf ← try checkedProof (← mkAppM ``Function.Injective #[f]) catch _ => return none
  let xf ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit p.batch.sealed.n)) fun i => do
    let x ← mkAppOptM ``MvPolynomial.X #[D, σ, none, mkApp f i]
    mkLambdaFVars #[i] x
  let hv ← finiteEq p.batch.sealed.n p.valuation xf
  let levels := [← getDecLevel D, ← getDecLevel σ, fieldLevel]
  let args := #[p.valuation, f, hf, hv, p.polynomial, mkNatLit r.threshold]
  let data ← match p.data with
    | .integer _ => mkAppM' (mkConst ``idealData_int levels) args
    | .residue q _ => mkAppM' (mkConst ``Residue.idealData levels) (#[mkNatLit q] ++ args)
  return some (D, σ, data)

/-- Return the fixed record; this interface never creates side goals. -/
def result (r : Result) (cfg : Config := {}) (fieldLevel : Level := .zero) : MetaM Expr := withEvidence (fun p f => f p) (evidence r.matrix.batch) do
  let p := r.matrix
  let env ← mkListLit p.lit.carrier p.batch.sealed.atoms.toList
  let len ← mkEqRefl (mkNatLit p.batch.sealed.n)
  let v ← mkAppM ``HexMatrixMathlib.vecOfList #[mkNatLit p.batch.sealed.n, env]
  let sealed ← finiteEq p.batch.sealed.n p.valuation v
  let some (_, values, _) := (← inferType r.generatorsProof).eq?
    | throwError "rank_locus: invalid generator theorem"
  let shown ← mkListLit p.lit.carrier (r.generators.toList.map (·.display))
  let some first := p.batch.entries[0]? | throwError "rank_locus: empty batch"
  let C := first.conversion.provider.coeffType
  let ring ← synthInstance (← mkAppM ``CommRing #[C])
  let decEq ← synthInstance (← mkAppM ``DecidableEq #[C])
  let beq ← synthInstance (← mkAppM ``BEq #[C])
  let lawful ← synthInstance (← mkAppOptM ``LawfulBEq #[C, beq])
  let poly ← mkAppM ``PolyData.mk
    #[ring, decEq, beq, lawful, env, len, p.valuation, sealed, p.coefficientMap, p.polynomial,
      values, r.generatorsProof, p.interpretation, r.displayProof]
  let ideal ← match ← ideal? r fieldLevel with
    | some (_, _, data) => mkAppM ``Option.some #[data]
    | none => do
      let type ← mkAppM' (mkConst ``IdealData [← getDecLevel p.lit.carrier, .zero, fieldLevel])
        #[p.coefficientMap, p.valuation, p.polynomial, mkNatLit r.threshold,
          p.lit.carrier, mkConst ``Empty]
      mkAppOptM ``Option.none #[type]
  let result ← mkAppM ``LocusResult.mk #[shown, r.iffProof, poly, ideal]
  let _ ← checkProofBudget p #[result] cfg
  return result

/-- Programmatic entry point returning the same checked record as `rank_locus%`.
`fieldLevel` selects the universe of the ideal payload's field-valued points.
It never creates goals or changes the source context. -/
def rankLocus (A : Expr) (r : Nat) (cfg : Config := {}) (fieldLevel : Level := .zero) : MetaM Expr := do
  result (← locus (← reify A cfg) r cfg) cfg fieldLevel

end HexDeterminantalIdealMathlib.Provider
