/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.State
public import HexReflect.Proof
public import Lean.Meta.Sym.Arith
public import Lean.Data.RArray
public meta import HexReflect.State
public meta import HexReflect.Proof
public meta import HexMvPoly
public meta import HexBasic
public meta import Lean

public meta section

/-!
The reflection session: atom allocation, batch reification, sealing, provider
selection, direct conversion, and proof reconstruction.

Every operation is polymorphic over the capabilities it uses (`SymM`
lifting, session state, and errors), so the same operation can run over the
standalone `ReflectM` or over a richer monad that already sits above `SymM`.
A standalone invocation calls `SymM.run` exactly once, in `run`.

Each entry point instantiates metavariables, declines while any relevant
metavariable remains, canonicalizes the source and its carrier, classifies
the canonical carrier, and only then consults caches and the reifier with the
exact instances recorded by the classification.
-/

namespace Hex.Reflect

open Lean Meta Sym Arith

attribute [hex_reflect_provider] intCoefficients

/-- The standalone canonicalization capabilities of `SymM`. -/
instance : MonadCanon SymM where
  canonExpr := Sym.canon
  synthInstance? := Sym.synthInstance?

/-- The standalone session monad. -/
abbrev ReflectM := StateRefT State SymM

/-- Session configuration. -/
structure Config where
  budget : Budget := Budget.default
  /-- The `Lean.Meta.Sym.Arith` numeral-evaluation threshold. It governs
  classification and reification only, not polynomial expansion. -/
  expThreshold : Nat := 8
  /-- Type-check every generated proof and report an ill-typed proof as a
  failure. -/
  checkProofs : Bool := false

section Ops

variable {m : Type → Type} [Monad m] [MonadLiftT SymM m] [MonadLiftT MetaM m]
  [MonadStateOf State m] [MonadError m]

/-! # Declines, failures, and budgets -/

/-- Record a decline and abort the current entry point. -/
def declineWith (d : Decline) : m α := do
  modifyThe State fun s => { s with pendingDecline := some d, declines := s.declines.push d }
  throwError "hex-reflect declined: {d.toMessageData}"

/-- Record a failure and abort the current entry point. -/
def failWith (f : Failure) : m α := do
  modifyThe State fun s => { s with pendingFailure := some f, failures := s.failures.push f }
  throwError "hex-reflect failure: {f.toMessageData}"

/-- Consume `amount` in dimension `d`, declining on exhaustion. -/
def charge (d : BudgetDimension) (amount : Nat) : m Unit := do
  let s ← getThe State
  match s.budget.charge d amount with
  | .ok b => set { s with budget := b }
  | .error e => declineWith (.budgetExhausted e)

/-- Check that `amount` fits dimension `d` without consuming it. -/
def checkBudget (d : BudgetDimension) (amount : Nat) : m Unit := do
  match (← getThe State).budget.check d amount with
  | .ok () => return ()
  | .error e => declineWith (.budgetExhausted e)

/-- The budget consumed so far. -/
def consumed : m BudgetUsage :=
  return (← getThe State).budget.consumed

/-- Run an entry point, turning a recorded decline or failure into the
corresponding outcome and reporting the budget it consumed. Other exceptions
propagate. -/
def withOutcome (x : m α) : m (ProviderOutcome α) := do
  let before ← consumed
  modifyThe State fun s => { s with pendingDecline := none, pendingFailure := none }
  try
    let v ← x
    return .success v ((← consumed).sub before)
  catch ex =>
    let s ← getThe State
    if let some f := s.pendingFailure then
      set { s with pendingFailure := none }
      return .failure f
    if let some d := s.pendingDecline then
      set { s with pendingDecline := none }
      return .declined d (s.budget.consumed.sub before)
    throw ex

/-! # Atoms -/

/-- A capped count of source syntax nodes. -/
partial def sourceNodeCount (e : Expr) (cap : Nat) : Nat :=
  go e 0
where
  go (e : Expr) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match e with
    | .app f a => go a (go f (acc + 1))
    | .lam _ t b _ | .forallE _ t b _ => go b (go t (acc + 1))
    | .letE _ t v b _ => go b (go v (go t (acc + 1)))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b (acc + 1)
    | _ => acc + 1

/-- Intern a canonical atom in the growing environment, assigning consecutive
identifiers. Repeated canonical atoms receive the same identifier. -/
def mkAtom (e : Expr) : m Nat := do
  let e ← (Sym.canon e : SymM Expr)
  let s ← getThe State
  match s.vars with
  | .sealed .. => failWith (.internal "atom allocation after sealing")
  | .growing atoms index =>
    if let some i := index[({ expr := e } : ExprPtr)]? then
      return i
    charge .atoms 1
    let i := atoms.size
    modifyThe State fun s =>
      { s with vars := .growing (atoms.push e) (index.insert { expr := e } i) }
    return i

/-- Read an atom by identifier; an invalid identifier is an internal failure. -/
def getAtom (i : Nat) : m Expr := do
  let atoms := (← getThe State).vars.atoms
  if h : i < atoms.size then
    return atoms[i]
  else
    failWith (.variableOutOfRange i atoms.size)

/-- The ordered atoms allocated so far. -/
def atoms : m (Array Expr) :=
  return (← getThe State).vars.atoms

instance : MonadMkVar m where
  mkVar := mkAtom

/-- Canonicalization through the lifted `SymM`. -/
instance : MonadCanon m where
  canonExpr e := (Sym.canon e : SymM Expr)
  synthInstance? e := (Sym.synthInstance? e : SymM (Option Expr))

instance : MonadGetVar m where
  getVar := getAtom

/-- Seal the environment at its current size. Sealing an already sealed
environment returns the same sealed identity. -/
def sealAtoms : m Sealed := do
  let s ← getThe State
  match s.vars with
  | .growing atoms _ =>
    let epoch := s.sealEpoch + 1
    set { s with vars := .sealed atoms.size atoms rfl, sealEpoch := epoch }
    return { n := atoms.size, atoms := atoms, size_eq := rfl, epoch := epoch }
  | .sealed n atoms h =>
    return { n := n, atoms := atoms, size_eq := h, epoch := s.sealEpoch }

/-- The sealed environment, if sealing has happened. -/
def sealed? : m (Option Sealed) := do
  let s ← getThe State
  match s.vars with
  | .growing .. => return none
  | .sealed n atoms h => return some { n := n, atoms := atoms, size_eq := h, epoch := s.sealEpoch }

/-! # Views over the `Sym.Arith` classification state -/

/-- Error reporting through the classification reader. -/
instance : MonadError (ReaderT Nat m) where
  add ref msg := (AddErrorMessageContext.add ref msg : m _)

/-- Commutative-ring capabilities for the classification identity supplied by
the reader. The record is read from, and written back to,
`Lean.Meta.Sym.Arith.State`. -/
instance : MonadCommRing (ReaderT Nat m) where
  getCommRing := do
    let id ← read
    let s ← (getArithState : SymM Arith.State)
    return s.rings[id]!
  modifyCommRing f := do
    let id ← read
    (modifyArithState fun s => { s with rings := s.rings.modify id f } : SymM Unit)

/-- Commutative-semiring capabilities for the classification identity supplied
by the reader. -/
instance : MonadCommSemiring (ReaderT Nat m) where
  getCommSemiring := do
    let id ← read
    let s ← (getArithState : SymM Arith.State)
    return s.semirings[id]!
  modifyCommSemiring f := do
    let id ← read
    (modifyArithState fun s => { s with semirings := s.semirings.modify id f } : SymM Unit)

/-- The classification record of a reified ring, read from `SymM`. -/
def ringOf (r : ReifiedRing) : m Arith.CommRing := do
  let s ← (getArithState : SymM Arith.State)
  if h : r.ringId < s.rings.size then
    return s.rings[r.ringId]
  else
    failWith (.internal "stale ring classification identity")

/-! # Entry points -/

/-- Instantiate, check for metavariables, and canonicalize a source expression
and its carrier. -/
def prepare (input : Expr) : m (Expr × Expr) := do
  let e ← (instantiateMVarsS input : SymM Expr)
  if e.hasMVar then declineWith (.unresolvedMetavariable e)
  let carrier ← (inferType e : MetaM Expr)
  let carrier ← (instantiateMVarsS carrier : SymM Expr)
  if carrier.hasMVar then declineWith (.unresolvedMetavariable carrier)
  let e ← (shareCommon e : SymM Expr)
  let e ← (Sym.canon e : SymM Expr)
  let carrier ← (shareCommon carrier : SymM Expr)
  let carrier ← (Sym.canon carrier : SymM Expr)
  let limit := (← getThe State).budget.remaining.sourceNodes
  charge .sourceNodes (sourceNodeCount e (limit + 1))
  return (e, carrier)

private def describeClassification : ClassifyResult → String
  | .commRing _ => "commutative ring"
  | .nonCommRing _ => "non-commutative ring"
  | .commSemiring _ => "commutative semiring"
  | .nonCommSemiring _ => "non-commutative semiring"
  | .none => "unclassified"

/-- Reify one commutative-ring input, allocating atoms in the growing
environment. -/
def reifyCommRing (input : Expr) : m (ProviderOutcome ReifiedRing) := withOutcome do
  let (e, carrier) ← prepare input
  match ← (classify? carrier : SymM ClassifyResult) with
  | .commRing id =>
    let ring := (← (getArithState : SymM Arith.State)).rings[id]!
    let key : ViewKey := {
      source := e
      carrier := carrier
      view := .commRing
      structureId := id
      instances := #[ring.commRingInst, ring.ringInst, ring.semiringInst] }
    if let some r := (← getThe State).views.ring.find? (·.key.agrees key) then
      return r
    let some re ← (reifyRing? e (skipVar := false) : ReaderT Nat m (Option RingExpr)).run id
      | failWith (.internal "ring reifier returned nothing with atoms enabled")
    charge .exponent (RingExpr.maxExponent re)
    charge .reflectedNodes (RingExpr.size re)
    let r : ReifiedRing := {
      key := key
      source := e
      carrier := carrier
      ringId := id
      charInst? := ring.charInst?
      expr := re }
    modifyThe State fun s => { s with views := { s.views with ring := s.views.ring.push r } }
    return r
  | .none => declineWith (.unsupportedCarrier carrier)
  | other => declineWith (.unsupportedView .commRing (describeClassification other))

/-- Reify one commutative-semiring input, allocating atoms in the growing
environment. -/
def reifyCommSemiring (input : Expr) : m (ProviderOutcome ReifiedSemiring) := withOutcome do
  let (e, carrier) ← prepare input
  match ← (classify? carrier : SymM ClassifyResult) with
  | .commSemiring id =>
    let sr := (← (getArithState : SymM Arith.State)).semirings[id]!
    let key : ViewKey := {
      source := e
      carrier := carrier
      view := .commSemiring
      structureId := id
      instances := #[sr.commSemiringInst, sr.semiringInst] }
    if let some r := (← getThe State).views.semiring.find? (·.key.agrees key) then
      return r
    let some re ← (reifySemiring? e : ReaderT Nat m (Option SemiringExpr)).run id
      | failWith (.internal "semiring reifier returned nothing")
    charge .exponent (RingExpr.maxExponent re)
    charge .reflectedNodes (RingExpr.size re)
    let r : ReifiedSemiring := { key := key, source := e, carrier := carrier, semiringId := id, expr := re }
    modifyThe State fun s => { s with views := { s.views with semiring := s.views.semiring.push r } }
    return r
  | .none => declineWith (.unsupportedCarrier carrier)
  | other => declineWith (.unsupportedView .commSemiring (describeClassification other))

/-- Bind a reified semiring input to the sealed environment. -/
def sealSemiring (r : ReifiedSemiring) (s : Sealed) : m (ProviderOutcome SealedSemiring) :=
  withOutcome do
    if RingExpr.varBound r.expr > s.n then
      failWith (.variableOutOfRange (RingExpr.varBound r.expr - 1) s.n)
    return { reflected := r, sealed := s }

/-! # Provider selection -/

/-- Check that coefficient evidence proves `CoeffLaws` for the carrier's exact
ring instance. -/
def validateCoefficients (ring : Arith.CommRing) (p : CoeffProvider) : m Unit := do
  let expected := mkAppN (mkConst ``CoeffLaws [ring.u])
    #[p.coeffType, ring.type, p.zeroInst, p.addInst, ring.ringInst, p.ofInt, p.interp]
  let ok ← (observing? (do
      let ty ← inferType p.laws
      isDefEq ty expected) : MetaM (Option Bool))
  unless ok == some true do
    failWith (.invalidProviderEvidence p.id "the laws do not prove CoeffLaws for the carrier")

/-- Select a provider for a capability on a classified commutative ring.
Registrations are consulted in registration order; the highest priority
among the recognizing providers wins, and two distinct providers at that
priority are an ambiguity decline. -/
def selectProvider (cap : Capability) (ring : Arith.CommRing) :
    m (ProviderOutcome Evidence) := do
  let key : ProviderKey := {
    capability := cap
    carrier := ring.type
    structureId := ring.id
    instances := #[ring.commRingInst] }
  if let some (_, o) := (← getThe State).providers.find? (·.1.agrees key) then
    return o
  let regs ← (registrations : MetaM (Array Registration))
  let mut candidates : Array (Registration × Evidence) := #[]
  for r in regs do
    if r.capability == cap then
      if let some ev ← (r.recognize ring : SymM (Option Evidence)) then
        candidates := candidates.push (r, ev)
  let outcome ← withOutcome do
    if candidates.isEmpty then
      declineWith (.missingCapability cap ring.type)
    let top := candidates.foldl (fun acc c => Nat.max acc c.1.priority) 0
    let best := candidates.filter (·.1.priority == top)
    if best.size > 1 then
      declineWith (.ambiguousProvider cap (best.map (·.1.id)))
    let some (reg, ev) := best[0]?
      | failWith (.internal "no best provider after a non-empty candidate list")
    match ev with
    | .coefficients p =>
      unless p.id == reg.id do
        failWith (.invalidProviderEvidence reg.id "evidence names a different provider")
      validateCoefficients ring p
    | .record .. => pure ()
    return ev
  let outcome := match outcome with
    | .declined (.missingCapability c t) u => .declined (.missingCapability c t) u
    | o => o
  modifyThe State fun s => { s with providers := s.providers.push (key, outcome) }
  return outcome

/-! # Conversion -/

/-- Convert a reified ring input against a sealed environment under the
requested order. -/
def convert (r : ReifiedRing) (s : Sealed) (order : MonoOrder) :
    m (ProviderOutcome Conversion) := withOutcome do
  let ring ← ringOf r
  let provider ← match ← selectProvider .commRingNormalize ring with
    | .success (.coefficients p) _ => pure p
    | .success (.record name _) _ =>
      failWith (.invalidProviderEvidence { name } "expected coefficient evidence")
    | .notApplicable => declineWith (.missingCapability .commRingNormalize ring.type)
    | .declined d _ => declineWith d
    | .failure f => failWith f
  let key : ConversionKey := {
    reflected := r.key
    epoch := s.epoch
    n := s.n
    char? := ring.charInst?.map (·.2)
    charInst? := ring.charInst?.map (·.1)
    provider := provider.id
    coeffType := provider.coeffType
    interp := provider.interp
    order := order.name }
  if let some c := (← getThe State).converted.find? (·.key.agrees key) then
    return c
  charge .exponent (RingExpr.maxExponent r.expr)
  let remaining := (← getThe State).budget.remaining.terms
  checkBudget .terms (RingExpr.termBound (remaining + 1) r.expr)
  if RingExpr.varBound r.expr > s.n then
    failWith (.variableOutOfRange (RingExpr.varBound r.expr - 1) s.n)
  let some ts := convertTerms? s.n key.char? r.expr
    | failWith (.internal "conversion failed after the variable bound check")
  charge .terms ts.length
  charge .coefficientBits (coefficientBits ts)
  let usage := (← consumed)
  let c : Conversion := { key := key, reflected := r, sealed := s, provider := provider, order := order, terms := ts, usage := usage }
  modifyThe State fun st => { st with converted := st.converted.push c }
  return c

/-! # Proof reconstruction -/

/-- Quote an exponent vector as a `Vector` literal. -/
def quoteMono (n : Nat) (mo : Mono n) : Expr :=
  mkApp4 (mkConst ``Vector.mk [.zero]) (mkConst ``Nat) (mkNatLit n) (toExpr mo.toArray)
    (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) (mkNatLit n))

/-- The type `Hex.Mono n`. -/
def monoType (n : Nat) : Expr :=
  mkApp (mkConst ``Hex.Mono) (mkNatLit n)

/-- The type `Hex.Mono n × Int`. -/
def termType (n : Nat) : Expr :=
  mkApp2 (mkConst ``Prod [.zero, .zero]) (monoType n) (mkConst ``Int)

/-- Quote an integer-coefficient term list. -/
def quoteTerms (n : Nat) (ts : List (Mono n × Int)) : Expr :=
  let ty := termType n
  ts.foldr
    (fun t acc =>
      mkApp3 (mkConst ``List.cons [.zero]) ty
        (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) (monoType n) (mkConst ``Int)
          (quoteMono n t.1) (toExpr t.2))
        acc)
    (mkApp (mkConst ``List.nil [.zero]) ty)

/-- The denotation context of a sealed environment as an `RArray` literal. An
empty environment uses the ring's zero, which no variable reads. -/
def contextExpr (ring : Arith.CommRing) (s : Sealed) : m Expr := do
  if h : 0 < s.atoms.size then
    (RArray.toExpr ring.type id (RArray.ofFn (s.atoms[·]) h) : MetaM Expr)
  else
    let zero := mkApp3 (mkConst ``OfNat.ofNat [ring.u]) ring.type (mkRawNatLit 0)
      (mkApp3 (mkConst ``Lean.Grind.Semiring.ofNat [ring.u]) ring.type ring.semiringInst
        (mkRawNatLit 0))
    return mkApp2 (mkConst ``RArray.leaf [ring.u]) ring.type zero

/-- The quoted converted polynomial `ofIntTerms ofInt ts`. -/
def Conversion.quotedValue (c : Conversion) : Expr :=
  let n := c.sealed.n
  mkAppN (mkConst ``ofIntTerms)
    #[mkNatLit n, c.provider.coeffType, c.provider.zeroInst, c.provider.addInst,
      c.provider.beqInst, c.provider.lawfulBEqInst, c.order.quoteCmp n,
      c.order.quoteTransCmp n, c.order.quoteLawfulEqCmp n, c.provider.ofInt,
      quoteTerms n c.terms]

/-- Assemble the interpretation proof of a conversion. The proof applies the
general soundness theorem to the quoted reflected syntax, sealed context, and
term list; the equality between the pure conversion and the quoted term list
is left to reduction of concrete reflected data; and the result is related to
the canonical source and to the caller's instantiated source by definitional
equality. -/
def Conversion.mkProof (c : Conversion) (input : Expr) (cfg : Config := {}) :
    m (ProviderOutcome EqualityResult) := withOutcome do
  let ring ← ringOf c.reflected
  let n := c.sealed.n
  let ctx ← contextExpr ring c.sealed
  let tsE := quoteTerms n c.terms
  let eE := toExpr c.reflected.expr
  let listTy := mkApp (mkConst ``List [.zero]) (termType n)
  let someTs := mkApp2 (mkConst ``Option.some [.zero]) listTy tsE
  let hE := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkApp (mkConst ``Option [.zero]) listTy) someTs
  let common := #[ring.type, mkNatLit n, c.provider.coeffType, c.provider.zeroInst,
    c.provider.addInst, c.provider.beqInst, c.provider.lawfulBEqInst, c.order.quoteCmp n,
    c.order.quoteTransCmp n, c.order.quoteLawfulEqCmp n, c.provider.ofInt, c.provider.interp,
    ring.commRingInst]
  let proofCanon :=
    match ring.charInst? with
    | some (charInst, char) =>
      mkAppN (mkConst ``eval₂_convertTermsC_ctx [ring.u])
        (common ++ #[mkNatLit char, charInst, c.provider.laws, ctx, eE, tsE, hE])
    | none =>
      mkAppN (mkConst ``eval₂_convertTerms_ctx [ring.u])
        (common ++ #[c.provider.laws, ctx, eE, tsE, hE])
  let limit := (← getThe State).budget.remaining.proofNodes
  charge .proofNodes (sourceNodeCount proofCanon (limit + 1))
  let ty ← (inferType proofCanon : MetaM Expr)
  let some (_, lhs, _) := ty.eq?
    | failWith (.internal "the soundness theorem did not produce an equality")
  let denoted ← (denoteRingExpr c.sealed.atoms c.reflected.expr : ReaderT Nat m Expr).run c.reflected.ringId
  let proofDenoted ← (mkExpectedTypeHint proofCanon
    (mkApp3 (mkConst ``Eq [.succ ring.u]) ring.type lhs denoted) : MetaM Expr)
  let source ← (instantiateMVars input : MetaM Expr)
  let target := mkApp3 (mkConst ``Eq [.succ ring.u]) ring.type lhs source
  let proof ← (mkExpectedTypeHint proofDenoted target : MetaM Expr)
  if cfg.checkProofs then
    match ← (observing? (Meta.check proof) : MetaM (Option Unit)) with
    | some () => pure ()
    | none => failWith (.illTypedProof "the generated proof does not type-check")
  return { source := source, value := c.quotedValue, interpretation := lhs, proof := proof, atoms := c.sealed.atoms }

/-! # Conditions -/

/-- Record a condition, canonicalizing its proposition and deduplicating by
provenance and canonical proposition identity. -/
def addConditionM (c : Condition) : m Unit := do
  let prop ← (Sym.canon (← (shareCommon c.proposition : SymM Expr)) : SymM Expr)
  modifyThe State fun s =>
    { s with conditions := addCondition s.conditions { c with proposition := prop } }

/-- The conditions recorded so far, in first-occurrence order. -/
def conditions : m (Array Condition) :=
  return (← getThe State).conditions

/-- The declines recorded so far. -/
def declines : m (Array Decline) :=
  return (← getThe State).declines

/-- The failures recorded so far. -/
def failures : m (Array Failure) :=
  return (← getThe State).failures

end Ops

/-- Cheap normalizers a frontend configures for discharging conditions. Each
returns a proof of the proposition or `none`. -/
structure ConditionPolicy where
  normalizers : Array (Expr → MetaM (Option Expr)) := #[]

/-- Try to discharge conditions by definitional equality with a local
hypothesis, then by the configured normalizers. Unresolved conditions are
returned rather than turned into goals. -/
def dischargeConditions (cs : Array Condition) (policy : ConditionPolicy := {}) :
    MetaM (Array (Condition × Expr) × Array Condition) := do
  let mut resolved := #[]
  let mut unresolved := #[]
  for c in cs do
    let mut proof? : Option Expr := none
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type c.proposition then
        proof? := some decl.toExpr
        break
    if proof?.isNone then
      for normalize in policy.normalizers do
        if let some p ← normalize c.proposition then
          proof? := some p
          break
    match proof? with
    | some p => resolved := resolved.push (c, p)
    | none => unresolved := unresolved.push c
  return (resolved, unresolved)

/-! # Standalone runner -/

/-- Run a standalone session, entering `SymM.run` exactly once. -/
def run (x : ReflectM α) (cfg : Config := {}) : MetaM α :=
  SymM.run do
    withExpThreshold cfg.expThreshold do
      x.run' (State.init cfg.budget)

/-- One converted batch entry together with its proof. -/
structure RingEntry where
  input : Expr
  reflected : ReifiedRing
  conversion : Conversion
  result : EqualityResult

/-- A sealed commutative-ring batch. -/
structure RingBatch where
  sealed : Sealed
  entries : Array RingEntry
  usage : BudgetUsage

/-- Lift a non-success outcome to another value type. -/
def ProviderOutcome.recast : ProviderOutcome α → Except (ProviderOutcome β) α
  | .success v _ => .ok v
  | .notApplicable => .error .notApplicable
  | .declined d u => .error (.declined d u)
  | .failure f => .error (.failure f)

/-- Reify every input as one batch, sealAtoms once, convert every entry against the
same sealed environment, and reconstruct every proof. -/
def ringBatch (inputs : Array Expr) (order : MonoOrder := MonoOrder.grevlex)
    (cfg : Config := {}) : ReflectM (ProviderOutcome RingBatch) := do
  let mut reified := #[]
  for input in inputs do
    match (← reifyCommRing input).recast with
    | .ok r => reified := reified.push (input, r)
    | .error o => return o
  let s ← sealAtoms
  let mut entries := #[]
  for (input, r) in reified do
    match (← convert r s order).recast with
    | .error o => return o
    | .ok c =>
      match (← c.mkProof input cfg).recast with
      | .error o => return o
      | .ok result => entries := entries.push { input := input, reflected := r, conversion := c, result := result }
  return .success { sealed := s, entries := entries, usage := (← consumed) } (← consumed)

/-- The standalone batch runner. -/
def reflectRingBatch (inputs : Array Expr) (order : MonoOrder := MonoOrder.grevlex)
    (cfg : Config := {}) : MetaM (ProviderOutcome RingBatch) :=
  run (ringBatch inputs order cfg) cfg

/-- The standalone single-expression runner. A matrix frontend must not call
this once per entry; it passes all entries to `reflectRingBatch`. -/
def reflectRing (input : Expr) (order : MonoOrder := MonoOrder.grevlex) (cfg : Config := {}) :
    MetaM (ProviderOutcome RingEntry) := do
  match ← reflectRingBatch #[input] order cfg with
  | .success b u =>
    match b.entries[0]? with
    | some e => return .success e u
    | none => return .failure (.internal "empty batch result")
  | .notApplicable => return .notApplicable
  | .declined d u => return .declined d u
  | .failure f => return .failure f

end Hex.Reflect

end
