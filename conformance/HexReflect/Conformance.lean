/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflect
import HexReflect.TestProviders

/-!
# HexReflect conformance

**Oracle:** none.

**Mode:** `always`.

**Covered operations:**

* budgets: `BudgetState.charge`, `BudgetState.check`, and exhaustion reports;
* conditions: `addCondition`, `dedupConditions`, and `dischargeConditions`;
* pure conversion: `RingExpr.size`, `RingExpr.maxExponent`,
  `RingExpr.varBound`, `RingExpr.termBound`, `monoOfMon?`, `polyTerms?`,
  `convertTerms?`, `convert?`, and `ofIntTerms`;
* sessions: `run`, `reifyCommRing`, `reifyCommSemiring`, `sealAtoms`,
  `sealSemiring`, `selectProvider`, `convert`, `Conversion.mkProof`,
  `reflectRingBatch`, and `reflectRing`.

**Covered properties:**

* a standalone batch enters `SymM.run` once, and the same operations run
  over a richer monad without a nested run;
* canonicalization precedes classification, cache lookup, and reification,
  and unresolved metavariables decline before any view is cached;
* repeated atoms share one index, different atoms remain different, and every
  batch result uses one sealed size;
* wrong operation instances become atoms and never reuse a view cached for
  the exact instances;
* characteristic-zero, positive-characteristic, cast, literal-power,
  symbolic-power, division-as-atom, and empty-environment conversions
  produce kernel-checked interpretation proofs;
* semiring batches reify and seal without a ring conversion;
* conversion sorts terms by the requested comparator, merges translated
  collisions, and drops coefficients mapped to zero;
* conversion proofs use concrete reflected-data equality and the soundness
  theorem, never a kernel decision of symbolic evaluation;
* cache keys distinguish source, exact instances, sealed identity, and
  comparator;
* conditions preserve first-occurrence order and deduplicate by provenance;
* budget exhaustion is a decline with exact usage, and malformed provider
  evidence is a failure;
* importing a provider changes provider selection only, never the
  `Sym.Arith` view.

**Covered edge cases:** empty batches, constants, the zero polynomial modulo
the characteristic, out-of-range reflected variables, ambiguous, declining,
and malformed providers, a numeral with a nonstandard `OfNat` instance, a
symbolic semiring power, a batch mixing two carriers, a metavariable assigned
between attempts, and declines for unclassified carriers and mismatched views.
-/

namespace Hex.ReflectConformance

open Lean Meta Hex Hex.Reflect

/-! # Budgets -/

private def tight : BudgetState :=
  BudgetState.ofBudget {
    sourceNodes := 10
    atoms := 2
    reflectedNodes := 10
    exponent := 4
    terms := 5
    coefficientBits := 8
    proofNodes := 100 }

#guard (tight.charge .atoms 1).toOption.map (·.consumed.atoms) == some 1
#guard ((tight.charge .atoms 1).toOption.bind (·.charge .atoms 1 |>.toOption)).map
  (·.consumed.atoms) == some 2
#guard match (tight.charge .atoms 1).toOption.bind (fun s => s.charge .atoms 2 |>.toOption) with
  | none => true
  | some _ => false
#guard match tight.charge .atoms 3 with
  | .error e => e == { dimension := .atoms, limit := 2, consumed := 0, requested := 3 }
  | .ok _ => false
-- limit dimensions compare the requested value itself and record the maximum
#guard (tight.charge .exponent 4).toOption.map (·.consumed.exponent) == some 4
#guard ((tight.charge .exponent 4).toOption.bind (·.charge .exponent 3 |>.toOption)).map
  (·.consumed.exponent) == some 4
#guard match tight.charge .exponent 5 with
  | .error e => e.dimension == .exponent && e.requested == 5
  | .ok _ => false
#guard match tight.check .terms 5 with
  | .ok () => true
  | .error _ => false
#guard match tight.check .terms 6 with
  | .error e => e.limit == 5
  | .ok _ => false
#guard tight.remaining.terms == 5

/-! # Pure conversion -/

private def e1 : RingExpr := .add (.var 0) (.var 1)
private def e2 : RingExpr := .mul e1 e1
private def e3 : RingExpr := .sub e2 (.mul (.num 2) (.var 0))
private def e4 : RingExpr := .pow (.var 0) 3
private def e5 : RingExpr := .neg (.natCast 3)

#guard RingExpr.size e1 == 3
#guard RingExpr.size e3 == 11
#guard RingExpr.maxExponent e3 == 0
#guard RingExpr.maxExponent (.mul e4 (.pow e1 5)) == 5
#guard RingExpr.varBound e3 == 2
#guard RingExpr.varBound e5 == 0
#guard RingExpr.termBound 100 e2 == 4
#guard RingExpr.termBound 100 (.pow e1 5) == 32
#guard RingExpr.termBound 10 (.pow e1 5) == 10

private def m2 (a b : Nat) : Mono 2 :=
  Mono.mul (Mono.scale a (Mono.unit 0)) (Mono.scale b (Mono.unit 1))

#guard convertTerms? 2 none e1 == some [(m2 1 0, 1), (m2 0 1, 1)]
#guard convertTerms? 2 none e2 == some [(m2 2 0, 1), (m2 1 1, 2), (m2 0 2, 1)]
#guard convertTerms? 2 none e3 == some [(m2 2 0, 1), (m2 1 1, 2), (m2 0 2, 1), (m2 1 0, -2)]
#guard convertTerms? 2 none e4 == some [(m2 3 0, 1)]
#guard convertTerms? 2 none e5 == some [(Mono.zero, -3)]
#guard convertTerms? 2 none (.intCast (-4)) == some [(Mono.zero, -4)]
#guard convertTerms? 2 none (.num 0) == some []
-- an identifier outside the sealed size is an error, never reduced modulo the size
#guard convertTerms? 1 none e1 == none
#guard convertTerms? 0 none (.num 5) == some [(Mono.zero, 5)]
-- characteristic-aware normalization
#guard convertTerms? 2 (some 7) (.pow e1 7) == some [(m2 7 0, 1), (m2 0 7, 1)]
#guard convertTerms? 2 (some 7) (.mul (.num 7) (.var 0)) == some []
#guard convertTerms? 2 (some 0) e3 == convertTerms? 2 none e3

example : convertTerms? 2 none e2 = some [(m2 2 0, 1), (m2 1 1, 2), (m2 0 2, 1)] := by
  decide +kernel

example : convertTerms? 2 (some 7) (.pow e1 7) = some [(m2 7 0, 1), (m2 0 7, 1)] := by
  decide +kernel

-- the requested comparator orders the terms, collisions merge, mapped zeros vanish
#guard (ofIntTerms (cmp := Mono.lex) id [(m2 2 0, 1), (m2 0 3, 1)]).termsList ==
  [(m2 0 3, 1), (m2 2 0, 1)]
#guard (ofIntTerms (cmp := Mono.grevlex) id [(m2 0 3, 1), (m2 2 0, 1)]).termsList ==
  [(m2 2 0, 1), (m2 0 3, 1)]
#guard (ofIntTerms (cmp := Mono.lex) id [(m2 1 0, 1), (m2 1 0, 2)]).termsList == [(m2 1 0, 3)]
#guard (ofIntTerms (cmp := Mono.lex) id [(m2 1 0, 1), (m2 1 0, -1)]).termsList == []
#guard (ofIntTerms (cmp := Mono.lex) (fun k => (k % 2 : Int))
  [(m2 1 0, 2), (m2 0 1, 3)]).termsList == [(m2 0 1, 1)]
#guard (convert? 2 none Mono.lex (C := Int) id e1).map (·.termsList) ==
  some [(m2 0 1, 1), (m2 1 0, 1)]
#guard (convert? 1 none Mono.lex (C := Int) id e1).isNone

/-! # Conditions -/

private def cond (prop : Lean.Expr) (provider : Name) (reason : String) : Condition :=
  { proposition := prop, provider := provider, source := prop, operation := "pivot",
    reason := reason }

private def propA : Lean.Expr := mkConst ``True
private def propB : Lean.Expr := mkConst ``False

#guard (dedupConditions #[cond propA `p "r", cond propA `p "r"]).size == 1
#guard (dedupConditions #[cond propA `p "r", cond propA `q "r"]).size == 2
#guard (dedupConditions #[cond propA `p "r", cond propB `p "r"]).size == 2
#guard (dedupConditions #[cond propB `p "r", cond propA `p "r", cond propB `p "r"]).map
  (·.proposition.constName!) == #[``False, ``True]

/-! # Sessions -/

private def expect (ok : Bool) (message : String) : MetaM Unit := do
  unless ok do throwError "conformance failure: {message}"

private def intExpr : Lean.Expr := mkConst ``Int

private def finExpr (n : Nat) : Lean.Expr := mkApp (mkConst ``Fin) (mkNatLit n)

private def natLit (n : Nat) : Lean.Expr := mkNatLit n

private def intLit (n : Nat) : MetaM Lean.Expr :=
  mkAppOptM ``OfNat.ofNat #[intExpr, mkRawNatLit n, none]

private def add (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HAdd.hAdd #[a, b]
private def mul (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HMul.hMul #[a, b]
private def sub (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HSub.hSub #[a, b]
private def pow (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HPow.hPow #[a, b]
private def div (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HDiv.hDiv #[a, b]

/-- Add the interpretation proof of an entry as a theorem, abstracting the
free variables, so the kernel checks it. -/
private def kernelCheck (fvars : Array Lean.Expr) (entry : RingEntry) : MetaM Unit := do
  let ty ← inferType entry.result.proof
  let ty ← mkForallFVars fvars ty
  let val ← mkLambdaFVars fvars entry.result.proof
  let name ← mkFreshUserName `Hex.ReflectConformance.proof
  addDecl (.thmDecl { name, levelParams := [], type := ty, value := val })
  -- the proof relates the interpretation of the quoted value to the caller's source
  let some (_, lhs, rhs) := (← instantiateMVars (← inferType entry.result.proof)).eq?
    | throwError "proof is not an equality"
  expect (← isDefEq lhs entry.result.interpretation) "interpretation mismatch"
  expect (← isDefEq rhs entry.input) "source mismatch"

private def terms (entry : RingEntry) : List (List Nat × Int) :=
  entry.conversion.terms.map fun t => (t.1.toList, t.2)

private def entry (bt : RingBatch) (i : Nat) : MetaM RingEntry :=
  match bt.entries[i]? with
  | some e => pure e
  | none => throwError "missing batch entry {i}"

private def showTerms (entries : Array RingEntry) : String :=
  "\n".intercalate (entries.toList.map fun e => toString (repr (terms e)))

private def checkProofs : Hex.Reflect.Config := { checkProofs := true }

-- Repeated atoms share one index, different atoms differ, division is one
-- atom, and every proof is kernel-checked against the caller's source.
/--
info: batch over Int: sealed 3 entries 5
[([1, 0, 0], 1), ([0, 1, 0], 1)]
[([2, 0, 0], 1), ([1, 1, 0], 2), ([0, 2, 0], 1)]
[([2, 0, 0], 1), ([1, 1, 0], 2), ([0, 2, 0], 1), ([1, 0, 0], -2)]
[([3, 0, 0], 1)]
[([0, 1, 0], 1), ([0, 0, 1], 1)]
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `y intExpr fun y => do
    let s1 ← add x y
    let s2 ← mul s1 s1
    let s3 ← sub s2 (← mul (← intLit 2) x)
    let s4 ← pow x (natLit 3)
    let s5 ← add (← div x y) y
    match ← reflectRingBatch #[s1, s2, s3, s4, s5] .grevlex checkProofs with
    | .success bt _ =>
      logInfo m!"batch over Int: sealed {bt.sealed.n} entries {bt.entries.size}\n\
        {showTerms bt.entries}"
      expect (bt.sealed.atoms.size == 3) "three atoms"
      expect (bt.sealed.atoms[0]! == x && bt.sealed.atoms[1]! == y) "atom order"
      for e in bt.entries do
        expect (e.conversion.sealed.n == 3) "one sealed size"
        expect (e.conversion.char? == some 0) "Int has characteristic evidence 0"
        kernelCheck #[x, y] e
    | o => throwError (o.toMessageData fun _ => m!"?")

-- Characteristic 7: the freshman's dream, and the zero polynomial.
/--
info: batch over Fin 7: sealed 2
[([7, 0], 1), ([0, 7], 1)]
[]
-/
#guard_msgs in
run_meta do
  withLocalDeclD `a (finExpr 7) fun a => do
  withLocalDeclD `b (finExpr 7) fun b => do
    let s1 ← pow (← add a b) (natLit 7)
    let seven ← mkAppOptM ``OfNat.ofNat #[finExpr 7, mkRawNatLit 7, none]
    let s2 ← mul seven a
    match ← reflectRingBatch #[s1, s2] .lex checkProofs with
    | .success bt _ =>
      logInfo m!"batch over Fin 7: sealed {bt.sealed.n}\n{showTerms bt.entries}"
      for e in bt.entries do
        expect (e.conversion.char? == some 7) "characteristic 7"
        kernelCheck #[a, b] e
    | o => throwError (o.toMessageData fun _ => m!"?")

-- Casts, a symbolic exponent as an atom, and an empty environment.
/--
info: casts and atoms: sealed 2
[([1, 0], 1), ([0, 0], 3)]
[([0, 0], -2)]
[([0, 1], 1)]
---
info: constant batch: sealed 0
[([], 5)]
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    let three ← mkAppOptM ``NatCast.natCast #[intExpr, none, natLit 3]
    let s1 ← add x three
    let minusTwo ← mkAppOptM ``IntCast.intCast
      #[intExpr, none, ← mkAppM ``Neg.neg #[← intLit 2]]
    let s3 ← pow x k
    match ← reflectRingBatch #[s1, minusTwo, s3] .lex checkProofs with
    | .success bt _ =>
      logInfo m!"casts and atoms: sealed {bt.sealed.n}\n{showTerms bt.entries}"
      expect ((← entry bt 2).reflected.expr == .var 1) "symbolic power is one atom"
      for e in bt.entries do kernelCheck #[x, k] e
    | o => throwError (o.toMessageData fun _ => m!"?")
    match ← reflectRingBatch #[← intLit 5] .lex checkProofs with
    | .success bt _ =>
      logInfo m!"constant batch: sealed {bt.sealed.n}\n{showTerms bt.entries}"
      kernelCheck #[] (← entry bt 0)
    | o => throwError (o.toMessageData fun _ => m!"?")

-- The empty batch seals at size zero.
/-- info: empty batch: sealed 0, entries 0 -/
#guard_msgs in
run_meta do
  match ← reflectRingBatch #[] .lex with
  | .success bt _ => logInfo m!"empty batch: sealed {bt.sealed.n}, entries {bt.entries.size}"
  | o => throwError (o.toMessageData fun _ => m!"?")

-- A wrong addition instance makes the application one atom and does not
-- reuse the view cached for the exact instance.
/-- info: wrong instance: views 2, atoms 3 -/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `y intExpr fun y => do
    let good ← add x y
    let weird := mkApp2 (mkConst ``instHAdd [.zero]) intExpr
      (mkApp2 (mkConst ``Add.mk [.zero]) intExpr
        (mkLambda `a .default intExpr (mkLambda `b .default intExpr
          (mkApp2 (mkConst ``Int.mul) (.bvar 1) (.bvar 0)))))
    let bad := mkAppN (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
      #[intExpr, intExpr, intExpr, weird, x, y]
    Hex.Reflect.run do
      let .success r1 _ ← reifyCommRing good | throwError "good input declined"
      let .success r2 _ ← reifyCommRing bad | throwError "bad input declined"
      expect (r1.expr == .add (.var 0) (.var 1)) "exact instance is recognized"
      expect (r2.expr == .var 2) "wrong instance is one atom"
      let st ← getThe Hex.Reflect.State
      logInfo m!"wrong instance: views {st.views.ring.size}, atoms {st.vars.atoms.size}"

-- Unresolved metavariables decline before any view is cached; unclassified
-- carriers and mismatched views decline.
/--
info: unresolved metavariable in
  x + ?m
---
info: views cached: 0
---
info: no supported algebraic structure on carrier
  String
---
info: requested a commutative ring view but the carrier classifies as commutative semiring
---
info: requested a commutative semiring view but the carrier classifies as commutative ring
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `s (mkConst ``String) fun s => do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let m ← mkFreshExprMVar intExpr (userName := `m)
    let hole ← add x m
    Hex.Reflect.run do
      let .declined d _ ← reifyCommRing hole | throwError "expected a decline"
      logInfo d.toMessageData
      logInfo m!"views cached: {(← getThe Hex.Reflect.State).views.ring.size}"
      let .declined d _ ← reifyCommRing (← mkAppM ``String.append #[s, s])
        | throwError "expected a decline"
      logInfo d.toMessageData
      let .declined d _ ← reifyCommRing (← add n n) | throwError "expected a decline"
      logInfo d.toMessageData
      let .declined d _ ← reifyCommSemiring (← add x x) | throwError "expected a decline"
      logInfo d.toMessageData

-- Semiring batches reify and seal, retaining the reflected expression and
-- the atom array, and offer no ring conversion. A symbolic top-level power,
-- which the pinned semiring reifier does not accept, is one atom.
/--
info: semiring: sealed 3, reflected Lean.Grind.CommRing.Expr.add
  (Lean.Grind.CommRing.Expr.mul (Lean.Grind.CommRing.Expr.var 0) (Lean.Grind.CommRing.Expr.var 1))
  (Lean.Grind.CommRing.Expr.num 3)
---
info: symbolic semiring power: Lean.Grind.CommRing.Expr.var 2
-/
#guard_msgs in
run_meta do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    let e ← add (← mul n k) (natLit 3)
    let p ← pow n k
    Hex.Reflect.run do
      let .success r _ ← reifyCommSemiring e | throwError "semiring input declined"
      let .success rp _ ← reifyCommSemiring p | throwError "symbolic power declined"
      let s ← sealAtoms
      let .success sr _ ← sealSemiring r s | throwError "sealing failed"
      logInfo m!"semiring: sealed {sr.sealed.n}, reflected {repr sr.reflected.expr}"
      logInfo m!"symbolic semiring power: {repr rp.expr}"
      expect (sr.sealed.atoms == #[n, k, p]) "atoms retained"

-- Cache identity: the same canonical source is one view; each requested
-- comparator is one conversion, keyed by the quoted comparator rather than
-- by its name, so an order renamed to `lex` but comparing by `grevlex` hits
-- the `grevlex` conversion; and a different carrier is a different provider
-- selection.
/-- info: cache: views 2, conversions 3, provider selections 2 -/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `y intExpr fun y => do
  withLocalDeclD `a (finExpr 7) fun a => do
    let e ← add x y
    Hex.Reflect.run do
      let .success r _ ← reifyCommRing e | throwError "declined"
      let .success r' _ ← reifyCommRing (← add x y) | throwError "declined"
      let .success ra _ ← reifyCommRing (← add a a) | throwError "declined"
      expect (r.expr == r'.expr) "same view"
      let s ← sealAtoms
      let .success c1 _ ← convert r s .lex | throwError "conversion declined"
      let .success c2 _ ← convert r s .grevlex | throwError "conversion declined"
      let .success c3 _ ← convert r' s .lex | throwError "conversion declined"
      let impostor : MonoOrder := { MonoOrder.grevlex with name := MonoOrder.lex.name }
      let .success c4 _ ← convert r s impostor | throwError "conversion declined"
      let .success ca _ ← convert ra s .lex | throwError "conversion declined"
      expect (c1.key.cmp == MonoOrder.lex.quoteCmp 3 && c2.key.cmp == MonoOrder.grevlex.quoteCmp 3)
        "comparator quotations"
      expect (c4.key.cmp == c2.key.cmp && c4.key.cmp != c1.key.cmp)
        "a renamed comparator is keyed by its quotation"
      expect (c1.terms.map (fun t => (t.1.toList, t.2)) ==
        c3.terms.map (fun t => (t.1.toList, t.2))) "cached conversion"
      expect (c1.key.char? == some 0 && ca.key.char? == some 7) "characteristic in the key"
      let st ← getThe Hex.Reflect.State
      logInfo m!"cache: views {st.views.ring.size}, conversions {st.converted.size}, \
        provider selections {st.providers.size}"

-- Budget exhaustion is a decline carrying the dimension and the usage of the
-- whole batch so far. Bounds saturate one above the remaining budget, so a
-- report shows the smallest increment that already exceeds the limit. Each
-- expansion dimension is checked before the expanding operation runs.
/--
info: budget exhausted in dimension literal exponent: limit 8, consumed 0, requested 40
---
info: budget exhausted in dimension polynomial terms: limit 5, consumed 0, requested 6
---
info: budget exhausted in dimension atoms: limit 1, consumed 1, requested 1
---
info: budget exhausted in dimension source nodes: limit 3, consumed 0, requested 4
---
info: budget exhausted in dimension reflected nodes: limit 4, consumed 0, requested 7
---
info: budget exhausted in dimension coefficient bits: limit 16, consumed 0, requested 17
---
info: budget exhausted in dimension proof nodes: limit 32, consumed 0, requested 110
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `y intExpr fun y => do
    let big ← pow (← add x y) (natLit 40)
    let small ← pow (← add x y) (natLit 5)
    let cfg : Hex.Reflect.Config :=
      { budget := { Budget.default with exponent := 8, terms := 5 } }
    match ← reflectRingBatch #[big] .lex cfg with
    | .declined d u => logInfo d.toMessageData; expect (u.atoms == 2) "usage reports the atoms"
    | o => throwError (o.toMessageData fun _ => m!"?")
    match ← reflectRingBatch #[small] .lex cfg with
    | .declined d u =>
      logInfo d.toMessageData
      expect (u.atoms == 2 && u.sourceNodes > 0 && u.reflectedNodes == 4)
        "a conversion decline reports the reification usage of the batch"
    | o => throwError (o.toMessageData fun _ => m!"?")
    let cfg : Hex.Reflect.Config := { budget := { Budget.default with atoms := 1 } }
    match ← reflectRingBatch #[← add x y] .lex cfg with
    | .declined d _ => logInfo d.toMessageData
    | o => throwError (o.toMessageData fun _ => m!"?")
    let cfg : Hex.Reflect.Config := { budget := { Budget.default with sourceNodes := 3 } }
    match ← reflectRingBatch #[← add x y] .lex cfg with
    | .declined d _ => logInfo d.toMessageData
    | o => throwError (o.toMessageData fun _ => m!"?")
    let cfg : Hex.Reflect.Config := { budget := { Budget.default with reflectedNodes := 4 } }
    match ← reflectRingBatch #[← add (← add x y) (← mul x y)] .lex cfg with
    | .declined d _ => logInfo d.toMessageData
    | o => throwError (o.toMessageData fun _ => m!"?")
    -- `(x + 3) ^ 12` has one monomial per degree but a coefficient of 3 ^ 12,
    -- which exceeds 16 bits; the decline fires before normalization.
    let cfg : Hex.Reflect.Config := { budget := { Budget.default with coefficientBits := 16 } }
    let three ← intLit 3
    match ← reflectRingBatch #[← pow (← add x three) (natLit 12)] .lex cfg with
    | .declined d _ => logInfo d.toMessageData
    | o => throwError (o.toMessageData fun _ => m!"?")
    let cfg : Hex.Reflect.Config := { budget := { Budget.default with proofNodes := 32 } }
    match ← reflectRingBatch #[← add x y] .lex cfg with
    | .declined d _ => logInfo d.toMessageData
    | o => throwError (o.toMessageData fun _ => m!"?")

-- A batch mixing two carriers declines before sealing, and reports the
-- reification usage.
/--
info: a batch must use one carrier, but found both
  Int
and
  Fin 7
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `a (finExpr 7) fun a => do
    match ← reflectRingBatch #[x, a] .lex with
    | .declined d u => logInfo d.toMessageData; expect (u.atoms == 2) "usage reports both atoms"
    | o => throwError (o.toMessageData fun _ => m!"?")

-- A numeral with a nonstandard `OfNat` instance is accepted by the pinned
-- reifier as the literal `2`, so the denoted syntax is not the source; the
-- session reports an ill-typed proof rather than a success.
/-- info: failure: generated proof is ill-typed: the denoted reflected syntax is not definitionally the source -/
#guard_msgs in
run_meta do
  let inst37 := mkApp2 (mkConst ``OfNat.mk [.zero]) intExpr
    (mkApp3 (mkConst ``OfNat.ofNat [.zero]) intExpr (mkRawNatLit 37)
      (mkApp (mkConst ``instOfNat) (mkRawNatLit 37)))
  let e := mkApp3 (mkConst ``OfNat.ofNat [.zero]) intExpr (mkRawNatLit 2) inst37
  logInfo ((← reflectRingBatch #[e] .lex).toMessageData fun _ => m!"converted")

-- A metavariable assigned between attempts no longer declines.
/--
info: unresolved metavariable in
  x * ?m + ?m
---
info: after assignment: [([1, 1], 1), ([0, 1], 1)]
-/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `y intExpr fun y => do
    let m ← mkFreshExprMVar intExpr (userName := `m)
    let hole ← add (← mul x m) m
    Hex.Reflect.run do
      let .declined d _ ← reifyCommRing hole | throwError "expected a decline"
      logInfo d.toMessageData
      m.mvarId!.assign y
      let .success r _ ← reifyCommRing hole | throwError "expected a success"
      let s ← sealAtoms
      let .success c _ ← convert r s .lex | throwError "conversion declined"
      logInfo m!"after assignment: {repr (c.terms.map fun t => (t.1.toList, t.2))}"

/-! # Providers -/

-- Importing providers changes selection only: the views still reify,
-- malformed evidence is a failure, equal priorities are an ambiguity decline,
-- a recognized decline propagates, and an unclaimed carrier keeps the integer
-- provider.
/--
info: failure: invalid evidence from provider Hex.ReflectConformance.bogusCoefficients: laws is not a well-typed value of the expected type
---
info: declined: ambiguous providers for commutative-ring normalization: [Hex.ReflectConformance.rivalCoefficients,
 Hex.ReflectConformance.otherCoefficients]
---
info: failure: invalid evidence from provider Hex.ReflectConformance.malformedInstanceCoefficients: LawfulBEq instance is not a well-typed value of the expected type
---
info: declined: unsupported source type
  Fin 23
---
info: Fin 17 still converts: [([0, 0, 0, 0, 1], 1)]
-/
#guard_msgs in
run_meta do
  withLocalDeclD `a (finExpr 11) fun a => do
  withLocalDeclD `b (finExpr 13) fun b => do
  withLocalDeclD `d (finExpr 19) fun d => do
  withLocalDeclD `e (finExpr 23) fun e => do
  withLocalDeclD `c (finExpr 17) fun c => do
    Hex.Reflect.run do
      let .success ra _ ← reifyCommRing (← add a a) | throwError "view declined"
      let .success rb _ ← reifyCommRing (← add b b) | throwError "view declined"
      let .success rd _ ← reifyCommRing (← add d d) | throwError "view declined"
      let .success re _ ← reifyCommRing (← add e e) | throwError "view declined"
      let .success rc _ ← reifyCommRing c | throwError "view declined"
      let s ← sealAtoms
      logInfo ((← convert ra s .lex).toMessageData fun _ => m!"converted")
      logInfo ((← convert rb s .lex).toMessageData fun _ => m!"converted")
      logInfo ((← convert rd s .lex).toMessageData fun _ => m!"converted")
      logInfo ((← convert re s .lex).toMessageData fun _ => m!"converted")
      let .success cc _ ← convert rc s .lex | throwError "Fin 17 conversion failed"
      expect (cc.provider.id == intCoefficientsId) "integer provider"
      logInfo m!"Fin 17 still converts: {repr (cc.terms.map fun t => (t.1.toList, t.2))}"

-- A non-integer coefficient provider: rational coefficients over `Rat`. The
-- quoted value maps the integer terms through the cast, and the proof is
-- kernel-checked against the rational interpretation.
/--
info: rational provider Hex.ReflectConformance.ratCoefficients: [([2], 1), ([1], 6), ([0], 9)]
---
info: quoted value: ofIntTerms Int.cast [(#v[2], 1), (#v[1], 6), (#v[0], 9)]
-/
#guard_msgs in
run_meta do
  withLocalDeclD `q (mkConst ``Rat) fun q => do
    let three ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 3, none]
    let e ← pow (← add q three) (natLit 2)
    match ← reflectRingBatch #[e] .lex checkProofs with
    | .success bt _ =>
      let en ← entry bt 0
      logInfo m!"rational provider {en.conversion.provider.id.name}: {repr (terms en)}"
      logInfo m!"quoted value: {en.result.value}"
      kernelCheck #[q] en
    | o => throwError (o.toMessageData fun _ => m!"?")

/-! # Conditions in a session -/

-- Conditions keep first-occurrence order and deduplicate by provenance and
-- canonical proposition.
/-- info: conditions: 2, resolved 1, unresolved 1 -/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
    let zero ← intLit 0
    let ne ← mkAppM ``Ne #[x, zero]
    let ne' ← mkAppM ``Ne #[x, zero]
    let eq ← mkAppM ``Eq #[x, zero]
    withLocalDeclD `h ne fun h => do
      let mk (prop : Lean.Expr) (reason : String) : Condition :=
        { proposition := prop, provider := `p, source := x, operation := "pivot",
          reason := reason }
      let cs ← Hex.Reflect.run do
        addConditionM (mk ne "nonzero")
        addConditionM (mk eq "zero")
        addConditionM (mk ne' "nonzero")
        conditions
      let (resolved, unresolved) ← dischargeConditions cs
      expect (resolved.size == 1 && resolved[0]!.2 == h) "local hypothesis discharges"
      expect (cs[0]!.reason == "nonzero" && cs[1]!.reason == "zero") "first-occurrence order"
      logInfo m!"conditions: {cs.size}, resolved {resolved.size}, unresolved {unresolved.size}"

/-! # A richer monad without a nested run -/

/-- The session operations run over a state transformer stacked on a reader
above `SymM`, inside one `SymM.run`. -/
abbrev RichM := StateRefT Hex.Reflect.State (ReaderT String Lean.Meta.Sym.SymM)

/-- info: richer monad: sealed 2 with tag batch -/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
  withLocalDeclD `y intExpr fun y => do
    let e ← mul x y
    let act : RichM Unit := do
      let .success r _ ← reifyCommRing e | throwError "declined"
      let s ← sealAtoms
      let .success c _ ← convert r s .grevlex | throwError "conversion declined"
      let tag ← (read : ReaderT String Lean.Meta.Sym.SymM String)
      logInfo m!"richer monad: sealed {s.n} with tag {tag}"
      expect (c.terms.length == 1) "one term"
    Lean.Meta.Sym.SymM.run ((act.run' (Hex.Reflect.State.init Budget.default)).run "batch")

/-! # Single-expression runner -/

/-- info: single: [([2], 1)] -/
#guard_msgs in
run_meta do
  withLocalDeclD `x intExpr fun x => do
    match ← reflectRing (← mul x x) .lex checkProofs with
    | .success e _ =>
      logInfo m!"single: {repr (terms e)}"
      kernelCheck #[x] e
    | o => throwError (o.toMessageData fun _ => m!"?")

end Hex.ReflectConformance
