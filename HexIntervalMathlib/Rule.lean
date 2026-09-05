/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Proof
public import HexIntervalMathlib.Addition
public import HexIntervalMathlib.Subtraction
public import HexIntervalMathlib.Multiplication
public import HexIntervalMathlib.Power
public import HexIntervalMathlib.Absolute
public import HexIntervalMathlib.MinMax
public import HexIntervalMathlib.Inverse
public import HexIntervalMathlib.Division
public import HexIntervalMathlib.Regularize

@[expose] public section

/-!
# Built-in arithmetic proof rules

This is the first supported arithmetic package for the generic proof replay
boundary. A package fixes its endpoint, power, and precision resources.
Dyadic and natural literals are value-agnostic program rows whose exact values
are authenticated by node-indexed initial facts. Power consumes both a real
base and a natural-domain exponent row.
Runtime search may propose facts and recipe bodies, but the package schemas
recompute the public checked interval operation and prove its one-way real
enclosure.

Source nodes are caller assumptions, not rules. Reciprocal, division, and
regularization use the package's fixed precision resources and the public
one-way real image theorems; no runtime result enters proof evidence without
being recomputed by its schema.
-/

namespace Hex.Interval.Rule

open Proof

/-- Resources owned by one immutable arithmetic package. -/
structure Config where
  endpoint : EndpointLimit
  powerWork : Arithmetic.PowLimits
  precisionLimits : Arithmetic.PrecisionLimits
  precision : Precision
  /-- Authenticated meanings owned by independently assembled packages. They
  follow the stable built-in prefix and have no built-in rule authority. -/
  extraMeanings : Array (Program.Meaning ℝ) := #[]

def realDomain : DomainId := { index := 0 }
def natDomain : DomainId := { index := 1 }

def sourceOp : Operation :=
  { key := { name := "hex.interval.source" }, inputs := [], output := realDomain }
def negOp : Operation :=
  { key := { name := "hex.interval.neg" }, inputs := [realDomain], output := realDomain }
def addOp : Operation :=
  { key := { name := "hex.interval.add" }, inputs := [realDomain, realDomain], output := realDomain }
def subOp : Operation :=
  { key := { name := "hex.interval.sub" }, inputs := [realDomain, realDomain], output := realDomain }
def mulOp : Operation :=
  { key := { name := "hex.interval.mul" }, inputs := [realDomain, realDomain], output := realDomain }
def powOp : Operation :=
  { key := { name := "hex.interval.pow.nat", version := 2 },
    inputs := [realDomain, natDomain], output := realDomain }
def absOp : Operation :=
  { key := { name := "hex.interval.abs" }, inputs := [realDomain], output := realDomain }
def minOp : Operation :=
  { key := { name := "hex.interval.min" }, inputs := [realDomain, realDomain], output := realDomain }
def maxOp : Operation :=
  { key := { name := "hex.interval.max" }, inputs := [realDomain, realDomain], output := realDomain }
def dyadicLiteralOp : Operation :=
  { key := { name := "hex.interval.literal.dyadic", version := 1 },
    inputs := [], output := realDomain }
def invOp : Operation :=
  { key := { name := "hex.interval.inv" }, inputs := [realDomain], output := realDomain }
def divOp : Operation :=
  { key := { name := "hex.interval.div" }, inputs := [realDomain, realDomain], output := realDomain }
def regularizeOp : Operation :=
  { key := { name := "hex.interval.regularize" }, inputs := [realDomain], output := realDomain }
def natLiteralOp : Operation :=
  { key := { name := "hex.interval.literal.nat", version := 1 },
    inputs := [], output := natDomain }

/-- Exact operation order owned by the built-in package. -/
def operations : Array Operation :=
  #[sourceOp, negOp, addOp, subOp, mulOp, powOp, absOp, minOp, maxOp, dyadicLiteralOp,
    invOp, divOp, regularizeOp, natLiteralOp]

def sourceMeaning : Program.Meaning ℝ := { operation := sourceOp, relation := fun _ _ => True }
def negMeaning : Program.Meaning ℝ :=
  { operation := negOp, relation := fun xs z => ∃ x, xs = [x] ∧ z = -x }
def addMeaning : Program.Meaning ℝ :=
  { operation := addOp, relation := fun xs z => ∃ x y, xs = [x, y] ∧ z = x + y }
def subMeaning : Program.Meaning ℝ :=
  { operation := subOp, relation := fun xs z => ∃ x y, xs = [x, y] ∧ z = x - y }
def mulMeaning : Program.Meaning ℝ :=
  { operation := mulOp, relation := fun xs z => ∃ x y, xs = [x, y] ∧ z = x * y }
def powMeaning : Program.Meaning ℝ :=
  { operation := powOp
    relation := fun xs z => ∃ base : ℝ, ∃ exponent : Nat,
      xs = [base, (exponent : ℝ)] ∧ z = base ^ exponent }
def absMeaning : Program.Meaning ℝ :=
  { operation := absOp, relation := fun xs z => ∃ x, xs = [x] ∧ z = |x| }
def minMeaning : Program.Meaning ℝ :=
  { operation := minOp, relation := fun xs z => ∃ x y, xs = [x, y] ∧ z = min x y }
def maxMeaning : Program.Meaning ℝ :=
  { operation := maxOp, relation := fun xs z => ∃ x y, xs = [x, y] ∧ z = max x y }
def dyadicLiteralMeaning : Program.Meaning ℝ :=
  { operation := dyadicLiteralOp, relation := fun xs _ => xs = [] }
def invMeaning : Program.Meaning ℝ :=
  { operation := invOp, relation := fun xs z => ∃ x, xs = [x] ∧ z = x⁻¹ }
def divMeaning : Program.Meaning ℝ :=
  { operation := divOp, relation := fun xs z => ∃ x y, xs = [x, y] ∧ z = x / y }
def regularizeMeaning : Program.Meaning ℝ :=
  { operation := regularizeOp, relation := fun xs z => ∃ x, xs = [x] ∧ z = x }
def natLiteralMeaning : Program.Meaning ℝ :=
  { operation := natLiteralOp, relation := fun xs _ => xs = [] }

def builtinMeanings (_config : Config) : Array (Program.Meaning ℝ) :=
  #[sourceMeaning, negMeaning, addMeaning, subMeaning, mulMeaning,
    powMeaning, absMeaning, minMeaning, maxMeaning, dyadicLiteralMeaning,
    invMeaning, divMeaning, regularizeMeaning, natLiteralMeaning]

def meanings (config : Config) : Array (Program.Meaning ℝ) :=
  builtinMeanings config ++ config.extraMeanings

theorem prefixMeaning (config : Config) {index : Nat}
    (within : index < (builtinMeanings config).size) :
    (meanings config)[index]? = (builtinMeanings config)[index]? := by
  exact Array.getElem?_append_left within

def semantics (config : Config) : Proof.Semantics Hex.Interval :=
  .ofMeanings (meanings config) Hex.Interval.Contains

def ready? : BuildResult → Option Hex.Interval
  | .ready interval => some interval
  | .resourceLimit _ => none

def arithmeticReady? : Arithmetic.Result → Option Hex.Interval
  | .ready interval => some interval
  | .resourceLimit _ => none

theorem ready?_eq {result : BuildResult} {interval : Hex.Interval}
    (h : ready? result = some interval) : result = .ready interval := by
  cases result <;> simp_all [ready?]

theorem arithmeticReady?_eq {result : Arithmetic.Result} {interval : Hex.Interval}
    (h : arithmeticReady? result = some interval) : result = .ready interval := by
  cases result <;> simp_all [arithmeticReady?]

theorem laws (config : Config) : Proof.Laws (semantics config) :=
  { holdsEq := by
      intro program valuation left right fact _ equality
      simpa [semantics, Proof.Semantics.ofMeanings] using
        congrArg (fun value => fact.Contains value) equality }

/-- Intersection is the only fact-domain narrowing law.  Its checked public
result is recomputed before the conjunction theorem enters evidence. -/
def domain (config : Config) : Proof.Domain (semantics config) :=
    { top := fun _ => Hex.Interval.whole
      topSound := by
        intro _ _ _ _ _ _
        change Raw.Contains Hex.Interval.whole.view _
        rw [view_whole]
        exact And.intro trivial trivial
      meet := fun program node previous proposed installed =>
        match found : ready? (intersectWithin config.endpoint previous proposed) with
        | some result =>
            if equal : result = installed then
              some ⟨by
                subst result
                intro valuation _
                simpa [semantics, Proof.Semantics.ofMeanings] using
                  contains_intersectWithin (ready?_eq found) (valuation node)⟩
            else none
        | none => none }

def negKey : RuleKey := { name := "hex.interval.rule.neg" }
def addKey : RuleKey := { name := "hex.interval.rule.add" }
def subKey : RuleKey := { name := "hex.interval.rule.sub" }
def mulKey : RuleKey := { name := "hex.interval.rule.mul" }
def powKey : RuleKey := { name := "hex.interval.rule.pow.nat" }
def absKey : RuleKey := { name := "hex.interval.rule.abs" }
def minKey : RuleKey := { name := "hex.interval.rule.min" }
def maxKey : RuleKey := { name := "hex.interval.rule.max" }
def invKey : RuleKey := { name := "hex.interval.rule.inv" }
def divKey : RuleKey := { name := "hex.interval.rule.div" }
def regularizeKey : RuleKey := { name := "hex.interval.rule.regularize" }

def schemaKey (key : RuleKey) : Proof.Key := { rule := key, role := .fact, bodySchema := 1 }

def unaryRegistration (key : RuleKey) (operation : Operation) : Registration :=
  { key, head := operation.key, kind := .forward,
    watches := [.argument 0], writes := [.result] }

def binaryRegistration (key : RuleKey) (operation : Operation) : Registration :=
  { key, head := operation.key, kind := .forward,
    watches := [.argument 0, .argument 1], writes := [.result] }

def registrations : Array Registration :=
  #[unaryRegistration negKey negOp,
    binaryRegistration addKey addOp,
    binaryRegistration subKey subOp,
    binaryRegistration mulKey mulOp,
    binaryRegistration powKey powOp,
    unaryRegistration absKey absOp,
    binaryRegistration minKey minOp,
    binaryRegistration maxKey maxOp,
    unaryRegistration invKey invOp,
    binaryRegistration divKey divOp,
    unaryRegistration regularizeKey regularizeOp]

def exactBody (tag : Nat) (body : List Nat) : Option Unit :=
  if body = [tag] then some () else none

theorem nodeMeaning (config : Config) {program : Program} {valuation : NodeId → ℝ}
    (model : Program.Models (meanings config) program valuation)
    {node : NodeId} {instruction : Node} (found : program.node? node = some instruction) :
    Program.MeaningAt (meanings config) valuation node instruction :=
  model.2 node instruction found

theorem negRelation (config : Config) {valuation : NodeId → ℝ}
    {node input : NodeId}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index := 1 }, args := [input] }) :
    valuation node = -valuation input := by
  rcases meaning with ⟨meaning, found, related⟩
  rw [prefixMeaning config (index := 1) (by simp [builtinMeanings])] at found
  simp [builtinMeanings] at found
  subst meaning
  simpa [negMeaning] using related

theorem binaryRelation (config : Config) {valuation : NodeId → ℝ}
    {node left right : NodeId} {index : Nat} {relation : ℝ → ℝ → ℝ}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index }, args := [left, right] })
    (indexShape : (index = 2 ∧ relation = fun x y => x + y) ∨
      (index = 3 ∧ relation = fun x y => x - y) ∨
      (index = 4 ∧ relation = fun x y => x * y) ∨
      (index = 7 ∧ relation = min) ∨
      (index = 8 ∧ relation = max)) :
    valuation node = relation (valuation left) (valuation right) := by
  rcases indexShape with h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    rcases meaning with ⟨meaning, found, related⟩ <;>
    simp [meanings, Array.getElem?_append, builtinMeanings] at found <;>
    subst meaning <;>
    simpa [addMeaning, subMeaning, mulMeaning, minMeaning, maxMeaning] using related

theorem powRelation (config : Config) {valuation : NodeId → ℝ}
    {node base exponentNode : NodeId}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index := 5 }, args := [base, exponentNode] }) :
    ∃ exponent : Nat, valuation exponentNode = (exponent : ℝ) ∧
      valuation node = valuation base ^ exponent := by
  rcases meaning with ⟨meaning, found, related⟩
  rw [prefixMeaning config (index := 5) (by simp [builtinMeanings])] at found
  simp [builtinMeanings] at found
  subst meaning
  change ∃ input : ℝ, ∃ exponent : Nat,
    [valuation base, valuation exponentNode] = [input, (exponent : ℝ)] ∧
      valuation node = input ^ exponent at related
  rcases related with ⟨input, exponent, arguments, output⟩
  have baseEq : valuation base = input := (List.cons.inj arguments).1
  have exponentEq : valuation exponentNode = (exponent : ℝ) :=
    (List.cons.inj (List.cons.inj arguments).2).1
  exact ⟨exponent, exponentEq, output.trans (congrArg (fun x => x ^ exponent) baseEq.symm)⟩

theorem absRelation (config : Config) {valuation : NodeId → ℝ} {node input : NodeId}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index := 6 }, args := [input] }) :
    valuation node = |valuation input| := by
  rcases meaning with ⟨meaning, found, related⟩
  rw [prefixMeaning config (index := 6) (by simp [builtinMeanings])] at found
  simp [builtinMeanings] at found
  subst meaning
  simpa [absMeaning] using related

theorem invRelation (config : Config) {valuation : NodeId → ℝ}
    {node input : NodeId}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index := 10 }, args := [input] }) :
    valuation node = (valuation input)⁻¹ := by
  rcases meaning with ⟨meaning, found, related⟩
  rw [prefixMeaning config (index := 10) (by simp [builtinMeanings])] at found
  simp [builtinMeanings] at found
  subst meaning
  simpa [invMeaning] using related

theorem divRelation (config : Config) {valuation : NodeId → ℝ}
    {node left right : NodeId}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index := 11 }, args := [left, right] }) :
    valuation node = valuation left / valuation right := by
  rcases meaning with ⟨meaning, found, related⟩
  rw [prefixMeaning config (index := 11) (by simp [builtinMeanings])] at found
  simp [builtinMeanings] at found
  subst meaning
  simpa [divMeaning] using related

theorem regularizeRelation (config : Config) {valuation : NodeId → ℝ}
    {node input : NodeId}
    (meaning : Program.MeaningAt (meanings config) valuation node
      { domain := realDomain, op := { index := 12 }, args := [input] }) :
    valuation node = valuation input := by
  rcases meaning with ⟨meaning, found, related⟩
  rw [prefixMeaning config (index := 12) (by simp [builtinMeanings])] at found
  simp [builtinMeanings] at found
  subst meaning
  change ∃ x, [valuation input] = [x] ∧ valuation node = x at related
  rcases related with ⟨x, hinput, hnode⟩
  simp only [List.cons.injEq, and_true] at hinput
  exact hnode.trans hinput.symm

theorem constant_mem {limit : EndpointLimit} {value : Dyadic} {result : Hex.Interval}
    (checked : singletonWithin limit value = .ready result) :
    result.Contains (toReal value) := by
  change result.view.Contains (toReal value)
  rw [view_singletonWithin_ready checked, contains_normalize]
  exact And.intro le_rfl le_rfl

theorem toReal_ofInt (value : Int) :
    toReal (Dyadic.ofInt value) = (value : ℝ) := by
  change (((Dyadic.ofInt value).toRat : Rat) : ℝ) = (value : ℝ)
  rw [show Dyadic.ofInt value = (value : Dyadic) by rfl, Dyadic.toRat_intCast]
  norm_num

/-- Expose a dyadic's exact rational numerator and denominator to the
Mathlib-facing quotation layer. -/
theorem toReal_rat (value : Dyadic) :
    toReal value = (value.toRat.num : ℝ) / value.toRat.den := by
  simp [toReal, Rat.cast_def]

theorem eq_of_singletonValue {raw : Raw} {value : Dyadic} {x : ℝ}
    (shape : raw.singletonValue? = some value) (member : raw.Contains x) :
    x = toReal value := by
  cases raw with
  | empty => simp [Raw.singletonValue?] at shape
  | bounds lower upper =>
      cases lower with
      | unbounded => simp [Raw.singletonValue?] at shape
      | finite lower lowerStrict =>
          cases upper with
          | unbounded => simp [Raw.singletonValue?] at shape
          | finite upper upperStrict =>
              cases lowerStrict <;> cases upperStrict <;>
                simp [Raw.singletonValue?] at shape member
              rcases shape with ⟨rfl, rfl⟩
              exact le_antisymm member.2 member.1

/-- Decode exactly a closed singleton containing a nonnegative integer. -/
def closedNat? (fact : Hex.Interval) : Option Nat := do
  let value ← fact.view.singletonValue?
  let rational := value.toRat
  if rational.den = 1 then
    if 0 ≤ rational.num then some rational.num.toNat else none
  else none

theorem closedNat?_sound {fact : Hex.Interval} {value : ℝ} {exponent : Nat}
    (found : closedNat? fact = some exponent) (member : fact.Contains value) :
    value = (exponent : ℝ) := by
  unfold closedNat? at found
  generalize shape : fact.view.singletonValue? = singleton at found
  cases singleton with
  | none => simp at found
  | some dyadic =>
      simp only [Option.bind_eq_bind, Option.bind_some] at found
      split at found
      · next denEq =>
        split at found
        · next numNonnegative =>
          simp at found
          subst exponent
          have exact := eq_of_singletonValue shape member
          rw [exact]
          change ((dyadic.toRat : Rat) : ℝ) = ((dyadic.toRat.num.toNat : Nat) : ℝ)
          rw [← Rat.num_div_den dyadic.toRat]
          simp only [denEq, Nat.cast_one, div_one]
          exact_mod_cast (Int.toNat_of_nonneg numNonnegative).symm
        · simp at found
      · simp at found

-- Concrete schemas keep each semantic relation and checked public operation
-- visible; an executable recipe tag alone never selects a theorem.

def negSchema (config : Config) : Proof.FactSchema (semantics config) :=
  { key := schemaKey negKey, Certificate := Unit, decode := exactBody 1
    prove := fun c _ => match c.assumptions with
      | [a] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := 1 }, args := [a.node] } then
          match found : ready? (negWithin config.endpoint a.fact) with
          | some result =>
              if equal : result = c.proposed.fact then
                some ⟨by
                  subst result
                  intro v m hs
                  change NodeId → ℝ at v
                  have hm := negRelation config (nodeMeaning config m hn)
                  change c.proposed.fact.Contains (v c.proposed.node)
                  rw [hm]
                  exact (contains_negWithin (ready?_eq found) (-v a.node)).2 (by
                    simpa only [neg_neg] using (show a.fact.Contains (v a.node) from by
                      simpa [semantics, Proof.Semantics.ofMeanings] using hs a (by simp)))⟩
              else none
          | none => none
        else none
      | _ => none }

def binarySchema (config : Config) (key : RuleKey) (tag opIndex : Nat)
    (run : Hex.Interval → Hex.Interval → Option Hex.Interval)
    (relation : ℝ → ℝ → ℝ)
    (indexShape : (opIndex = 2 ∧ relation = fun x y => x + y) ∨
      (opIndex = 3 ∧ relation = fun x y => x - y) ∨
      (opIndex = 4 ∧ relation = fun x y => x * y) ∨
      (opIndex = 7 ∧ relation = min) ∨
      (opIndex = 8 ∧ relation = max))
    (image : ∀ {left right result : Hex.Interval} {x y : ℝ},
      run left right = some result → left.Contains x → right.Contains y →
        result.Contains (relation x y)) : Proof.FactSchema (semantics config) :=
  { key := schemaKey key, Certificate := Unit, decode := exactBody tag
    prove := fun c _ => match c.assumptions with
      | [a, b] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := opIndex }, args := [a.node, b.node] } then
          match found : run a.fact b.fact with
          | some result =>
              if equal : result = c.proposed.fact then
                some ⟨by
                  subst result
                  intro v m hs
                  have hm := binaryRelation config (nodeMeaning config m hn) indexShape
                  have ha : a.fact.Contains (v a.node) := by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs a (by simp)
                  have hb : b.fact.Contains (v b.node) := by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs b (by simp)
                  change c.proposed.fact.Contains (v c.proposed.node)
                  rw [hm]
                  exact image found ha hb⟩
              else none
          | none => none
        else none
      | _ => none }

def addSchema (config : Config) :=
  binarySchema config addKey 2 2
    (fun left right => ready? (addWithin config.endpoint left right))
    (fun x y => x + y)
    (Or.inl ⟨rfl, rfl⟩)
    (fun hc ha hb => add_mem_addWithin (ready?_eq hc) ha hb)
def subSchema (config : Config) :=
  binarySchema config subKey 3 3
    (fun left right => ready? (subWithin config.endpoint left right))
    (fun x y => x - y)
    (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (fun hc ha hb => sub_mem_subWithin (ready?_eq hc) ha hb)
def mulSchema (config : Config) :=
  binarySchema config mulKey 4 4
    (fun left right => arithmeticReady? (mulWithin config.endpoint left right))
    (fun x y => x * y)
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    (fun hc ha hb => mul_mem_mulWithin (arithmeticReady?_eq hc) ha hb)
def minSchema (config : Config) :=
  binarySchema config minKey 7 7
    (fun left right => ready? (minWithin config.endpoint left right)) min
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    (fun hc ha hb => min_mem_minWithin (ready?_eq hc) ha hb)
def maxSchema (config : Config) :=
  binarySchema config maxKey 8 8
    (fun left right => ready? (maxWithin config.endpoint left right)) max
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    (fun hc ha hb => max_mem_maxWithin (ready?_eq hc) ha hb)

def powSchema (config : Config) : Proof.FactSchema (semantics config) :=
  { key := schemaKey powKey, Certificate := Unit, decode := exactBody 5
    prove := fun c _ => match c.assumptions with
      | [base, exponentFact] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := 5 },
              args := [base.node, exponentFact.node] } then
          match exponentFound : closedNat? exponentFact.fact with
          | some exponent =>
              match found : arithmeticReady?
                  (powWithin config.endpoint config.powerWork base.fact exponent) with
              | some result =>
                  if equal : result = c.proposed.fact then
                    some ⟨by
                      subst result
                      intro v m hs
                      have baseMember : base.fact.Contains (v base.node) := by
                        simpa [semantics, Proof.Semantics.ofMeanings] using hs base (by simp)
                      have exponentMember : exponentFact.fact.Contains (v exponentFact.node) := by
                        simpa [semantics, Proof.Semantics.ofMeanings] using
                          hs exponentFact (by simp)
                      have exponentValue := closedNat?_sound exponentFound exponentMember
                      rcases powRelation config (nodeMeaning config m hn) with
                        ⟨semanticExponent, semanticValue, outputValue⟩
                      have exponentEq : semanticExponent = exponent := by
                        apply Nat.cast_injective (R := ℝ)
                        rw [← semanticValue, exponentValue]
                      change c.proposed.fact.Contains (v c.proposed.node)
                      rw [outputValue, exponentEq]
                      exact pow_mem_powWithin (arithmeticReady?_eq found) baseMember⟩
                  else none
              | none => none
          | none => none
        else none
      | _ => none }

def absSchema (config : Config) : Proof.FactSchema (semantics config) :=
  { key := schemaKey absKey, Certificate := Unit, decode := exactBody 6
    prove := fun c _ => match c.assumptions with
      | [a] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := 6 }, args := [a.node] } then
          match found : ready? (absWithin config.endpoint a.fact) with
          | some result =>
              if equal : result = c.proposed.fact then
                some ⟨by
                  subst result
                  intro v m hs
                  have hm := absRelation config (nodeMeaning config m hn)
                  change c.proposed.fact.Contains (v c.proposed.node)
                  rw [hm]
                  exact abs_mem_absWithin (ready?_eq found) (by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs a (by simp))⟩
              else none
          | none => none
        else none
      | _ => none }

def invSchema (config : Config) : Proof.FactSchema (semantics config) :=
  { key := schemaKey invKey, Certificate := Unit, decode := exactBody 10
    prove := fun c _ => match c.assumptions with
      | [a] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := 10 }, args := [a.node] } then
          match found : arithmeticReady?
              (invWithin config.precisionLimits config.precision a.fact) with
          | some result =>
              if equal : result = c.proposed.fact then
                some ⟨by
                  subst result
                  intro v m hs
                  have hm := invRelation config (nodeMeaning config m hn)
                  change c.proposed.fact.Contains (v c.proposed.node)
                  rw [hm]
                  exact inv_mem_invWithin (arithmeticReady?_eq found) (by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs a (by simp))⟩
              else none
          | none => none
        else none
      | _ => none }

def divSchema (config : Config) : Proof.FactSchema (semantics config) :=
  { key := schemaKey divKey, Certificate := Unit, decode := exactBody 11
    prove := fun c _ => match c.assumptions with
      | [a, b] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := 11 }, args := [a.node, b.node] } then
          match found : arithmeticReady?
              (divWithin config.precisionLimits config.precision a.fact b.fact) with
          | some result =>
              if equal : result = c.proposed.fact then
                some ⟨by
                  subst result
                  intro v m hs
                  have hm := divRelation config (nodeMeaning config m hn)
                  have ha : a.fact.Contains (v a.node) := by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs a (by simp)
                  have hb : b.fact.Contains (v b.node) := by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs b (by simp)
                  change c.proposed.fact.Contains (v c.proposed.node)
                  rw [hm]
                  exact div_mem_divWithin (arithmeticReady?_eq found) ha hb⟩
              else none
          | none => none
        else none
      | _ => none }

def regularizeSchema (config : Config) : Proof.FactSchema (semantics config) :=
  { key := schemaKey regularizeKey, Certificate := Unit, decode := exactBody 12
    prove := fun c _ => match c.assumptions with
      | [a] =>
        if hn : c.program.node? c.proposed.node = some
            { domain := realDomain, op := { index := 12 }, args := [a.node] } then
          match found : arithmeticReady?
              (regularizeWithin config.precisionLimits config.precision a.fact) with
          | some result =>
              if equal : result = c.proposed.fact then
                some ⟨by
                  subst result
                  intro v m hs
                  have hm := regularizeRelation config (nodeMeaning config m hn)
                  change c.proposed.fact.Contains (v c.proposed.node)
                  rw [hm]
                  exact mem_regularizeWithin (arithmeticReady?_eq found) (by
                    simpa [semantics, Proof.Semantics.ofMeanings] using hs a (by simp))⟩
              else none
          | none => none
        else none
      | _ => none }

def package (config : Config) : Proof.Package (semantics config) :=
  { registrations
    facts := #[negSchema config, addSchema config, subSchema config, mulSchema config,
      powSchema config, absSchema config, minSchema config, maxSchema config,
      invSchema config, divSchema config,
      regularizeSchema config] }

inductive BuildError where
  | wrongOperations
  | registry (error : Proof.BuildError)
  deriving Repr

/-- Checked assembly with additional independently owned packages. The exact
program operation array must equal the complete meaning array; the arithmetic
operations retain their stable prefix indices while arbitrary-function
meanings and packages form an authenticated suffix. `Proof.Limits` bounds the
retained package/schema registry after caller construction. This direct trusted
entry point does not preempt construction or equality of the program and
meaning arrays; decoded search callers must first cross the supported `Search`
resource envelope. -/
def buildWithWithin (limits : Proof.Limits) (config : Config) (program : Program)
    (extraPackages : Array (Proof.Package (semantics config))) :
    Except BuildError (Proof.Registry (semantics config)) := do
  if program.operations != (meanings config).map (Program.Meaning.operation) then
    throw .wrongOperations
  match Proof.Registry.buildWithin limits program (#[package config] ++ extraPackages) with
  | .ok registry => pure registry
  | .error error => throw (.registry error)

/-- Convenience assembly for an arithmetic-only registry. -/
def buildWithin (limits : Proof.Limits) (config : Config) (program : Program) :
    Except BuildError (Proof.Registry (semantics config)) :=
  buildWithWithin limits config program #[]

/-- Package-owned replay recipe retained as the opaque cause of a supported
state update.  Search validates the action and update; replay separately
validates every field and the body. -/
structure Cause where
  scope : Policy.ScopeId
  action : Action
  proposed : Hex.Interval
  schema : Proof.Key
  body : List Nat

/-- Quote the exact accepted update history of a supported search branch.
This is a data conversion only; malformed causes remain rejected by replay. -/
def quote (branch : State.Branch Hex.Interval Cause) : List (Proof.Event Hex.Interval) :=
  branch.history.toList.map fun update => .fact
    { scope := update.cause.scope
      programVersion := update.programVersion
      action := update.cause.action
      node := update.node
      previous := update.previous
      version := update.version
      proposed := update.cause.proposed
      installed := update.fact
      assumptions := update.cause.action.inputs
      schema := update.cause.schema
      body := update.cause.body }

/-- Quote the proof-relevant branch of a supported search session. Offers,
policy state, accounting, and diagnostic trace remain outside evidence. -/
def quoteSession
    (session : Search.Session Hex.Interval Cause OfferId SemanticKey) :
    List (Proof.Event Hex.Interval) :=
  quote session.branch

end Hex.Interval.Rule
