/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.RationalTable

@[expose] public section

/-!
# Resource-preflighted rational arithmetic edges

This module adds a first Mathlib-free arithmetic replay boundary for canonical
raw rational tables.  Its edge language is deliberately independent of an
interval propagation strategy: edges merely assert exact arithmetic or order
relations between table slots.

The checker has three strictly ordered phases:

1. validate the complete rational table and bound the edge collection;
2. validate every index and all caller-owned lookup, temporary-width, and
   arithmetic-work limits while constructing a bounded resolved `List`;
3. replay naive integer identities and report the first false edge.

Thus no checked cross-product is formed unless the entire edge list passes
preflight.  Indexed `List` lookup is charged by the exact number of constructors
visited (`index + 1` for every valid reference).  Temporary widths use the
standard conservative bounds `bits (x*y) <= bits x + bits y` and the analogous
sum-or-difference bound `max (bits x) (bits y) + 1`.  Arithmetic work is an
explicit schoolbook proxy: multiplying widths costs their product, and either
adding or comparing two temporaries costs the larger width.  The checker
computes each edge's fixed, small aggregate from these bounded counters, then
subtracts it from the caller-owned remaining total.  These formulas inspect
only the bit lengths of already-retained inputs; they do not allocate any
arithmetic cross-product.

This is an experiment, not a frozen storage or certificate format.  In
particular it adds no interval projection, wire decoder, cancellation-aware
replay, planner policy, or tactic frontend.
-/

namespace Hex.Interval.Experiment.RationalEdge

open Center RationalTable

/-! ## Strategy-neutral edge language -/

/-- An exact arithmetic or comparison assertion over rational-table indices. -/
inductive ArithEdge where
  | add (left right result : Nat)
  | sub (left right result : Nat)
  | mul (left right result : Nat)
  | inv (input result : Nat)
  | eq (left right : Nat)
  | le (left right : Nat)
  | lt (left right : Nat)
  deriving DecidableEq, Repr

/-- Stable names for references in deterministic index failures. -/
inductive Reference where
  | left
  | right
  | input
  | result
  deriving DecidableEq, Repr

/-- Caller-owned limits for the arithmetic-edge boundary. -/
structure Limit where
  maxEdges : Nat
  maxLookupSteps : Nat
  maxTemporaryBits : Nat
  maxArithmeticWork : Nat
  deriving DecidableEq, Repr

/-- Logical failures found without accepting a false identity. -/
inductive Invalid where
  | badIndex (reference : Reference) (index : Nat)
  | resolutionMismatch
  | wrongIdentity
  deriving DecidableEq, Repr

/-- Edge-specific resource failures.  Raw-table failures retain the separate
`RawRat.Resource` vocabulary. -/
inductive Resource where
  | edges
  | lookupSteps
  | temporaryBits
  | arithmeticWork
  deriving DecidableEq, Repr

/-- Deterministic public result.  Collection failures have no edge index;
per-edge failures identify the first failing edge. -/
inductive Result where
  | ready
  | malformedTable (index : Nat) (reason : RawRat.Invalid)
  | tableResource (index : Option Nat) (reason : RawRat.Resource)
  | malformedEdge (index : Nat) (reason : Invalid)
  | edgeResource (index : Option Nat) (reason : Resource)
  deriving DecidableEq, Repr

namespace ArithEdge

/-- Exact `List` traversal cost of all references in one valid edge. -/
def lookupSteps : ArithEdge → Nat
  | .add left right result | .sub left right result | .mul left right result =>
      (left + 1) + (right + 1) + (result + 1)
  | .inv input result => (input + 1) + (result + 1)
  | .eq left right | .le left right | .lt left right =>
      (left + 1) + (right + 1)

/-- Return the first out-of-range reference in constructor field order.  This
uses only comparisons with the already-bounded table length. -/
def firstBadIndex (tableSize : Nat) : ArithEdge → Option (Reference × Nat)
  | .add left right result | .sub left right result | .mul left right result =>
      if tableSize ≤ left then some (.left, left)
      else if tableSize ≤ right then some (.right, right)
      else if tableSize ≤ result then some (.result, result)
      else none
  | .inv input result =>
      if tableSize ≤ input then some (.input, input)
      else if tableSize ≤ result then some (.result, result)
      else none
  | .eq left right | .le left right | .lt left right =>
      if tableSize ≤ left then some (.left, left)
      else if tableSize ≤ right then some (.right, right)
      else none

end ArithEdge

/-! ## Resolved arithmetic and allocation-independent costs -/

/-- A preflighted edge with table entries resolved.  Values are shared from
the input list; no rational arithmetic result is retained here. -/
inductive Resolved where
  | add (left right result : RawRat)
  | sub (left right result : RawRat)
  | mul (left right result : RawRat)
  | inv (input result : RawRat)
  | eq (left right : RawRat)
  | le (left right : RawRat)
  | lt (left right : RawRat)
  deriving DecidableEq, Repr

/-- Preflight cost of one resolved edge.  `temporaryBits` is a maximum while
`arithmeticWork` is additive across all primitive operations in the identity. -/
structure Cost where
  temporaryBits : Nat
  arithmeticWork : Nat
  deriving DecidableEq, Repr

namespace Cost

/-- Conservative width of a product from operand widths. -/
def mulBits (left right : Nat) : Nat :=
  if left = 0 || right = 0 then 0 else left + right

/-- Conservative width of a signed sum or difference. -/
def addBits (left right : Nat) : Nat :=
  if left = 0 then right
  else if right = 0 then left
  else max left right + 1

/-- Schoolbook multiplication work proxy. -/
def mulWork (left right : Nat) : Nat := left * right

end Cost

namespace Resolved

/-- Allocation-independent preflight cost for one naive identity. -/
def cost : Resolved → Cost
  | .add left right result | .sub left right result =>
      let lc := left.cost
      let rc := right.cost
      let oc := result.cost
      let denominatorBits := Cost.mulBits lc.denominatorBits rc.denominatorBits
      let leftTermBits := Cost.mulBits lc.numeratorBits rc.denominatorBits
      let rightTermBits := Cost.mulBits rc.numeratorBits lc.denominatorBits
      let numeratorBits := Cost.addBits leftTermBits rightTermBits
      let leftResultBits := Cost.mulBits oc.numeratorBits denominatorBits
      let rightResultBits := Cost.mulBits numeratorBits oc.denominatorBits
      { temporaryBits := max denominatorBits <| max leftTermBits <|
          max rightTermBits <| max numeratorBits <|
          max leftResultBits rightResultBits
        arithmeticWork :=
          Cost.mulWork lc.denominatorBits rc.denominatorBits +
          Cost.mulWork lc.numeratorBits rc.denominatorBits +
          Cost.mulWork rc.numeratorBits lc.denominatorBits +
          (max leftTermBits rightTermBits + 1) +
          Cost.mulWork oc.numeratorBits denominatorBits +
          Cost.mulWork numeratorBits oc.denominatorBits +
          max leftResultBits rightResultBits }
  | .mul left right result =>
      let lc := left.cost
      let rc := right.cost
      let oc := result.cost
      let numeratorBits := Cost.mulBits lc.numeratorBits rc.numeratorBits
      let denominatorBits := Cost.mulBits lc.denominatorBits rc.denominatorBits
      let leftResultBits := Cost.mulBits oc.numeratorBits denominatorBits
      let rightResultBits := Cost.mulBits numeratorBits oc.denominatorBits
      { temporaryBits := max numeratorBits <| max denominatorBits <|
          max leftResultBits rightResultBits
        arithmeticWork :=
          Cost.mulWork lc.numeratorBits rc.numeratorBits +
          Cost.mulWork lc.denominatorBits rc.denominatorBits +
          Cost.mulWork oc.numeratorBits denominatorBits +
          Cost.mulWork numeratorBits oc.denominatorBits +
          max leftResultBits rightResultBits }
  | .inv input result =>
      let ic := input.cost
      let rc := result.cost
      if ic.numeratorBits = 0 then
        { temporaryBits := 0
          arithmeticWork := rc.numeratorBits }
      else
        let leftResultBits := Cost.mulBits rc.numeratorBits ic.numeratorBits
        let rightResultBits := Cost.mulBits ic.denominatorBits rc.denominatorBits
        { temporaryBits := max leftResultBits rightResultBits
          arithmeticWork :=
            ic.numeratorBits +
            Cost.mulWork rc.numeratorBits ic.numeratorBits +
            Cost.mulWork ic.denominatorBits rc.denominatorBits +
            max leftResultBits rightResultBits }
  | .eq left right | .le left right | .lt left right =>
      let lc := left.cost
      let rc := right.cost
      let leftResultBits := Cost.mulBits lc.numeratorBits rc.denominatorBits
      let rightResultBits := Cost.mulBits rc.numeratorBits lc.denominatorBits
      { temporaryBits := max
          leftResultBits rightResultBits
        arithmeticWork :=
          Cost.mulWork lc.numeratorBits rc.denominatorBits +
          Cost.mulWork rc.numeratorBits lc.denominatorBits +
          max leftResultBits rightResultBits }

/-- Naive addition identity, without normalization or cancellation. -/
def checkAdd (left right result : RawRat) : Bool :=
  let commonDenominator := left.den * right.den
  let numerator := left.num * (right.den : Int) + right.num * (left.den : Int)
  result.num * (commonDenominator : Int) == numerator * (result.den : Int)

/-- Naive subtraction identity, without normalization or cancellation. -/
def checkSub (left right result : RawRat) : Bool :=
  let commonDenominator := left.den * right.den
  let numerator := left.num * (right.den : Int) - right.num * (left.den : Int)
  result.num * (commonDenominator : Int) == numerator * (result.den : Int)

/-- Naive multiplication identity, without cross-cancellation. -/
def checkMul (left right result : RawRat) : Bool :=
  let numerator := left.num * right.num
  let denominator := left.den * right.den
  result.num * (denominator : Int) == numerator * (result.den : Int)

/-- Naive inverse identity.  Core rational inversion is total, so zero maps to
canonical zero; nonzero inputs use the signed cross-product identity. -/
def checkInv (input result : RawRat) : Bool :=
  if input.num = 0 then result.num == 0
  else result.num * input.num == (input.den : Int) * (result.den : Int)

/-- Naive rational equality by positive-denominator cross-products. -/
def checkEq (left right : RawRat) : Bool :=
  left.num * (right.den : Int) == right.num * (left.den : Int)

/-- Naive non-strict order by positive-denominator cross-products. -/
def checkLe (left right : RawRat) : Bool :=
  left.num * (right.den : Int) ≤ right.num * (left.den : Int)

/-- Naive strict order by positive-denominator cross-products. -/
def checkLt (left right : RawRat) : Bool :=
  left.num * (right.den : Int) < right.num * (left.den : Int)

/-- Replay one fully preflighted edge. -/
def check : Resolved → Bool
  | .add left right result => checkAdd left right result
  | .sub left right result => checkSub left right result
  | .mul left right result => checkMul left right result
  | .inv input result => checkInv input result
  | .eq left right => checkEq left right
  | .le left right => checkLe left right
  | .lt left right => checkLt left right

/-- Mathematical proposition asserted by a resolved edge. -/
def Holds : Resolved → Prop
  | .add left right result => result.value = left.value + right.value
  | .sub left right result => result.value = left.value - right.value
  | .mul left right result => result.value = left.value * right.value
  | .inv input result => result.value = input.value⁻¹
  | .eq left right => left.value = right.value
  | .le left right => left.value ≤ right.value
  | .lt left right => left.value < right.value

/-- Canonicality assumptions supplied by successful complete-table validation. -/
def Canonical : Resolved → Prop
  | .add left right result | .sub left right result | .mul left right result =>
      left.Canonical ∧ right.Canonical ∧ result.Canonical
  | .inv input result => input.Canonical ∧ result.Canonical
  | .eq left right | .le left right | .lt left right =>
      left.Canonical ∧ right.Canonical

end Resolved

/-! ## Core `Rat` soundness -/

namespace RawRat

/-- Canonical raw fields are exactly the fields of their Core `Rat` value. -/
theorem fields_of_canonical {q : RawRat} (h : q.Canonical) :
    q.value.num = q.num ∧ q.value.den = q.den := by
  have hvalue : q.value = Rat.mk' q.num q.den h.1 h.2 := by
    exact (Rat.mk_eq_mkRat q.num q.den h.1 h.2).symm
  rw [hvalue]
  exact ⟨rfl, rfl⟩

end RawRat

namespace Resolved

/-- Soundness of the naive addition cross-product. -/
theorem add_sound {left right result : RawRat}
    (hl : left.Canonical) (hr : right.Canonical) (ho : result.Canonical)
    (h : checkAdd left right result = true) :
    result.value = left.value + right.value := by
  have hlf := RawRat.fields_of_canonical hl
  have hrf := RawRat.fields_of_canonical hr
  have hid :
      result.num * ((left.den * right.den : Nat) : Int) =
        (left.num * (right.den : Int) + right.num * (left.den : Int)) *
          (result.den : Int) := by
    simpa [checkAdd] using h
  rw [Rat.add_def', hlf.1, hlf.2, hrf.1, hrf.2]
  unfold RawRat.value
  exact (Rat.mkRat_eq_iff ho.1 (Nat.mul_ne_zero hl.1 hr.1)).2 hid

/-- Soundness of the naive subtraction cross-product. -/
theorem sub_sound {left right result : RawRat}
    (hl : left.Canonical) (hr : right.Canonical) (ho : result.Canonical)
    (h : checkSub left right result = true) :
    result.value = left.value - right.value := by
  have hlf := RawRat.fields_of_canonical hl
  have hrf := RawRat.fields_of_canonical hr
  have hid :
      result.num * ((left.den * right.den : Nat) : Int) =
        (left.num * (right.den : Int) - right.num * (left.den : Int)) *
          (result.den : Int) := by
    simpa [checkSub] using h
  rw [Rat.sub_def', hlf.1, hlf.2, hrf.1, hrf.2]
  unfold RawRat.value
  exact (Rat.mkRat_eq_iff ho.1 (Nat.mul_ne_zero hl.1 hr.1)).2 hid

/-- Soundness of the naive multiplication cross-product. -/
theorem mul_sound {left right result : RawRat}
    (hl : left.Canonical) (hr : right.Canonical) (ho : result.Canonical)
    (h : checkMul left right result = true) :
    result.value = left.value * right.value := by
  have hlf := RawRat.fields_of_canonical hl
  have hrf := RawRat.fields_of_canonical hr
  have hid :
      result.num * ((left.den * right.den : Nat) : Int) =
        (left.num * right.num) * (result.den : Int) := by
    simpa [checkMul] using h
  rw [Rat.mul_def', hlf.1, hlf.2, hrf.1, hrf.2]
  unfold RawRat.value
  exact (Rat.mkRat_eq_iff ho.1 (Nat.mul_ne_zero hl.1 hr.1)).2 hid

/-- Soundness of the naive inverse check, including Core's `0⁻¹ = 0`. -/
theorem inv_sound {input result : RawRat}
    (hi : input.Canonical) (hr : result.Canonical)
    (h : checkInv input result = true) :
    result.value = input.value⁻¹ := by
  by_cases hn : input.num = 0
  · have hrn : result.num = 0 := by
      simpa [checkInv, hn] using h
    have hi0 : input.value = 0 := by
      unfold RawRat.value
      exact (Rat.mkRat_eq_zero hi.1).2 hn
    have hr0 : result.value = 0 := by
      unfold RawRat.value
      exact (Rat.mkRat_eq_zero hr.1).2 hrn
    rw [hi0, hr0, Rat.inv_zero]
  · have hif := RawRat.fields_of_canonical hi
    have hid : result.num * input.num =
        (input.den : Int) * (result.den : Int) := by
      simpa [checkInv, hn] using h
    have hrd : (result.den : Int) ≠ 0 := by
      exact mt Int.natCast_eq_zero.mp hr.1
    calc
      result.value = Rat.divInt result.num (result.den : Int) := by
        exact (Rat.divInt_ofNat result.num result.den).symm
      _ = Rat.divInt (input.den : Int) input.num :=
        (Rat.divInt_eq_divInt_iff hrd hn).2 hid
      _ = input.value⁻¹ := by
        rw [Rat.inv_def, hif.1, hif.2]

/-- Soundness of the naive equality cross-product. -/
theorem eq_sound {left right : RawRat}
    (hl : left.Canonical) (hr : right.Canonical)
    (h : checkEq left right = true) : left.value = right.value := by
  have hlf := RawRat.fields_of_canonical hl
  have hrf := RawRat.fields_of_canonical hr
  apply Rat.eq_iff_mul_eq_mul.2
  rw [hlf.1, hlf.2, hrf.1, hrf.2]
  simpa [checkEq] using h

/-- Soundness of the naive non-strict order cross-product. -/
theorem le_sound {left right : RawRat}
    (hl : left.Canonical) (hr : right.Canonical)
    (h : checkLe left right = true) : left.value ≤ right.value := by
  have hlf := RawRat.fields_of_canonical hl
  have hrf := RawRat.fields_of_canonical hr
  apply (Rat.le_iff left.value right.value).2
  rw [hlf.1, hlf.2, hrf.1, hrf.2]
  simpa [checkLe] using h

/-- Soundness of the naive strict order cross-product. -/
theorem lt_sound {left right : RawRat}
    (hl : left.Canonical) (hr : right.Canonical)
    (h : checkLt left right = true) : left.value < right.value := by
  have hlf := RawRat.fields_of_canonical hl
  have hrf := RawRat.fields_of_canonical hr
  apply (Rat.lt_iff left.value right.value).2
  rw [hlf.1, hlf.2, hrf.1, hrf.2]
  simpa [checkLt] using h

/-- Every checked resolved edge is sound in Core `Rat`. -/
theorem sound {edge : Resolved} (hc : edge.Canonical)
    (h : edge.check = true) : edge.Holds := by
  cases edge with
  | add left right result => exact add_sound hc.1 hc.2.1 hc.2.2 h
  | sub left right result => exact sub_sound hc.1 hc.2.1 hc.2.2 h
  | mul left right result => exact mul_sound hc.1 hc.2.1 hc.2.2 h
  | inv input result => exact inv_sound hc.1 hc.2 h
  | eq left right => exact eq_sound hc.1 hc.2 h
  | le left right => exact le_sound hc.1 hc.2 h
  | lt left right => exact lt_sound hc.1 hc.2 h

end Resolved

/-! ## Full preflight and replay -/

/-- Remaining additive budgets during a preflight scan. -/
structure Remaining where
  lookupSteps : Nat
  arithmeticWork : Nat
  deriving DecidableEq, Repr

/-- Internal preflight failures exclude `ready` by construction. -/
inductive PreflightFailure where
  | malformed (index : Nat) (reason : Invalid)
  | resource (index : Option Nat) (reason : Resource)
  deriving DecidableEq, Repr

namespace PreflightFailure

/-- Embed an internal edge-preflight failure into the public result. -/
def result : PreflightFailure → Result
  | .malformed index reason => .malformedEdge index reason
  | .resource index reason => .edgeResource index reason

end PreflightFailure

/-- Internal result of resolving the complete edge list. -/
inductive Preflight where
  | ready (plan : List Resolved)
  | failed (failure : PreflightFailure)
  deriving DecidableEq, Repr

/-- Resolve an edge after its indices have been checked.  The `none` branch is
retained rather than replaced by defaults, so any future change to index
validation still fails closed. -/
def resolve? (table : List RawRat) : ArithEdge → Option Resolved
  | .add left right result =>
      match table[left]?, table[right]?, table[result]? with
      | some l, some r, some o => some (.add l r o)
      | _, _, _ => none
  | .sub left right result =>
      match table[left]?, table[right]?, table[result]? with
      | some l, some r, some o => some (.sub l r o)
      | _, _, _ => none
  | .mul left right result =>
      match table[left]?, table[right]?, table[result]? with
      | some l, some r, some o => some (.mul l r o)
      | _, _, _ => none
  | .inv input result =>
      match table[input]?, table[result]? with
      | some i, some o => some (.inv i o)
      | _, _ => none
  | .eq left right =>
      match table[left]?, table[right]? with
      | some l, some r => some (.eq l r)
      | _, _ => none
  | .le left right =>
      match table[left]?, table[right]? with
      | some l, some r => some (.le l r)
      | _, _ => none
  | .lt left right =>
      match table[left]?, table[right]? with
      | some l, some r => some (.lt l r)
      | _, _ => none

namespace ArithEdge

/-- Mathematical meaning of an indexed edge.  Missing indices make the
proposition false; successful checker use supplies a particular resolved edge. -/
def Holds (table : List RawRat) (edge : ArithEdge) : Prop :=
  ∃ resolved, resolve? table edge = some resolved ∧ resolved.Holds

end ArithEdge

/-- A successful optional list lookup returns a member of that list. -/
theorem mem_of_lookup {table : List RawRat} {index : Nat} {entry : RawRat}
    (h : table[index]? = some entry) : entry ∈ table := by
  induction table generalizing index with
  | nil => simp at h
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at h
          subst entry
          simp
      | succ index =>
          simp at h
          exact List.mem_cons_of_mem head (ih h)

/-- Resolving from a completely validated table preserves canonicality. -/
theorem canonical_of_resolve {table : List RawRat} {edge : ArithEdge}
    {resolved : Resolved} (hc : ∀ entry ∈ table, entry.Canonical)
    (h : resolve? table edge = some resolved) : resolved.Canonical := by
  cases edge with
  | add left right result =>
      cases hl : table[left]? with
      | none => simp [resolve?, hl] at h
      | some l =>
          cases hr : table[right]? with
          | none => simp [resolve?, hl, hr] at h
          | some r =>
              cases ho : table[result]? with
              | none => simp [resolve?, hl, hr, ho] at h
              | some o =>
                  simp [resolve?, hl, hr, ho] at h
                  subst resolved
                  exact ⟨hc l (mem_of_lookup hl), hc r (mem_of_lookup hr),
                    hc o (mem_of_lookup ho)⟩
  | sub left right result =>
      cases hl : table[left]? with
      | none => simp [resolve?, hl] at h
      | some l =>
          cases hr : table[right]? with
          | none => simp [resolve?, hl, hr] at h
          | some r =>
              cases ho : table[result]? with
              | none => simp [resolve?, hl, hr, ho] at h
              | some o =>
                  simp [resolve?, hl, hr, ho] at h
                  subst resolved
                  exact ⟨hc l (mem_of_lookup hl), hc r (mem_of_lookup hr),
                    hc o (mem_of_lookup ho)⟩
  | mul left right result =>
      cases hl : table[left]? with
      | none => simp [resolve?, hl] at h
      | some l =>
          cases hr : table[right]? with
          | none => simp [resolve?, hl, hr] at h
          | some r =>
              cases ho : table[result]? with
              | none => simp [resolve?, hl, hr, ho] at h
              | some o =>
                  simp [resolve?, hl, hr, ho] at h
                  subst resolved
                  exact ⟨hc l (mem_of_lookup hl), hc r (mem_of_lookup hr),
                    hc o (mem_of_lookup ho)⟩
  | inv input result =>
      cases hi : table[input]? with
      | none => simp [resolve?, hi] at h
      | some i =>
          cases ho : table[result]? with
          | none => simp [resolve?, hi, ho] at h
          | some o =>
              simp [resolve?, hi, ho] at h
              subst resolved
              exact ⟨hc i (mem_of_lookup hi), hc o (mem_of_lookup ho)⟩
  | eq left right =>
      cases hl : table[left]? with
      | none => simp [resolve?, hl] at h
      | some l =>
          cases hr : table[right]? with
          | none => simp [resolve?, hl, hr] at h
          | some r =>
              simp [resolve?, hl, hr] at h
              subst resolved
              exact ⟨hc l (mem_of_lookup hl), hc r (mem_of_lookup hr)⟩
  | le left right =>
      cases hl : table[left]? with
      | none => simp [resolve?, hl] at h
      | some l =>
          cases hr : table[right]? with
          | none => simp [resolve?, hl, hr] at h
          | some r =>
              simp [resolve?, hl, hr] at h
              subst resolved
              exact ⟨hc l (mem_of_lookup hl), hc r (mem_of_lookup hr)⟩
  | lt left right =>
      cases hl : table[left]? with
      | none => simp [resolve?, hl] at h
      | some l =>
          cases hr : table[right]? with
          | none => simp [resolve?, hl, hr] at h
          | some r =>
              simp [resolve?, hl, hr] at h
              subst resolved
              exact ⟨hc l (mem_of_lookup hl), hc r (mem_of_lookup hr)⟩

/-- Pointwise correspondence between indexed edges and a resolved plan. -/
inductive Relates (table : List RawRat) : List ArithEdge → List Resolved → Prop where
  | nil : Relates table [] []
  | cons {edge edges resolved plan}
      (head : resolve? table edge = some resolved)
      (tail : Relates table edges plan) :
      Relates table (edge :: edges) (resolved :: plan)

/-- Validate and resolve every edge before any identity replay.  Per edge the
order is index validity, lookup budget, temporary width, aggregate arithmetic
work, then continuation to the next edge. -/
def preflightFrom (limit : Limit) (table : List RawRat) (tableSize : Nat) :
    Nat → Remaining → List ArithEdge → Preflight
  | _, _, [] => .ready []
  | edgeIndex, remaining, edge :: tail =>
      match edge.firstBadIndex tableSize with
      | some (reference, index) =>
          .failed (.malformed edgeIndex (.badIndex reference index))
      | none =>
          let lookupCost := edge.lookupSteps
          if lookupCost > remaining.lookupSteps then
            .failed (.resource (some edgeIndex) .lookupSteps)
          else
            match resolve? table edge with
            | none =>
                -- Unreachable for the current `firstBadIndex`; kept fail-closed.
                .failed (.malformed edgeIndex .resolutionMismatch)
            | some resolved =>
                let edgeCost := resolved.cost
                if edgeCost.temporaryBits > limit.maxTemporaryBits then
                  .failed (.resource (some edgeIndex) .temporaryBits)
                else if edgeCost.arithmeticWork > remaining.arithmeticWork then
                  .failed (.resource (some edgeIndex) .arithmeticWork)
                else
                  let nextRemaining : Remaining :=
                    { lookupSteps := remaining.lookupSteps - lookupCost
                      arithmeticWork :=
                        remaining.arithmeticWork - edgeCost.arithmeticWork }
                  match preflightFrom limit table tableSize (edgeIndex + 1)
                      nextRemaining tail with
                  | .ready plan => .ready (resolved :: plan)
                  | .failed failure => .failed failure

/-- Successful full preflight preserves pointwise edge/plan correspondence. -/
theorem relates_of_preflight {limit : Limit} {table : List RawRat}
    {tableSize edgeIndex : Nat} {remaining : Remaining}
    {edges : List ArithEdge} {plan : List Resolved}
    (h : preflightFrom limit table tableSize edgeIndex remaining edges =
      .ready plan) : Relates table edges plan := by
  induction edges generalizing edgeIndex remaining plan with
  | nil =>
      simp [preflightFrom] at h
      subst plan
      exact .nil
  | cons edge tail ih =>
      unfold preflightFrom at h
      cases hbad : edge.firstBadIndex tableSize with
      | some bad => simp [hbad] at h
      | none =>
          simp only [hbad] at h
          split at h
          next => contradiction
          next =>
            cases hresolve : resolve? table edge with
            | none => simp [hresolve] at h
            | some resolved =>
                simp only [hresolve] at h
                split at h
                next => contradiction
                next =>
                  split at h
                  next => contradiction
                  next =>
                    cases htail : preflightFrom limit table tableSize
                        (edgeIndex + 1)
                        { lookupSteps := remaining.lookupSteps - edge.lookupSteps
                          arithmeticWork :=
                            remaining.arithmeticWork - resolved.cost.arithmeticWork }
                        tail with
                    | failed result => simp [htail] at h
                    | ready tailPlan =>
                        simp [htail] at h
                        subst plan
                        exact .cons hresolve (ih htail)

/-- Replay a completely preflighted plan and return the first false identity. -/
def replayFrom : Nat → List Resolved → Result
  | _, [] => .ready
  | index, edge :: tail =>
      if edge.check then replayFrom (index + 1) tail
      else .malformedEdge index .wrongIdentity

/-- Validate a table and its complete arithmetic-edge list.  No cross-product
in `Resolved.check` is reached until `preflightFrom` has accepted every edge. -/
def check (tableLimit : RawRat.Limit) (edgeLimit : Limit)
    (table : List RawRat) (edges : List ArithEdge) : Result :=
  match RationalTable.Table.check tableLimit table with
  | .malformed index reason => .malformedTable index reason
  | .resourceLimit index reason => .tableResource index reason
  | .ready =>
      if lengthWithin edgeLimit.maxEdges edges then
        let remaining : Remaining :=
          { lookupSteps := edgeLimit.maxLookupSteps
            arithmeticWork := edgeLimit.maxArithmeticWork }
        match preflightFrom edgeLimit table table.length 0 remaining edges with
        | .ready plan => replayFrom 0 plan
        | .failed failure => failure.result
      else
        .edgeResource none .edges

/-- A successful replay of a related plan proves every indexed edge. -/
theorem holds_of_replay {table : List RawRat} {edges : List ArithEdge}
    {plan : List Resolved} {index : Nat}
    (hc : ∀ entry ∈ table, entry.Canonical)
    (related : Relates table edges plan)
    (h : replayFrom index plan = .ready) :
    ∀ edge ∈ edges, edge.Holds table := by
  induction related generalizing index with
  | nil => simp
  | @cons edge edges resolved plan hresolve tail ih =>
      unfold replayFrom at h
      cases hcheck : resolved.check with
      | false => simp [hcheck] at h
      | true =>
          simp only [hcheck, ↓reduceIte] at h
          intro candidate hmem
          simp only [List.mem_cons] at hmem
          cases hmem with
          | inl hhead =>
              subst candidate
              exact ⟨resolved, hresolve,
                Resolved.sound (canonical_of_resolve hc hresolve) hcheck⟩
          | inr htail => exact ih h candidate htail

/-- Proof-facing soundness of the public checker: `ready` proves the
mathematical meaning of every indexed edge in Core `Rat`. -/
theorem sound_of_check {tableLimit : RawRat.Limit} {edgeLimit : Limit}
    {table : List RawRat} {edges : List ArithEdge}
    (h : check tableLimit edgeLimit table edges = .ready) :
    ∀ edge ∈ edges, edge.Holds table := by
  unfold check at h
  cases htable : RationalTable.Table.check tableLimit table with
  | malformed index reason => simp [htable] at h
  | resourceLimit index reason => simp [htable] at h
  | ready =>
      simp only [htable] at h
      split at h
      next =>
        cases hpreflight : preflightFrom edgeLimit table table.length 0
            { lookupSteps := edgeLimit.maxLookupSteps
              arithmeticWork := edgeLimit.maxArithmeticWork } edges with
        | failed failure =>
            cases failure <;> simp [hpreflight, PreflightFailure.result] at h
        | ready plan =>
            simp only [hpreflight] at h
            exact holds_of_replay
              (RationalTable.Table.canonical_of_check htable)
              (relates_of_preflight hpreflight) h
      next => contradiction

/-! ## Fixed all-operation canaries -/

/-- Canonical table used by every arithmetic-edge constructor. -/
def fixtureTable : List RawRat :=
  [⟨1, 2⟩, ⟨1, 3⟩, ⟨5, 6⟩, ⟨1, 6⟩, ⟨2, 1⟩]

/-- Table limits with one spare slot for total zero-inverse tests. -/
def fixtureTableLimit : RawRat.Limit :=
  { maxEntries := 6
    maxNumeratorBits := 8
    maxDenominatorBits := 8 }

/-- One successful edge of every first-slice operation. -/
def fixtureEdges : List ArithEdge :=
  [ .add 0 1 2
  , .sub 0 1 3
  , .mul 0 1 3
  , .inv 0 4
  , .eq 3 3
  , .le 1 0
  , .lt 1 0 ]

/-- Exact conservative resource total for `fixtureEdges`: seven edges, forty
`List` constructors visited, seven temporary bits, and 130 work units. -/
def fixtureLimit : Limit :=
  { maxEdges := 7
    maxLookupSteps := 40
    maxTemporaryBits := 7
    maxArithmeticWork := 130 }

/-- Acceptance, exact/one-over resources, complete preflight, and logical
failure canaries for the arithmetic-edge boundary. -/
def checksEdges : Bool :=
  check fixtureTableLimit fixtureLimit fixtureTable fixtureEdges == .ready &&
    check fixtureTableLimit { fixtureLimit with maxEdges := 6 }
      fixtureTable fixtureEdges == .edgeResource none .edges &&
    check fixtureTableLimit { fixtureLimit with maxLookupSteps := 39 }
      fixtureTable fixtureEdges == .edgeResource (some 6) .lookupSteps &&
    check fixtureTableLimit { fixtureLimit with maxTemporaryBits := 6 }
      fixtureTable fixtureEdges == .edgeResource (some 0) .temporaryBits &&
    check fixtureTableLimit { fixtureLimit with maxArithmeticWork := 129 }
      fixtureTable fixtureEdges == .edgeResource (some 6) .arithmeticWork &&
    check fixtureTableLimit fixtureLimit fixtureTable [.add 0 1 0] ==
      .malformedEdge 0 .wrongIdentity &&
    check fixtureTableLimit fixtureLimit fixtureTable [.add 0 99 2] ==
      .malformedEdge 0 (.badIndex .right 99) &&
    check fixtureTableLimit fixtureLimit (fixtureTable ++ [⟨0, 1⟩]) [.inv 5 5] ==
      .ready &&
    check fixtureTableLimit fixtureLimit fixtureTable
      [.add 0 1 0, .mul 0 99 3] ==
        .malformedEdge 1 (.badIndex .right 99)

/-- Ordinary-kernel canary for complete arithmetic-edge validation. -/
theorem checksEdges_eq_true : checksEdges = true := by
  decide +kernel

end Hex.Interval.Experiment.RationalEdge
