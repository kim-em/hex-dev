/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvFactor.Eez
public import HexMvFactor.Irred

@[expose] public section
set_option backward.proofsInPublic true

/-!
The bounded public factorization driver.

The executable route removes structural and monomial content, uses the
checked multivariate squarefree decomposition, recursively factors
named-variable content and EEZ leading coefficients one arity down, and
normalizes and merges the resulting factors.  A proposed answer is exposed
only after `checkDecomp` has accepted it.  On failure the caller receives an
explicitly coarse, but still checked, decomposition of the original input.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- Public, stable failure distinctions for bounded factorization. -/
inductive Failure (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  /-- The input is the zero polynomial. -/
  | zero
  /-- Evaluation-point search exhausted its budget. -/
  | point (attempts : Nat) (last : Option PointReject)
  /-- Multivariate Hensel lifting rejected the constructed input or stopped. -/
  | lift (inner : MvHensel.Failure)
  /-- Grouped recombination exhausted its level budget. -/
  | recombine (levels : Nat)
  /-- No available certificate proved the reported factor irreducible. -/
  | irreducible (factor : MvPoly n Int cmp)
  /-- Random-word generation failed. -/
  | random (error : RandError)

/-- A checked coarse answer together with the reason bounded search stopped
and the generator state reached at that point. -/
structure Partial {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp]
    (f : MvPoly n Int cmp) where
  /-- Checked decomposition accumulated before the search stopped. -/
  found : CheckedDecomp f
  /-- Exact reason why the bounded search stopped. -/
  reason : Failure n cmp
  /-- Random-generator state reached when the search stopped. -/
  rand : Rand

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp]

/-! # Checked coarse fallback -/

/-- Canonical one-block decomposition used only in `Partial`: constants have
no polynomial entry; a nonconstant input has its scalar content split off
and its normalized primitive part retained as one coarse factor. -/
def coarseDecomp (f : MvPoly n Int cmp) : Decomp n cmp :=
  let split := MvPoly.sqfPrimitiveSplit f
  if split.2.vars.isEmpty then
    ⟨split.1, []⟩
  else
    ⟨split.1, [⟨split.2, 1⟩]⟩

/-- A normalized primitive constant over the integers is the polynomial one. -/
private theorem normalizedPrimitive_eq_one (q : MvPoly n Int cmp)
    (hq : q ≠ 0) (hvars : q.vars = [])
    (hnormalized : polyNormalize q = q) (hprimitive : content q = 1) :
    q = 1 := by
  let c := coeff Mono.zero q
  have hqC : q = C c := eq_C_of_vars_eq_nil q hvars
  have hc : c ≠ 0 := by
    intro hzero
    apply hq
    rw [hqC, hzero, C_zero]
  have hnormalizedC : polyNormalize (C c : MvPoly n Int cmp) = C c := by
    rw [← hqC]
    exact hnormalized
  have hcontent : normalize c = 1 := by
    rw [hqC] at hprimitive
    unfold content scalarContent at hprimitive
    rw [termsList_C, ite_eq_right hc] at hprimitive
    exact hprimitive
  change c * (if c < 0 then -1 else 1) = 1 at hcontent
  by_cases hneg : c < 0
  · rw [ite_eq_left hneg] at hcontent
    have hcneg : c = -1 := by omega
    exfalso
    rw [hcneg] at hnormalizedC
    unfold polyNormalize polyNormUnit at hnormalizedC
    rw [leadingTerm_C (by decide : (-1 : Int) ≠ 0)] at hnormalizedC
    change monomial Mono.zero (-1 : Int) * monomial Mono.zero (-1 : Int) =
      monomial Mono.zero (-1 : Int) at hnormalizedC
    rw [monomial_mul_monomial, Mono.zero_mul] at hnormalizedC
    have hcoefficient := congrArg (coeff (Mono.zero : Mono n)) hnormalizedC
    rw [coeff_monomial, coeff_monomial,
      ite_eq_left rfl, ite_eq_left rfl] at hcoefficient
    omega
  · rw [ite_eq_right hneg] at hcontent
    have hcOne : c = 1 := by omega
    rw [hqC, hcOne]
    rfl

/-- The coarse fallback is a genuine D1--D5 decomposition. -/
theorem coarse_checks (f : MvPoly n Int cmp) :
    checkDecomp f (coarseDecomp f) = true := by
  let split := MvPoly.sqfPrimitiveSplit f
  unfold coarseDecomp
  change checkDecomp f
    (if split.2.vars.isEmpty then ⟨split.1, []⟩
      else ⟨split.1, [⟨split.2, 1⟩]⟩) = true
  by_cases hempty : split.2.vars.isEmpty = true
  · rw [ite_eq_left hempty]
    have hvars : split.2.vars = [] := List.isEmpty_iff.mp hempty
    by_cases hzero : split.2 = 0
    · have hproduct := MvPoly.sqfPrimitiveSplit_product f
      change C split.1 * split.2 = f at hproduct
      rw [hzero, MvPoly.mul_zero] at hproduct
      have hf : f = 0 := hproduct.symm
      have hscalar : split.1 = 0 := by
        subst f
        simp only [split, MvPoly.sqfPrimitiveSplit, content_zero,
          primPart_zero, leadingCoeff_zero, Lean.Grind.Semiring.zero_mul]
      simp only [checkDecomp, Decomp.product, List.foldl_nil,
        distinctFactors, Bool.and_eq_true, beq_iff_eq]
      rw [hscalar, C_zero]
      exact ⟨⟨hf.symm, rfl⟩, True.intro⟩
    · have hone : split.2 = 1 := normalizedPrimitive_eq_one split.2 hzero
        hvars (MvPoly.sqfPrimitiveSplit_normalized f)
        (MvPoly.sqfPrimitiveSplit_primitive f hzero)
      have hproduct := MvPoly.sqfPrimitiveSplit_product f
      change C split.1 * split.2 = f at hproduct
      rw [hone, MvPoly.mul_one] at hproduct
      simp only [checkDecomp, Decomp.product, List.foldl_nil,
        distinctFactors, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hproduct, rfl⟩, True.intro⟩
  · rw [ite_eq_right hempty]
    have hvars : split.2.vars ≠ [] := by
      intro hnil
      apply hempty
      exact List.isEmpty_iff.mpr hnil
    have hzero : split.2 ≠ 0 := by
      intro hzero
      rw [hzero, vars_zero] at hvars
      contradiction
    have hfactor : checkFactor (⟨split.2, 1⟩ : Factor n cmp) = true := by
      simp only [checkFactor, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      exact ⟨⟨⟨by decide, hvars⟩,
        MvPoly.sqfPrimitiveSplit_normalized f⟩,
        MvPoly.sqfPrimitiveSplit_primitive f hzero⟩
    have hproduct := MvPoly.sqfPrimitiveSplit_product f
    change C split.1 * split.2 = f at hproduct
    simp only [checkDecomp, Decomp.product, List.foldl_cons,
      List.foldl_nil, distinctFactors, Bool.and_eq_true, beq_iff_eq]
    rw [MvPoly.pow_succ split.2 0, MvPoly.pow_zero, MvPoly.one_mul]
    refine ⟨⟨hproduct, ?_⟩, ⟨rfl, True.intro⟩⟩
    simpa only [List.all_cons, List.all_nil, Bool.and_true] using hfactor

def coarseChecked (f : MvPoly n Int cmp) : CheckedDecomp f :=
  ⟨coarseDecomp f, coarse_checks f⟩

def stopped (f : MvPoly n Int cmp) (reason : Failure n cmp)
    (r : Rand) : Except (Partial f) (CheckedDecomp f × Rand) :=
  .error ⟨coarseChecked f, reason, r⟩

/-- Retain an exact accumulated proposal when it passes D1--D5, falling
back to the checked coarse answer only if an internal producer invariant was
violated. -/
def stoppedWith (f : MvPoly n Int cmp) (D : Decomp n cmp)
    (reason : Failure n cmp) (r : Rand) :
    Except (Partial f) (CheckedDecomp f × Rand) :=
  if h : checkDecomp f D = true then
    .error ⟨⟨D, h⟩, reason, r⟩
  else stopped f (.lift .imageProduct) r

/-! # Normalization and multiplicity merge -/

/-- Normalize one factor and return the inverse unit which must be moved to
the scalar in order to preserve the represented product. -/
def normalizeEntry (entry : Factor n cmp) : Int × Factor n cmp :=
  let unit := GcdOps.normUnit entry.factor.leadingCoeff
  let inverse := GcdOps.exactDiv 1 unit
  (inverse ^ entry.multiplicity,
    ⟨MvPoly.polyNormalize entry.factor, entry.multiplicity⟩)

def mergeEntry (entry : Factor n cmp) :
    List (Factor n cmp) → List (Factor n cmp)
  | [] => [entry]
  | head :: tail =>
      if entry.factor == head.factor then
        ⟨head.factor, head.multiplicity + entry.multiplicity⟩ :: tail
      else head :: mergeEntry entry tail

def insertMultiplicity (entry : Factor n cmp) :
    List (Factor n cmp) → List (Factor n cmp)
  | [] => [entry]
  | head :: tail =>
      if entry.multiplicity < head.multiplicity then entry :: head :: tail
      else head :: insertMultiplicity entry tail

def sortFactors (factors : List (Factor n cmp)) : List (Factor n cmp) :=
  factors.foldl (fun sorted entry => insertMultiplicity entry sorted) []

/-- Canonicalize signs, merge equal factors, and sort by multiplicity. -/
def normalizeDecomp (content : Int) (factors : List (Factor n cmp)) :
    Decomp n cmp :=
  let normalized := factors.foldl
    (fun state entry =>
      let next := normalizeEntry entry
      (state.1 * next.1, mergeEntry next.2 state.2))
    (content, [])
  ⟨normalized.1, sortFactors normalized.2⟩

/-! # Arity-indexed recursion -/

def publicFailure {m : Nat}
    {order : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order] :
    Failure m order → EezFailure
  | .zero => .lift .arity
  | .point attempts last => .point attempts last
  | .lift inner => .lift inner
  | .recombine levels => .recombine levels
  | .irreducible _ => .recombine 0
  | .random error => .random error

def eezFailure (failure : EezFailure) : Failure n cmp :=
  match failure with
  | .point attempts last => .point attempts last
  | .lift inner => .lift inner
  | .recombine levels => .recombine levels
  | .random error => .random error

/-- Result accumulated while factoring the squarefree components. -/
structure Components (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  content : Int
  factors : List (Factor n cmp)
  rand : Rand

/-- Exact progress after a squarefree component stops.  Completed factors
are retained and the stopped/current and later components remain as coarse
exact entries. -/
structure ComponentsProgress (n : Nat)
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  error : EezError
  content : Int
  factors : List (Factor n cmp)

variable {m : Nat}
  {outer : Mono (m + 1) → Mono (m + 1) → Ordering}
  [IsMonomialOrder outer]

def factorComponents (lower : LowerFactor m) (cfg : Config) :
    List (MvPoly.SqfFactor (m + 1) Int outer) → Int →
      List (Factor (m + 1) outer) → Rand →
        Except (ComponentsProgress (m + 1) outer)
          (Components (m + 1) outer)
  | [], content, factors, r => .ok ⟨content, factors.reverse, r⟩
  | entry :: entries, content, factors, r =>
      match factorSquarefree lower cfg entry.factor r with
      | .error progress =>
          let current := progress.factors.map fun factor =>
            ⟨factor, entry.multiplicity⟩
          let pending := entries.map fun later =>
            ⟨later.factor, later.multiplicity⟩
          .error
            ⟨progress.error,
              content * progress.content ^ entry.multiplicity,
              factors.reverse ++ current ++ pending⟩
      | .ok result =>
          let lifted := result.factors.map fun factor =>
            ⟨factor, entry.multiplicity⟩
          factorComponents lower cfg entries
            (content * result.content ^ entry.multiplicity)
            (lifted.reverse ++ factors) result.rand

/-- Package the comparator-polymorphic operation at one arity so recursive
descent is visibly structural in `n`. -/
structure FactorOpsAt (n : Nat) : Type 1 where
  run : (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → (cfg : Config) →
    (f : MvPoly n Int cmp) → (r : Rand) →
      Except (Partial f) (CheckedDecomp f × Rand)

def factorBase : FactorOpsAt 0 where
  run := fun _ _ _cfg f r =>
    match h : structural? f with
    | some D => .ok (⟨D, structural_checks h⟩, r)
    | none => stopped f (.lift .arity) r

def factorStep {m : Nat} (lowerOps : FactorOpsAt m) :
    FactorOpsAt (m + 1) where
  run := fun outer _ cfg f r =>
    match hstruct : structural? f with
    | some D => .ok (⟨D, structural_checks hstruct⟩, r)
    | none =>
        let common := MvPoly.monoContent f
        let monomialPart : MvPoly (m + 1) Int outer :=
          MvPoly.monomial common 1
        match MvPoly.divExact? f monomialPart with
        | none => stopped f (.lift .imageProduct) r
        | some core =>
            let squarefree := MvPoly.sqfDecomp core
            let lower : LowerFactor m := fun p r' =>
              match lowerOps.run Mono.lex cfg p r' with
              | .ok answer => .ok answer
              | .error stoppedAnswer =>
                  .error
                    ⟨⟨publicFailure stoppedAnswer.reason,
                      stoppedAnswer.rand⟩,
                    some stoppedAnswer.found⟩
            match factorComponents lower cfg squarefree.factors
                squarefree.content (monomialFactors common) r with
            | .error progress =>
                let D := normalizeDecomp progress.content progress.factors
                stoppedWith f D (eezFailure progress.error.reason)
                  progress.error.rand
            | .ok result =>
                let D := normalizeDecomp result.content result.factors
                if h : checkDecomp f D = true then
                  .ok (⟨D, h⟩, result.rand)
                else
                  stopped f (.lift .imageProduct) result.rand

/-- The structurally recursive family of factorization operations. -/
def factorOps : (n : Nat) → FactorOpsAt n
  | 0 => factorBase
  | n + 1 => factorStep (factorOps n)

/-- Bounded factorization with explicit configuration and generator state. -/
def factorWith (cfg : Config) (f : MvPoly n Int cmp) :
    Except (Partial f) (CheckedDecomp f × Rand) :=
  (factorOps n).run cmp cfg f cfg.rand

/-- Deterministic convenience entry point using `Config.default`. -/
def factor? (f : MvPoly n Int cmp) :
    Except (Partial f) (CheckedDecomp f) :=
  match factorWith Config.default f with
  | .ok (answer, _) => .ok answer
  | .error failure => .error failure

/-! # Irreducibility certificate production -/

/-- Internal certificate failure with the exact generator state reached.
The public `irredCert?` projects the documented `Failure`; `completeWith`
retains the state in its `Partial`. -/
structure IrredError {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] where
  reason : Failure n cmp
  rand : Rand

/-- Try every named variable for the obligation-free degree-one route. -/
def degreeOneCert? {m : Nat}
    {outer : Mono (m + 1) → Mono (m + 1) → Ordering}
    [IsMonomialOrder outer] (g : MvPoly (m + 1) Int outer) :
    List (Fin (m + 1)) → Option (IrredCert (m + 1) outer)
  | [] => none
  | i :: is =>
      if MvPoly.degreeOf i g = 1 then
        let prim := MvPoly.contentInCert i Mono.lex g
        let cert : IrredCert (m + 1) outer := .degreeOne i Mono.lex prim
        if checkIrred g cert then some cert else degreeOneCert? g is
      else
        degreeOneCert? g is

/-- A point produces an image certificate only when the exact univariate
factorization has one primitive factor with multiplicity one and that factor
is precisely the obligation exposed by `checkIrred`. -/
def imageCertAt? {m : Nat}
    {outer : Mono (m + 1) → Mono (m + 1) → Ordering}
    [IsMonomialOrder outer] (i : Fin (m + 1))
    (g : MvPoly (m + 1) Int outer) (point : Fin m → Int) :
    Option (IrredCert (m + 1) outer) :=
  if MvPoly.eval point (MvHensel.lcIn i Mono.lex g) = 0 then none
  else
    let image := MvHensel.imageAt i Mono.lex point g
    let factorization := ZPoly.factorize image
    match factorization.factors.toList with
    | [(factor, 1)] =>
        let primitive := ZPoly.primitivePart image
        if factor == primitive || -factor == primitive then
          let prim := MvPoly.contentInCert i Mono.lex g
          let cert : IrredCert (m + 1) outer :=
            .image i Mono.lex point prim
          if checkIrred g cert then some cert else none
        else none
    | _ => none

/-- Bounded point loop for the image route.  `attempts` counts every point;
`scouts` counts the degree-preserving points whose image is factored. -/
def imagePoints {m : Nat}
    {outer : Mono (m + 1) → Mono (m + 1) → Ordering}
    [IsMonomialOrder outer] (cfg : Config) (i : Fin (m + 1))
    (g : MvPoly (m + 1) Int outer) :
    Nat → Nat → List (Fin m → Int) →
      Option (IrredCert (m + 1) outer)
  | _, _, [] => none
  | attempts, scouts, point :: points =>
      if attempts = cfg.pointFuel || scouts = cfg.pointScouts then none
      else
        let keepsDegree :=
          MvPoly.eval point (MvHensel.lcIn i Mono.lex g) != 0
        match imageCertAt? i g point with
        | some cert => some cert
        | none => imagePoints cfg i g (attempts + 1)
            (if keepsDegree then scouts + 1 else scouts) points

/-- Try the preferred main variable at randomized points in increasing
shell order, returning the advanced shell-ordering state even on failure. -/
def imageCert? {m : Nat}
    {outer : Mono (m + 1) → Mono (m + 1) → Ordering}
    [IsMonomialOrder outer] (cfg : Config)
    (g : MvPoly (m + 1) Int outer) (r : Rand) :
    Option (IrredCert (m + 1) outer) × Rand :=
  match chooseMain g with
  | none => (none, r)
  | some i =>
      let ordered := boundedShellOrder m cfg.pointShell cfg.pointFuel r
      (imagePoints cfg i g 0 0 ordered.1, ordered.2)

/-- Comparator-polymorphic certificate production at one arity. -/
structure IrredOpsAt (n : Nat) : Type 1 where
  run : (cmp : Mono n → Mono n → Ordering) →
    [_order : IsMonomialOrder cmp] → Config → MvPoly n Int cmp → Rand →
      Except (IrredError (cmp := cmp)) (IrredCert n cmp × Rand)

def irredBase : IrredOpsAt 0 where
  run := fun _order _ _cfg g r =>
    if g == 0 then .error ⟨.zero, r⟩
    else .error ⟨.irreducible g, r⟩

/-- Try missing variables in order, recursively certifying the exact
coefficient extracted from the constant recursive view. -/
def embedCert? {m : Nat} (lower : IrredOpsAt m)
    {outer : Mono (m + 1) → Mono (m + 1) → Ordering}
    [IsMonomialOrder outer] (cfg : Config)
    (g : MvPoly (m + 1) Int outer) :
    List (Fin (m + 1)) → Rand →
      Except (IrredError (cmp := outer)) (IrredCert (m + 1) outer × Rand)
  | [], r => .error ⟨.irreducible g, r⟩
  | i :: is, r =>
      if MvPoly.degreeOf i g = 0 then
        let sub := MvPoly.coeffIn i Mono.lex 0 g
        match lower.run Mono.lex cfg sub r with
        | .ok (cert, r') =>
            let embedded : IrredCert (m + 1) outer :=
              .embed i Mono.lex sub cert
            if checkIrred g embedded then .ok (embedded, r')
            else embedCert? lower cfg g is r'
        | .error failure =>
            match failure.reason with
            | .random error => .error ⟨.random error, failure.rand⟩
            | _ => embedCert? lower cfg g is failure.rand
      else
        embedCert? lower cfg g is r

/-- Kronecker is attempted only when enabled and the sparse encoded degree
fits the configured producer budget.  Dense image construction happens only
after that rejection point, and the accepted path reuses the prepared image. -/
def kronCert? {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] (cfg : Config) (g : MvPoly k Int order) :
    Option (IrredCert k order) :=
  if !cfg.kronecker then none
  else kronProduce? cfg.kroneckerDeg g

def irredStep {m : Nat} (lower : IrredOpsAt m) : IrredOpsAt (m + 1) where
  run := fun _outer _ cfg g r =>
    if g == 0 then .error ⟨.zero, r⟩
    else if g.vars.isEmpty then .error ⟨.irreducible g, r⟩
    else
      match degreeOneCert? g (List.finRange (m + 1)) with
      | some cert => .ok (cert, r)
      | none =>
          let image := imageCert? cfg g r
          match image.1 with
          | some cert => .ok (cert, image.2)
          | none =>
              match embedCert? lower cfg g (List.finRange (m + 1)) image.2 with
              | .ok answer => .ok answer
              | .error failure =>
                  match failure.reason with
                  | .random _ => .error failure
                  | _ =>
                      match kronCert? cfg g with
                      | some cert => .ok (cert, failure.rand)
                      | none =>
                          .error ⟨.irreducible g, failure.rand⟩

def irredOps : (n : Nat) → IrredOpsAt n
  | 0 => irredBase
  | n + 1 => irredStep (irredOps n)

/-- Produce a checked irreducibility certificate, preserving the explicit
generator state on success and the public failure taxonomy on failure. -/
def irredCert? (cfg : Config) (g : MvPoly n Int cmp) :
    Except (Failure n cmp) (IrredCert n cmp × Rand) :=
  match (irredOps n).run cmp cfg g cfg.rand with
  | .ok answer => .ok answer
  | .error failure => .error failure.reason

/-! # Complete checked factorization -/

/-- Certify each decomposition entry in order while threading the exact
generator state. -/
def certifyFactors (ops : IrredOpsAt n) (cfg : Config) :
    List (Factor n cmp) → Rand →
      Except (IrredError (cmp := cmp)) (List (IrredCert n cmp) × Rand)
  | [], r => .ok ([], r)
  | entry :: entries, r =>
      match ops.run cmp cfg entry.factor r with
      | .error failure => .error failure
      | .ok (cert, r') =>
          match certifyFactors ops cfg entries r' with
          | .error failure => .error failure
          | .ok (certs, r'') => .ok (cert :: certs, r'')

/-- Bounded factorization followed by checked certificate production for
every returned factor.  No complete result is exposed without final replay. -/
def completeWith (cfg : Config) (f : MvPoly n Int cmp) :
    Except (Partial f) (CheckedComplete f × Rand) :=
  match factorWith cfg f with
  | .error stoppedAnswer => .error stoppedAnswer
  | .ok (decomp, r) =>
      if f == 0 then
        .error ⟨decomp, .zero, r⟩
      else
        match certifyFactors (irredOps n) cfg decomp.raw.factors r with
        | .error failure =>
            .error ⟨decomp, failure.reason, failure.rand⟩
        | .ok (certs, r') =>
            let complete : Complete n cmp := ⟨decomp.raw, certs⟩
            if h : checkComplete f complete = true then
              .ok (⟨complete, h⟩, r')
            else
              .error ⟨decomp, .lift .imageProduct, r'⟩

/-- Deterministic complete factorization at `Config.default`. -/
def complete? (f : MvPoly n Int cmp) :
    Except (Partial f) (CheckedComplete f) :=
  match completeWith Config.default f with
  | .ok (answer, _) => .ok answer
  | .error failure => .error failure

end Hex.MvFactor
