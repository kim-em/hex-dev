/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvFactor.Input
public import HexMvGcd.Squarefree

@[expose] public section

/-!
The bounded EEZ layer for one squarefree component.

This module owns only same-arity point/lift/recombination search.  Recursive
factorization of named-variable content and leading coefficients is supplied
as an arity-lowering callback by `Factor`.  Every Hensel proposal is accepted
by `MvHensel.liftWith`, whose result has already passed exact certificate
replay.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- Arity-independent failures produced inside one EEZ component. -/
inductive EezFailure where
  | point (attempts : Nat) (last : Option PointReject)
  | lift (inner : MvHensel.Failure)
  | recombine (levels : Nat)
  | random (error : RandError)
  deriving Repr

/-- An EEZ failure paired with the generator state reached before the
failure.  Point scouting consumes randomness even when no usable point is
found, so storing this state outside `Failure` is essential for composable
search. -/
structure EezError where
  reason : EezFailure
  rand : Rand

/-- Factors and scalar produced for one squarefree component. -/
structure EezResult {n : Nat} (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  content : Int
  factors : List (MvPoly n Int cmp)
  rand : Rand

/-- A stopped component with an exact, possibly coarse factor list for the
whole component.  `Factor` can combine this with completed squarefree
components instead of forgetting successful work. -/
structure EezProgress {n : Nat} (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  error : EezError
  content : Int
  factors : List (MvPoly n Int cmp)

/-- Result of trying one point: either final image-certified pieces or a
two-block grouping that must be put back through the EEZ queue. -/
inductive SplitResult {n : Nat}
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  | atoms (factors : List (MvPoly n Int cmp))
  | grouped (left right : MvPoly n Int cmp)

/-- A nonfatal decline of one accepted point.  Prime exhaustion changes the
point; recombination exhaustion is retained as its own public diagnosis. -/
inductive ProbeDecline where
  | primes
  | recombine
  deriving Repr, BEq, DecidableEq

/-- Outcome after trying every accepted probe. -/
inductive ProbeSearch {n : Nat}
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  | found (result : SplitResult cmp)
  | declined (reason : ProbeDecline)

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  [IsMonomialOrder cmp]

/-! # Main-variable heuristic -/

/-- Whether the main-variable leading coefficient is a nonzero constant. -/
def constantLeading (s : MvPoly (n + 1) Int cmp) (i : Fin (n + 1)) : Bool :=
  let lc := MvHensel.lcIn i Mono.lex s
  lc != 0 && lc.vars.isEmpty

/-- The SPEC's lexicographic preference: constant leading coefficient,
smaller leading-coefficient support, then larger main degree. -/
def betterMain (s : MvPoly (n + 1) Int cmp)
    (candidate incumbent : Fin (n + 1)) : Bool :=
  let candidateLc := MvHensel.lcIn candidate Mono.lex s
  let incumbentLc := MvHensel.lcIn incumbent Mono.lex s
  let candidateConst := candidateLc != 0 && candidateLc.vars.isEmpty
  let incumbentConst := incumbentLc != 0 && incumbentLc.vars.isEmpty
  if candidateConst != incumbentConst then candidateConst
  else if candidateLc.termCount != incumbentLc.termCount then
    candidateLc.termCount < incumbentLc.termCount
  else MvPoly.degreeOf incumbent s < MvPoly.degreeOf candidate s

/-- Choose a variable which occurs in the subject. -/
def chooseMain (s : MvPoly (n + 1) Int cmp) : Option (Fin (n + 1)) :=
  match s.vars with
  | [] => none
  | i :: is => some (is.foldl (fun best j => if betterMain s j best then j else best) i)

/-! # Subset recombination -/

def selectedCount (mask : List Bool) : Nat :=
  mask.foldl (fun count selected => if selected then count + 1 else count) 0

def maskLevel (mask : List Bool) : Nat :=
  min (selectedCount mask) (mask.length - selectedCount mask)

/-- Boolean vectors with one of the requested cardinalities, in the same
`false`-before-`true` lexicographic order as full mask enumeration.  Branches
whose requested cardinality exceeds the remaining length are discarded
before recursion. -/
def masksWithCounts : (length : Nat) → List Nat → List (List Bool)
  | 0, counts => if counts.contains 0 then [[]] else []
  | length + 1, counts =>
      let counts := counts.filter fun count => count ≤ length + 1
      let withHead := counts.filterMap fun
        | 0 => none
        | count + 1 => some count
      (masksWithCounts length counts).map (false :: ·) ++
        (masksWithCounts length withHead).map (true :: ·)

/-- Level-one representatives: the selected singleton containing index zero,
followed by complements of the other singletons. -/
def singletonMasks (length : Nat) : List (List Bool) :=
  let chosenFirst := (List.range length).map fun i => i == 0
  chosenFirst :: (List.range (length - 1)).map fun omitted =>
    (List.range length).map fun i => i != omitted + 1

/-- Representatives at one smaller-block cardinality.  Requiring the first
bit selects exactly one mask from each complementary pair.  Away from the
half-size tie, both possible cardinalities are generated in one pruned
lexicographic traversal so their old relative order is retained. -/
def masksAtLevel (length level : Nat) : List (List Bool) :=
  if level = 0 || length ≤ level then []
  else if level = 1 then singletonMasks length
  else
    let selected :=
      if 2 * level = length then [level - 1]
      else [level - 1, length - level - 1]
    (masksWithCounts (length - 1) selected).map (true :: ·)

/-- One representative of every proper complementary pair, in increasing
smaller-block cardinality.  Only requested cardinalities are constructed;
in particular level one produces `length` candidates instead of visiting a
power set.  At two images the original split is deliberately not retried. -/
def recombinationMasks (length levels : Nat) : List (List Bool) :=
  if length ≤ 2 then []
  else
    (List.range (min levels (length / 2))).flatMap fun zeroLevel =>
      masksAtLevel length (zeroLevel + 1)

structure Grouped {n : Nat}
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] where
  leftImages : List ZPoly
  rightImages : List ZPoly
  leftLeading : List (MvPoly n Int cmp')
  rightLeading : List (MvPoly n Int cmp')

def groupEntries {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp'] :
    List Bool → List ZPoly → List (MvPoly n Int cmp') →
      Option (Grouped cmp')
  | [], [], [] => some ⟨[], [], [], []⟩
  | selected :: mask, image :: images, leading :: leadings => do
      let grouped ← groupEntries mask images leadings
      if selected then
        some { grouped with
          leftImages := image :: grouped.leftImages
          leftLeading := leading :: grouped.leftLeading }
      else
        some { grouped with
          rightImages := image :: grouped.rightImages
          rightLeading := leading :: grouped.rightLeading }
  | _, _, _ => none

/-- Collapse one proper subset to a two-image probe. -/
def groupProbe {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp'] (probe : Probe n cmp cmp')
    (mask : List Bool) : Option (Probe n cmp cmp') := do
  let grouped ← groupEntries mask probe.images probe.leading
  if grouped.leftImages.isEmpty || grouped.rightImages.isEmpty then none
  else
    some
      { point := probe.point
        images := [MvHensel.uniProduct grouped.leftImages,
          MvHensel.uniProduct grouped.rightImages]
        leading := [MvHensel.mvProduct grouped.leftLeading,
          MvHensel.mvProduct grouped.rightLeading]
        uni := [] }

/-! # Prime, lift, and recombination attempts -/

def henselConfig (cfg : Config) : MvHensel.Config :=
  { doublings := cfg.doublings }

def tryGrouped {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp'] (cfg : Config) (i : Fin (n + 1))
    (target : MvPoly (n + 1) Int cmp) (probe : Probe n cmp cmp')
    (r : Rand) :
    List (List Bool) → Except EezError (Option (SplitResult cmp))
  | [] => .ok none
  | mask :: rest =>
      match groupProbe probe mask with
      | none => tryGrouped cfg i target probe r rest
      | some grouped =>
          match inputForProbe? cfg i target grouped with
          | .error .primesExhausted => tryGrouped cfg i target probe r rest
          | .error (.invalid failure) => .error ⟨.lift failure, r⟩
          | .ok inp =>
              match MvHensel.liftWith (henselConfig cfg) inp with
              | .ok cert =>
                  match cert.factors with
                  | [left, right] => .ok (some (.grouped left right))
                  | _ => .error ⟨.lift .arity, r⟩
              | .error (.reconstruct _) => tryGrouped cfg i target probe r rest
              | .error failure => .error ⟨.lift failure, r⟩

def tryProbe {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp'] (cfg : Config) (i : Fin (n + 1))
    (target : MvPoly (n + 1) Int cmp) (probe : Probe n cmp cmp')
    (r : Rand) : Except EezError (ProbeSearch cmp) :=
  if probe.images.length = 1 then
    .ok (.found (.atoms [target]))
  else
    match inputForProbe? cfg i target probe with
    | .error .primesExhausted => .ok (.declined .primes)
    | .error (.invalid failure) => .error ⟨.lift failure, r⟩
    | .ok inp =>
        match MvHensel.liftWith (henselConfig cfg) inp with
        | .ok cert => .ok (.found (.atoms cert.factors))
        | .error (.reconstruct _) =>
            match tryGrouped cfg i target probe r
                (recombinationMasks probe.images.length cfg.recombLevels) with
            | .error failure => .error failure
            | .ok (some result) => .ok (.found result)
            | .ok none => .ok (.declined .recombine)
        | .error failure => .error ⟨.lift failure, r⟩

def tryProbes {cmp' : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp'] (cfg : Config) (i : Fin (n + 1))
    (target : MvPoly (n + 1) Int cmp) (r : Rand) : Bool →
    List (Probe n cmp cmp') → Except EezError (ProbeSearch cmp)
  | sawRecombine, [] =>
      if sawRecombine then .ok (.declined .recombine)
      else .ok (.declined .primes)
  | sawRecombine, probe :: probes =>
      match tryProbe cfg i target probe r with
      | .error failure => .error failure
      | .ok (.found result) => .ok (.found result)
      | .ok (.declined .recombine) =>
          tryProbes cfg i target r true probes
      | .ok (.declined .primes) =>
          tryProbes cfg i target r sawRecombine probes

/-! # Same-arity work queue -/

/-- A lower-arity failure may retain a checked partial decomposition of the
coefficient polynomial.  Public recursion always supplies it; `none` keeps
the callback usable by small route tests which deliberately stop before
building a lower answer. -/
structure LowerProgress {n : Nat}
    (cmp : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp]
    (p : MvPoly n Int cmp) where
  error : EezError
  found : Option (CheckedDecomp p)

/-- The arity-lowering factorization operation supplied by `Factor`. -/
abbrev LowerFactor (n : Nat) :=
  (p : MvPoly n Int Mono.lex) → Rand →
    Except (LowerProgress Mono.lex p) (CheckedDecomp p × Rand)

/-- Embed a lower-arity decomposition's polynomial factors, expanding their
multiplicities because the EEZ queue records multiplicity-free atoms. -/
def embedFactors (i : Fin (n + 1)) (D : Decomp n Mono.lex) :
    List (MvPoly (n + 1) Int cmp) :=
  D.factors.flatMap fun entry =>
    List.replicate entry.multiplicity
      (MvPoly.constIn (cmp := cmp) i Mono.lex entry.factor)

def splitAt (lower : LowerFactor n) (cfg : Config) (i : Fin (n + 1))
    (target : MvPoly (n + 1) Int cmp) (r : Rand) :
    Except EezError (SplitResult cmp × Rand) :=
  let leadingCoeff := MvHensel.lcIn i Mono.lex target
  match lower leadingCoeff r with
  | .error progress => .error progress.error
  | .ok (leadingDecomp, r') =>
      let scouting := scoutPoints cfg i Mono.lex target leadingDecomp.raw r'
      if scouting.accepted.isEmpty then
        .error ⟨.point scouting.attempts scouting.lastReject, scouting.rand⟩
      else
        match tryProbes cfg i target scouting.rand false scouting.accepted with
        | .error failure => .error failure
        | .ok (.found result) => .ok (result, scouting.rand)
        | .ok (.declined .primes) =>
            .error ⟨.point scouting.attempts scouting.lastReject,
              scouting.rand⟩
        | .ok (.declined .recombine) =>
            .error ⟨.recombine cfg.recombLevels, scouting.rand⟩

def factorQueue (lower : LowerFactor n) (cfg : Config) (i : Fin (n + 1)) :
    Nat → List (MvPoly (n + 1) Int cmp) →
      List (MvPoly (n + 1) Int cmp) → Rand →
        Except (EezProgress cmp)
          (List (MvPoly (n + 1) Int cmp) × Rand)
  | _, [], done, r => .ok (done.reverse, r)
  | 0, target :: pending, done, r =>
      .error ⟨⟨.recombine cfg.recombLevels, r⟩, 1,
        done.reverse ++ (target :: pending)⟩
  | fuel + 1, target :: pending, done, r =>
      match splitAt lower cfg i target r with
      | .error failure =>
          .error ⟨failure, 1, done.reverse ++ (target :: pending)⟩
      | .ok (.atoms factors, r') =>
          factorQueue lower cfg i fuel pending (factors.reverse ++ done) r'
      | .ok (.grouped left right, r') =>
          factorQueue lower cfg i fuel (left :: right :: pending) done r'

/-- Factor one squarefree component, recursively extracting its content in
the selected main variable and then processing grouped factors with explicit
same-arity fuel. -/
def factorSquarefree (lower : LowerFactor n) (cfg : Config)
    (s : MvPoly (n + 1) Int cmp) (r : Rand) :
    Except (EezProgress cmp) (EezResult cmp) :=
  match chooseMain s with
  | none => .error ⟨⟨.lift .arity, r⟩, 1, [s]⟩
  | some i =>
      let coefficientPart := MvPoly.contentIn i Mono.lex s
      let mainPart := MvPoly.primPartIn i Mono.lex s
      match lower coefficientPart r with
      | .error progress =>
          match progress.found with
          | none => .error ⟨progress.error, 1, [s]⟩
          | some coefficientDecomp =>
              let embedded := embedFactors i coefficientDecomp.raw
              if MvPoly.polyIsUnit mainPart then
                .error
                  ⟨progress.error,
                    coefficientDecomp.raw.content * mainPart.leadingCoeff,
                    embedded⟩
              else
                .error
                  ⟨progress.error, coefficientDecomp.raw.content,
                    embedded ++ [mainPart]⟩
      | .ok (coefficientDecomp, r') =>
          /- Preserve the checked lower decomposition literally.  Squarefree
          semantics imply these multiplicities are one, but the executable
          producer must not need that theorem in order to retain the product. -/
          let embedded := embedFactors i coefficientDecomp.raw
          if MvPoly.polyIsUnit mainPart then
            .ok
              ⟨coefficientDecomp.raw.content * mainPart.leadingCoeff,
                embedded, r'⟩
          else
            match factorQueue lower cfg i (2 * mainPart.totalDegree + 1)
                [mainPart] [] r' with
            | .error progress =>
                .error
                  ⟨progress.error, coefficientDecomp.raw.content,
                    embedded ++ progress.factors⟩
            | .ok (mainFactors, r'') =>
                .ok ⟨coefficientDecomp.raw.content,
                  embedded ++ mainFactors, r''⟩

end Hex.MvFactor
