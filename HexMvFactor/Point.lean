/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.Rand
public import HexBerlekampZassenhaus.Factorization
public import HexMvFactor.Leading
public import HexPolyZGcd.SquareFree

@[expose] public section

/-!
Evaluation-point probing and shell enumeration for Wang's EEZ driver.

Degree loss is rejected before factorization, relative rational
squarefreeness is tested on the primitive image, and the complete leading
coefficient assignment is retained in an accepted probe.  Shells are visited
in increasing infinity norm; a fresh splitmix word gives every point in one
shell a deterministic random ordering key.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

/-- Search budgets shared by the point layer and the downstream EEZ driver. -/
structure Config where
  /-- Initial deterministic random-generator state. -/
  rand : Rand
  /-- Maximum number of evaluation points examined. -/
  pointFuel : Nat
  /-- Maximum number of admissible probes retained. -/
  pointScouts : Nat
  /-- Maximum infinity-norm shell enumerated for evaluation points. -/
  pointShell : Nat
  /-- Maximum number of candidate primes examined. -/
  primeFuel : Nat
  /-- Maximum number of reconstruction-modulus doublings. -/
  doublings : Nat
  /-- Number of grouped recombination levels attempted. -/
  recombLevels : Nat
  /-- Whether the Kronecker route may be used. -/
  kronecker : Bool
  /-- Maximum encoded univariate degree accepted by Kronecker substitution. -/
  kroneckerDeg : Nat
  deriving Repr, DecidableEq

namespace Config

/-- Reproducible default search policy from the factorization SPEC. -/
def default : Config :=
  { rand := Rand.ofSeed 0
    pointFuel := 256
    pointScouts := 4
    pointShell := 8
    primeFuel := 16
    doublings := 6
    recombLevels := 3
    kronecker := false
    kroneckerDeg := 4096 }

end Config

/-- The first condition which rejected a candidate evaluation point. -/
inductive PointReject where
  | degreeDrop
  | notSquarefree
  | leadingSplit
  deriving Repr, BEq, DecidableEq

/-- Data computed once at an accepted point and consumed unchanged by input
construction and recombination.  Here `n` is the number of non-main
variables; the target itself has arity `n + 1`. -/
structure Probe (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] where
  point : Fin n → Int
  images : List ZPoly
  leading : List (MvPoly n Int cmp')
  uni : List ZPoly

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

def primitiveFactors : List (ZPoly × Nat) → Option (List ZPoly)
  | [] => some []
  | (h, multiplicity) :: hs => do
      if multiplicity != 1 then none else pure ()
      match h.degree? with
      | none => none
      | some 0 => none
      | some (_ + 1) =>
          let tail ← primitiveFactors hs
          some (h :: tail)

/-- Executable relative squarefreeness test through the checked integer-gcd
route.  Taking the primitive part is essential: nonunit image content is
irrelevant to multiplicities of the polynomial part. -/
def squareFreeImage (image : ZPoly) : Bool :=
  let primitive := ZPoly.primitivePart image
  let derivative := DensePoly.derivative primitive
  (ZPoly.gcd primitive derivative).size ≤ 1

/-- Probe one caller-supplied point.  Factorization is deterministic, so the
random state is returned unchanged; only shell ordering advances it. -/
def probe (_cfg : Config) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (s : MvPoly (n + 1) Int cmp)
    (lc : Decomp n cmp') (r : Rand) :
    Except PointReject (Probe n cmp cmp' × Rand) :=
  let leadingCoeff := MvHensel.lcIn i cmp' s
  if MvPoly.eval a leadingCoeff = 0 then
    .error .degreeDrop
  else
    let image := MvHensel.imageAt i cmp' a s
    if !squareFreeImage image then
      .error .notSquarefree
    else
      let factorization := ZPoly.factorize image
      match primitiveFactors factorization.factors.toList with
      | none => .error .notSquarefree
      | some uni =>
          match distribute? i cmp' a lc uni factorization.scalar with
          | none => .error .leadingSplit
          | some (leading, images) =>
              if MvHensel.uniProduct images != image ||
                  MvHensel.mvProduct leading != leadingCoeff then
                .error .leadingSplit
              else
                .ok (⟨a, images, leading, uni⟩, r)

/-! # Increasing-shell enumeration -/

/-- Integer coordinates from `-radius` through `radius`. -/
def shellCoordinates (radius : Nat) : List Int :=
  (List.range (2 * radius + 1)).map fun k =>
    Int.ofNat k - Int.ofNat radius

/-- Every point in the closed infinity-norm cube of the given radius. -/
def cubePoints : (dimension radius : Nat) → List (Fin dimension → Int)
  | 0, _ => [fun i => Fin.elim0 i]
  | dimension + 1, radius =>
      (shellCoordinates radius).flatMap fun head =>
        (cubePoints dimension radius).map fun tail =>
          fun i => Fin.cases head tail i

/-- Infinity norm of an integer point. -/
def pointNorm (a : Fin n → Int) : Nat :=
  (List.finRange n).foldl (fun bound i => max bound (a i).natAbs) 0

/-- Points on the shell of exact infinity norm `radius`. -/
def shellPoints (dimension radius : Nat) : List (Fin dimension → Int) :=
  (cubePoints dimension radius).filter fun a => pointNorm a = radius

def insertKey {alpha : Type} (entry : UInt64 × alpha) :
    List (UInt64 × alpha) → List (UInt64 × alpha)
  | [] => [entry]
  | x :: xs =>
      if entry.1 < x.1 then entry :: x :: xs
      else x :: insertKey entry xs

def keyPoints {alpha : Type} :
    List alpha → Rand → List (UInt64 × alpha) × Rand
  | [], r => ([], r)
  | x :: xs, r =>
      let (key, r') := r.next
      let (tail, r'') := keyPoints xs r'
      (insertKey (key, x) tail, r'')

/-- Randomized order within one shell, with explicit state advancement. -/
def orderShell (points : List (Fin n → Int)) (r : Rand) :
    List (Fin n → Int) × Rand :=
  let keyed := keyPoints points r
  (keyed.1.map Prod.snd, keyed.2)

/-- Concatenate randomly ordered shells from radius zero through `maxShell`.
The shell order itself remains deterministic and size-preferring. -/
def shellOrder (dimension : Nat) : Nat → Rand →
    List (Fin dimension → Int) × Rand
  | 0, r => orderShell (shellPoints dimension 0) r
  | maxShell + 1, r =>
      let prior := shellOrder dimension maxShell r
      let current := orderShell (shellPoints dimension (maxShell + 1)) prior.2
      (prior.1 ++ current.1, current.2)

/-! # Fuel-bounded shell enumeration

The materialized helpers above remain useful for small route tests.  Search
uses the bounded rank/unrank route below: it never constructs more points
than the caller can try and its counters saturate at that budget, so a large
arity cannot turn a small point fuel into a dense cube allocation.
-/

def capAdd (cap a b : Nat) : Nat :=
  min cap (a + b)

def capMul (cap a b : Nat) : Nat :=
  if a = 0 || b = 0 then 0
  else if cap / a < b then cap else min cap (a * b)

def cubeCountBound : Nat → Nat → Nat → Nat
  | 0, _, cap => min cap 1
  | dimension + 1, radius, cap =>
      capMul cap (2 * radius + 1)
        (cubeCountBound dimension radius cap)

/-- Number of exact-shell points, saturated at `cap`. -/
def shellCountBound : Nat → Nat → Nat → Nat
  | 0, 0, cap => min cap 1
  | 0, _ + 1, _ => 0
  | _dimension + 1, 0, cap => min cap 1
  | dimension + 1, radius + 1, cap =>
      let boundary := capMul cap 2
        (cubeCountBound dimension (radius + 1) cap)
      let interior := capMul cap (2 * radius + 1)
        (shellCountBound dimension (radius + 1) cap)
      capAdd cap boundary interior

/-- Unrank a point of the closed cube.  Counts are saturated at `rank + 1`:
that is enough to decide every branch while avoiding arity-sized powers. -/
def cubePointAt : (dimension radius rank : Nat) → Fin dimension → Int
  | 0, _, _ => fun i => Fin.elim0 i
  | dimension + 1, radius, rank =>
      let tailCount := cubeCountBound dimension radius (rank + 1)
      let headIndex := if tailCount = 0 then 0 else rank / tailCount
      let tailRank := if tailCount = 0 then 0 else rank % tailCount
      fun i => Fin.cases
        (Int.ofNat headIndex - Int.ofNat radius)
        (cubePointAt dimension radius tailRank) i

/-- Unrank the budget-visible prefix of an exact infinity-norm shell. -/
def shellPointAt : (dimension radius rank : Nat) → Fin dimension → Int
  | 0, _, _ => fun i => Fin.elim0 i
  | _dimension + 1, 0, _ => fun i => Fin.cases 0 (fun _ => 0) i
  | dimension + 1, radius + 1, rank =>
      let actualRadius := radius + 1
      let cap := rank + 1
      let cubeTail := cubeCountBound dimension actualRadius cap
      if rank < cubeTail then
        fun i => Fin.cases (-Int.ofNat actualRadius)
          (cubePointAt dimension actualRadius rank) i
      else
        let afterLeft := rank - cubeTail
        let shellTail := shellCountBound dimension actualRadius
          (afterLeft + 1)
        let interiorCount := capMul (afterLeft + 1) (2 * radius + 1)
          shellTail
        if afterLeft < interiorCount && shellTail != 0 then
          let headIndex := afterLeft / shellTail
          let tailRank := afterLeft % shellTail
          fun i => Fin.cases
            (Int.ofNat (headIndex + 1) - Int.ofNat actualRadius)
            (shellPointAt dimension actualRadius tailRank) i
        else
          let tailRank := afterLeft - interiorCount
          fun i => Fin.cases (Int.ofNat actualRadius)
            (cubePointAt dimension actualRadius tailRank) i

def rotatedRanks (count : Nat) (word : UInt64) : List Nat :=
  if count = 0 then []
  else
    let offset := word.toNat % count
    let backwards := word.toNat % 2 = 1
    (List.range count).map fun k =>
      if backwards then (offset + count - k % count) % count
      else (offset + k) % count

/-- At most `fuel` points from increasing shells through `maxShell`.
Small shells are visited completely; a shell larger than the remaining
budget contributes a randomized, duplicate-free prefix.  One random word is
consumed per nonempty visited shell and zero fuel is the identity on `Rand`. -/
def boundedShellOrder (dimension maxShell fuel : Nat) (r : Rand) :
    List (Fin dimension → Int) × Rand :=
  let rec go : Nat → Nat → Nat → List (Fin dimension → Int) →
      Rand → List (Fin dimension → Int) × Rand
    | 0, _, _, acc, r => (acc.reverse, r)
    | shells + 1, radius, remaining, acc, r =>
      if remaining = 0 then (acc.reverse, r)
      else
      let count := shellCountBound dimension radius remaining
      if count = 0 then go shells (radius + 1) remaining acc r
      else
        let next := r.next
        let points := (rotatedRanks count next.1).map fun rank =>
          shellPointAt dimension radius rank
        go shells (radius + 1) (remaining - count)
          (points.reverse ++ acc) next.2
  go (maxShell + 1) 0 fuel [] r

/-- Result of a bounded scouting pass, including rejection diagnostics and
the generator state after shell randomization. -/
structure PointSearchResult (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp'] where
  best : Option (Probe n cmp cmp')
  /-- All admissible probes, ordered by increasing image-factor count. -/
  accepted : List (Probe n cmp cmp')
  attempts : Nat
  lastReject : Option PointReject
  rand : Rand

def insertProbe (candidate : Probe n cmp cmp') :
    List (Probe n cmp cmp') → List (Probe n cmp cmp')
  | [] => [candidate]
  | probe :: probes =>
      if candidate.images.length < probe.images.length then
        candidate :: probe :: probes
      else probe :: insertProbe candidate probes

/-- Enumerate bounded evaluation-point shells and retain the best probes. -/
def scoutPoints (cfg : Config) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (s : MvPoly (n + 1) Int cmp) (lc : Decomp n cmp') (r : Rand) :
    PointSearchResult n cmp cmp' :=
  let ordered := boundedShellOrder n cfg.pointShell cfg.pointFuel r
  let rec go (fuel scouts attempts : Nat) (last : Option PointReject)
      (best : Option (Probe n cmp cmp'))
      (accepted : List (Probe n cmp cmp')) :
      List (Fin n → Int) → PointSearchResult n cmp cmp'
    | [] => ⟨best, accepted, attempts, last, ordered.2⟩
    | a :: points =>
        if fuel = 0 || scouts = cfg.pointScouts then
          ⟨best, accepted, attempts, last, ordered.2⟩
        else
          match probe cfg i cmp' a s lc ordered.2 with
          | .error reject =>
              go (fuel - 1) scouts (attempts + 1) (some reject) best
                accepted points
          | .ok (candidate, _) =>
              let best := match best with
                | none => some candidate
                | some incumbent =>
                    if candidate.images.length < incumbent.images.length then
                      some candidate
                    else some incumbent
              let accepted := insertProbe candidate accepted
              if candidate.images.length = 1 then
                ⟨some candidate, accepted, attempts + 1, last, ordered.2⟩
              else
                go (fuel - 1) (scouts + 1) (attempts + 1) last best
                  accepted points
  go cfg.pointFuel 0 0 none none [] ordered.1

end Hex.MvFactor
