/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus

/-!
Measurement spike (UNPROVEN) for issue #8625: recursive per-remainder re-lift
for sub-floor classical irreducibility certification.

Today the classical tier runs ONE Hensel lift of the whole core at
`precisionForCoeffBound (exhaustiveLiftBound core B) p` and certifies
irreducibility of unsplit remainders through coverage of that single lift,
whose partition completeness is gated at the monic-core Mignotte floor
`2 * defaultFactorCoeffBound (toMonic core).monic < p^k` (see #8620). The only
sound route below that floor is to give each unsplit remainder a FRESH
lift/partition/coverage stack of its own, at the remainder's OWN monic floor.

This file prototypes that recursion executably (unproven, like
`classicalFactorIntK` in `ClassicalSpike.lean`) in two variants:

* **fresh-prime**: each remainder gets its own `choosePrimeData?` (prime walk
  plus Berlekamp) and its own escalation ladder. Maximum flexibility (a
  remainder that is irreducible mod its fresh prime certifies with no lift at
  all, via the `SmallModSingleton` chain), but re-pays prime selection per
  node.
* **same-prime**: each remainder keeps the parent's prime and its own
  mod-p factors (known from the split that produced it), and re-lifts just
  those to the remainder's own floor. No per-node prime walk or Berlekamp;
  the inherited r = 1 case (a remainder covering a single local factor) still
  certifies for free. This is also the smaller proof-surface variant.

Accounting per certification node: target degree, prime, local factor count
`r`, own floor exponent, ladder exponent reached, recombination scans run.
Per input we compare today's single-lift exponent `k_today`, the core-local
floor `k_corelocal` (#8620 rewrite-1 reference), and each recursion's
`sum k` / degree-weighted work model `sum deg^2 * k` (lift cost scales with
the square of the target degree at fixed exponent, so a raw `sum k` flatters
neither side).

The recombination scan shared by all arms prefilters candidates with the
classic d-1 test and replaces `exactQuotient?`'s full `divMod` with a bounded
division that aborts once a quotient coefficient exceeds the target's Mignotte
factor bound (no true cofactor can). Without the bound, failing candidates in
below-recovery-precision scans grow geometrically and their multi-limb
divisions dominate wallclock, which would charge the ladder for a defect of
the naive scan rather than for lifting. Production recombination
(`scaledRecombinationSmart`) already has equivalent-or-stronger residue
filters.

Restricted to monic squarefree cores (every corpus core below is monic; the
non-squarefree `adv/high_multiplicity` input enters via its squarefree core,
exactly as production does after `normalizeForFactor`).

Proves nothing. This is a measurement artifact gating deliverable 2 of #8625.
-/

open Hex

local instance : Inhabited ZPoly := ⟨0⟩

/-! ### Recombination (smart subset scan, after `ClassicalSpike.lean`) -/

/-- All size-`k` sub-lists of `xs`, each paired with its complement. Structural;
worst-case `2^|xs|`, but the caller tries small `k` first and stops early. -/
def chooseWithComplement {α : Type} : List α → Nat → List (List α × List α)
  | xs, 0 => [([], xs)]
  | [], _ + 1 => []
  | x :: xs, k + 1 =>
      (chooseWithComplement xs k).map (fun sc => (x :: sc.1, sc.2)) ++
      (chooseWithComplement xs (k + 1)).map (fun sc => (sc.1, x :: sc.2))

def firstSomeList {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f => match f x with | some y => some y | none => firstSomeList xs f

/-- Reduce every coefficient of `g` into `[0, m)`. -/
def reduceModInt (g : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs (g.toArray.map (fun c => Int.emod c (Int.ofNat m)))

/-- Product of a subset of lifted factors, reduced mod `m` after each multiply. -/
def productModInt (s : List ZPoly) (m : Nat) : ZPoly :=
  s.foldl (fun acc g => reduceModInt (acc * g) m) (1 : ZPoly)

/-- Exact division of `target` by a MONIC `cand` of degree >= 1, aborting as
soon as a quotient coefficient exceeds `qbound` in absolute value — a true
cofactor of `target` respects the Mignotte factor bound, while a failing
candidate's synthetic-division coefficients grow geometrically. The abort caps
each failing candidate at a few division steps instead of a full multi-limb
`divMod`. -/
def boundedExactQuotientMonic? (target cand : ZPoly) (qbound : Nat) :
    Option ZPoly := Id.run do
  let n := target.size
  let m := cand.size
  if m < 2 || m > n then return none
  if cand.coeff (m - 1) != 1 then return none
  let mut rem := target.toArray
  let dq := n - m
  let mut q : Array Int := Array.replicate (dq + 1) 0
  for step in [0:dq + 1] do
    let i := dq - step
    let c := rem[i + m - 1]!
    if c.natAbs > qbound then return none
    if c != 0 then
      q := q.set! i c
      for j in [0:m] do
        rem := rem.set! (i + j) (rem[i + j]! - c * cand.coeff j)
  for j in [0:m - 1] do
    if rem[j]! != 0 then return none
  return some (DensePoly.ofCoeffs q)

/-- One recombination entry: the factor lifted to the current modulus paired
with its base mod-`p` factor (lifted to `Z`), tracked so a split piece keeps
its own local factors for the same-prime sub-lift. -/
abbrev LiftedPair := ZPoly × ZPoly

/-- First subset of `remaining` (sizes `size..hi`) whose centered product
exactly divides `target`; returns the integer factor, the base mod-p factors
it came from, the quotient, and the unused pairs. Smallest size first, so
fully-split inputs peel singletons in O(r). Candidates pass the d-1
trailing-coefficient test and the bounded division against `qbound`. -/
partial def findDivisorPairs
    (target : ZPoly) (remaining : List LiftedPair) (modulus qbound : Nat)
    (size hi : Nat) :
    Option (ZPoly × List ZPoly × ZPoly × List LiftedPair) :=
  if size > hi then none
  else
    let t0 := target.coeff 0
    let scan := firstSomeList (chooseWithComplement remaining size) fun sc =>
      let cand := centeredLiftPoly (productModInt (sc.1.map (·.1)) modulus) modulus
      let c0 := cand.coeff 0
      if c0 != 0 && Int.emod t0 c0 != 0 then none
      else
        match boundedExactQuotientMonic? target cand qbound with
        | some q => some (cand, sc.1.map (·.2), q, sc.2)
        | none => none
    match scan with
    | some res => some res
    | none => findDivisorPairs target remaining modulus qbound (size + 1) hi

/-- Peel integer factors off `target` one at a time, each paired with its base
mod-p factors; when no proper subset (size `1..r/2`) divides, the whole
remaining target is pushed unsplit with all remaining base factors. `qbound`
is a Mignotte factor bound for the ORIGINAL node target, computed once by the
caller (every peeled cofactor is a factor of it, so the bound stays sound down
the peel chain; recomputing per quotient is expensive big-int work). -/
partial def recombPairs
    (target : ZPoly) (remaining : List LiftedPair) (modulus qbound hiCap : Nat)
    (acc : Array (ZPoly × List ZPoly)) : Array (ZPoly × List ZPoly) :=
  let r := remaining.length
  if r == 0 then acc
  else
    match findDivisorPairs target remaining modulus qbound 1 (min hiCap (r / 2)) with
    | some (cand, candBase, quotient, rest) =>
        recombPairs quotient rest modulus qbound hiCap (acc.push (cand, candBase))
    | none => acc.push (target, remaining.map (·.2))

/-- Base-factor-blind wrapper (pairs each lifted factor with itself). -/
def recombInt (target : ZPoly) (factors : List ZPoly) (modulus qbound : Nat) :
    Array ZPoly :=
  (recombPairs target (factors.map fun g => (g, g)) modulus qbound
    factors.length #[]).map (·.1)

/-! ### The recursive per-remainder certification -/

/-- Accounting record for one certification node (one remainder). -/
structure NodeRec where
  deg : Nat
  p : Nat
  r : Nat
  /-- The remainder's own monic-transform Mignotte floor exponent at `p`. -/
  floorK : Nat
  /-- Ladder exponent actually reached (0 for the lift-free certificates). -/
  kStop : Nat
  /-- Number of lift+recombination rungs run on this node. -/
  rungs : Nat
  outcome : String
  deriving Inhabited

/-- Escalation ladder for one remainder under a FRESH prime selection: lift
`g`'s modular factors to `k = 1, 2, 4, ...` (clamped at `floorK`) and try to
recombine. Returns `(kStop, rungs, pieces)`; a singleton `pieces` means `g`
never split, so the final rung was the floor and `g` is certified irreducible
by fresh coverage. -/
partial def reliftLadder
    (g : ZPoly) (pd : PrimeChoiceData) (singletonSubFloor : Bool)
    (qbound floorK k rungs : Nat) :
    Nat × Nat × Array (ZPoly × List ZPoly) :=
  let kk := min k floorK
  let ld := henselLiftData g kk pd
  letI := pd.bounds
  let base := pd.factorsModP.toList.map FpPoly.liftToZ
  let pairs := ld.liftedFactors.toList.zip base
  let hiCap := if singletonSubFloor && kk != floorK then 1 else pairs.length
  let pieces := recombPairs g pairs (pd.p ^ kk) qbound hiCap #[]
  if pieces.size ≥ 2 then (kk, rungs + 1, pieces)
  else if kk == floorK then (kk, rungs + 1, #[(g, base)])
  else reliftLadder g pd singletonSubFloor qbound floorK (k * 2) (rungs + 1)

/-- Fresh-prime recursion: certify `g` (monic, squarefree) against a fresh
prime selection and lift of its own, recursing on any split pieces. Returns
the certified-irreducible factors and the per-node accounting. -/
partial def certifyAux (g : ZPoly) (recs : Array NodeRec) :
    Array ZPoly × Array NodeRec :=
  let deg := g.degree?.getD 0
  if deg ≤ 1 then
    (#[g], recs.push { deg, p := 0, r := 0, floorK := 0, kStop := 0, rungs := 0,
                       outcome := "deg<=1" })
  else
    match choosePrimeData? g with
    | none =>
        (#[g], recs.push { deg, p := 0, r := 0, floorK := 0, kStop := 0, rungs := 0,
                           outcome := "NO-PRIME" })
    | some pd =>
        let r := pd.factorsModP.size
        if r ≤ 1 then
          (#[g], recs.push { deg, p := pd.p, r, floorK := 0, kStop := 0, rungs := 0,
                             outcome := "modp-irreducible" })
        else
          let qbound := ZPoly.defaultFactorCoeffBound (ZPoly.toMonic g).monic
          let floorK := precisionForCoeffBound qbound pd.p
          let (kStop, rungs, pieces) := reliftLadder g pd false qbound floorK 1 0
          if pieces.size == 1 then
            (#[g], recs.push { deg, p := pd.p, r, floorK, kStop, rungs,
                               outcome := "floor-certified" })
          else
            let recs := recs.push { deg, p := pd.p, r, floorK, kStop, rungs,
                                    outcome := "split" }
            pieces.foldl (init := (#[], recs)) fun st piece =>
              let (fs, rs) := certifyAux piece.1 st.2
              (st.1 ++ fs, rs)

/-- Factor-only wrapper for wallclock timing (fresh-prime variant). -/
def recursiveFactorInt (core : ZPoly) : Array ZPoly :=
  (certifyAux core #[]).1

/-- Escalation ladder for one remainder at the PARENT's prime, re-lifting the
remainder's own base mod-p factors to the remainder's own floor. -/
partial def reliftLadderSamePrime
    (pd : PrimeChoiceData) (subFloorCap : Nat) (g : ZPoly)
    (baseFactors : List ZPoly)
    (qbound floorK k rungs : Nat) : Nat × Nat × Array (ZPoly × List ZPoly) :=
  letI := pd.bounds
  let kk := min k floorK
  let lifted := ZPoly.multifactorLiftQuadratic pd.p kk g baseFactors.toArray
  let pairs := lifted.toList.zip baseFactors
  let hiCap := if kk != floorK then min subFloorCap pairs.length else pairs.length
  let pieces := recombPairs g pairs (pd.p ^ kk) qbound hiCap #[]
  if pieces.size ≥ 2 then (kk, rungs + 1, pieces)
  else if kk == floorK then (kk, rungs + 1, #[(g, baseFactors)])
  else reliftLadderSamePrime pd subFloorCap g baseFactors qbound floorK
    (k * 2) (rungs + 1)

/-- Same-prime recursion: certify `g` against a fresh lift of its OWN base
mod-p factors (inherited from the parent's split) at the parent's prime, to
`g`'s own floor. No per-node prime walk or Berlekamp. -/
partial def certifySamePrimeAux
    (pd : PrimeChoiceData) (subFloorCap : Nat) (g : ZPoly)
    (baseFactors : List ZPoly)
    (recs : Array NodeRec) : Array ZPoly × Array NodeRec :=
  let deg := g.degree?.getD 0
  let r := baseFactors.length
  if deg ≤ 1 then
    (#[g], recs.push { deg, p := pd.p, r, floorK := 0, kStop := 0, rungs := 0,
                       outcome := "deg<=1" })
  else if r ≤ 1 then
    (#[g], recs.push { deg, p := pd.p, r, floorK := 0, kStop := 0, rungs := 0,
                       outcome := "modp-irreducible" })
  else
    let qbound := ZPoly.defaultFactorCoeffBound (ZPoly.toMonic g).monic
    let floorK := precisionForCoeffBound qbound pd.p
    let (kStop, rungs, pieces) :=
      reliftLadderSamePrime pd subFloorCap g baseFactors qbound floorK 1 0
    if pieces.size == 1 then
      (#[g], recs.push { deg, p := pd.p, r, floorK, kStop, rungs,
                         outcome := "floor-certified" })
    else
      let recs := recs.push { deg, p := pd.p, r, floorK, kStop, rungs,
                              outcome := "split" }
      pieces.foldl (init := (#[], recs)) fun st piece =>
        let (fs, rs) := certifySamePrimeAux pd subFloorCap piece.1 piece.2 st.2
        (st.1 ++ fs, rs)

/-- Same-prime recursion entry point. `subFloorCap` caps the subset size the
recombination scan tries at rungs BELOW the floor (the floor rung always runs
the full scan). Sub-floor rungs necessarily fail on every candidate the rung
cannot yet recover, and the failed tail costs one bounded division per
candidate, so the cap trades sub-floor discovery of multi-local-factor splits
(`cap >= 2`, e.g. the mignotte_swell quartics) against a failed tail that
grows like `C(r, cap)` per rung. -/
def certifySamePrime (core : ZPoly) (subFloorCap : Nat) :
    Array ZPoly × Array NodeRec :=
  match choosePrimeData? core with
  | none =>
      (#[core], #[{ deg := core.degree?.getD 0, p := 0, r := 0, floorK := 0,
                    kStop := 0, rungs := 0, outcome := "NO-PRIME" }])
  | some pd =>
      letI := pd.bounds
      certifySamePrimeAux pd subFloorCap core
        (pd.factorsModP.toList.map FpPoly.liftToZ) #[]

/-- Wallclock wrapper: same-prime, full scan at every rung. -/
def recursiveFactorSamePrime (core : ZPoly) : Array ZPoly :=
  (certifySamePrime core 1000000).1

/-- Wallclock wrapper: same-prime, singleton-only sub-floor rungs. -/
def recursiveFactorSamePrimeCap1 (core : ZPoly) : Array ZPoly :=
  (certifySamePrime core 1).1

/-- Wallclock wrapper: same-prime, sub-floor rungs capped at size-2 subsets. -/
def recursiveFactorSamePrimeCap2 (core : ZPoly) : Array ZPoly :=
  (certifySamePrime core 2).1

/-- Today's single-lift classical run on a monic squarefree `core`, at the
production precision for caller bound `B` (`exhaustiveLiftBound core B`). -/
def classicalFactorTodayWithB (core : ZPoly) (B : Nat) : Array ZPoly :=
  match ZPoly.toMonicPrimeData? core with
  | none => #[]
  | some pd =>
      let qbound := ZPoly.exhaustiveLiftBound core B
      let k := precisionForCoeffBound qbound pd.p
      let ld := henselLiftData core k pd
      recombInt core ld.liftedFactors.toList (pd.p ^ k) qbound

/-! ### Inputs -/

/-- `(x-1-s)(x-2-s)...(x-n-s)`: shifted fully-split family (distinct inputs). -/
def linearProductShift (n s : Nat) : ZPoly :=
  (List.range n).foldl
    (fun acc i => acc * DensePoly.ofCoeffs #[-(Int.ofNat (i + 1 + s)), 1]) (1 : ZPoly)

/-- Deterministic split family with roots scaled by `height + 1` (mirrors
`splitDegreeHeightInput` in `bench/HexBerlekampZassenhaus/Bench.lean`). -/
def splitDegreeHeight (degree height : Nat) : ZPoly :=
  let scale := Int.ofNat (height + 1)
  (Array.range degree).foldl
    (fun acc i => acc * DensePoly.ofCoeffs #[-(scale * Int.ofNat (i + 1)), 1])
    (1 : ZPoly)

/-- 15th cyclotomic polynomial: irreducible over `Z`, splits mod p. -/
def phi15 : ZPoly := DensePoly.ofCoeffs #[1, -1, 0, 1, -1, 1, 0, -1, 1]

/-- Swinnerton-Dyer `SD_3`: irreducible, splits into low degrees mod every p. -/
def advSD3 : ZPoly := DensePoly.ofCoeffs #[576, 0, -960, 0, 352, 0, -40, 0, 1]

/-- Swinnerton-Dyer `SD_4` (degree 16). -/
def advSD4 : ZPoly :=
  DensePoly.ofCoeffs
    #[46225, 0, -5596840, 0, 13950764, 0, -7453176, 0, 1513334, 0, -141912, 0,
      6476, 0, -136, 0, 1]

/-- `adv/mignotte_swell` fixture: `(x^4-100x+1)(x^4+100x+1)`, height-100
quartic factors inside a height-10000 degree-8 core. -/
def advMignotteSwell : ZPoly := DensePoly.ofCoeffs #[1, 0, -10000, 0, 2, 0, 0, 0, 1]

/-- `adv/high_multiplicity` fixture: `(x^2+1)^3 (x-3)^2` (non-squarefree). -/
def advHighMultiplicity : ZPoly :=
  DensePoly.ofCoeffs #[9, -6, 28, -18, 30, -18, 12, -6, 1]

/-- Taylor shift `g(x+s)` by Horner over polynomial arithmetic: distinct-input
families from a single adversarial fixture (defeats hoisting; preserves degree
and irreducibility over `Z`, though the selected prime and modular split may
differ per shift). -/
def shiftPoly (g : ZPoly) (s : Int) : ZPoly :=
  let xps : ZPoly := DensePoly.ofCoeffs #[s, 1]
  g.toArray.foldr (fun c acc => acc * xps + DensePoly.C c) (0 : ZPoly)

/-! ### Reporting -/

/-- Sorted multiset of factor degrees, for a quick correctness signature. -/
def degreeSignature (fs : Array ZPoly) : List Nat :=
  (fs.toList.map (fun g => g.degree?.getD 0)).mergeSort (· ≤ ·)

def sumBy (recs : Array NodeRec) (f : NodeRec → Nat) : Nat :=
  recs.foldl (fun a n => a + f n) 0

def NodeRec.line (n : NodeRec) : String :=
  s!"      deg={n.deg} p={n.p} r={n.r} floorK={n.floorK} kStop={n.kStop} rungs={n.rungs} {n.outcome}"

/-- Summarize one recursion variant's records against the core. -/
def variantSummary (label : String) (core : ZPoly)
    (result : Array ZPoly × Array NodeRec) : IO Unit := do
  let (factors, recs) := result
  let sumK := sumBy recs (·.kStop)
  let maxK := recs.foldl (fun a n => max a n.kStop) 0
  let rungs := sumBy recs (·.rungs)
  let bigNodes := recs.foldl (fun a n => a + if n.p != 0 && n.r > 1 then 1 else 0) 0
  let workRec := sumBy recs (fun n => n.deg * n.deg * n.kStop)
  let productOk := (Array.polyProduct factors).toArray == core.toArray
  IO.println s!"    {label}: sumK={sumK} maxK={maxK} work={workRec} nodes={recs.size} lifted_nodes={bigNodes} recomb_scans={rungs} factors={degreeSignature factors} product_ok={productOk}"
  for n in recs do
    if n.p != 0 || n.deg > 1 then IO.println n.line

/-- Accounting report for one input: `f` is the full caller input (sets today's
`B`), `core` its monic squarefree core (what the tier actually factors). -/
def reportCase (name : String) (f core : ZPoly) : IO Unit := do
  let degC := core.degree?.getD 0
  match ZPoly.toMonicPrimeData? core with
  | none => IO.println s!"{name}: NO PRIME SELECTED"
  | some pd =>
      let kToday :=
        precisionForCoeffBound
          (ZPoly.exhaustiveLiftBound core (ZPoly.defaultFactorCoeffBound f)) pd.p
      let kLocal :=
        precisionForCoeffBound
          (max (ZPoly.defaultFactorCoeffBound core)
            (ZPoly.defaultFactorCoeffBound (ZPoly.toMonic core).monic)) pd.p
      IO.println s!"{name} (deg {degC}, p {pd.p}): k_today={kToday} (work {degC * degC * kToday})  k_corelocal={kLocal} (work {degC * degC * kLocal})"
      variantSummary "fresh-prime    " core (certifyAux core #[])
      variantSummary "same-prime-full" core (certifySamePrime core 1000000)
      variantSummary "same-prime-cap1" core (certifySamePrime core 1)
      variantSummary "same-prime-cap2" core (certifySamePrime core 2)
  (← IO.getStdout).flush

/-- Checksum the actual factor coefficients so the optimizer cannot drop the
factorization (defeats CSE/dead-code elimination). -/
def factorChecksum (fs : Array ZPoly) : UInt64 :=
  fs.foldl (fun acc g =>
    g.toArray.foldl (fun a c => a * 1000003 + UInt64.ofNat c.natAbs) acc) 7

/-- Generic phase timer over a distinct-input family; `sink` forces evaluation. -/
def timePhase (label : String) (reps : Nat) (inputs : Array ZPoly)
    (act : ZPoly → UInt64) : IO Unit := do
  let out ← IO.getStdout
  let m := inputs.size
  let mut w : UInt64 := 0
  for i in [0:Nat.min m 4] do w := w + act inputs[i]!
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := w
  for i in [0:reps] do acc := acc + act (inputs[i % m]!)
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/call (reps={reps}, sink={acc})"
  out.flush

/-- Production classical tier on the core (`classicalCoreFactorsWithBound`:
`toMonicLiftData` + `scaledRecombinationSmart` with its own residue filters and
subset budget). Anchors the shared-scan baseline against real production
recombination; `none` (declined, budget exhausted) checksums as empty. -/
def classicalFactorProduction (core : ZPoly) (B : Nat) : Array ZPoly :=
  match ZPoly.toMonicPrimeData? core with
  | none => #[]
  | some pd => (classicalCoreFactorsWithBound core B pd).getD #[]

/-- Wallclock arms: production, shared-scan baseline, recursion variants. -/
def timeArms (reps : Nat) (inputs : Array ZPoly) (coreOf : ZPoly → ZPoly)
    (bOf : ZPoly → Nat) : IO Unit := do
  timePhase "production " reps inputs
    (fun f => factorChecksum (classicalFactorProduction (coreOf f) (bOf f)))
  timePhase "today      " reps inputs
    (fun f => factorChecksum (classicalFactorTodayWithB (coreOf f) (bOf f)))
  timePhase "fresh-prime" reps inputs
    (fun f => factorChecksum (recursiveFactorInt (coreOf f)))
  timePhase "same-prime " reps inputs
    (fun f => factorChecksum (recursiveFactorSamePrime (coreOf f)))
  timePhase "same-p-cap1" reps inputs
    (fun f => factorChecksum (recursiveFactorSamePrimeCap1 (coreOf f)))
  timePhase "same-p-cap2" reps inputs
    (fun f => factorChecksum (recursiveFactorSamePrimeCap2 (coreOf f)))

def main : IO Unit := do
  -- Focused profile mode: `RELIFT_PROFILE=today|recursive|sameprime|phases`
  -- runs only the split deg-24 family under the selected arm (for
  -- `perf record`), then exits.
  if let some arm ← IO.getEnv "RELIFT_PROFILE" then
    let inputs := (Array.range 8).map (linearProductShift 24)
    if arm == "recursive" then
      timePhase "profile recursive" 30 inputs
        (fun f => factorChecksum (recursiveFactorInt f))
    else if arm == "sameprime" then
      timePhase "profile same-prime" 30 inputs
        (fun f => factorChecksum (recursiveFactorSamePrime f))
    else if arm == "phases" then
      -- Per-phase breakdown of one recursive node level on the deg-24 split
      -- input: prime selection, the k=1 lift, and the k=1 recombination scan.
      timePhase "choosePrimeData?" 30 inputs (fun f =>
        match choosePrimeData? f with
        | none => 0
        | some pd => UInt64.ofNat pd.p + UInt64.ofNat pd.factorsModP.size)
      timePhase "lift k=1        " 30 inputs (fun f =>
        match choosePrimeData? f with
        | none => 0
        | some pd => factorChecksum (henselLiftData f 1 pd).liftedFactors)
      timePhase "recomb at k=1   " 30 inputs (fun f =>
        match choosePrimeData? f with
        | none => 0
        | some pd =>
            let ld := henselLiftData f 1 pd
            factorChecksum
              (recombInt f ld.liftedFactors.toList (pd.p ^ 1)
                (ZPoly.defaultFactorCoeffBound f)))
    else
      timePhase "profile today" 30 inputs
        (fun f => factorChecksum (classicalFactorTodayWithB f (ZPoly.defaultFactorCoeffBound f)))
    return
  IO.println "=== recursive per-remainder re-lift spike (#8625): lift-precision accounting ==="
  IO.println "    k_today: today's single lift at exhaustiveLiftBound core (mignotte f)"
  IO.println "    k_corelocal: the #8620 rewrite-1 core-local floor (reference)"
  IO.println "    work: degree-weighted lift model sum deg^2 * k"
  IO.println ""
  -- Split families (degree/height grid; the bzClassicalDegreeHeightComplexity axes).
  for (d, h) in [(3, 2), (4, 2), (4, 8), (5, 8), (6, 32), (12, 32)] do
    let g := splitDegreeHeight d h
    reportCase s!"split deg{d} height{h}" g g
  for d in [8, 12, 16, 20, 24] do
    let g := splitDegreeHeight d 0
    reportCase s!"split deg{d} height0" g g
  -- High-content / high-multiplicity adversarial fixtures.
  let hmCore := (normalizeForFactor advHighMultiplicity).squareFreeCore
  reportCase "adv/high_multiplicity (core of (x^2+1)^3(x-3)^2)" advHighMultiplicity hmCore
  reportCase "adv/mignotte_swell" advMignotteSwell advMignotteSwell
  -- High-degree irreducibles: the predicted loss cases.
  reportCase "cyclotomic phi15" phi15 phi15
  reportCase "SD3" advSD3 advSD3
  reportCase "SD4" advSD4 advSD4
  -- Small factor of a large irreducible core: the other predicted loss case.
  let sd3x := DensePoly.ofCoeffs #[-1, 1] * advSD3
  let sd4x := DensePoly.ofCoeffs #[-1, 1] * advSD4
  reportCase "(x-1)*SD3" sd3x sd3x
  reportCase "(x-1)*SD4" sd4x sd4x

  IO.println ""
  IO.println "=== wallclock (distinct-input families; today = single production-precision lift) ==="
  for n in [12, 16, 20, 24] do
    let inputs := (Array.range 8).map (linearProductShift n)
    IO.println s!"--- split deg{n} ---"
    timeArms 30 inputs id (fun f => ZPoly.defaultFactorCoeffBound f)
  IO.println "--- adv/mignotte_swell (shift family) ---"
  let swellFamily := (Array.range 8).map (fun s => shiftPoly advMignotteSwell (Int.ofNat s))
  timeArms 30 swellFamily id (fun f => ZPoly.defaultFactorCoeffBound f)
  IO.println "--- adv/high_multiplicity (shift family; today's B from the full input) ---"
  let hmFamily := (Array.range 8).map (fun s => shiftPoly advHighMultiplicity (Int.ofNat s))
  timeArms 30 hmFamily (fun f => (normalizeForFactor f).squareFreeCore)
    (fun f => ZPoly.defaultFactorCoeffBound f)
  IO.println "--- phi15 (shift family) ---"
  let phiFamily := (Array.range 8).map (fun s => shiftPoly phi15 (Int.ofNat s))
  timeArms 30 phiFamily id (fun f => ZPoly.defaultFactorCoeffBound f)
  IO.println "--- SD3 (shift family) ---"
  let sd3Family := (Array.range 4).map (fun s => shiftPoly advSD3 (Int.ofNat s))
  timeArms 10 sd3Family id (fun f => ZPoly.defaultFactorCoeffBound f)
  IO.println "--- SD4 (shift family) ---"
  let sd4Family := (Array.range 2).map (fun s => shiftPoly advSD4 (Int.ofNat s))
  timeArms 2 sd4Family id (fun f => ZPoly.defaultFactorCoeffBound f)
  IO.println "--- (x-1)*SD3 (shift family) ---"
  let sd3xFamily := (Array.range 4).map (fun s => shiftPoly sd3x (Int.ofNat s))
  timeArms 10 sd3xFamily id (fun f => ZPoly.defaultFactorCoeffBound f)
