/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import Hex.BenchOracle.Flint
import Lean.Data.Json

/-!
# Warm factorization service for the cross-system benchmark suite

A persistent process speaking the suite line protocol (identical to the verified
Isabelle comparator `scripts/oracle/bz-isabelle/Main.hs`):

* request (one line): `{"coeffs":[c0,c1,...]}` — integer coefficients, **ascending**
  degree order.
* reply (one line): `{"ok":true,"result":{"scalar":s,"factors":[{"coeffs":[...],
  "multiplicity":m},...]}}` on success, `{"ok":true,"result":null}` when the
  selected entry declines (counted as unsolved on the charts, deliberately not
  distinguished from a timeout), or `{"ok":false,"error":"..."}` on a malformed
  request.

The `--entry` flag selects which library entry answers each request:

* `factor` — the production cost-based hybrid (`Hex.ZPoly.factorize`); never declines.
* `factorLattice` — the van Hoeij CLD lattice tier (`Hex.factorLattice`).
* `factorTrace` — the direct classical tier plus its typed execution trace;
  a diagnostic response rather than the cross-system factorization protocol.
* `proposalTrace` — retained peeling and selected-column lattice diagnostics.
* `proposalProfile` — nanosecond phase timings for the proposal experiment;
  it also evaluates the wider columns after first success to test stability.
* `factorPhaseProfile` — nanosecond, per-phase attribution of the *production*
  cascade: normalization, the bounded good-prime walk, the Hensel lift, direct
  recombination, and whichever fallback tier answers. Each phase runs the
  production function it names, in production order, so the counters and the
  times come from one execution rather than from a second factorization.
* `primeCounterfactual` — for every good prime the bounded walk retained, the
  downstream lift and recombination cost of having stopped there.

This is a comparator driver, not a hex-internal benchmark harness: it emits raw
timings for the external orchestrator, keeping the one-harness rule intact.
-/

open Lean (Json JsonNumber)
open Hex
open Hex.BenchOracle.Flint (intsToJson)

namespace HexBench.FactorService

/-- Which library entry answers each request. -/
inductive Entry where
  | factor
  | factorLattice
  | factorTrace
  | proposalTrace
  | proposalProfile
  | factorPhaseProfile
  | primeCounterfactual
deriving Repr, DecidableEq

def Entry.ofString? : String → Option Entry
  | "factor" => some .factor
  | "factorLattice" => some .factorLattice
  | "factorTrace" => some .factorTrace
  | "proposalTrace" => some .proposalTrace
  | "proposalProfile" => some .proposalProfile
  | "factorPhaseProfile" => some .factorPhaseProfile
  | "primeCounterfactual" => some .primeCounterfactual
  | _ => none

/-- Entries answered by an `IO`-timed profiler rather than by `handleLine`. -/
def Entry.timed : Entry → Bool
  | .proposalProfile => true
  | .factorPhaseProfile => true
  | .primeCounterfactual => true
  | _ => false

/-- Dispatch to the selected entry. `none` means the entry declined; the
production `factor` never declines (it wraps its total `Factorization`). -/
def Entry.run : Entry → ZPoly → Option Factorization
  | .factor, f => some (Hex.ZPoly.factorize f)
  | .factorLattice, f => Hex.factorLattice f
  | .factorTrace, f => (Hex.factorClassicalTraced f).1
  | .proposalTrace, f =>
      (Hex.factorProposedTraced f).1.map fun proposal =>
        factorizationOfFactors f proposal.factors
  | .proposalProfile, _ => none
  | .factorPhaseProfile, _ => none
  | .primeCounterfactual, _ => none

/-- Parse a request line into its ascending coefficient list. -/
def parseCoeffs (line : String) : Except String (List Int) := do
  let j ← Json.parse line
  let cj ← j.getObjVal? "coeffs"
  let arr ← cj.getArr?
  arr.toList.mapM Json.getInt?

/-- Encode a total factorization as the protocol `result` object. -/
def factorizationToJson (φ : Factorization) : Json :=
  Json.mkObj
    [ ("scalar", Json.num (JsonNumber.fromInt φ.scalar)),
      ("factors",
        Json.arr (φ.factors.map fun (p, m) =>
          Json.mkObj
            [ ("coeffs", intsToJson p.toArray.toList),
              ("multiplicity", Json.num (JsonNumber.fromInt (Int.ofNat m))) ])) ]

/-- Encode the bounded classical tier's selected-prime diagnostics. -/
def factorTraceToJson (trace : DirectFactorTrace) : Json :=
  Json.mkObj
    [ ("method", Json.str trace.method.name),
      ("decline",
        trace.classicalDecline.map (Json.str ·.name) |>.getD Json.null),
      ("prime",
        Json.num (JsonNumber.fromInt (Int.ofNat trace.classical.prime))),
      ("primeProbes",
        Json.num (JsonNumber.fromInt (Int.ofNat trace.classical.primeProbes))),
      ("liftedFactorCount",
        Json.num
          (JsonNumber.fromInt (Int.ofNat trace.classical.liftedFactorCount))),
      ("henselLifts",
        Json.num (JsonNumber.fromInt (Int.ofNat trace.classical.henselLifts))),
      ("candidatesTried",
        Json.num
          (JsonNumber.fromInt (Int.ofNat trace.classical.candidatesTried))),
      ("completedLevels",
        Json.arr (trace.classical.completedLevels.map fun level =>
          Json.num (JsonNumber.fromInt (Int.ofNat level)))) ]

/-- Encode the retained peel and incremental coordinate-lattice diagnostics. -/
def proposalTraceToJson (trace : ProposalTrace) : Json :=
  Json.mkObj
    [ ("prime", Json.num (JsonNumber.fromInt (Int.ofNat trace.classical.prime))),
      ("primeProbes",
        Json.num (JsonNumber.fromInt (Int.ofNat trace.classical.primeProbes))),
      ("liftedFactorCount",
        Json.num
          (JsonNumber.fromInt (Int.ofNat trace.classical.liftedFactorCount))),
      ("henselLifts",
        Json.num (JsonNumber.fromInt (Int.ofNat trace.classical.henselLifts))),
      ("candidatesTried",
        Json.num
          (JsonNumber.fromInt (Int.ofNat trace.classical.candidatesTried))),
      ("unforcedLeaves",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.unforced.leaves))),
      ("unforcedDegreeSurvivors",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.unforced.degreeSurvivors))),
      ("unforcedTrailingSurvivors",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.unforced.trailingSurvivors))),
      ("unforcedConstructed",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.unforced.constructed))),
      ("unforcedRecordable",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.unforced.recordable))),
      ("unforcedExactDivisions",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.unforced.exactDivisions))),
      ("unforcedCompletedLevels",
        Json.arr (trace.classical.unforcedCompletedLevels.map fun level =>
          Json.num (JsonNumber.fromInt (Int.ofNat level)))),
      ("unforcedDecline",
        trace.classical.unforcedDecline.map (Json.str ·.name) |>.getD Json.null),
      ("peeledFactorDegrees",
        Json.arr (trace.classical.peeledFactorDegrees.map fun degree =>
          Json.num (JsonNumber.fromInt (Int.ofNat degree)))),
      ("peeledSupportSizes",
        Json.arr (trace.classical.peeledSupportSizes.map fun size =>
          Json.num (JsonNumber.fromInt (Int.ofNat size)))),
      ("peeledComplementSizes",
        Json.arr (trace.classical.peeledComplementSizes.map fun size =>
          Json.num (JsonNumber.fromInt (Int.ofNat size)))),
      ("residualLiftedFactorCount",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.residualLiftedFactorCount))),
      ("remainingSubsetBudget",
        Json.num
          (JsonNumber.fromInt
            (Int.ofNat trace.classical.remainingSubsetBudget))),
      ("lattices",
        Json.arr (trace.lattices.map fun lattice =>
          Json.mkObj
            [ ("residualDegree",
                Json.num
                  (JsonNumber.fromInt (Int.ofNat lattice.residualDegree))),
              ("liftedFactorCount",
                Json.num
                  (JsonNumber.fromInt (Int.ofNat lattice.liftedFactorCount))),
              ("coordinates",
                Json.arr (lattice.coordinates.map fun coordinate =>
                  Json.num (JsonNumber.fromInt (Int.ofNat coordinate)))),
              ("cutThresholds",
                Json.arr (lattice.cutThresholds.map fun threshold =>
                  Json.num (JsonNumber.fromInt (Int.ofNat threshold)))),
              ("dimension",
                Json.num (JsonNumber.fromInt (Int.ofNat lattice.dimension))),
              ("henselPrecision",
                Json.num
                  (JsonNumber.fromInt (Int.ofNat lattice.henselPrecision))),
              ("reducer", Json.str "certified-selector"),
              ("maxEntryBits",
                Json.num (JsonNumber.fromInt (Int.ofNat lattice.maxEntryBits))),
              ("reducedRows",
                Json.num
                  (JsonNumber.fromInt (Int.ofNat lattice.reducedRows))),
              ("projectedRows",
                Json.num
                  (JsonNumber.fromInt (Int.ofNat lattice.projectedRows))),
              ("indicatorCount",
                Json.num
                  (JsonNumber.fromInt (Int.ofNat lattice.indicatorCount))),
              ("supportSizes",
                Json.arr (lattice.supportSizes.map fun size =>
                  Json.num (JsonNumber.fromInt (Int.ofNat size)))),
              ("candidateDegrees",
                Json.arr (lattice.candidateDegrees.map fun degree =>
                  Json.num (JsonNumber.fromInt (Int.ofNat degree)))),
              ("accepted", Json.bool lattice.accepted) ])),
      ("pieceDegrees",
        Json.arr (trace.pieceDegrees.map fun degree =>
          Json.num (JsonNumber.fromInt (Int.ofNat degree)))),
      ("factorDegrees",
        Json.arr (trace.factorDegrees.map fun degree =>
          Json.num (JsonNumber.fromInt (Int.ofNat degree)))) ]

private def natJson (n : Nat) : Json :=
  Json.num (JsonNumber.fromInt (Int.ofNat n))

private def nanosJson (n : Nat) : Json :=
  natJson n

private def natArrayJson (values : Array Nat) : Json :=
  Json.arr (values.map natJson)

private def externalReducerJson : IO Json := do
  let active ← lll.externalReducerActive
  let diagnostics ← Internal.ExternalReducer.diagnostics
  return Json.mkObj
    [ ("active", Json.bool active),
      ("absent", natJson diagnostics.absent),
      ("reductionError", natJson diagnostics.reductionError),
      ("rejected", natJson diagnostics.rejected),
      ("accepted", natJson diagnostics.accepted) ]

private structure ProfiledLattice where
  candidate : Option (Array ZPoly)
  supportSizes : Array Nat
  profile : Json

/-- Force a pure stage before taking the following timestamp. -/
private def observeNat (sink : IO.Ref Nat) (value : Nat) : IO Unit :=
  sink.set value

/-- Time the construction, exact native reduction, cut, partition extraction,
and exact reconstruction stages of one leading-column proposal lattice. -/
private def profileLattice
    (sink : IO.Ref Nat) (f : ZPoly) (d : LiftData)
    (prepared : BhksLeadingLogDerivativeData) (width : Nat) :
    IO ProfiledLattice := do
  let prepareStart ← IO.monoNanosNow
  let L := prepared.coordinateLattice width
  let maxEntryBits := coordinateLatticeMaxEntryBits L
  observeNat sink (maxEntryBits + L.cldRows.size +
    L.cldRows.foldl (fun sum row => sum + row.size) 0)
  let prepareStop ← IO.monoNanosNow
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let reductionStart ← IO.monoNanosNow
    let reducedRows :=
      lll.shortVectors L.basis (3 / 4) (by grind)
        lll_delta_upper hrows
    observeNat sink <| reducedRows.foldl
      (fun sum row => row.toArray.foldl
        (fun sum entry => sum + entry.natAbs % 65521) sum) 0
    let reductionStop ← IO.monoNanosNow
    let cutStart ← IO.monoNanosNow
    let reducedBasis :=
      bhksRowsArrayToMatrix (L.factorCount + L.coeffWidth) reducedRows
    let projected : BhksProjectedRows :=
      { factorCount := L.factorCount
        coeffWidth := L.coeffWidth
        cutRadiusSq4 := bhksCutRadiusSq4 L
        reducedRowCount := reducedRows.size
        projectedRows := bhksCutProjectReducedRows L reducedBasis }
    observeNat sink <| projected.projectedRows.foldl
      (fun sum row => row.foldl (fun sum entry => sum + entry.natAbs) sum) 0
    let cutStop ← IO.monoNanosNow
    let partitionStart ← IO.monoNanosNow
    let indicators := bhksEquivalenceClassIndicators projected
    let supportSizes := indicatorSupportSizes indicators
    let degenerate := bhksDegenerateIndicatorPartition projected indicators
    observeNat sink (supportSizes.foldl (· + ·) 0 + indicators.size)
    let partitionStop ← IO.monoNanosNow
    let reconstructionStart ← IO.monoNanosNow
    let candidate :=
      if degenerate then none
      else
        match bhksIndicatorCandidates? f d indicators with
        | some pieces =>
            if Array.polyProduct pieces = f then some pieces else none
        | none => none
    let candidateDegrees :=
      candidate.map (fun pieces => pieces.map (·.degree?.getD 0)) |>.getD #[]
    observeNat sink (candidateDegrees.foldl (· + ·) 0)
    let reconstructionStop ← IO.monoNanosNow
    return {
      candidate := candidate
      supportSizes := supportSizes
      profile :=
          Json.mkObj
            [ ("width", natJson width),
              ("coordinates", natArrayJson prepared.coordinates),
              ("cutThresholds", natArrayJson L.cutThresholds),
              ("dimension", natJson (L.factorCount + L.coeffWidth)),
              ("maxEntryBits", natJson maxEntryBits),
              ("reducer", Json.str "certified-selector"),
              ("reducedRows", natJson reducedRows.size),
              ("projectedRows", natJson projected.projectedRows.size),
              ("supportSizes", natArrayJson supportSizes),
              ("candidateDegrees", natArrayJson candidateDegrees),
              ("accepted", Json.bool candidate.isSome),
            ("timingNs", Json.mkObj
                [ ("construction", nanosJson (prepareStop - prepareStart)),
                  ("reduction", nanosJson (reductionStop - reductionStart)),
                  ("cut", nanosJson (cutStop - cutStart)),
                  ("partition", nanosJson (partitionStop - partitionStart)),
                  ("reconstruction",
                    nanosJson (reconstructionStop - reconstructionStart)) ]) ] }
  else
    return {
      candidate := none
      supportSizes := #[]
      profile :=
          Json.mkObj
            [ ("width", natJson width),
              ("dimension", natJson (L.factorCount + L.coeffWidth)),
              ("accepted", Json.bool false),
              ("timingNs", Json.mkObj
                [("construction", nanosJson (prepareStop - prepareStart))]) ] }

/-- Profile every deterministic width, even after the production schedule's
first success, so support-partition stability is directly observable. -/
private def profileLattices (sink : IO.Ref Nat) (f : ZPoly) (d : LiftData)
    (prepared : BhksLeadingLogDerivativeData) :
    List Nat → Option (Array ZPoly) → Array (Array Nat) → Array Json →
      IO (Option (Array ZPoly) × Array (Array Nat) × Array Json)
  | [], first, supports, profiles => pure (first, supports, profiles)
  | width :: widths, first, supports, profiles => do
      let result ← profileLattice sink f d prepared width
      let first := match first with
        | some pieces => some pieces
        | none => result.candidate
      profileLattices sink f d prepared widths first
        (supports.push result.supportSizes) (profiles.push result.profile)

/-- Time one proved classical replay call and retain its ordinary search trace. -/
private def profileReplay (sink : IO.Ref Nat) (piece : ZPoly) :
    IO (Option (Array ZPoly) × Json) := do
  let start ← IO.monoNanosNow
  let run := runClassical piece
  let factorDegrees :=
    run.factors.map (fun factors => factors.map (·.degree?.getD 0)) |>.getD #[]
  observeNat sink (run.trace.classical.candidatesTried +
    factorDegrees.foldl (· + ·) 0)
  let stop ← IO.monoNanosNow
  return (run.factors,
      Json.mkObj
        [ ("pieceDegree", natJson (piece.degree?.getD 0)),
          ("factorDegrees", natArrayJson factorDegrees),
          ("liftedFactorCount", natJson run.trace.classical.liftedFactorCount),
          ("candidatesTried", natJson run.trace.classical.candidatesTried),
          ("completedLevels",
            natArrayJson run.trace.classical.completedLevels),
          ("timingNs", nanosJson (stop - start)) ])

private def profileReplayList (sink : IO.Ref Nat) : List ZPoly → Array Json →
    IO (Option (Array ZPoly) × Array Json)
  | [], profiles => pure (some #[], profiles)
  | piece :: pieces, profiles => do
      let (pieceFactors, profile) ← profileReplay sink piece
      let (remaining, profiles) ←
        profileReplayList sink pieces (profiles.push profile)
      return (match pieceFactors, remaining with
          | some left, some right => some (left ++ right)
          | _, _ => none,
        profiles)

/-- Detailed phase profile of the general proposal-and-replay composition. -/
private def proposalProfile (f : ZPoly) : IO Json := do
  Internal.ExternalReducer.resetDiagnostics
  let sink ← IO.mkRef 0
  let totalStart ← IO.monoNanosNow
  let normalizationStart ← IO.monoNanosNow
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  observeNat sink (core.poly.degree?.getD 0 + (core.poly.coeff 0).natAbs)
  let normalizationStop ← IO.monoNanosNow
  let planningStart ← IO.monoNanosNow
  let modular := directPrimePlan? core
  observeNat sink <| modular.map
    (fun plan => plan.data.factorsModP.size + plan.probes.size + plan.prime) |>.getD 0
  let planningStop ← IO.monoNanosNow
  match modular with
  | none =>
      let externalReducer ← externalReducerJson
      return Json.mkObj
        [ ("accepted", Json.bool false),
          ("reason", Json.str "noGoodPrime"),
          ("externalReducer", externalReducer),
          ("timingNs", Json.mkObj
            [ ("normalization", nanosJson (normalizationStop - normalizationStart)),
              ("primePlan", nanosJson (planningStop - planningStart)) ]) ]
  | some modular =>
      let productionEligible := decide
        (proposalEligible core.poly modular.data.factorsModP.size ∧ core.poly = f)
      let henselStart ← IO.monoNanosNow
      let liftPlan := directLiftPlan core modular
      let lifted := (directLiftedBasis core modular liftPlan).data
      let liftedCount := lifted.liftedFactors.size
      observeNat sink (liftedCount + lifted.k +
        lifted.liftedFactors.foldl
          (fun sum factor => sum + factor.degree?.getD 0) 0)
      let henselStop ← IO.monoNanosNow
      let peelStart ← IO.monoNanosNow
      let initialStats : ClassicalStats :=
        { prime := modular.prime
          primeProbes := modular.probes.size
          liftedFactorCount := liftedCount
          henselLifts := 1 }
      let peeled := peelDirect (DensePoly.leadingCoeff core.poly)
        core.poly lifted 3 2 proposalSubsetBudget initialStats
      observeNat sink (peeled.stats.candidatesTried + peeled.support.length +
        peeled.residual.degree?.getD 0)
      let peelStop ← IO.monoNanosNow
      let residualFactors :=
        (peeled.support.map (directLiftedFactor lifted)).toArray
      let residualLift : LiftData :=
        { p := lifted.p
          p_pos := lifted.p_pos
          k := lifted.k
          liftedFactors := residualFactors }
      let cldStart ← IO.monoNanosNow
      let maxWidth := coordinateLatticeWidths.foldl max 0
      let prepared := bhksLeadingLogDerivativeData peeled.residual
        residualLift.p residualLift.k residualLift.liftedFactors maxWidth
      observeNat sink (prepared.coordinates.size + prepared.cldRows.size +
        prepared.cldRows.foldl (fun sum row => sum + row.size) 0)
      let cldStop ← IO.monoNanosNow
      let latticeStart ← IO.monoNanosNow
      let (residualPieces, supportAttempts, latticeProfiles) ←
        if peeled.factors.isEmpty then
          pure (none, #[], #[])
        else
          profileLattices sink peeled.residual residualLift prepared
            coordinateLatticeWidths none #[] #[]
      let latticeStop ← IO.monoNanosNow
      let residualPieces := match residualPieces with
        | some pieces => some pieces
        | none =>
            if peeled.factors.isEmpty then none else some #[peeled.residual]
      let pieces := residualPieces.map (peeled.factors ++ ·)
      let exactStart ← IO.monoNanosNow
      let exactPieces := pieces.filter (Array.polyProduct · = core.poly)
      observeNat sink <| exactPieces.map
        (fun pieces => pieces.foldl
          (fun sum piece => sum + piece.degree?.getD 0) 0) |>.getD 0
      let exactStop ← IO.monoNanosNow
      let replayStart ← IO.monoNanosNow
      let (factors, replayProfiles) ←
        match exactPieces with
        | some pieces => profileReplayList sink pieces.toList #[]
        | none => pure (none, #[])
      let replayStop ← IO.monoNanosNow
      let acceptanceStart ← IO.monoNanosNow
      let accepted :=
        factors.any fun factors =>
          Factorization.product (factorizationOfFactors f factors) = f
      observeNat sink (if accepted then 1 else 0)
      let acceptanceStop ← IO.monoNanosNow
      let totalStop ← IO.monoNanosNow
      let externalReducer ← externalReducerJson
      let stable :=
        match supportAttempts.toList with
        | [] => true
        | support :: supports => supports.all (· = support)
      return Json.mkObj
        [ ("accepted", Json.bool accepted),
          ("productionEligible", Json.bool productionEligible),
          ("prime", natJson modular.prime),
          ("primeProbes", natJson modular.probes.size),
          ("liftedFactorCount", natJson liftedCount),
          ("henselPrecision", natJson lifted.k),
          ("peel", proposalTraceToJson { classical := peeled.stats }),
          ("residualDegree", natJson (peeled.residual.degree?.getD 0)),
          ("lattices", Json.arr latticeProfiles),
          ("partitionStable", Json.bool stable),
          ("externalReducer", externalReducer),
          ("replay", Json.arr replayProfiles),
          ("timingNs", Json.mkObj
            [ ("normalization", nanosJson (normalizationStop - normalizationStart)),
              ("primePlan", nanosJson (planningStop - planningStart)),
              ("hensel", nanosJson (henselStop - henselStart)),
              ("peel", nanosJson (peelStop - peelStart)),
              ("cldPreparation", nanosJson (cldStop - cldStart)),
              ("latticeSchedule", nanosJson (latticeStop - latticeStart)),
              ("pieceProduct", nanosJson (exactStop - exactStart)),
              ("replay", nanosJson (replayStop - replayStart)),
              ("acceptance", nanosJson (acceptanceStop - acceptanceStart)),
              ("profileTotal", nanosJson (totalStop - totalStart)) ]) ]

/-! ## Phase-attributed profile of the production cascade

The entries below decompose `Hex.ZPoly.factorize` into the production functions
it calls, in production order, and time each one.  Nothing here is reachable
from the production cascade, so an ordinary factorization pays nothing for it.

The one place the diagnostic does not call a production function verbatim is
recombination: `countedSearch` below is a leaf-for-leaf mirror of `searchDirect`
that threads `DirectCandidateStats` instead of a bare leaf count, so the stage
breakdown the production forced search does not retain (cheap-filter
rejections, candidate products materialized, exact divisions attempted) is
recorded from the execution actually being timed.  Every leaf predicate is the
shared one, and the `factorTrace` entry on the same input is the cross-check
that the mirror visits the same candidates and returns the same factors.
-/

/-- One time-and-allocation observation point.  Lean's heartbeat counter is the
number of small allocations performed on this thread, so its delta across a
phase is that phase's small-allocation count. -/
private structure Mark where
  /-- Monotonic nanoseconds. -/
  nanos : Nat
  /-- Small allocations performed on this thread so far. -/
  allocs : Nat

private def mark : IO Mark := do
  let allocs ← IO.getNumHeartbeats
  let nanos ← IO.monoNanosNow
  return { nanos, allocs }

private def spanJson (start stop : Mark) : Json :=
  Json.mkObj
    [ ("nanos", natJson (stop.nanos - start.nanos)),
      ("smallAllocs", natJson (stop.allocs - start.allocs)) ]

private def phaseEntry (name : String) (start stop : Mark) : String × Json :=
  (name, spanJson start stop)

private def candidateStatsJson (stats : DirectCandidateStats) : Json :=
  Json.mkObj
    [ ("nodes", natJson stats.leaves),
      ("degreeSurvivors", natJson stats.degreeSurvivors),
      ("trailingSurvivors", natJson stats.trailingSurvivors),
      ("cheapFilterRejections",
        natJson (stats.leaves - stats.trailingSurvivors)),
      ("productsMaterialized", natJson stats.constructed),
      ("recordable", natJson stats.recordable),
      ("exactDivisionsAttempted", natJson stats.exactDivisions) ]

/-- Counted mirror of `scanDirectCombinations`: the same head-forced traversal
order and the same leaf predicates, carrying the `DirectCandidateStats` stage
counters that `scanDirectSubsets` already records for the unforced sweep. -/
private def countedScanCombinations
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectSubsetLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      let selected := head :: selectedRev.reverse
      let remaining := rejectedRev.reverse ++ xs
      let visited : DirectCandidateStats := { leaves := 1 }
      if directDegreePrefilter coreLc target selectedDegree then
        let degreePassed := { visited with degreeSurvivors := 1 }
        if directTrailingPrefilter coreLc target (liftModulus basis) selectedTrail then
          let filtered := { degreePassed with trailingSurvivors := 1 }
          let candidate := directCandidate coreLc (liftModulus basis)
            (directSelectedFactors basis selected)
          let constructed := { filtered with constructed := 1 }
          if shouldRecordPolynomialFactor candidate then
            let divided :=
              { constructed with recordable := 1, exactDivisions := 1 }
            match exactQuotient? target candidate with
            | some quotient =>
                .found { selected, remaining, candidate, quotient } divided
            | none => .exhausted divided
          else
            .exhausted constructed
        else
          .exhausted degreePassed
      else
        .exhausted visited
  | [], _ + 1, _, _, _, _ => .exhausted {}
  | x :: xs, choose + 1, selectedRev, rejectedRev,
      selectedDegree, selectedTrail =>
      let factor := directLiftedFactor basis x
      let included :=
        countedScanCombinations coreLc target basis head xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + factor.degree?.getD 0)
          (selectedTrail * factor.coeff 0 % (liftModulus basis : Int))
      match included with
      | .found split stats => .found split stats
      | .exhausted leftStats =>
          match countedScanCombinations coreLc target basis head xs (choose + 1)
              selectedRev (x :: rejectedRev) selectedDegree selectedTrail with
          | .found split rightStats => .found split (leftStats.add rightStats)
          | .exhausted rightStats => .exhausted (leftStats.add rightStats)

/-- Counted mirror of `DirectHeadResult`. -/
private inductive CountedHeadResult (basis : LiftData) where
  | found (split : DirectSplit basis) (budget : Nat)
      (stats : DirectCandidateStats) (completed : Array Nat)
  | declined (reason : DeclineReason) (budget : Nat)
      (stats : DirectCandidateStats) (completed : Array Nat)

/-- Counted mirror of `findDirectHead`. -/
private def countedFindHead
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (head : DirectLiftedIndex basis) (tail : List (DirectLiftedIndex basis)) :
    (levels : List Nat) → (budget : Nat) → (stats : DirectCandidateStats) →
      (completed : Array Nat) → CountedHeadResult basis
  | [], budget, stats, completed =>
      .declined .invalidCandidate budget stats completed
  | level :: levels, budget, stats, completed =>
      let levelCost := Nat.choose tail.length level
      if levelCost > budget then
        .declined .subsetBudget budget stats completed
      else
        let factor := directLiftedFactor basis head
        match countedScanCombinations coreLc target basis head tail level [] []
            (factor.degree?.getD 0)
            (factor.coeff 0 % (liftModulus basis : Int)) with
        | .found split levelStats =>
            .found split (budget - levelStats.leaves) (stats.add levelStats)
              completed
        | .exhausted levelStats =>
            countedFindHead coreLc target basis head tail levels
              (budget - levelStats.leaves) (stats.add levelStats)
              (completed.push level)

/-- Outcome of the counted recombination mirror. -/
private structure CountedSearch where
  /-- The recovered factors, when the search completed. -/
  factors : Option (List ZPoly)
  /-- Why the bounded search stopped, when it did. -/
  decline : Option DeclineReason
  /-- Stage counters accumulated over every visited leaf. -/
  stats : DirectCandidateStats
  /-- Subset cardinalities exhausted completely, in execution order. -/
  completed : Array Nat
  /-- Successful exact divisors committed by the search. -/
  divisors : Nat

/-- Counted mirror of `searchDirectAux`. -/
private def countedSearchAux (coreLc : Int) (basis : LiftData) :
    Nat → ZPoly → List (DirectLiftedIndex basis) → Nat →
      DirectCandidateStats → Array Nat → CountedSearch
  | 0, _, _, _, stats, completed =>
      { factors := none, decline := some .liftFailure, stats, completed,
        divisors := 0 }
  | fuel + 1, target, localFactors, budget, stats, completed =>
      if target = 1 then
        { factors := some [], decline := none, stats, completed, divisors := 0 }
      else
        match localFactors with
        | [] =>
            { factors := none, decline := some .liftFailure, stats, completed,
              divisors := 0 }
        | head :: tail =>
            match countedFindHead coreLc target basis head tail
                (List.range (tail.length + 1)) budget {} #[] with
            | .declined reason budget' levelStats levelCompleted =>
                let _ := budget'
                { factors := none, decline := some reason,
                  stats := stats.add levelStats,
                  completed := completed ++ levelCompleted, divisors := 0 }
            | .found split budget' levelStats levelCompleted =>
                let rest := countedSearchAux coreLc basis fuel split.quotient
                  split.remaining budget' (stats.add levelStats)
                  (completed ++ levelCompleted)
                { rest with
                  factors := rest.factors.map (split.candidate :: ·)
                  divisors := rest.divisors + 1 }

/-- Counted mirror of `searchDirect`. -/
private def countedSearch (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (budget : Nat := defaultSubsetBudget) : CountedSearch :=
  countedSearchAux coreLc basis (basis.liftedFactors.size + 1) target
    (List.finRange basis.liftedFactors.size) budget {} #[]

/-- Retained good-prime candidate, its modular factor-degree pattern, and
whether the bounded walk selected it. -/
private def probeJson {core : SquareFreeInput} (coeffBound selectedPrime : Nat)
    (probe : DirectPrimeProbe core) : Json :=
  Json.mkObj
    [ ("prime", natJson probe.data.p),
      ("modularFactorCount", natJson probe.data.factorsModP.size),
      ("factorDegrees", natArrayJson probe.factorDegrees),
      ("reachableProperDegrees", natJson (directReachableProperCount probe)),
      ("forcedSubsetCost",
        natJson (directSubsetCost probe.data.factorsModP.size)),
      ("henselPrecision",
        natJson (precisionForCoeffBound coeffBound probe.data.p)),
      ("selected", Json.bool (probe.data.p == selectedPrime)) ]

/-- Bit length of a natural number, as a proxy for word versus bignum work. -/
private def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- Widest coefficient of a lifted factor, in bits. -/
private def maxCoeffBits (factors : Array ZPoly) : Nat :=
  factors.foldl (fun best g =>
    g.toArray.foldl (fun best c => max best (bitLength c.natAbs)) best) 0

/-- Modular sub-phase attribution at one candidate prime.

Unlike the cascade phases, this is a *repeat* of the modular factorization at
the already-selected prime: the production planner calls `probePrimeData?`,
which does not expose its internal stages.  The record labels it as such.  The
production route uses equal-degree splitting from the fixed-space kernel, so
there is no distinct-degree stage to attribute. -/
private def modularSubPhases (sink : IO.Ref Nat) (core : ZPoly)
    (c : SmallPrimeCandidate) : IO Json :=
  letI := c.bounds
  letI : ZMod64.PrimeModulus c.p := ZMod64.primeModulusOfPrime c.prime
  do
  let m0 ← mark
  let fModP := ZPoly.modP c.p core
  observeNat sink fModP.size
  let m1 ← mark
  let good := isGoodPrime core c.p
  observeNat sink (if good then 1 else 0)
  let m2 ← mark
  if hzero : fModP.isZero = false then
    let monic := monicModularImage fModP
    let hmonic := monicModularImage_monic c.prime fModP hzero
    let m3 ← mark
    let fixed := Berlekamp.fixedSpaceMatrix monic hmonic
    observeNat sink (Berlekamp.basisSize monic)
    let m4 ← mark
    let kernel := Matrix.nullspace fixed
    observeNat sink kernel.size
    let m5 ← mark
    let factors := (Berlekamp.berlekampFactor monic hmonic).factors
    observeNat sink factors.length
    let m6 ← mark
    -- `berlekampFactor` recomputes the fixed-space kernel internally, so the
    -- equal-degree splitting cost is what remains once the separately measured
    -- matrix construction and row reduction are removed from its total.
    let matrixNanos := m4.nanos - m3.nanos
    let reduceNanos := m5.nanos - m4.nanos
    let factorNanos := m6.nanos - m5.nanos
    return Json.mkObj
      [ ("measurement", Json.str "repeat-at-selected-prime"),
        ("prime", natJson c.p),
        ("modularDegree", natJson (fModP.degree?.getD 0)),
        ("kernelDimension", natJson kernel.size),
        ("distinctDegree", Json.str "not-applicable"),
        ("modularImage", spanJson m0 m1),
        ("goodPrimeTest", spanJson m1 m2),
        ("berlekampMatrix", spanJson m3 m4),
        ("rowReduction", spanJson m4 m5),
        ("berlekampFactorTotal", spanJson m5 m6),
        ("splittingNanos", natJson (factorNanos - matrixNanos - reduceNanos)) ]
  else
    return Json.mkObj
      [ ("measurement", Json.str "repeat-at-selected-prime"),
        ("prime", natJson c.p),
        ("modularImage", spanJson m0 m1),
        ("goodPrimeTest", spanJson m1 m2),
        ("zeroModularImage", Json.bool true) ]

/-- Assemble the answer and close out the profile.

`excluded` accumulates the cost of measurements the production cascade would
not have performed (currently only the modular sub-phase repeat), so the
reported total is the cost of the cascade itself. -/
private def finishPhaseProfile (f : ZPoly) (sink : IO.Ref Nat)
    (excluded : IO.Ref (Nat × Nat)) (m0 : Mark)
    (method : String) (phases extras : Array (String × Json))
    (factors : Array ZPoly) : IO Json := do
  let assemblyStart ← mark
  let φ := factorizationOfFactors f factors
  let reconstructs := Factorization.product φ = f
  observeNat sink (if reconstructs then 1 else 0)
  let assemblyStop ← mark
  let phases := phases.push (phaseEntry "assembly" assemblyStart assemblyStop)
  let total ← mark
  let (skipNanos, skipAllocs) ← excluded.get
  let phases := phases.push ("total", Json.mkObj
    [ ("nanos", natJson (total.nanos - m0.nanos - skipNanos)),
      ("smallAllocs", natJson (total.allocs - m0.allocs - skipAllocs)) ])
  let phases := phases.push ("diagnosticOverhead", Json.mkObj
    [ ("nanos", natJson skipNanos), ("smallAllocs", natJson skipAllocs) ])
  return Json.mkObj <|
    [ ("method", Json.str method),
      ("degree", natJson (f.degree?.getD 0)),
      ("reconstructs", Json.bool reconstructs),
      ("factorDegrees",
        natArrayJson (φ.factors.map fun entry => entry.1.degree?.getD 0)),
      ("multiplicities", natArrayJson (φ.factors.map fun entry => entry.2)),
      ("phases", Json.mkObj phases.toList) ] ++ extras.toList

/-- Phase-attributed profile of one production factorization. -/
private def factorPhaseProfile (f : ZPoly) : IO Json := do
  let sink ← IO.mkRef 0
  let excluded ← IO.mkRef (0, 0)
  let m0 ← mark
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  observeNat sink (core.poly.degree?.getD 0 + (core.poly.coeff 0).natAbs)
  let m1 ← mark
  let phases := #[phaseEntry "normalization" m0 m1]
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    return ← finishPhaseProfile f sink excluded m0 "constant" phases #[]
      (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  let quadratic := quadraticIntegerRootFactors? normalized.squareFreeCore
  observeNat sink (quadratic.map (·.size) |>.getD 0)
  let m2 ← mark
  let phases := phases.push (phaseEntry "quadratic" m1 m2)
  match quadratic with
  | some coreFactors =>
      return ← finishPhaseProfile f sink excluded m0 "quadratic" phases #[]
        (reassemblePolynomialFactors normalized coreFactors)
  | none => pure ()
  let plan := directPrimePlan? core
  observeNat sink <| plan.map
    (fun p => p.data.factorsModP.size + p.probes.size + p.prime) |>.getD 0
  let m3 ← mark
  let phases := phases.push (phaseEntry "primeWalk" m2 m3)
  match plan with
  | none =>
      let trialStart ← mark
      let factors := factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
      observeNat sink factors.size
      let trialStop ← mark
      let phases := phases.push (phaseEntry "trial" trialStart trialStop)
      return ← finishPhaseProfile f sink excluded m0 "trial" phases
        #[("primeWalk", Json.mkObj [("goodPrimeFound", Json.bool false)])] factors
  | some modular =>
      let coreBound := ZPoly.defaultFactorCoeffBound core.poly
      let walkJson := Json.mkObj
        [ ("goodPrimeFound", Json.bool true),
          ("selectedPrime", natJson modular.prime),
          ("retainedGoodPrimes", natJson modular.probes.size),
          ("coeffBound", natJson coreBound),
          ("coeffBoundBits", natJson (bitLength coreBound)),
          ("candidates",
            Json.arr (modular.probes.map (probeJson coreBound modular.prime))) ]
      let modularStart ← mark
      let modularJson ← modularSubPhases sink core.poly modular.selected.candidate
      let modularStop ← mark
      excluded.modify fun (n, a) =>
        (n + (modularStop.nanos - modularStart.nanos),
          a + (modularStop.allocs - modularStart.allocs))
      let extras := #[("primeWalk", walkJson), ("modular", modularJson)]
      -- `routeClassical` yields eligible normalized large-support inputs to
      -- proposal replay *before* running the classical engine.
      if heligible : proposalEligible core.poly modular.data.factorsModP.size ∧
          core.poly = f then
        let proposalStart ← mark
        let proposal := proposeFactorization f heligible.2 modular
        observeNat sink (proposal.1.map (·.factors.size) |>.getD 0)
        let proposalStop ← mark
        let phases := phases.push (phaseEntry "proposal" proposalStart proposalStop)
        match proposal.1 with
        | some result =>
            return ← finishPhaseProfile f sink excluded m0 "replay" phases extras result.factors
        | none =>
            let latticeStart ← mark
            let lattice := factorLatticeFactorsWithPlan normalized
              (latticePrecisionCap f) modular
            observeNat sink (lattice.map (·.size) |>.getD 0)
            let latticeStop ← mark
            let phases := phases.push (phaseEntry "lattice" latticeStart latticeStop)
            match lattice with
            | some factors =>
                if Factorization.product (factorizationOfFactors f factors) = f then
                  return ← finishPhaseProfile f sink excluded m0 "lattice" phases extras factors
                else
                  return ← runTrialTail f sink excluded m0 phases extras
            | none => return ← runTrialTail f sink excluded m0 phases extras
      else
        let liftStart ← mark
        let liftPlan := directLiftPlan core modular
        let basis := (directLiftedBasis core modular liftPlan).data
        observeNat sink (basis.k + basis.liftedFactors.size)
        let liftStop ← mark
        let phases := phases.push (phaseEntry "henselLift" liftStart liftStop)
        let henselJson := Json.mkObj
          [ ("prime", natJson basis.p),
            ("precision", natJson basis.k),
            ("modulusBits", natJson (bitLength (basis.p ^ basis.k))),
            ("liftedFactorCount", natJson basis.liftedFactors.size),
            ("liftedFactorDegrees",
              natArrayJson (basis.liftedFactors.map (·.degree?.getD 0))),
            ("liftedMaxCoeffBits", natJson (maxCoeffBits basis.liftedFactors)),
            -- `multifactorLiftQuadraticList` recurses on a balanced split, so
            -- the product tree is binary with one `henselLiftFactors` call per
            -- internal node; the split point itself is degree-dependent.
            ("treeShape", Json.str "balanced-split binary product tree"),
            ("treeLeaves", natJson basis.liftedFactors.size),
            ("treeInternalLifts", natJson (basis.liftedFactors.size - 1)) ]
        let searchStart ← mark
        let search := countedSearch (DensePoly.leadingCoeff core.poly) core.poly basis
        observeNat sink (search.stats.leaves +
          (search.factors.map (·.length) |>.getD 0))
        let searchStop ← mark
        let phases := phases.push (phaseEntry "recombination" searchStart searchStop)
        let searchJson := Json.mkObj
          [ ("stages", candidateStatsJson search.stats),
            ("successfulDivisors", natJson search.divisors),
            ("completedLevels", natArrayJson search.completed),
            ("decline",
              search.decline.map (Json.str ·.name) |>.getD Json.null),
            ("budget", natJson defaultSubsetBudget) ]
        let extras := extras.push ("hensel", henselJson)
        let extras := extras.push ("recombination", searchJson)
        match search.factors with
        | some factors =>
            let validStart ← mark
            let valid := validDirectFactors core.poly factors
            observeNat sink (if valid then 1 else 0)
            let validStop ← mark
            let phases := phases.push (phaseEntry "validation" validStart validStop)
            if valid then
              let reassembled :=
                reassemblePolynomialFactors normalized factors.toArray
              if Factorization.product (factorizationOfFactors f reassembled) = f then
                return ← finishPhaseProfile f sink excluded m0 "classical" phases extras
                  reassembled
              else
                return ← runTrialTail f sink excluded m0 phases extras
            else
              return ← runLatticeTail f sink excluded m0 normalized modular phases extras
        | none => return ← runLatticeTail f sink excluded m0 normalized modular phases extras
where
  /-- The proved trial-division backstop, timed. -/
  runTrialTail (f : ZPoly) (sink : IO.Ref Nat) (excluded : IO.Ref (Nat × Nat))
      (m0 : Mark) (phases extras : Array (String × Json)) : IO Json := do
    let trialStart ← mark
    let factors := factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
    observeNat sink factors.size
    let trialStop ← mark
    finishPhaseProfile f sink excluded m0 "trial"
      (phases.push (phaseEntry "trial" trialStart trialStop)) extras factors
  /-- The full CLD lattice tier, then the trial backstop, timed. -/
  runLatticeTail (f : ZPoly) (sink : IO.Ref Nat) (excluded : IO.Ref (Nat × Nat))
      (m0 : Mark) (normalized : FactorNormalizationData)
      (modular : DirectPrimePlan (SquareFreeInput.ofNormalized normalized))
      (phases extras : Array (String × Json)) : IO Json := do
    let latticeStart ← mark
    let lattice := factorLatticeFactorsWithPlan normalized
      (latticePrecisionCap f) modular
    observeNat sink (lattice.map (·.size) |>.getD 0)
    let latticeStop ← mark
    let phases := phases.push (phaseEntry "lattice" latticeStart latticeStop)
    match lattice with
    | some factors =>
        if Factorization.product (factorizationOfFactors f factors) = f then
          finishPhaseProfile f sink excluded m0 "lattice" phases extras factors
        else
          runTrialTail f sink excluded m0 phases extras
    | none => runTrialTail f sink excluded m0 phases extras

/-- Downstream cost of stopping the bounded prime walk at one retained good
prime.  The production selection is one of the rows; the others are
counterfactual, and are the only place this service does work the production
cascade would not have done. -/
private def primeCounterfactual (f : ZPoly) : IO Json := do
  let sink ← IO.mkRef 0
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  match directPrimePlan? core with
  | none => return Json.mkObj [("goodPrimeFound", Json.bool false)]
  | some modular =>
      let coreBound := ZPoly.defaultFactorCoeffBound core.poly
      let mut rows : Array Json := #[]
      for probe in modular.probes do
        let plan := DirectPrimePlan.ofSelection probe #[]
        let liftStart ← mark
        let liftPlan := directLiftPlan core plan
        let basis := (directLiftedBasis core plan liftPlan).data
        observeNat sink (basis.k + basis.liftedFactors.size)
        let liftStop ← mark
        let searchStart ← mark
        let search := countedSearch (DensePoly.leadingCoeff core.poly) core.poly basis
        observeNat sink search.stats.leaves
        let searchStop ← mark
        rows := rows.push <| Json.mkObj
          [ ("prime", natJson probe.data.p),
            ("selected", Json.bool (probe.data.p == modular.prime)),
            ("modularFactorCount", natJson probe.data.factorsModP.size),
            ("factorDegrees", natArrayJson probe.factorDegrees),
            ("henselPrecision", natJson basis.k),
            ("liftedMaxCoeffBits", natJson (maxCoeffBits basis.liftedFactors)),
            ("henselLift", spanJson liftStart liftStop),
            ("recombination", spanJson searchStart searchStop),
            ("downstreamNanos",
              natJson ((liftStop.nanos - liftStart.nanos) +
                (searchStop.nanos - searchStart.nanos))),
            ("stages", candidateStatsJson search.stats),
            ("successfulDivisors", natJson search.divisors),
            ("completedLevels", natArrayJson search.completed),
            ("solved", Json.bool search.factors.isSome),
            ("decline", search.decline.map (Json.str ·.name) |>.getD Json.null) ]
      return Json.mkObj
        [ ("goodPrimeFound", Json.bool true),
          ("degree", natJson (f.degree?.getD 0)),
          ("selectedPrime", natJson modular.prime),
          ("coeffBound", natJson coreBound),
          ("candidates", Json.arr rows) ]

def replyOk (result : Json) : Json :=
  Json.mkObj [("ok", Json.bool true), ("result", result)]

def replyDecline : Json :=
  Json.mkObj [("ok", Json.bool true), ("result", Json.null)]

def replyError (msg : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str msg)]

/-- Answer one request line (pure: factoring is total, so no exception path). -/
def handleLine (entry : Entry) (line : String) : Json :=
  match parseCoeffs line with
  | .error msg =>
      replyError s!"expected JSON object with integer array field coeffs: {msg}"
  | .ok coeffs =>
      let f := DensePoly.ofCoeffs coeffs.toArray
      if entry == .factorTrace then
        let (result, trace) := Hex.factorClassicalTraced f
        replyOk <| Json.mkObj
          [ ("factorization", result.map factorizationToJson |>.getD Json.null),
            ("trace", factorTraceToJson trace) ]
      else if entry == .proposalTrace then
        let (result, trace) := Hex.factorProposedTraced f
        replyOk <| Json.mkObj
          [ ("factorization",
              result.map
                  (fun proposal =>
                    factorizationToJson <|
                      factorizationOfFactors f proposal.factors)
                |>.getD Json.null),
            ("trace", proposalTraceToJson trace) ]
      else
        match entry.run f with
        | some φ => replyOk (factorizationToJson φ)
        | none => replyDecline

/-- Answer one of the IO-timed profiler entries. -/
private def handleProfileLine (entry : Entry) (line : String) : IO Json :=
  match parseCoeffs line with
  | .error msg =>
      pure <| replyError
        s!"expected JSON object with integer array field coeffs: {msg}"
  | .ok coeffs => do
      let f := DensePoly.ofCoeffs coeffs.toArray
      if entry == .factorPhaseProfile then
        return replyOk (← factorPhaseProfile f)
      else if entry == .primeCounterfactual then
        return replyOk (← primeCounterfactual f)
      else
        return replyOk (← proposalProfile f)

partial def runLoop (entry : Entry) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then
      return ()  -- EOF: getLine yields "" only at end of stream
    else
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty then
        loop  -- skip blank keep-alive lines
      else
        let response ←
          if entry.timed then
            handleProfileLine entry trimmed
          else
            pure (handleLine entry trimmed)
        stdout.putStrLn response.compress
        stdout.flush
        loop
  loop

/-- `--entry <name>`; defaults to `factor`. -/
def parseEntryArg : List String → String
  | "--entry" :: v :: _ => v
  | _ :: rest => parseEntryArg rest
  | [] => "factor"

def main (args : List String) : IO Unit := do
  match ← IO.getEnv "HEX_FPLLL_FFI_LIB" with
  | some path => if path != "" then discard <| lll.loadExternalReducer path
  | none => pure ()
  let entryName := parseEntryArg args
  match Entry.ofString? entryName with
  | none =>
      throw <| IO.userError
        s!"unknown --entry {entryName}; expected \
          factor|factorLattice|factorTrace|proposalTrace|proposalProfile\
          |factorPhaseProfile|primeCounterfactual"
  | some entry => runLoop entry

end HexBench.FactorService

def main (args : List String) : IO Unit :=
  HexBench.FactorService.main args
