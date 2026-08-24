/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import HexBench.BerlekampKernel
import HexBerlekampZassenhaus.QuadraticNormRecover
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
* `retainedPrimeProbe` — counted counterfactual for issue #9153: how many
  proposal-traversal leaves the retained good primes' subset-degree bitsets
  would reject beyond the production degree check, and what consulting them
  costs.
* `primeCounterfactual` — for every good prime the bounded walk retained, the
  downstream lift and recombination cost of having stopped there.
* `primeScout` — for every good prime in a bounded prefix of the hot-path
  candidate list, the cost of learning its modular degree pattern four ways: a
  bounded scout against the first good prime's width, the complete degree
  pattern, the Berlekamp matrix plus its kernel, and a full Berlekamp split.
  The scouted pattern is checked against the split.
* `quadraticNormProbe` — paired pricing of the iterated-quadratic-norm
  irreducibility certificate (issue #9133) against the production cascade on
  the same input: radicand recovery, the square-class independence test, the
  iterated-norm coefficient construction, and the equality test, each timed
  separately, alongside one production factorization.
* `kernelProfile` — stage-by-stage attribution of the Berlekamp fixed-space
  kernel at the production-selected prime, together with the price of a packed
  contiguous finite-field representation (issue #9132). Like `primeScout`, none
  of this is work the production cascade does.

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
  | obstructionProbe
  | retainedPrimeProbe
  | primeCounterfactual
  | primeScout
  | kernelProfile
  | henselTreeProfile
  | quadraticNormProbe
  | quadraticNormCertificate
deriving Repr, DecidableEq

def Entry.ofString? : String → Option Entry
  | "factor" => some .factor
  | "factorLattice" => some .factorLattice
  | "factorTrace" => some .factorTrace
  | "proposalTrace" => some .proposalTrace
  | "proposalProfile" => some .proposalProfile
  | "factorPhaseProfile" => some .factorPhaseProfile
  | "obstructionProbe" => some .obstructionProbe
  | "retainedPrimeProbe" => some .retainedPrimeProbe
  | "primeCounterfactual" => some .primeCounterfactual
  | "primeScout" => some .primeScout
  | "kernelProfile" => some .kernelProfile
  | "henselTreeProfile" => some .henselTreeProfile
  | "quadraticNormProbe" => some .quadraticNormProbe
  | "quadraticNormCertificate" => some .quadraticNormCertificate
  | _ => none

/-- Entries answered by an `IO`-timed profiler rather than by `handleLine`. -/
def Entry.timed : Entry → Bool
  | .proposalProfile => true
  | .factorPhaseProfile => true
  | .obstructionProbe => true
  | .retainedPrimeProbe => true
  | .primeCounterfactual => true
  | .primeScout => true
  | .kernelProfile => true
  | .henselTreeProfile => true
  | .quadraticNormProbe => true
  | .quadraticNormCertificate => true
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
  | .obstructionProbe, _ => none
  | .retainedPrimeProbe, _ => none
  | .primeCounterfactual, _ => none
  | .primeScout, _ => none
  | .kernelProfile, _ => none
  | .henselTreeProfile, _ => none
  | .quadraticNormProbe, _ => none
  | .quadraticNormCertificate, _ => none

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
counters that `scanDirectSubsets` already records for the unforced sweep.

`obstruct` selects whether a recordable candidate is put to the word-prime
divisibility obstruction before exact division.  With it on the mirror is the
production leaf, and `recordable - exactDivisions` is the number of exact
divisions the obstruction removed; with it off the mirror is the leaf as it
stood before the obstruction existed.  Running the same traversal both ways is
what makes the filter's effect a measurement rather than an inference. -/
private def countedScanCombinations
    (obstruct : Bool) (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (lift : LiftSupport basis) (image : TargetImage target)
    (head : DirectLiftedIndex basis) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      DirectSubsetLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      -- `directLeaf` runs the recorded-data filters (short-circuited, degree
      -- first) exactly once, and only then reverses the selected indices, maps
      -- them to lifted factors, builds the candidate, and -- on success --
      -- concatenates the complementary support. Splitting the prefilter into
      -- its two components here is what makes the stage counters separable;
      -- every materialization stays at the production operational point.
      let visited : DirectCandidateStats := { leaves := 1 }
      if directDegreePrefilter coreLc target selectedDegree then
        let degreePassed := { visited with degreeSurvivors := 1 }
        if directTrailingPrefilter coreLc target lift.modulus selectedTrail then
          let filtered := { degreePassed with trailingSurvivors := 1 }
          let selected := head :: selectedRev.reverse
          let selectedFactors := directSelectedFactors basis selected
          let candidate := directCandidate coreLc lift.modulus.nat selectedFactors
          let constructed := { filtered with constructed := 1 }
          if shouldRecordPolynomialFactor candidate then
            let recorded := { constructed with recordable := 1 }
            if obstruct && Hex.obstructs image candidate then
              .exhausted recorded
            else
            let divided := { recorded with exactDivisions := 1 }
            match exactQuotient? target candidate with
            | some quotient =>
                .found
                  { selected, remaining := rejectedRev.reverse ++ xs,
                    candidate, quotient } divided
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
      match countedScanCombinations obstruct coreLc target basis lift image
          head xs choose
          (x :: selectedRev) rejectedRev
          (selectedDegree + lift.degree x)
          (selectedTrail * lift.trail x % lift.modulus.int) with
      | .found split stats => .found split stats
      | .exhausted leftStats =>
          match countedScanCombinations obstruct coreLc target basis
              lift image head xs
              (choose + 1) selectedRev (x :: rejectedRev) selectedDegree
              selectedTrail with
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
    (obstruct : Bool) (coreLc : Int) (target : ZPoly) (basis : LiftData)
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
        let lift := liftSupport basis
        match countedScanCombinations obstruct coreLc target basis lift
            (targetImage target) head tail level
            [] [] (lift.degree head) (lift.trail head % lift.modulus.int) with
        | .found split levelStats =>
            .found split (budget - levelStats.leaves) (stats.add levelStats)
              completed
        | .exhausted levelStats =>
            countedFindHead obstruct coreLc target basis head tail levels
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
private def countedSearchAux (obstruct : Bool) (coreLc : Int) (basis : LiftData) :
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
            match countedFindHead obstruct coreLc target basis head tail
                (List.range (tail.length + 1)) budget {} #[] with
            | .declined reason budget' levelStats levelCompleted =>
                let _ := budget'
                { factors := none, decline := some reason,
                  stats := stats.add levelStats,
                  completed := completed ++ levelCompleted, divisors := 0 }
            | .found split budget' levelStats levelCompleted =>
                let rest := countedSearchAux obstruct coreLc basis fuel
                  split.quotient
                  split.remaining budget' (stats.add levelStats)
                  (completed ++ levelCompleted)
                { rest with
                  factors := rest.factors.map (split.candidate :: ·)
                  divisors := rest.divisors + 1 }

/-- Counted mirror of `searchDirect`. -/
private def countedSearch (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (budget : Nat := defaultSubsetBudget) (obstruct : Bool := true) :
    CountedSearch :=
  countedSearchAux obstruct coreLc basis (basis.liftedFactors.size + 1) target
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
  letI : ZMod64.PrimeModulus c.m := ZMod64.primeModulusOfPrime c.prime
  do
  let m0 ← mark
  let fModP := ZPoly.modP c.m core
  observeNat sink fModP.size
  let m1 ← mark
  let good := isGoodPrime core c.m
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
    -- On the kernel branch `berlekampFactor` recomputes the fixed-space kernel
    -- internally, so the equal-degree splitting cost is what remains once the
    -- separately measured matrix construction and row reduction are removed
    -- from its total. On the root-extraction branch it builds no matrix and no
    -- nullspace, so that subtraction would not describe anything: the total is
    -- the scan and the linear-factor construction, and there is no splitting
    -- stage to attribute.
    -- Re-runs the selection point outside the measured span. It repeats the
    -- residue scan, which the span above already paid for, but the branch tag
    -- is not otherwise recoverable from the factor list and this repeat cannot
    -- perturb a mark that has already been taken.
    let rootExtraction := (Berlekamp.rootFactors? monic).isSome
    let matrixNanos := m4.nanos - m3.nanos
    let reduceNanos := m5.nanos - m4.nanos
    let factorNanos := m6.nanos - m5.nanos
    return Json.mkObj
      [ ("measurement", Json.str "repeat-at-selected-prime"),
        ("prime", natJson c.m),
        ("modularDegree", natJson (fModP.degree?.getD 0)),
        ("kernelDimension", natJson kernel.size),
        ("distinctDegree", Json.str "not-applicable"),
        ("rootExtraction", Json.bool rootExtraction),
        ("modularImage", spanJson m0 m1),
        ("goodPrimeTest", spanJson m1 m2),
        ("berlekampMatrix", spanJson m3 m4),
        ("rowReduction", spanJson m4 m5),
        ("berlekampFactorTotal", spanJson m5 m6),
        ("splittingNanos",
          if rootExtraction then Json.str "not-applicable"
          else natJson (factorNanos - matrixNanos - reduceNanos)) ]
  else
    return Json.mkObj
      [ ("measurement", Json.str "repeat-at-selected-prime"),
        ("prime", natJson c.m),
        ("modularImage", spanJson m0 m1),
        ("goodPrimeTest", spanJson m1 m2),
        ("zeroModularImage", Json.bool true) ]

/-- Emit the finished profile.

The modular sub-phase repeat runs here, after the cascade's `total` mark, so it
cannot perturb the cache, allocator, or memory state of any phase it is meant
to describe. It is a second observation of the selected prime, not part of the
timed execution, and the record labels it that way. -/
private def emitPhaseProfile (f : ZPoly) (sink : IO.Ref Nat)
    (repeatAt : IO.Ref (Option SmallPrimeCandidate)) (core : ZPoly)
    (m0 : Mark) (method : String) (phases extras : Array (String × Json))
    (φ : Factorization) (reconstructs : Bool) : IO Json := do
  let total ← mark
  let phases := phases.push (phaseEntry "total" m0 total)
  let extras ←
    match ← repeatAt.get with
    | none => pure extras
    | some candidate =>
        pure (extras.push ("modular", ← modularSubPhases sink core candidate))
  return Json.mkObj <|
    [ ("method", Json.str method),
      ("degree", natJson (f.degree?.getD 0)),
      ("reconstructs", Json.bool reconstructs),
      ("factorDegrees",
        natArrayJson (φ.factors.map fun entry => entry.1.degree?.getD 0)),
      ("multiplicities", natArrayJson (φ.factors.map fun entry => entry.2)),
      ("phases", Json.mkObj phases.toList) ] ++ extras.toList

/-- Assemble and self-certify the answer, exactly once.

The constant, quadratic, classical, and lattice methods are self-certifying in
production: `runFactor` accepts them only when `Factorization.product φ = f`,
and otherwise falls through to the proved trial backstop. `certify := true`
reproduces that fall-through. Proposal replay and trial division are accepted
unconditionally in production, so they pass `certify := false`; the check still
runs, because the record reports whether the answer reconstructs, but it never
changes the route. -/
private def finishPhaseProfile (f : ZPoly) (sink : IO.Ref Nat)
    (repeatAt : IO.Ref (Option SmallPrimeCandidate)) (core : ZPoly) (m0 : Mark)
    (method : String) (phases extras : Array (String × Json))
    (factors : Array ZPoly) (certify : Bool := true) : IO Json := do
  let assemblyStart ← mark
  let φ := factorizationOfFactors f factors
  let reconstructs := Factorization.product φ = f
  observeNat sink (if reconstructs then 1 else 0)
  let assemblyStop ← mark
  let phases := phases.push (phaseEntry "assembly" assemblyStart assemblyStop)
  if reconstructs || !certify then
    emitPhaseProfile f sink repeatAt core m0 method phases extras φ reconstructs
  else
    let trialStart ← mark
    let trialFactors :=
      factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
    observeNat sink trialFactors.size
    let trialStop ← mark
    let trialAssemblyStart ← mark
    let ψ := factorizationOfFactors f trialFactors
    let trialReconstructs := Factorization.product ψ = f
    observeNat sink (if trialReconstructs then 1 else 0)
    let trialAssemblyStop ← mark
    emitPhaseProfile f sink repeatAt core m0 "trial"
      ((phases.push (phaseEntry "trial" trialStart trialStop)).push
        (phaseEntry "trialAssembly" trialAssemblyStart trialAssemblyStop))
      extras ψ trialReconstructs

/-- Phase-attributed profile of one production factorization.

With `probe`, recombination additionally runs a second time with the word-prime
divisibility obstruction enabled, and the record carries both spans and both
stage-counter sets.  Production is unaffected either way: the obstruction lives
in the mirror, not in `searchDirect`. -/
private def factorPhaseProfile (f : ZPoly) (probe : Bool := false) : IO Json := do
  let sink ← IO.mkRef 0
  let repeatAt ← IO.mkRef (none : Option SmallPrimeCandidate)
  let m0 ← mark
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  observeNat sink (core.poly.degree?.getD 0 + (core.poly.coeff 0).natAbs)
  let m1 ← mark
  let phases := #[phaseEntry "normalization" m0 m1]
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    return ← finishPhaseProfile f sink repeatAt core.poly m0 "constant" phases #[]
      (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
  let quadratic := quadraticIntegerRootFactors? normalized.squareFreeCore
  observeNat sink (quadratic.map (·.size) |>.getD 0)
  let m2 ← mark
  let phases := phases.push (phaseEntry "quadratic" m1 m2)
  match quadratic with
  | some coreFactors =>
      return ← finishPhaseProfile f sink repeatAt core.poly m0 "quadratic" phases #[]
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
      return ← finishPhaseProfile f sink repeatAt core.poly m0 "trial" phases
        #[("primeWalk", Json.mkObj [("goodPrimeFound", Json.bool false)])] factors
        (certify := false)
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
      repeatAt.set (some modular.selected.candidate)
      let extras := #[("primeWalk", walkJson)]
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
            return ← finishPhaseProfile f sink repeatAt core.poly m0 "replay" phases extras
              result.factors (certify := false)
        | none =>
            let latticeStart ← mark
            let lattice := factorLatticeFactorsWithPlan normalized
              (latticePrecisionCap f) modular
            observeNat sink (lattice.map (·.size) |>.getD 0)
            let latticeStop ← mark
            let phases := phases.push (phaseEntry "lattice" latticeStart latticeStop)
            match lattice with
            | some factors =>
                return ←
                  finishPhaseProfile f sink repeatAt core.poly m0 "lattice" phases extras factors
            | none => return ← runTrialTail f sink repeatAt core.poly m0 phases extras
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
            -- `balancedSplitIndex` halves by factor count, except when one
            -- modular factor carries more than half the total degree, where it
            -- picks the least degree-imbalanced prefix instead. Either way the
            -- product tree is binary with one `henselLiftFactors` call per
            -- internal node.
            ("treeShape",
              Json.str "count-balanced binary product tree with a guarded \
                dominant-degree split"),
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
        let extras ← if !probe then pure extras else do
          -- Counterbalanced: unfiltered, filtered, unfiltered, after the
          -- production filtered run.  A fixed order would confound the filter
          -- with allocator warmth and cache state, so each variant is measured
          -- both early and late.
          --
          -- Each repeat gets its own budget offset read out of a fresh `IO.Ref`.
          -- The offsets are all zero, so every run is the same search; what
          -- they change is that the four calls are no longer syntactically
          -- identical, which is what stops the compiler from sharing one
          -- evaluation between them.  Without this the repeats return in a few
          -- hundred nanoseconds and time nothing.  `sameRepeatCounters` below
          -- is the check that they really are the same search.
          let offsetA ← (← IO.mkRef (0 : Nat)).get
          let unfilteredFirstStart ← mark
          let unfilteredFirst :=
            countedSearch (DensePoly.leadingCoeff core.poly) core.poly basis
              (budget := defaultSubsetBudget + offsetA) (obstruct := false)
          observeNat sink (unfilteredFirst.stats.leaves +
            (unfilteredFirst.factors.map (·.length) |>.getD 0))
          let unfilteredFirstStop ← mark
          let offsetB ← (← IO.mkRef (0 : Nat)).get
          let filteredSecond :=
            countedSearch (DensePoly.leadingCoeff core.poly) core.poly basis
              (budget := defaultSubsetBudget + offsetB) (obstruct := true)
          observeNat sink (filteredSecond.stats.leaves +
            (filteredSecond.factors.map (·.length) |>.getD 0))
          let filteredSecondStop ← mark
          let offsetC ← (← IO.mkRef (0 : Nat)).get
          let unfilteredSecond :=
            countedSearch (DensePoly.leadingCoeff core.poly) core.poly basis
              (budget := defaultSubsetBudget + offsetC) (obstruct := false)
          observeNat sink (unfilteredSecond.stats.leaves +
            (unfilteredSecond.factors.map (·.length) |>.getD 0))
          let unfilteredSecondStop ← mark
          pure <| extras.push ("obstruction", Json.mkObj
            [ ("prime", natJson Hex.obstructionPrime),
              ("order",
                Json.str "filtered (production), unfiltered, filtered, unfiltered"),
              ("filteredRecombination", spanJson searchStart searchStop),
              ("filteredRecombinationSecond",
                spanJson unfilteredFirstStop filteredSecondStop),
              ("unfilteredRecombinationFirst",
                spanJson unfilteredFirstStart unfilteredFirstStop),
              ("unfilteredRecombinationSecond",
                spanJson filteredSecondStop unfilteredSecondStop),
              ("filteredStages", candidateStatsJson search.stats),
              ("unfilteredStages", candidateStatsJson unfilteredFirst.stats),
              ("reachedFilter", natJson search.stats.recordable),
              ("modularRejections",
                natJson (search.stats.recordable - search.stats.exactDivisions)),
              ("exactFallThroughs", natJson search.stats.exactDivisions),
              ("exactDivisionsAvoided",
                natJson (unfilteredFirst.stats.exactDivisions -
                  search.stats.exactDivisions)),
              -- Equality of the recovered factor *polynomials*, not of their
              -- degrees: two different divisors of the same degree would pass
              -- a degree-multiset check.
              ("sameFactors",
                Json.bool (unfilteredFirst.factors == search.factors &&
                  unfilteredSecond.factors == search.factors &&
                  filteredSecond.factors == search.factors)),
              ("sameDecline",
                Json.bool (unfilteredFirst.decline == search.decline)),
              ("sameRepeatCounters",
                Json.bool (filteredSecond.stats == search.stats &&
                  unfilteredSecond.stats == unfilteredFirst.stats)),
              ("sameSearchShape",
                Json.bool (unfilteredFirst.divisors == search.divisors &&
                  unfilteredFirst.completed == search.completed &&
                  unfilteredFirst.stats.leaves == search.stats.leaves &&
                  unfilteredFirst.stats.recordable == search.stats.recordable)) ])
        match search.factors with
        | some factors =>
            let validStart ← mark
            let valid := validDirectFactors core.poly factors
            observeNat sink (if valid then 1 else 0)
            let validStop ← mark
            let phases := phases.push (phaseEntry "validation" validStart validStop)
            if valid then
              return ← finishPhaseProfile f sink repeatAt core.poly m0 "classical" phases
                extras (reassemblePolynomialFactors normalized factors.toArray)
            else
              return ← runLatticeTail f sink repeatAt core.poly m0 normalized modular phases extras
        | none => return ← runLatticeTail f sink repeatAt core.poly m0 normalized modular phases extras
where
  /-- The proved trial-division backstop, timed. -/
  runTrialTail (f : ZPoly) (sink : IO.Ref Nat)
      (repeatAt : IO.Ref (Option SmallPrimeCandidate)) (core : ZPoly)
      (m0 : Mark) (phases extras : Array (String × Json)) : IO Json := do
    let trialStart ← mark
    let factors := factorTrialFactorsWithBound f (ZPoly.defaultFactorCoeffBound f)
    observeNat sink factors.size
    let trialStop ← mark
    finishPhaseProfile f sink repeatAt core m0 "trial"
      (phases.push (phaseEntry "trial" trialStart trialStop)) extras factors
      (certify := false)
  /-- The full CLD lattice tier, then the trial backstop, timed. -/
  runLatticeTail (f : ZPoly) (sink : IO.Ref Nat)
      (repeatAt : IO.Ref (Option SmallPrimeCandidate)) (core : ZPoly)
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
        finishPhaseProfile f sink repeatAt core m0 "lattice" phases extras factors
    | none => runTrialTail f sink repeatAt core m0 phases extras

/-- Width threshold of the fixed comparison set the counterfactual prices.

The comparison set is deliberately *not* the set the production plan retains:
the plan splits only what its own policy accepts, so following it would shrink
the comparison set exactly where that policy is being evaluated.  The set is
fixed instead at the first good prime, plus -- when that first image is wide --
the next two good primes.  That is the set the pre-scout fixed policy retained,
so the table stays row-for-row comparable with the recorded baseline.

It is pinned here rather than read off the planner, so that changing the
production policy cannot move it: this threshold and `fixedComparisonFuel` are
the pre-scout rule's, and stay at their historical values however the planner
evolves. -/
private def fixedComparisonWidth : Nat := 8

/-- The pre-scout fixed rule's scouting allowance; see `fixedComparisonWidth`. -/
private def fixedComparisonFuel : Nat := 2

/-- Good primes the counterfactual compares; see `fixedComparisonWidth`. -/
private def counterfactualCandidates (core : SquareFreeInput) :
    Nat → List SmallPrimeCandidate → Array (DirectPrimeProbe core) →
      Array (DirectPrimeProbe core)
  | _, [], probes => probes
  | 0, _, probes => probes
  | fuel + 1, candidate :: candidates, probes =>
      match probePrimeData? core.poly candidate with
      | none => counterfactualCandidates core (fuel + 1) candidates probes
      | some data =>
          let probe := DirectPrimeProbe.ofData core candidate data
          let probes := probes.push probe
          if probes.size == 1 && data.factorsModP.size ≤ fixedComparisonWidth then
            probes
          else
            counterfactualCandidates core fuel candidates probes

/-- Downstream cost of stopping the bounded prime walk at one good prime.  The
production selection is one of the rows; the others are counterfactual, and are
the only place this service does work the production cascade would not have
done.

`downstreamNanos` is the *direct* route only: the Hensel lift plus the counted
subset search.  A plan whose search declines falls through to proposal replay,
the lattice tier or trial division in production, and none of that is priced
here, so these rows compare primes that answer directly and say nothing about
one that would not. -/
private def primeCounterfactual (f : ZPoly) : IO Json := do
  let sink ← IO.mkRef 0
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  match directPrimePlan? core with
  | none => return Json.mkObj [("goodPrimeFound", Json.bool false)]
  | some modular =>
      let coreBound := ZPoly.defaultFactorCoeffBound core.poly
      let candidates :=
        counterfactualCandidates core (fixedComparisonFuel + 1) hotPathCandidates #[]
      let mut rows : Array Json := #[]
      for probe in candidates do
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

/-! ## Counterfactual: candidate degrees against every retained prime

Classical recombination filters a selected support by its degree at the
selected prime and by the target degree.  A genuine integer factor also
reduces, at *every* other good prime the planner retained, to a subproduct of
that prime's modular irreducible factors, so its degree must be a subset sum of
that prime's factor degrees too.  `HexBerlekampZassenhausMathlib.Modular`
proves that (`reachableDegrees_of_dvd`); what it does not say is whether the
extra test rejects anything.

The mirror below answers that.  It is a leaf-for-leaf copy of the production
unforced traversal -- same order, same filters, same accepting step -- with
the retained-prime tests *counted and then discarded*, so the traversal it
measures visits exactly the leaves production visits and returns exactly the
factors production returns.  Nothing here is reachable from the production
cascade.
-/

/-- Stage counters of the unforced sweep, extended with the retained-prime
degree tests production does not run. -/
private structure RetainedStats where
  /-- Combinatorial leaves visited. -/
  leaves : Nat := 0
  /-- Leaves surviving the production selected-support degree check. -/
  degreeSurvivors : Nat := 0
  /-- Degree survivors each retained probe still admits, in plan order. -/
  probeSurvivors : Array Nat := #[]
  /-- Degree survivors every retained probe admits. -/
  intersectionSurvivors : Nat := 0
  /-- Bitset lookups performed. -/
  lookups : Nat := 0
  /-- Leaves also surviving the trailing-coefficient test. -/
  trailingSurvivors : Nat := 0
  /-- Integer candidate polynomials constructed. -/
  constructed : Nat := 0
  /-- Constructed candidates passing the nonunit recording filter. -/
  recordable : Nat := 0
  /-- Recordable candidates the word-prime obstruction rejected. -/
  obstructionRejections : Nat := 0
  /-- Candidates sent to exact polynomial division. -/
  exactDivisions : Nat := 0

/-- Componentwise sum of two per-probe counter arrays, tolerating an empty
side (the counterfactual runs with the tests off as well as on). -/
private def addCounts (left right : Array Nat) : Array Nat :=
  (List.range (max left.size right.size)).toArray.map fun i =>
    left[i]?.getD 0 + right[i]?.getD 0

private def RetainedStats.add (left right : RetainedStats) : RetainedStats :=
  { leaves := left.leaves + right.leaves
    degreeSurvivors := left.degreeSurvivors + right.degreeSurvivors
    probeSurvivors := addCounts left.probeSurvivors right.probeSurvivors
    intersectionSurvivors :=
      left.intersectionSurvivors + right.intersectionSurvivors
    lookups := left.lookups + right.lookups
    trailingSurvivors := left.trailingSurvivors + right.trailingSurvivors
    constructed := left.constructed + right.constructed
    recordable := left.recordable + right.recordable
    obstructionRejections :=
      left.obstructionRejections + right.obstructionRejections
    exactDivisions := left.exactDivisions + right.exactDivisions }

/-- Consult every retained probe's subset-degree bitset at one candidate
degree.  Returns the per-probe indicators, whether all of them admit it, and
the number of lookups performed. -/
private def retainedTests (bits : Array (Array Bool)) (degree : Nat) :
    Array Nat × Nat × Nat :=
  let flags := bits.map fun reachable => reachable[degree]?.getD false
  (flags.map (fun ok => if ok then 1 else 0),
    (if flags.all (· = true) then 1 else 0), flags.size)

/-- Outcome of one counted unforced subset-cardinality level. -/
private inductive RetainedLevelResult (basis : LiftData) where
  | found (split : DirectSplit basis) (stats : RetainedStats)
  | exhausted (stats : RetainedStats)

/-- Counted mirror of `scanDirectSubsets`.

`consult` selects whether the retained-prime bitsets are read and `act` whether
a rejection short-circuits the leaf.  Three arms matter: consulting without
acting visits exactly the leaves production visits, so its counters are the
counterfactual and its span minus the not-consulting span is the price of the
lookups; consulting *and* acting is the prototype, and its span against the
not-consulting span is the net.  A rejected leaf never reaches the
multi-limb trailing test, the candidate product, or exact division. -/
private def retainedScanSubsets
    (consult act : Bool) (bits : Array (Array Bool))
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (lift : LiftSupport basis) (image : TargetImage target) :
    (xs : List (DirectLiftedIndex basis)) → (choose : Nat) →
      (selectedRev rejectedRev : List (DirectLiftedIndex basis)) →
      (selectedDegree : Nat) → (selectedTrail : Int) →
      RetainedLevelResult basis
  | xs, 0, selectedRev, rejectedRev, selectedDegree, selectedTrail =>
      let visited : RetainedStats := { leaves := 1 }
      if directDegreePrefilter coreLc target selectedDegree then
        let degreePassed := { visited with degreeSurvivors := 1 }
        let (survivors, intersection, lookups) :=
          if consult then retainedTests bits selectedDegree else (#[], 1, 0)
        let degreePassed :=
          if consult then
            { degreePassed with
              probeSurvivors := survivors
              intersectionSurvivors := intersection
              lookups := lookups }
          else degreePassed
        -- With `consult` off this is the production shape of the predicate: a
        -- short-circuiting scan of the retained bitsets, allocating nothing and
        -- recording nothing.  With `consult` on it reuses the counters already
        -- computed, so the counted and acting arms stay one traversal.
        let rejected :=
          if act then
            if consult then intersection == 0
            else !(bits.all fun reachable => reachable[selectedDegree]?.getD false)
          else false
        if rejected then
          .exhausted degreePassed
        else if directTrailingPrefilter coreLc target lift.modulus selectedTrail then
          let filtered := { degreePassed with trailingSurvivors := 1 }
          let selected := selectedRev.reverse
          let candidate := directCandidate coreLc lift.modulus.nat
            (directSelectedFactors basis selected)
          let constructed := { filtered with constructed := 1 }
          if shouldRecordPolynomialFactor candidate then
            let recorded := { constructed with recordable := 1 }
            if Hex.obstructs image candidate then
              .exhausted { recorded with obstructionRejections := 1 }
            else
              let divided := { recorded with exactDivisions := 1 }
              match obstructedQuotient? image candidate with
              | some quotient =>
                  .found
                    { selected, remaining := rejectedRev.reverse ++ xs,
                      candidate, quotient } divided
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
      match retainedScanSubsets consult act bits coreLc target basis lift image
          xs choose (x :: selectedRev) rejectedRev
          (selectedDegree + lift.degree x)
          (selectedTrail * lift.trail x % lift.modulus.int) with
      | .found split stats => .found split stats
      | .exhausted leftStats =>
          match retainedScanSubsets consult act bits coreLc target basis lift
              image xs (choose + 1) selectedRev (x :: rejectedRev) selectedDegree
              selectedTrail with
          | .found split rightStats => .found split (leftStats.add rightStats)
          | .exhausted rightStats => .exhausted (leftStats.add rightStats)

/-- Outcome of one counted residual's cardinality schedule. -/
private inductive RetainedSweep (basis : LiftData) where
  | found (split : DirectSplit basis) (budget : Nat)
      (records : Array (Nat × RetainedStats)) (totals : RetainedStats)
  | stopped (reason : DeclineReason) (budget : Nat)
      (records : Array (Nat × RetainedStats)) (totals : RetainedStats)

/-- Counted mirror of `findDirectSubset`, retaining one record per attempted
cardinality level. -/
private def retainedFindSubset
    (consult act : Bool) (bits : Array (Array Bool))
    (coreLc : Int) (target : ZPoly) (basis : LiftData)
    (lift : LiftSupport basis) (image : TargetImage target)
    (support : List (DirectLiftedIndex basis)) :
    (levels : List Nat) → (budget : Nat) →
      (records : Array (Nat × RetainedStats)) → (totals : RetainedStats) →
      RetainedSweep basis
  | [], budget, records, totals => .stopped .cardinalityCap budget records totals
  | level :: levels, budget, records, totals =>
      let levelCost := Nat.choose support.length level
      if levelCost > budget then
        .stopped .subsetBudget budget records totals
      else
        match retainedScanSubsets consult act bits coreLc target basis lift image
            support level [] [] 0 1 with
        | .found split levelStats =>
            .found split (budget - levelStats.leaves)
              (records.push (level, levelStats)) (totals.add levelStats)
        | .exhausted levelStats =>
            retainedFindSubset consult act bits coreLc target basis lift image
              support levels (budget - levelStats.leaves)
              (records.push (level, levelStats)) (totals.add levelStats)

/-- What one mirrored peel run produced. -/
private structure RetainedPeelResult where
  /-- One record per attempted level: residual index, cardinality, counters. -/
  records : Array (Nat × Nat × RetainedStats) := #[]
  /-- Counters summed over every level. -/
  totals : RetainedStats := {}
  /-- The exact factors peeled, in peel order.  Retained as polynomials, not
  as degrees: two arms could peel same-degree but different factors, and a
  degree comparison would not notice. -/
  peeled : Array ZPoly := #[]
  /-- The residual the peel run stopped on. -/
  residual : ZPoly := 1
  /-- Indices of the complementary lifted support for that residual. -/
  remaining : Array Nat := #[]
  /-- Candidate budget left unconsumed. -/
  budget : Nat := 0
  /-- Why the run stopped, when it did. -/
  decline : Option DeclineReason := none

/-- Do two arms agree on everything a caller of the peel run consumes?  The
counter fields are excluded because only the counted arms fill them in. -/
private def RetainedPeelResult.sameOutcome
    (left right : RetainedPeelResult) : Bool :=
  left.peeled == right.peeled && left.residual == right.residual &&
    left.remaining == right.remaining && left.budget == right.budget &&
    left.decline.map (·.name) == right.decline.map (·.name)

/-- Counted mirror of `peelDirectAux`, tagging each level record with the
index of the residual it was attempted against. -/
private def retainedPeelAux
    (consult act : Bool) (bits : Array (Array Bool))
    (coreLc : Int) (basis : LiftData) (lift : LiftSupport basis)
    (repeatLevels : List Nat) :
    Nat → ZPoly → List (DirectLiftedIndex basis) → Nat → Nat →
      RetainedPeelResult → List Nat → RetainedPeelResult
  | 0, target, support, _, budget, acc, _ =>
      { acc with residual := target, remaining := (support.map (·.1)).toArray
                 budget, decline := some .liftFailure }
  | fuel + 1, target, support, residual, budget, acc, levels =>
      if target = 1 then
        { acc with residual := target, remaining := #[], budget }
      else
        match retainedFindSubset consult act bits coreLc target basis lift
            (targetImage target) support levels budget #[] {} with
        | .stopped reason budget' levelRecords sweepTotals =>
            { acc with
              records := acc.records ++
                levelRecords.map (fun r => (residual, r.1, r.2))
              totals := acc.totals.add sweepTotals
              residual := target
              remaining := (support.map (·.1)).toArray
              budget := budget'
              decline := some reason }
        | .found split budget' levelRecords sweepTotals =>
            retainedPeelAux consult act bits coreLc basis lift repeatLevels fuel
              split.quotient split.remaining (residual + 1) budget'
              { acc with
                records := acc.records ++
                  levelRecords.map (fun r => (residual, r.1, r.2))
                totals := acc.totals.add sweepTotals
                peeled := acc.peeled.push split.candidate }
              repeatLevels

/-- Counted mirror of `peelDirect` at the production operational point. -/
private def retainedPeel
    (consult act : Bool) (bits : Array (Array Bool))
    (coreLc : Int) (target : ZPoly) (basis : LiftData) :
    RetainedPeelResult :=
  let support := List.finRange basis.liftedFactors.size
  retainedPeelAux consult act bits coreLc basis (liftSupport basis)
    ((List.range 2).map (· + 1)) (support.length + 1) target support 0
    proposalSubsetBudget {} ((List.range 3).map (· + 1))

private def retainedStatsJson (stats : RetainedStats) : Json :=
  Json.mkObj
    [ ("leaves", natJson stats.leaves),
      ("degreeSurvivors", natJson stats.degreeSurvivors),
      ("probeSurvivors", natArrayJson stats.probeSurvivors),
      ("intersectionSurvivors", natJson stats.intersectionSurvivors),
      ("bitsetLookups", natJson stats.lookups),
      ("trailingSurvivors", natJson stats.trailingSurvivors),
      ("constructed", natJson stats.constructed),
      ("recordable", natJson stats.recordable),
      ("obstructionRejections", natJson stats.obstructionRejections),
      ("exactDivisions", natJson stats.exactDivisions) ]

/-- Price the retained-prime degree test over one input.

The peel run is mirrored three ways -- not consulting, consulting without
acting, consulting and acting -- twice over, interleaved, so a drift in host
load cannot land preferentially on one arm.  The counters come from the
consulting arm; the acting arm additionally reports the factors it peeled, so
the prototype is checked against the production traversal rather than assumed
to agree with it.

`rejectableDegrees` is the traversal-independent half of the same question: the
degrees the selected prime's own factorization can form that some retained
prime cannot.  When it is empty, no traversal over this lift can be helped by
this filter, whatever order it visits supports in. -/
private def retainedPrimeProbe (f : ZPoly) : IO Json := do
  let sink ← IO.mkRef 0
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  match directPrimePlan? core with
  | none => return Json.mkObj [("goodPrimeFound", Json.bool false)]
  | some modular =>
      let liftPlan := directLiftPlan core modular
      let basis := (directLiftedBasis core modular liftPlan).data
      let coreLc := DensePoly.leadingCoeff core.poly
      -- Only the trials the planner kept beyond the selected one carry
      -- information: a support enumerated at the selected prime is a subset of
      -- that prime's own factor degrees, so its bitset always admits it.
      let others := modular.otherProbes
      let bits := others.map (fun probe => probe.reachableDegrees)
      let selectedBits := modular.selected.reachableDegrees
      let rejectable := (List.range (core.poly.degree?.getD 0 + 1)).filter
        fun d =>
          selectedBits[d]?.getD false &&
            !(bits.all fun reachable => reachable[d]?.getD false)
      let runArm (consult act : Bool) : IO (Json × RetainedPeelResult) := do
        let start ← mark
        let run := retainedPeel consult act bits coreLc core.poly basis
        observeNat sink run.totals.leaves
        let stop ← mark
        return (spanJson start stop, run)
      let mut plainSpans : Array Json := #[]
      let mut countSpans : Array Json := #[]
      let mut predicateSpans : Array Json := #[]
      let mut actSpans : Array Json := #[]
      let mut counted : RetainedPeelResult := {}
      let mut acted : RetainedPeelResult := {}
      let mut predicate : RetainedPeelResult := {}
      let mut plain : RetainedPeelResult := {}
      -- Four arms, six rounds, the order reversed on alternate rounds.  Running
      -- the arms in a fixed order costs the first one the round's cache
      -- warm-up, which on the short rows is larger than anything being
      -- measured; reversing half the rounds cancels it.
      --
      -- `plain` against `predicate` is the timing comparison: the predicate arm
      -- carries no counters and allocates nothing per leaf, so it prices what
      -- production would run.  The counted arms carry the counterfactual and
      -- pay for it in allocation, so their spans price the diagnostic, not the
      -- filter.
      let arms := [(false, false), (true, false), (false, true), (true, true)]
      for round in [0:6] do
        let order := if round % 2 == 0 then arms else arms.reverse
        for (consult, act) in order do
          let (span, run) ← runArm consult act
          if consult && act then
            actSpans := actSpans.push span
            acted := run
          else if act then
            predicateSpans := predicateSpans.push span
            predicate := run
          else if consult then
            countSpans := countSpans.push span
            counted := run
          else
            plainSpans := plainSpans.push span
            plain := run
      -- Both acting arms must return exactly what the plain arm returns: the
      -- same peeled polynomials in the same order, the same residual, the same
      -- complementary support, the same unconsumed budget, the same decline.
      let sameOutcome :=
        plain.sameOutcome predicate && plain.sameOutcome acted
      let levelJson := counted.records.map fun (residual, cardinality, stats) =>
        Json.mkObj
          [ ("residual", natJson residual),
            ("cardinality", natJson cardinality),
            ("stats", retainedStatsJson stats) ]
      let probeJson := modular.probes.map fun probe =>
        Json.mkObj
          [ ("prime", natJson probe.data.p),
            ("selected", Json.bool (probe.data.p == modular.prime)),
            ("factorDegrees", natArrayJson probe.factorDegrees),
            ("reachableProperDegrees",
              natJson (directReachableProperCount probe)) ]
      return Json.mkObj
        [ ("goodPrimeFound", Json.bool true),
          ("degree", natJson (core.poly.degree?.getD 0)),
          ("selectedPrime", natJson modular.prime),
          ("retainedProbeCount", natJson others.size),
          ("probes", Json.arr probeJson),
          ("liftedFactorCount", natJson basis.liftedFactors.size),
          ("henselPrecision", natJson basis.k),
          ("rejectableDegrees", natArrayJson rejectable.toArray),
          ("levels", Json.arr levelJson),
          ("totals", retainedStatsJson counted.totals),
          ("actedTotals", retainedStatsJson acted.totals),
          ("decline", counted.decline.map (Json.str ·.name) |>.getD Json.null),
          ("peeledFactorDegrees",
            natArrayJson (plain.peeled.map (fun q => q.degree?.getD 0))),
          ("residualDegree", natJson (plain.residual.degree?.getD 0)),
          ("remainingSupport", natArrayJson plain.remaining),
          ("remainingBudget", natJson plain.budget),
          ("sameOutcome", Json.bool sameOutcome),
          ("plainSpans", Json.arr plainSpans),
          ("countSpans", Json.arr countSpans),
          ("predicateSpans", Json.arr predicateSpans),
          ("actSpans", Json.arr actSpans) ]

/-- How many good primes the scouting measurement examines.  Wider than any
policy would use, so the record can price a horizon rather than assume one. -/
private def scoutHorizon : Nat := 6

/-- Attribute the fixed-space kernel at one candidate prime. -/
private def kernelProfileAt (core : ZPoly) (c : SmallPrimeCandidate) :
    IO (List (String × Json)) :=
  letI := c.bounds
  letI : ZMod64.PrimeModulus c.m := ZMod64.primeModulusOfPrime c.prime
  do
  let fModP := ZPoly.modP c.m core
  if hzero : fModP.isZero = false then
    let monic := monicModularImage fModP
    let hmonic := monicModularImage_monic c.prime fModP hzero
    let kernel ← HexBench.BerlekampKernel.kernelPhases monic hmonic
    return [ ("status", Json.str "ok"),
             ("prime", natJson c.m),
             ("modularDegree", natJson (fModP.degree?.getD 0)),
             ("kernel", kernel) ]
  else
    return [ ("status", Json.str "zeroModularImage"), ("prime", natJson c.m) ]

/-- Stage-by-stage attribution of the Berlekamp fixed-space kernel at the
production-selected prime, together with the price of a packed contiguous
finite-field representation (issue #9132).

This repeats the modular work at the already-selected prime, after the
production plan has been computed, so it perturbs nothing the production
cascade measures; like `primeScout` it is diagnostic work the cascade never
does. The stage boundaries, the counted Gauss-Jordan mirror, and the packed
variants all live in `HexBench.BerlekampKernel`, which checks each packed
result against `Hex.Matrix.nullspace` before reporting its time. -/
private def kernelProfile (f : ZPoly) : IO Json := do
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  match directPrimePlan? core with
  | none => return Json.mkObj [("status", Json.str "noGoodPrime")]
  | some modular =>
      let extra : List (String × Json) :=
        [ ("retainedGoodPrimes", natJson modular.probes.size),
          ("modularFactorCount", natJson modular.data.factorsModP.size) ]
      return Json.mkObj
        (extra ++ (← kernelProfileAt core.poly modular.selected.candidate))

/-- Multiplicity of each degree at most `n`, for comparing degree multisets. -/
private def degreeHistogram (n : Nat) (degrees : Array Nat) : Array Nat :=
  degrees.foldl (fun h d => h.modify d (· + 1)) (Array.replicate (n + 1) 0)

/-- Cost of learning one candidate prime's modular degree pattern four ways: a
bounded scout against `target`, the complete degree pattern, the Berlekamp
matrix with its kernel, and a full Berlekamp split.  `none` when the candidate
is not a good prime.

`target` is fixed by the caller at the first good prime's width, which is the
target production uses until a scouted candidate wins and tightens it, so these
are scout prices at a fixed target rather than a replay of the production
walk.  The complete pattern prices what a scout with no target would cost, and
is what the split is checked against. -/
private def scoutRow (sink : IO.Ref Nat) (core : SquareFreeInput) (target : Nat)
    (c : SmallPrimeCandidate) : IO (Option Json) :=
  letI := c.bounds
  letI : ZMod64.PrimeModulus c.m := ZMod64.primeModulusOfPrime c.prime
  do
  let m0 ← mark
  let good := isGoodPrime core.poly c.m
  observeNat sink (if good then 1 else 0)
  let m1 ← mark
  if !good then
    return none
  let fModP := ZPoly.modP c.m core.poly
  if hzero : fModP.isZero = false then
    let n := fModP.degree?.getD 0
    let monic := monicModularImage fModP
    let hmonic := monicModularImage_monic c.prime fModP hzero
    let boundedStart ← mark
    let bounded := Berlekamp.scoutDegreePattern monic hmonic target
    observeNat sink (bounded.separated.size + bounded.residual)
    let boundedStop ← mark
    let scoutStart ← mark
    let pattern := Berlekamp.degreePattern? monic hmonic
    observeNat sink ((pattern.map (·.size)).getD 0)
    let scoutStop ← mark
    let matrixStart ← mark
    let fixed := Berlekamp.fixedSpaceMatrix monic hmonic
    observeNat sink (Berlekamp.basisSize monic)
    let matrixStop ← mark
    let kernel := Matrix.nullspace fixed
    observeNat sink kernel.size
    let kernelStop ← mark
    let splitStart ← mark
    let factors := (Berlekamp.berlekampFactor monic hmonic).factors
    observeNat sink factors.length
    let splitStop ← mark
    let splitDegrees := (factors.map fun g => g.degree?.getD 0).toArray
    let scoutDegrees := pattern.getD #[]
    return some <| Json.mkObj
      [ ("prime", natJson c.m),
        ("modularDegree", natJson n),
        ("kernelDimension", natJson kernel.size),
        ("scoutTarget", natJson target),
        -- The two shape quantities `Hex.scoutPays` prices a plan at this prime
        -- by: the machine words of its Hensel modulus, and the recombination
        -- candidates a complete head-forced search over its factors visits.
        ("liftWords", natJson (liftWords core c.m)),
        ("recombUnits",
          natJson (directSubsetCost splitDegrees.size * liftWords core c.m)),
        ("splitMaxDegree", natJson (splitDegrees.foldl max 0)),
        ("boundedScout", spanJson boundedStart boundedStop),
        ("boundedSeparated", natArrayJson bounded.separated),
        ("boundedResidual", natJson bounded.residual),
        ("boundedMinResidualDegree", natJson bounded.minResidualDegree),
        ("boundedLowerBound", natJson bounded.lowerBound),
        ("boundedUpperBound", natJson bounded.upperBound),
        ("boundedComplete", Json.bool bounded.complete),
        ("scoutComplete", Json.bool pattern.isSome),
        ("scoutDegrees", natArrayJson scoutDegrees),
        ("splitDegrees", natArrayJson splitDegrees),
        ("patternAgrees",
          Json.bool (pattern.isSome &&
            degreeHistogram n scoutDegrees == degreeHistogram n splitDegrees)),
        ("goodPrimeTest", spanJson m0 m1),
        ("scout", spanJson scoutStart scoutStop),
        ("berlekampMatrix", spanJson matrixStart matrixStop),
        ("rowReduction", spanJson matrixStop kernelStop),
        ("fullSplit", spanJson splitStart splitStop) ]
  else
    return some <| Json.mkObj
      [ ("prime", natJson c.m),
        ("goodPrimeTest", spanJson m0 m1),
        ("zeroModularImage", Json.bool true) ]

/-- Price the degree-pattern scout against a full Berlekamp split at every good
prime in a bounded prefix of the hot-path candidate list.

Everything here is extra work the production cascade would not have done: the
production planner splits only the primes its own policy retains.  The record
exists to choose that policy, so it prices all three ways of learning a pattern
at each candidate and checks the scouted pattern against the split. -/
private def primeScout (f : ZPoly) : IO Json := do
  let sink ← IO.mkRef 0
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  let firstWidth :=
    (counterfactualCandidates core 1 hotPathCandidates #[]).foldl
      (fun w probe => max w probe.data.factorsModP.size) 0
  -- Every candidate is priced against the *first* good prime's width, not the
  -- width the production walk would be carrying when it reaches that candidate:
  -- production tightens its target whenever a scouted candidate wins, so a
  -- later row here can be timed under a looser target than production uses.
  -- The record names the target it used so the two are never confused.
  let target := firstWidth
  let mut rows : Array Json := #[]
  let mut seen := 0
  for c in hotPathCandidates do
    if seen < scoutHorizon then
      match ← scoutRow sink core target c with
      | none => pure ()
      | some row =>
          seen := seen + 1
          rows := rows.push row
  return Json.mkObj
    [ ("degree", natJson (core.poly.degree?.getD 0)),
      ("scoutHorizon", natJson scoutHorizon),
      ("firstGoodPrimeWidth", natJson firstWidth),
      ("scoutTarget", natJson target),
      ("selectedPrime",
        natJson ((directPrimePlan? core).map (·.prime) |>.getD 0)),
      ("candidates", Json.arr rows) ]

/-! ## Node-level profile of the multifactor Hensel product tree

`henselTreeProfile` re-walks the production tree
`Hex.ZPoly.multifactorLiftQuadraticListImpl` in `IO`, timing every node's two
sub-products, its normalised XGCD, and every quadratic doubling step of that
node's exact-exponent lift. Bignum steps are additionally replayed piece by
piece, so the factor error, the `t · e` product, the monic modular division and
the residual coefficient reductions are priced separately.

The mirror runs the production functions themselves, in production order, and
its returned array is checked against `Hex.ZPoly.multifactorLiftQuadratic`
before any time is reported. The per-step replay is diagnostic overhead and is
reported under `replay`; the step's own `nanos` is the untimed production
call. -/

private def polyShapeJson (name : String) (f : ZPoly) : String × Json :=
  (name, Json.mkObj
    [ ("degree", natJson (f.degree?.getD 0)),
      ("size", natJson f.size),
      ("coeffBits", natJson (ZPoly.bitLen (ZPoly.maxAbs f))) ])

/-- Replay one bignum quadratic step's pieces, in the order
`quadraticHenselStepBignum` executes them, timing each. `factorOnly` stops
after the factor update, mirroring `quadraticHenselFactorsBignum`. -/
private def replayBignumStep (sink : IO.Ref Nat) (factorOnly : Bool)
    (m : Nat) (f g h s t : ZPoly) : IO Json := do
  let a0 ← mark
  let e := QuadraticLiftResult.factorError f g h
  observeNat sink e.size
  let a1 ← mark
  let te := ZPoly.mulModSquare t e m
  observeNat sink te.size
  let a2 ← mark
  let factorQR := ZPoly.divModMonicModSquare te g m
  observeNat sink (factorQR.1.size + factorQR.2.size)
  let a3 ← mark
  let g' := QuadraticLiftResult.reduceModSquare (g + factorQR.2) m
  let hCorrection := QuadraticLiftResult.reduceModSquare
    (ZPoly.mulModSquare s e m + ZPoly.mulModSquare factorQR.1 h m) m
  let h' := QuadraticLiftResult.reduceModSquare (h + hCorrection) m
  observeNat sink (g'.size + h'.size)
  let a4 ← mark
  let bezout ←
    if factorOnly then
      pure []
    else do
      let b0 ← mark
      let b := QuadraticLiftResult.reduceModSquare
        (QuadraticLiftResult.reduceModSquare
          (ZPoly.mulModSquare s g' m + ZPoly.mulModSquare t h' m) m - 1) m
      let tb := ZPoly.mulModSquare t b m
      observeNat sink tb.size
      let b1 ← mark
      let bezoutQR := ZPoly.divModMonicModSquare tb g' m
      observeNat sink (bezoutQR.1.size + bezoutQR.2.size)
      let b2 ← mark
      let t' := QuadraticLiftResult.reduceModSquare (t - bezoutQR.2) m
      let s' := QuadraticLiftResult.reduceModSquare
        (QuadraticLiftResult.reduceModSquare (s - ZPoly.mulModSquare s b m) m
          - ZPoly.mulModSquare bezoutQR.1 h' m) m
      observeNat sink (s'.size + t'.size)
      let b3 ← mark
      pure [ ("bezoutError", spanJson b0 b1), ("bezoutDivision", spanJson b1 b2),
             ("bezoutUpdate", spanJson b2 b3) ]
  return Json.mkObj <|
    [ ("factorError", spanJson a0 a1), ("errorProduct", spanJson a1 a2),
      ("factorDivision", spanJson a2 a3), ("factorUpdate", spanJson a3 a4),
      ("replayTotal", spanJson a0 a4),
      polyShapeJson "errorShape" e, polyShapeJson "errorProductShape" te,
      polyShapeJson "quotientShape" factorQR.1 ] ++ bezout

/-- Record one doubling step: its exponents, its modulus width, whether the
word-sized guard admits it, its production time, and its replay attribution. -/
private def stepJson (sink : IO.Ref Nat) (steps : IO.Ref (Array Json))
    (kind : String) (p exponent target : Nat) (start stop : Mark)
    (f g h s t : ZPoly) : IO Unit := do
  let m := p ^ exponent
  let word := decide (m * m < UInt64.word)
  let replay ←
    if word then pure Json.null
    else replayBignumStep sink (kind == "factors") m f g h s t
  steps.modify (·.push (Json.mkObj
    [ ("kind", Json.str kind),
      ("exponent", natJson exponent),
      ("target", natJson target),
      ("modulusBits", natJson (ZPoly.bitLen m)),
      ("wordPath", Json.bool word),
      ("span", spanJson start stop),
      ("replay", replay) ]))

/-- Mirror of `Hex.ZPoly.liftExactImpl`, timing every doubling step. -/
private partial def profileLiftExact (sink : IO.Ref Nat)
    (steps : IO.Ref (Array Json)) (p : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (k : Nat) (acc : QuadraticLiftResult) : IO QuadraticLiftResult := do
  if k ≤ 1 then
    let start ← mark
    let reduced := ZPoly.reduceLift p k acc
    observeNat sink (reduced.g.size + reduced.h.size + reduced.s.size + reduced.t.size)
    let stop ← mark
    stepJson sink steps "reduce" p k k start stop f acc.g acc.h acc.s acc.t
    return reduced
  else
    let half := (k + 1) / 2
    let prior ← profileLiftExact sink steps p f half acc
    let start ← mark
    let stepped := ZPoly.quadraticHenselStep (p ^ half) f prior.g prior.h prior.s prior.t
    observeNat sink (stepped.g.size + stepped.h.size + stepped.s.size + stepped.t.size)
    let stop ← mark
    stepJson sink steps "step" p half k start stop f prior.g prior.h prior.s prior.t
    if 2 * half = k then
      return stepped
    else
      let rstart ← mark
      let reduced := ZPoly.reduceLift p k stepped
      observeNat sink (reduced.g.size + reduced.h.size)
      let rstop ← mark
      stepJson sink steps "descend" p k k rstart rstop f stepped.g stepped.h
        stepped.s stepped.t
      return reduced

/-- Mirror of `Hex.ZPoly.henselLiftFactorsImpl`, timing its closing
factor-only step. -/
private def profileLiftFactors (sink : IO.Ref Nat) (steps : IO.Ref (Array Json))
    (p k : Nat) [ZMod64.Bounds p] (f g h s t : ZPoly) : IO (ZPoly × ZPoly) := do
  if k ≤ 1 then
    let start ← mark
    let pair := (ZPoly.reduceModPow g p k, ZPoly.reduceModPow h p k)
    observeNat sink (pair.1.size + pair.2.size)
    let stop ← mark
    stepJson sink steps "reduce" p k k start stop f g h s t
    return pair
  else
    let half := (k + 1) / 2
    let prior ← profileLiftExact sink steps p f half { g, h, s, t }
    let start ← mark
    let factors := ZPoly.quadraticHenselFactors (p ^ half) f prior.g prior.h prior.s prior.t
    observeNat sink (factors.1.size + factors.2.size)
    let stop ← mark
    stepJson sink steps "factors" p half k start stop f prior.g prior.h prior.s prior.t
    if 2 * half = k then
      return factors
    else
      let rstart ← mark
      let pair := (ZPoly.reduceModPow factors.1 p k, ZPoly.reduceModPow factors.2 p k)
      observeNat sink (pair.1.size + pair.2.size)
      let rstop ← mark
      stepJson sink steps "descend" p k k rstart rstop f factors.1 factors.2 prior.s prior.t
      return pair

/-- Mirror of `Hex.ZPoly.multifactorLiftQuadraticListImpl`, timing each node's
sub-products, XGCD and lift. -/
private partial def profileTreeNode (sink : IO.Ref Nat)
    (nodes : IO.Ref (Array Json)) (p k : Nat) [ZMod64.Bounds p]
    (depth : Nat) (f : ZPoly) : List ZPoly → IO (Array ZPoly)
  | [] => pure #[]
  | [_g] => pure #[f]
  | g₀ :: g₁ :: rest => do
      let gs := g₀ :: g₁ :: rest
      let start ← mark
      let split := ZPoly.balancedSplitIndex gs
      observeNat sink split
      let L := gs.take split
      let R := gs.drop split
      let splitStop ← mark
      let g := Array.polyProduct L.toArray
      let h := Array.polyProduct R.toArray
      observeNat sink (g.size + h.size)
      let productStop ← mark
      let xgcd := ZPoly.normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      observeNat sink (s.size + t.size)
      let xgcdStop ← mark
      let steps ← IO.mkRef (#[] : Array Json)
      let lifted ← profileLiftFactors sink steps p k f g h s t
      let liftStop ← mark
      let stepRows ← steps.get
      nodes.modify (·.push (Json.mkObj
        [ ("depth", natJson depth),
          ("factorCount", natJson gs.length),
          ("splitIndex", natJson split),
          ("targetDegree", natJson (f.degree?.getD 0)),
          ("split", spanJson start splitStop),
          ("subProducts", spanJson splitStop productStop),
          ("xgcd", spanJson productStop xgcdStop),
          ("lift", spanJson xgcdStop liftStop),
          ("node", spanJson start liftStop),
          polyShapeJson "left" g, polyShapeJson "right" h,
          polyShapeJson "bezoutLeft" s, polyShapeJson "bezoutRight" t,
          ("steps", Json.arr stepRows) ]))
      let left ← profileTreeNode sink nodes p k (depth + 1) lifted.1 L
      let right ← profileTreeNode sink nodes p k (depth + 1) lifted.2 R
      return left ++ right

/-- Integer lifts of one plan's modular factors, at the plan's own prime. -/
private def liftedModularFactors (p : Nat) [ZMod64.Bounds p]
    (factorsModP : Array (FpPoly p)) : Array ZPoly :=
  factorsModP.map (fun factor => FpPoly.liftToZ factor)

/-- Node-by-node attribution at a fixed prime, precision and monic target. -/
private def henselTreeAt (p : Nat) [ZMod64.Bounds p] (k : Nat)
    (target : ZPoly) (factors : Array ZPoly) : IO Json := do
  let sink ← IO.mkRef 0
  -- Production call, untimed decomposition, for the mirror check and the
  -- whole-lift reference time.
  let refStart ← mark
  let reference := ZPoly.multifactorLiftQuadratic p k target factors
  observeNat sink reference.size
  let refStop ← mark
  let nodes ← IO.mkRef (#[] : Array Json)
  let walkStart ← mark
  let mirrored ← profileTreeNode sink nodes p k 0 target factors.toList
  let walkStop ← mark
  let rows ← nodes.get
  return Json.mkObj
    [ ("accepted", Json.bool (mirrored == reference)),
      ("prime", natJson p),
      ("precision", natJson k),
      ("modularFactorCount", natJson factors.size),
      ("targetDegree", natJson (target.degree?.getD 0)),
      ("reference", spanJson refStart refStop),
      ("mirror", spanJson walkStart walkStop),
      ("nodes", Json.arr rows) ]

/-- Node-by-node attribution of the production multifactor Hensel lift. -/
private def henselTreeProfile (f : ZPoly) : IO Json := do
  let normalized := normalizeForFactor f
  let core := SquareFreeInput.ofNormalized normalized
  match directPrimePlan? core with
  | none => return Json.mkObj [("accepted", Json.bool false),
      ("reason", Json.str "noGoodPrime")]
  | some modular =>
      let p := modular.data.p
      let k := precisionForCoeffBound (ZPoly.defaultFactorCoeffBound core.poly) p
      let target := ZPoly.monicTarget core.poly p k
      let factors :=
        @liftedModularFactors p modular.data.bounds modular.data.factorsModP
      @henselTreeAt p modular.data.bounds k target factors

/-- Price the iterated-quadratic-norm irreducibility certificate on one input
(issue #9133's go/no-go gate).

The certificate side is reported in four spans, because the gate asks for
construction and checking separately: radicand recovery, the independence test
on the recovered square classes, the iterated-norm coefficient construction, and
the equality test against the input. A declining input reports only the recovery
span, which is the miss overhead a budget-gated production attempt would pay.

Every stage's result is folded into `witness` before its closing mark. Without
that the compiler sinks each pure `let` to its only use -- the reply object --
and the whole certificate cost lands in whichever span happens to be last.
`witness` is reported so the fold cannot itself be eliminated.

`paired` additionally runs one production factorization in the same process on
the same input, so the reported ratio is paired rather than assembled from two
sweeps. It must be off for an input the production cascade does not finish.

Every span runs the production definitions, the same ones
{name}`Hex.ZPoly.factorize` reaches through {name}`Hex.quadraticNormCertified`,
so the reported ratios describe production rather than a prototype. Recovery
carries no proof obligation -- a wrong guess dies in the check -- but the three
checked spans are exactly what the cascade runs, and their Mathlib
correspondence is in `HexBerlekampZassenhausMathlib.QuadraticNormIrreducible`.

The probe is unconditional: it prices the certificate on every input, including
the ones production's width floor never offers it. That is what makes the miss
table a property of the certificate rather than of the gate. -/
private def quadraticNormProbe (paired : Bool) (f : ZPoly) : IO Json := do
  let witness ← IO.mkRef (0 : Nat)
  let productionStart ← mark
  if paired then
    let φ := Hex.ZPoly.factorize f
    witness.modify (· + φ.factors.size)
  let productionStop ← mark
  let recoveryStart ← mark
  let recovered := Hex.QuadraticNormCertificate.recover? f
  witness.modify (· + (recovered.map fun c => c.radicands.size).getD 0)
  let recoveryStop ← mark
  let productionSpans : List (String × Json) :=
    if paired then [("production", spanJson productionStart productionStop)]
    else []
  match recovered with
  | none =>
      return Json.mkObj <|
        [ ("degree", natJson (f.degree?.getD 0)),
          ("certified", Json.bool false) ] ++ productionSpans ++
        [ ("recovery", spanJson recoveryStart recoveryStop),
          ("witness", natJson (← witness.get)) ]
  | some cert =>
      let independenceStart ← mark
      let independent := Hex.independentSquareClasses cert.radicands
      witness.modify (· + if independent then 1 else 0)
      let independenceStop ← mark
      let constructionStart ← mark
      let built := Hex.iteratedNorm cert.translation cert.radicands
      witness.modify (· + built.size)
      let constructionStop ← mark
      let equalityStart ← mark
      let equal := built == ZPoly.normalizePrimitiveSign f
      witness.modify (· + if equal then 1 else 0)
      let equalityStop ← mark
      return Json.mkObj <|
        [ ("degree", natJson (f.degree?.getD 0)),
          ("certified", Json.bool (independent && equal)) ] ++ productionSpans ++
        [ ("recovery", spanJson recoveryStart recoveryStop),
          ("independence", spanJson independenceStart independenceStop),
          ("construction", spanJson constructionStart constructionStop),
          ("equality", spanJson equalityStart equalityStop),
          ("translation", Json.num (JsonNumber.fromInt cert.translation)),
          ("radicands", intsToJson cert.radicands.toList),
          ("constructedSize", natJson built.size),
          ("independent", Json.bool independent),
          ("equal", Json.bool equal),
          ("witness", natJson (← witness.get)) ]

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
      if entry == .obstructionProbe then
        return replyOk (← factorPhaseProfile f (probe := true))
      else if entry == .retainedPrimeProbe then
        return replyOk (← retainedPrimeProbe f)
      else if entry == .primeCounterfactual then
        return replyOk (← primeCounterfactual f)
      else if entry == .primeScout then
        return replyOk (← primeScout f)
      else if entry == .kernelProfile then
        return replyOk (← kernelProfile f)
      else if entry == .henselTreeProfile then
        return replyOk (← henselTreeProfile f)
      else if entry == .quadraticNormProbe then
        return replyOk (← quadraticNormProbe (paired := true) f)
      else if entry == .quadraticNormCertificate then
        return replyOk (← quadraticNormProbe (paired := false) f)
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
          |factorPhaseProfile|primeCounterfactual|primeScout|kernelProfile\
          |henselTreeProfile|quadraticNormProbe|quadraticNormCertificate"
  | some entry => runLoop entry

end HexBench.FactorService

def main (args : List String) : IO Unit :=
  HexBench.FactorService.main args
