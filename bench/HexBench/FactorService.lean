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
deriving Repr, DecidableEq

def Entry.ofString? : String → Option Entry
  | "factor" => some .factor
  | "factorLattice" => some .factorLattice
  | "factorTrace" => some .factorTrace
  | "proposalTrace" => some .proposalTrace
  | "proposalProfile" => some .proposalProfile
  | _ => none

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

/-- Answer the IO-timed proposal profiler entry. -/
private def handleProfileLine (line : String) : IO Json :=
  match parseCoeffs line with
  | .error msg =>
      pure <| replyError
        s!"expected JSON object with integer array field coeffs: {msg}"
  | .ok coeffs =>
      return replyOk (← proposalProfile (DensePoly.ofCoeffs coeffs.toArray))

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
          if entry == .proposalProfile then
            handleProfileLine trimmed
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
          factor|factorLattice|factorTrace|proposalTrace|proposalProfile"
  | some entry => runLoop entry

end HexBench.FactorService

def main (args : List String) : IO Unit :=
  HexBench.FactorService.main args
