/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import Lean.Data.Json

/-!
# Prime-policy diagnostic for integer factorization

Reports the first-good and production adaptive prime choices, followed by the
production factorization trace, on representative hard corpus inputs. This is
a measurement aid only; it proves nothing.
-/

open Hex
open Lean (Json)

def multifactorLiftCountList
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) : Nat → List ZPoly → Array ZPoly
  | _, [] => #[]
  | _, [_g] => #[ZPoly.reduceModPow f p k]
  | 0, _gs => panic! "count-balanced diagnostic exhausted unreachable fuel"
  | fuel + 1, g₀ :: g₁ :: rest =>
      let gs := g₀ :: g₁ :: rest
      let half := gs.length / 2
      let L := gs.take half
      let R := gs.drop half
      let g := Array.polyProduct L.toArray
      let h := Array.polyProduct R.toArray
      let xgcd := ZPoly.normalizedXGCD p g h
      let lifted := ZPoly.henselLiftFactors p k f g h
        (FpPoly.liftToZ xgcd.left) (FpPoly.liftToZ xgcd.right)
      multifactorLiftCountList p k lifted.1 fuel L ++
        multifactorLiftCountList p k lifted.2 fuel R

def multifactorLiftCount
    (p k : Nat) [ZMod64.Bounds p] (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftCountList p k f factors.size factors.toList

def liftChecksum (factors : Array ZPoly) : UInt64 :=
  factors.foldl (fun acc g => acc + UInt64.ofNat g.size) 0

def timeLiftArm (iters : Nat) (run : Unit → Array ZPoly) : IO (Float × Array ZPoly) := do
  let _ ← IO.lazyPure run
  let t₀ ← IO.monoNanosNow
  let mut result := #[]
  let mut sink : UInt64 := 0
  for _ in [0:iters] do
    result ← IO.lazyPure run
    sink := sink + liftChecksum result
  let t₁ ← IO.monoNanosNow
  if sink = 0 then throw <| IO.userError "impossible empty lift checksum"
  pure ((t₁ - t₀).toFloat / iters.toFloat / 1.0e6, result)

/--
Largest degree of a proper candidate in the current head-forced subset search.
Every enumerated candidate contains the first local factor, so the largest
proper one omits the smallest degree in the tail.
-/
def headForcedMaxProperDegree (pd : PrimeChoiceData) : Nat :=
  match modularFactorDegrees pd with
  | [] => 0
  | [_] => pd.fModP.degree?.getD 0
  | head :: next :: tail =>
      let minTail := tail.foldl min next
      head + next + tail.sum - minTail

/-- Closed-form Mignotte opportunity bound when candidate degree is capped. -/
def factorCoeffBoundAtDegree (f : ZPoly) (degree : Nat) : Nat :=
  Nat.binom degree (degree / 2) * ZPoly.coeffL2NormBound f

/--
Measure the current M1 lift and the most optimistic degree cap admitted by the
existing head-forced search.  The capped arm is diagnostic only: production
continues to use the fully proved uniform bound.
-/
def compareM1Bounds (core : ZPoly) (pd : PrimeChoiceData) : IO Unit := do
  let corePd := ZPoly.corePrimeDataOfToMonic core pd
  let uniformBound := ZPoly.defaultFactorCoeffBound core
  let degreeBound := headForcedMaxProperDegree pd
  let cappedBound := factorCoeffBoundAtDegree core degreeBound
  let uniformK := precisionForCoeffBound uniformBound pd.p
  let cappedK := precisionForCoeffBound cappedBound pd.p
  let uniform ← timeLiftArm 7 (fun _ =>
    (ZPoly.coreLiftData core uniformBound corePd).liftedFactors)
  let capped ← timeLiftArm 7 (fun _ =>
    (ZPoly.coreLiftData core cappedBound corePd).liftedFactors)
  IO.println s!"  M1 bound: n={core.degree?.getD 0}, D={degreeBound}, \
    bits={uniformBound.log2 + 1}->{cappedBound.log2 + 1}, \
    k={uniformK}->{cappedK}, lift={uniform.1}->{capped.1} ms"

def compareLiftTrees
    (label : String) (f core monic : ZPoly) (pd : PrimeChoiceData) : IO Unit := do
  -- This isolates the lift tree at the exhaustive coefficient bound; it is not
  -- a reproduction of every bound override used by the recursive tier.
  let bound := ZPoly.exhaustiveLiftBound core (ZPoly.defaultFactorCoeffBound f)
  let k := precisionForCoeffBound bound pd.p
  let factors := pd.factorsModP.map (fun factor =>
    @FpPoly.liftToZ pd.p pd.bounds factor)
  let countPair := ← timeLiftArm 5 (fun _ =>
    @multifactorLiftCount pd.p k pd.bounds monic factors)
  let degreePair := ← timeLiftArm 5 (fun _ =>
    @ZPoly.multifactorLiftQuadratic pd.p k pd.bounds monic factors)
  let countMs := countPair.1
  let countResult := countPair.2
  let degreeMs := degreePair.1
  let degreeResult := degreePair.2
  if countResult != degreeResult then
    throw <| IO.userError s!"{label}: degree-balanced lift changed the ordered result"
  else
    pure ()
  IO.println s!"  lift count={countMs} ms, degree={degreeMs} ms, speedup={countMs / degreeMs}x"

def timePrimeChoice (label : String) (f : ZPoly) : IO Unit := do
  let normalized := normalizeForFactor f
  let core := normalized.squareFreeCore
  let monic := (ZPoly.toMonic core).monic
  let t0 ← IO.monoNanosNow
  let first ← IO.lazyPure (fun _ => choosePrimeData? monic)
  let t1 ← IO.monoNanosNow
  let adaptive ← IO.lazyPure (fun _ => ZPoly.toMonicPrimeData? core)
  let t2 ← IO.monoNanosNow
  let (_, trace) ← IO.lazyPure (fun _ => factorTraced f)
  let t3 ← IO.monoNanosNow
  let describe : Option PrimeChoiceData → String
    | none => "none"
    | some pd =>
        let degrees := pd.factorsModP.toList.map fun g =>
          toString (g.degree?.getD 0)
        let bound := ZPoly.exhaustiveLiftBound core (ZPoly.defaultFactorCoeffBound f)
        let k := precisionForCoeffBound bound pd.p
        s!"p={pd.p}, r={pd.factorsModP.size}, k={k}, degrees=[{String.intercalate "," degrees}]"
  IO.println s!"{label}: first [{describe first}] {(t1 - t0).toFloat / 1.0e6} ms; \
    adaptive [{describe adaptive}] {(t2 - t1).toFloat / 1.0e6} ms; \
    factor {(t3 - t2).toFloat / 1.0e6} ms \
    (tier={trace.tier}, p={trace.prime}, r={trace.liftedFactorCount}, \
    declined={trace.declined})"
  match adaptive with
  | none => pure ()
  | some pd =>
      compareLiftTrees label f core monic pd
      compareM1Bounds core pd
  ( ← IO.getStdout).flush

/-- Print the modular degree partitions at the first `limit` good candidates.
These are the degree-obstruction inputs available to an adaptive selector
without any Rabin-certificate scan. -/
def printGoodPrimeDegrees (label : String) (f : ZPoly) (limit : Nat := 6) :
    IO Unit := do
  let core := (normalizeForFactor f).squareFreeCore
  let mut seen := 0
  let mut lines : List String := []
  for c in smallPrimeCandidates ++ extendedSmallPrimeCandidates do
    if seen < limit then
      let t₀ ← IO.monoNanosNow
      let pd? ← IO.lazyPure (fun _ => probePrimeData? core c)
      let t₁ ← IO.monoNanosNow
      match pd? with
      | none => pure ()
      | some pd =>
          let degrees := pd.factorsModP.toList.map (fun g => g.degree?.getD 0)
          lines := lines ++
            [s!"p={pd.p} degrees={degrees} time={(t₁ - t₀).toFloat / 1.0e6}ms"]
          seen := seen + 1
  let joined := String.intercalate "; " lines
  IO.println s!"{label} good-prime degrees: {joined}"

/-- Read selected named cases from the checked-in comparison corpus. Keeping
the larger diagnostic inputs in the corpus avoids duplicating their coefficient
arrays here. -/
def timeCorpusCases (corpusPath : String) (wanted : List String) : IO Unit := do
  let corpus ← IO.FS.readFile corpusPath
  for line in corpus.splitOn "\n" do
    if !line.isEmpty then
      let parsed : Except String (String × List Int) := do
        let j ← Json.parse line
        let name ← (← j.getObjVal? "name").getStr?
        let coeffsJson ← (← j.getObjVal? "coeffs").getArr?
        let coeffs ← coeffsJson.toList.mapM Json.getInt?
        pure (name, coeffs)
      match parsed with
      | .error error => throw <| IO.userError s!"invalid corpus row: {error}"
      | .ok (name, coeffs) =>
          if wanted.contains name then
            let f := DensePoly.ofCoeffs coeffs.toArray
            timePrimeChoice name f
            if name == "legendre_P38" then
              printGoodPrimeDegrees name f 30
            else if ["legendre_P24", "legendre_P26", "legendre_P28",
                "legendre_P34"].contains name then
              printGoodPrimeDegrees name f 12

def main (args : List String) : IO Unit := do
  let corpusPath ← match args with
    | [] => pure "bench/corpus/hexbz-factor-corpus.jsonl"
    | [path] => pure path
    | _ => throw <| IO.userError "usage: hex_prime_policy_spike [corpus.jsonl]"
  let phi61 : ZPoly := DensePoly.ofCoeffs (Array.replicate 61 (1 : Int))
  let phi179 : ZPoly := DensePoly.ofCoeffs (Array.replicate 179 (1 : Int))
  let xpow105 : ZPoly := DensePoly.ofCoeffs
    (((Array.replicate 106 (0 : Int)).set! 0 (-1)).set! 105 1)
  let conway38 : ZPoly := DensePoly.ofCoeffs
    #[1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  let chebyshevU24 : ZPoly := DensePoly.ofCoeffs
    #[1, 0, -312, 0, 16016, 0, -320320, 0, 3294720, 0, -19914752, 0,
      76038144, 0, -190513152, 0, 317521920, 0, -348651520, 0, 242221056,
      0, -96468992, 0, 16777216]
  let chebyshevT24 : ZPoly := DensePoly.ofCoeffs
    #[1, 0, -288, 0, 13728, 0, -256256, 0, 2471040, 0, -14057472, 0,
      50692096, 0, -120324096, 0, 190513152, 0, -199229440, 0, 132120576,
      0, -50331648, 0, 8388608]
  let legendreP30 : ZPoly := DensePoly.ofCoeffs
    #[-155117520, 0, 72129646800, 0, -5553982803600, 0, 168470811709200, 0,
      -2671465728531600, 0, 25467973278667920, 0, -158210137034149200, 0,
      672827725628744400, 0, -2018483176886233200, 0, 4340398465330527600,
      0, -6716195520037763760, 0, 7413982067574154800, 0,
      -5694797820020727600, 0, 2891205047087446320, 0, -871950728486690160,
      0, 118264581564861424]
  let sd5 : ZPoly := DensePoly.ofCoeffs
    #[2000989041197056, 0, -44660812492570624, 0, 183876928237731840, 0,
      -255690851718529024, 0, 172580952324702208, 0, -65892492886671360, 0,
      15459151516270592, 0, -2349014746136576, 0, 239210760462336, 0,
      -16665641517056, 0, 801918722048, 0, -26625650688, 0, 602397952, 0,
      -9028096, 0, 84864, 0, -448, 0, 1]
  timePrimeChoice "Phi61" phi61
  timePrimeChoice "Phi179" phi179
  timePrimeChoice "x^105-1" xpow105
  timePrimeChoice "Conway(2,38)" conway38
  timePrimeChoice "Chebyshev U24" chebyshevU24
  printGoodPrimeDegrees "Chebyshev U24" chebyshevU24
  printGoodPrimeDegrees "Chebyshev T24" chebyshevT24
  timePrimeChoice "Legendre P30" legendreP30
  printGoodPrimeDegrees "Legendre P30" legendreP30 30
  timePrimeChoice "SD5" sd5
  timeCorpusCases corpusPath
    ["chebyshev_T10", "chebyshev_T15", "chebyshev_U12", "legendre_P16",
      "legendre_P24", "legendre_P26", "legendre_P28", "legendre_P34",
      "legendre_P38",
      "cyclo_phi385"]
