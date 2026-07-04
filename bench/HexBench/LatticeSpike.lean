/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus.Basic

/-!
Measurement artifact for the lattice tier's certificate-backed early
termination (#8395): single-shot wall-clock for `factorLattice` on the
Swinnerton-Dyer / cyclotomic irreducible family, where the pre-#8395 loop
ground the doubling schedule to the conservative BHKS precision cap
(SD2 14ms, Phi_15 216ms, SD3 1.8s, SD4 >120s).  Inputs are routed through an
`IO.Ref` so the compiler cannot fold the factorization; the coefficient
checksum sink forces the full result.  Proves nothing.
-/

open Hex

/-- Coefficient checksum over all emitted factors; forces the result. -/
def latticeSink (r : Option Factorization) : UInt64 :=
  match r with
  | some φ =>
      φ.factors.foldl
        (fun acc fp =>
          fp.1.toArray.foldl
            (fun a c => a * 1000003 + UInt64.ofNat c.natAbs) (acc + UInt64.ofNat fp.2))
        7
  | none => 0xffffffffffffffff

/-- Faithful reconstruction of the **pre-#8395** lattice-tier core: grind
`bhksRecoveryCoreWithBound` to the cap `B`, then a single trailing all-ones
check at cap precision.  Used by the `before` mode to measure the
before/after ratio on the same build; the surrounding normalization and
reassembly (µs, identical on both paths) are excluded on both sides. -/
def beforeLatticeCore (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    Option (Array ZPoly) :=
  if primeData.factorsModP.size ≤ 1 then
    some #[core]
  else
    match bhksRecoveryCoreWithBound core B primeData
        (initialHenselPrecision B) (ZPoly.quadraticDoublingSteps B + 2) with
    | some coreFactors => some coreFactors
    | none =>
        if bhksSingleAllOnesPartition core (ZPoly.toMonicLiftData core B primeData) then
          some #[core]
        else
          none

/-- Post-#8395 lattice-tier core at the same call shape as `beforeLatticeCore`
(the early-stop loop plus the floor-guarded trailing check). -/
def afterLatticeCore (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) :
    Option (Array ZPoly) :=
  latticeCoreFactorsWithBound core B primeData

/-- Coefficient checksum over a raw core factor array; forces the result. -/
def coreSink (r : Option (Array ZPoly)) : UInt64 :=
  match r with
  | some cf =>
      cf.foldl
        (fun acc g =>
          g.toArray.foldl (fun a c => a * 1000003 + UInt64.ofNat c.natAbs) acc)
        7
  | none => 0xffffffffffffffff

/-- Time one lattice-tier core call (before or after path) on the square-free
core of the polynomial held in `ref`; normalization and prime selection happen
outside the timed region. -/
def timeLatticeCore (label : String) (ref : IO.Ref ZPoly)
    (act : ZPoly → Nat → PrimeChoiceData → Option (Array ZPoly)) : IO Unit := do
  let out ← IO.getStdout
  let f ← ref.get
  let core := (normalizeForFactor f).squareFreeCore
  let cap := latticePrecisionCap f
  match ZPoly.toMonicPrimeData? core with
  | none => IO.println s!"{label}: no admissible prime"
  | some primeData =>
      let t0 ← IO.monoNanosNow
      let (r, sink) ← IO.lazyPure (fun _ =>
        let r := act core cap primeData
        (r, coreSink r))
      let t1 ← IO.monoNanosNow
      let factors := (r.map (·.size)).getD 0
      IO.println
        s!"{label}: {(t1 - t0).toFloat / 1.0e6} ms (coreFactors={factors}, sink={sink})"
      out.flush

/-- Time one `factorLattice` call on the polynomial held in `ref`.  The call and
its checksum run inside `IO.lazyPure` so the compiler cannot float the pure
computation past the monotonic-clock reads. -/
def timeLattice (label : String) (ref : IO.Ref ZPoly) : IO Unit := do
  let out ← IO.getStdout
  let f ← ref.get
  let t0 ← IO.monoNanosNow
  let (r, sink) ← IO.lazyPure (fun _ =>
    let r := factorLattice f
    (r, latticeSink r))
  let t1 ← IO.monoNanosNow
  let factors := (r.map (·.factors.size)).getD 0
  IO.println s!"{label}: {(t1 - t0).toFloat / 1.0e6} ms (factors={factors}, sink={sink})"
  out.flush

def main (args : List String) : IO Unit := do
  IO.println "=== factorLattice wall-clock (#8395 early-termination spike) ==="
  let sd2 ← IO.mkRef (DensePoly.ofCoeffs #[1, 0, -10, 0, 1] : ZPoly)
  let phi15 ← IO.mkRef (DensePoly.ofCoeffs #[1, -1, 0, 1, -1, 1, 0, -1, 1] : ZPoly)
  let sd3 ← IO.mkRef (DensePoly.ofCoeffs #[576, 0, -960, 0, 352, 0, -40, 0, 1] : ZPoly)
  let sd4 ← IO.mkRef (DensePoly.ofCoeffs
    #[46225, 0, -5596840, 0, 13950764, 0, -7453176, 0, 1513334, 0, -141912, 0,
      6476, 0, -136, 0, 1] : ZPoly)
  let sd5 ← IO.mkRef (DensePoly.ofCoeffs
    #[2000989041197056, 0, -44660812492570624, 0, 183876928237731840, 0,
      -255690851718529024, 0, 172580952324702208, 0, -65892492886671360, 0,
      15459151516270592, 0, -2349014746136576, 0, 239210760462336, 0,
      -16665641517056, 0, 801918722048, 0, -26625650688, 0, 602397952, 0,
      -9028096, 0, 84864, 0, -448, 0, 1] : ZPoly)
  let sd6 ← IO.mkRef (DensePoly.ofCoeffs
    #[198828783273803025550632280753863681, 0, -8316202966928528723117528333532208416, 0,
      100392008259975194458539996111340080624, 0, -511762449216265420619809586571618679392, 0,
      1258829468814790188483900997578812102776, 0, -1771080720430629161685158978892152599456,
      0, 1585722240968892813653220405983168716752, 0, -968316307427310602872375357706532108000,
      0, 423140580409718469187953106123559340828, 0, -137048942135190916858196960829292680864,
      0, 33785494292069713784801456649105169648, 0, -6471399892949448329687739464771529952, 0,
      978878175154164215599705915851796296, 0, -118444912349891951852181962142375200, 0,
      11582497564629879101390954172990800, 0, -922739669127277027441017551584608, 0,
      60261059130667890854325275719238, 0, -3240853899326109989616514647392, 0,
      143976257181996292530653998416, 0, -5292590468585153795497272608, 0,
      161038437520893531719546696, 0, -4051269676739248306877664, 0, 84041236543621002233072,
      0, -1431186296399427673760, 0, 19875965471079809820, 0, -223010452468129504, 0,
      1995413247403984, 0, -13981172308896, 0, 74737287288, 0, -293134944, 0, 792048, 0, -1312,
      0, 1] : ZPoly)
  let quad ← IO.mkRef (DensePoly.ofCoeffs #[6, 0, -5, 0, 1] : ZPoly)
  match args with
  | ["before"] =>
      -- Pre-#8395 core path (grind to cap).  SD5 is omitted: its cap-bound
      -- schedule is out of reach (SD4 already exceeds two minutes).
      timeLatticeCore "before reducible deg 4" quad beforeLatticeCore
      timeLatticeCore "before SD2   deg  4" sd2 beforeLatticeCore
      timeLatticeCore "before Phi15 deg  8" phi15 beforeLatticeCore
      timeLatticeCore "before SD3   deg  8" sd3 beforeLatticeCore
      timeLatticeCore "before SD4   deg 16" sd4 beforeLatticeCore
  | ["core"] =>
      -- Post-#8395 core path, same call shape as `before` for direct ratios.
      timeLatticeCore "after  reducible deg 4" quad afterLatticeCore
      timeLatticeCore "after  SD2   deg  4" sd2 afterLatticeCore
      timeLatticeCore "after  Phi15 deg  8" phi15 afterLatticeCore
      timeLatticeCore "after  SD3   deg  8" sd3 afterLatticeCore
      timeLatticeCore "after  SD4   deg 16" sd4 afterLatticeCore
      timeLatticeCore "after  SD5   deg 32" sd5 afterLatticeCore
      timeLatticeCore "after  SD6   deg 64" sd6 afterLatticeCore
  | ["hybrid"] =>
      -- Which tier answers each input under the public dispatcher, and how
      -- long the full hybrid takes end to end.
      let timeHybrid (label : String) (ref : IO.Ref ZPoly) : IO Unit := do
        let f ← ref.get
        let t0 ← IO.monoNanosNow
        let (φ, trace) ← IO.lazyPure (fun _ => factorHybridTraced f)
        let t1 ← IO.monoNanosNow
        IO.println s!"{label}: {(t1 - t0).toFloat / 1.0e6} ms \
          (tier={trace.tier}, declined={trace.declined}, factors={φ.factors.size})"
        (← IO.getStdout).flush
      timeHybrid "hybrid reducible deg 4" quad
      timeHybrid "hybrid SD2   deg  4" sd2
      timeHybrid "hybrid Phi15 deg  8" phi15
      timeHybrid "hybrid SD3   deg  8" sd3
      timeHybrid "hybrid SD4   deg 16" sd4
      timeHybrid "hybrid SD5   deg 32" sd5
      timeHybrid "hybrid SD6   deg 64" sd6
  | _ =>
      timeLattice "reducible (x^2-2)(x^2-3) deg 4" quad
      timeLattice "SD2   deg  4" sd2
      timeLattice "Phi15 deg  8" phi15
      timeLattice "SD3   deg  8" sd3
      timeLattice "SD4   deg 16" sd4
      timeLattice "SD5   deg 32" sd5
