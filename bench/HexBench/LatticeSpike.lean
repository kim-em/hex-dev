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

def main : IO Unit := do
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
  let quad ← IO.mkRef (DensePoly.ofCoeffs #[6, 0, -5, 0, 1] : ZPoly)
  timeLattice "reducible (x^2-2)(x^2-3) deg 4" quad
  timeLattice "SD2   deg  4" sd2
  timeLattice "Phi15 deg  8" phi15
  timeLattice "SD3   deg  8" sd3
  timeLattice "SD4   deg 16" sd4
  timeLattice "SD5   deg 32" sd5
