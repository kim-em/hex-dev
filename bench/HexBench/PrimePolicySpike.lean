/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus

/-!
# Prime-policy diagnostic for integer factorization

Reports the first-good and production adaptive prime choices, followed by the
production factorization trace, on representative hard corpus inputs. This is
a measurement aid only; it proves nothing.
-/

open Hex

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
    | some pd => s!"p={pd.p}, r={pd.factorsModP.size}"
  IO.println s!"{label}: first [{describe first}] {(t1 - t0).toFloat / 1.0e6} ms; \
    adaptive [{describe adaptive}] {(t2 - t1).toFloat / 1.0e6} ms; \
    factor {(t3 - t2).toFloat / 1.0e6} ms \
    (tier={trace.tier}, p={trace.prime}, r={trace.liftedFactorCount}, \
    declined={trace.declined})"
  ( ← IO.getStdout).flush

def main : IO Unit := do
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
  timePrimeChoice "Legendre P30" legendreP30
  timePrimeChoice "SD5" sd5
