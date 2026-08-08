/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp
import Lean.Data.Json

/-!
# Root-extraction versus Berlekamp splitting for fully split modular images

Diagnostic support for issue #9157's measurement gate.

A squarefree `f` over `F_p` splits into distinct linear factors exactly when
`f ∣ X^p - X`, that is when `X^p mod f = X`. The Berlekamp path already
computes `X^p mod f` as the first step of its fixed-space matrix, so that
certificate is available before any matrix is built. This driver prices the
three costs the production selection point needs to trade off:

* `frobenius` -- computing `X^p mod f`, the certificate ingredient;
* `scan` -- filtering the canonical residue list for roots of `f`;
* `extract` -- building the monic linear factors from those roots;

against `berlekampFactor`, the current production path, and against a
`fallbackPenalty` row that prices the one cost the fast path adds outside its
selected region: `X^p mod f` recomputed for a certificate that fails.

Every fast-path result is checked against the Berlekamp factor multiset before
its time is reported, so a variant that is fast because it is wrong cannot be
reported as fast.

Nothing here is reachable from `Hex.ZPoly.factorize`.
-/

open Lean (Json JsonNumber)
open Hex

namespace HexBench.RootSplitProbe

/-! ## Timing -/

/-- Median of a list of nanosecond observations. -/
private def median (xs : List Nat) : Nat :=
  let sorted := xs.toArray.qsort (· < ·)
  if sorted.size = 0 then 0 else sorted[sorted.size / 2]!

/-- Time one thunk, returning its checksum and the elapsed nanoseconds.

The closing clock read is taken from inside a branch on the computed checksum.
A pure `let` carries no effect, so the compiler is free to sink it past an
unrelated `IO` action; making the second `IO.monoNanosNow` depend on the value
pins the computation inside the measured window. -/
private def timed (f : Unit → UInt64) : IO (UInt64 × Nat) := do
  let t0 ← IO.monoNanosNow
  let v := f ()
  let t1 ← if v == 0 then IO.monoNanosNow else IO.monoNanosNow
  return (v, t1 - t0)

/-- Repeat a timed thunk and keep the median elapsed time. -/
private def timedRepeat (runs : Nat) (f : Unit → UInt64) : IO (UInt64 × Nat) := do
  let mut checksum : UInt64 := 0
  let mut samples : List Nat := []
  for _ in [0:runs] do
    let (v, dt) ← timed f
    checksum := v
    samples := dt :: samples
  return (checksum, median samples)

/-! ## Checksums -/

variable {p : Nat} [ZMod64.Bounds p]

/-- Order-independent checksum of a residue. -/
private def residueChecksum (c : ZMod64 p) : UInt64 :=
  c.val * 2654435761 + 1013904223

/-- Order-independent checksum of a polynomial's coefficients. -/
private def polyChecksum (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc c => acc * 1099511628211 + c.val + 1) 14695981039346656037

/-- Order-independent checksum of a factor list: the product of the per-factor
checksums, so a permuted factor list checksums the same. -/
private def factorsChecksum (fs : List (FpPoly p)) : UInt64 :=
  fs.foldl (fun acc g => acc * (polyChecksum g ||| 1)) 1

/-! ## The candidate fast path

These are the two executable pieces the production path would use. They are
written here exactly as they would be written in `HexBerlekamp`, so the
measurement prices the real thing. -/

/-- The roots of `f` in `F_p`, in canonical residue order. -/
def rootScan (f : FpPoly p) : List (ZMod64 p) :=
  (ZMod64.values p).filter fun c => DensePoly.evalImpl f c == 0

/-- The monic linear factors attached to a list of residues. -/
def linearFactors (roots : List (ZMod64 p)) : List (FpPoly p) :=
  roots.map fun c => FpPoly.X - FpPoly.C c

/-- The complete-splitting certificate: `X^p mod f = X`. -/
def splitsCompletely (f : FpPoly p) (hmonic : DensePoly.Monic f) : Bool :=
  FpPoly.frobeniusXMod f hmonic == FpPoly.X

/-! ## Input construction -/

/-- Monic product of the linear factors of a residue list. -/
def productOfRoots (roots : List (ZMod64 p)) : FpPoly p :=
  roots.foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) 1

/-- A deterministic linear-congruential residue stream. -/
private def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % (2 ^ 61)

/-- `n` distinct residues drawn deterministically from `F_p` (requires `n ≤ p`). -/
def distinctResidues (p : Nat) [ZMod64.Bounds p] (n seed : Nat) : List (ZMod64 p) :=
  let rec go : Nat → Nat → List Nat → List Nat
    | 0, _, acc => acc
    | fuel + 1, s, acc =>
        if acc.length ≥ n then acc
        else
          let s' := lcg s
          let c := s' % p
          if acc.contains c then go fuel s' acc else go fuel s' (c :: acc)
  (go (200 * n + 4000) seed []).map (fun v => ZMod64.ofNat p v)

/-- The Wilkinson image `∏_{i=1}^{n} (X - i)` over `F_p`. -/
def wilkinsonImage (p : Nat) [ZMod64.Bounds p] (n : Nat) : FpPoly p :=
  productOfRoots ((List.range n).map fun i => ZMod64.ofNat p (i + 1))

/-- A deterministic monic polynomial of degree `d`, generically not fully split. -/
def genericMonic (p : Nat) [ZMod64.Bounds p] (d seed : Nat) : FpPoly p :=
  let coeffs := (List.range d).map fun i =>
    ZMod64.ofNat p ((Nat.rec (motive := fun _ => Nat) seed (fun _ s => lcg s) (i + 1)) % p)
  DensePoly.ofList (coeffs ++ [(1 : ZMod64 p)])

/-! ## One measured case -/

/-- A prime modulus carried with its `Bounds` and primality witnesses. -/
structure PrimeCase where
  /-- The prime modulus. -/
  p : Nat
  /-- The small-modulus bound instance. -/
  [bounds : ZMod64.Bounds p]
  /-- The primality witness. -/
  prime : Nat.Prime p

/-- Build a `PrimeCase` from a prime below `2 ^ 31`, or fail loudly. -/
def primeCase? (p : Nat) : Option PrimeCase :=
  if hprime : Hex.Nat.isPrimeTrial p = true then
    if hbound : p < 2 ^ 31 then
      let prime := Hex.Nat.isPrimeTrial_isPrime hprime
      some { p, bounds := { pPos := prime.pos, pLtR := hbound }, prime }
    else none
  else none

/-- A named measurement input, described by the polynomial and its modulus. -/
structure Case where
  /-- Row name in the emitted record. -/
  name : String
  /-- Input family, for grouping in the analysis. -/
  family : String
  /-- The prime modulus. -/
  prime : Nat
  /-- How to build the modular polynomial at that modulus. -/
  build : (q : Nat) → [ZMod64.Bounds q] → FpPoly q

private def natJson (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

/-- Price one case at a resolved prime modulus. -/
private def measureAt (runs : Nat) (c : Case) (pc : PrimeCase) : IO Json :=
  letI := pc.bounds
  letI : ZMod64.PrimeModulus pc.p := ZMod64.primeModulusOfPrime pc.prime
  do
  let f : FpPoly pc.p := c.build pc.p
  if hlead : DensePoly.leadingCoeff f = (1 : ZMod64 pc.p) then
    have hmonic : DensePoly.Monic f := hlead
    -- Certificate ingredient.
    let frob ← timedRepeat runs fun _ => polyChecksum (FpPoly.frobeniusXMod f hmonic)
    let certified := splitsCompletely f hmonic
    -- Root scan.
    let scan ← timedRepeat runs fun _ =>
      (rootScan f).foldl (fun acc c => acc * 31 + residueChecksum c) 7
    let roots := rootScan f
    -- Extraction.
    let extract ← timedRepeat runs fun _ =>
      factorsChecksum (linearFactors (rootScan f))
    -- Production path.
    let berlekamp ← timedRepeat runs fun _ =>
      factorsChecksum (Berlekamp.berlekampFactor f hmonic).factors
    let berlekampCount := (Berlekamp.berlekampFactor f hmonic).factors.length
    let agree := certified && extract.1 == berlekamp.1
    return Json.mkObj
      [ ("name", Json.str c.name),
        ("family", Json.str c.family),
        ("prime", natJson pc.p),
        ("degree", natJson (f.size - 1)),
        ("certified", Json.bool certified),
        ("rootCount", natJson roots.length),
        ("berlekampFactorCount", natJson berlekampCount),
        ("agree", Json.bool agree),
        ("frobeniusNanos", natJson frob.2),
        ("scanNanos", natJson scan.2),
        ("extractNanos", natJson extract.2),
        ("fastTotalNanos", natJson (frob.2 + extract.2)),
        ("berlekampNanos", natJson berlekamp.2) ]
  else
    return Json.mkObj [("name", Json.str c.name), ("error", Json.str "input not monic")]

/-- Price one case: certificate, scan, extraction, and the production path. -/
def measure (runs : Nat) (c : Case) : IO Json := do
  match primeCase? c.prime with
  | none => return Json.mkObj [("name", Json.str c.name), ("error", Json.str "not a small prime")]
  | some pc => measureAt runs c pc

/-! ## The measured grid -/

/-- Smallest prime strictly greater than `n`, searched by trial division. -/
private partial def nextPrime (n : Nat) : Nat :=
  let rec go (k : Nat) : Nat := if Hex.Nat.isPrimeTrial k then k else go (k + 1)
  go (n + 1)

/-- Wilkinson rows over the primes the production planner selects for them. -/
private def wilkinsonCases : List Case :=
  [ { name := "wilkinson_40@47", family := "wilkinson", prime := 47,
      build := fun q => wilkinsonImage q 40 },
    { name := "wilkinson_40@41", family := "wilkinson", prime := 41,
      build := fun q => wilkinsonImage q 40 },
    { name := "wilkinson_48@61", family := "wilkinson", prime := 61,
      build := fun q => wilkinsonImage q 48 },
    { name := "wilkinson_48@53", family := "wilkinson", prime := 53,
      build := fun q => wilkinsonImage q 48 },
    { name := "wilkinson_56@67", family := "wilkinson", prime := 67,
      build := fun q => wilkinsonImage q 56 },
    { name := "wilkinson_56@59", family := "wilkinson", prime := 59,
      build := fun q => wilkinsonImage q 56 } ]

/-- Synthetic fully split inputs across degree and field size. -/
private def splitCases : List Case :=
  ((([8, 16, 32, 64, 128] : List Nat).flatMap fun d =>
      (([1, 2, 4, 16, 64, 256] : List Nat)).map fun mult =>
        let q := nextPrime (d * mult)
        ({ name := s!"split_d{d}_p{q}", family := "split", prime := q,
           build := fun r => productOfRoots (distinctResidues r d (1234567 + d * 7 + q)) } : Case)))

/-- Fully split inputs whose field is far too large for a residue scan. -/
private def wideFieldCases : List Case :=
  (([10007, 100003, 1000003] : List Nat)).flatMap fun q =>
    (([4, 16] : List Nat)).map fun d =>
      ({ name := s!"split_d{d}_p{q}", family := "wide-field", prime := q,
         build := fun r => productOfRoots (distinctResidues r d (99991 + d + q)) } : Case)

/-- Mixed-degree and irreducible controls: the certificate must reject these. -/
private def controlCases : List Case :=
  (([16, 32, 64] : List Nat)).flatMap fun d =>
    (([67, 1009] : List Nat)).map fun q =>
      ({ name := s!"generic_d{d}_p{q}", family := "control", prime := q,
         build := fun r => genericMonic r d (271828 + d * 13 + q) } : Case)

/-- Controls sitting just inside the `25 * p ≤ (deg f)^2` scan budget: these are
the inputs that pay a scan and then fall back, so they bound the overhead the
budget admits. -/
private def boundaryControlCases : List Case :=
  (([(16, 7), (32, 37), (64, 163), (128, 653), (240, 2297)] : List (Nat × Nat))).map
    fun dq =>
      ({ name := s!"boundary_d{dq.1}_p{dq.2}", family := "boundary", prime := dq.2,
         build := fun r => genericMonic r dq.1 (31337 + dq.1 * 11 + dq.2) } : Case)

/-- Every measured case, in emission order. -/
def allCases : List Case :=
  wilkinsonCases ++ splitCases ++ wideFieldCases ++ controlCases ++ boundaryControlCases

/-- Entry point: measure every case and print one JSON record. -/
def main (args : List String) : IO UInt32 := do
  let runs := (args.head?.bind (·.toNat?)).getD 5
  let mut rows : Array Json := #[]
  for c in allCases do
    rows := rows.push (← measure runs c)
  let record := Json.mkObj
    [ ("schema", Json.str "hexbz-root-split-probe/1"),
      ("runs", natJson runs),
      ("rows", Json.arr rows) ]
  IO.println record.pretty
  return 0

end HexBench.RootSplitProbe

/-- Driver entry point. -/
def main (args : List String) : IO UInt32 :=
  HexBench.RootSplitProbe.main args
