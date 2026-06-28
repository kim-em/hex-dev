import Hex.BenchOracle.Flint
import HexHensel.Multifactor
import HexHensel.Quadratic
import HexHensel.QuadraticMultifactor
import LeanBench

/-!
Benchmark registrations for `hex-hensel`.

This Phase 4 infrastructure slice measures the executable conversion operations,
linear and quadratic Hensel lift steps, and the ordered multifactor helpers.
Inputs are deterministic and use the fixed small prime `5`; timed targets
return compact checksums of the computed polynomial data.

Scientific registrations:

* `runModPChecksum`: coefficient reduction from `Z[x]` to `F_5[x]`, `O(n)`.
* `runLiftToZChecksum`: canonical lift from `F_5[x]` to `Z[x]`, `O(n)`.
* `runReduceModPowChecksum`: coefficient reduction modulo `5^k`, `O(n)`.
* `runLinearHenselStepChecksum`: one linear Hensel correction, `O(n^2)`.
* `runHenselLiftChecksum`: iterative linear lift over `(n, k)`, `O(n^2 k)`.
* `runQuadraticHenselStepChecksum`: one quadratic Hensel correction, `O(n^2)`.
* `runPolyProductChecksum`: ordered product of `n` linear factors, `O(n^2)`.
* `runMultifactorLiftChecksum`: two-factor ordered lift over `(n, k)`,
  `O(n^2 k)`.
* `runMultifactorLiftQuadraticChecksum`: production quadratic multifactor lift,
  `O(n^2 log k)`.

Compare groups:

* `compare runMultifactorLiftChecksum runMultifactorLiftQuadraticChecksum`
  checks the linear and quadratic multifactor lifters on the shared encoded
  `(n, k)` fixture schedule.

Informational external comparators (FLINT `nmod_poly_hensel_lift_*` via the
shared persistent-subprocess python-flint driver, per
`SPEC/Libraries/hex-hensel.md §"External comparators"` and
`SPEC/benchmarking.md §"External comparators" §"Process call"`):

* `runFlintLinearHenselStepChecksum*` ↔ `runLinearHenselStepChecksum*`
  (`nmod_poly_hensel.lift_once` at `k = 1`).
* `runFlintHenselLiftChecksum*` ↔ `runHenselLiftChecksum*`
  (`nmod_poly_hensel.lift` to `target_k = input.k`).
* `runFlintQuadraticHenselStepChecksum*` ↔ `runQuadraticHenselStepChecksum*`
  (`nmod_poly_hensel.lift_once` at `k = 1`, Bezout pair computed inside the
  driver to match Hex's `(s, t) = (0, 1)` seed).
* `runFlintMultifactorLiftChecksum*` ↔ `runMultifactorLiftChecksum*`
  (`nmod_poly_hensel.lift` to `target_k = input.k` on the two-factor fixture).
* `runFlintMultifactorLiftQuadraticChecksum*` ↔
  `runMultifactorLiftQuadraticChecksum*` (same FLINT call; both Hex targets
  share the encoded `(n, k)` fixture and reach the same lifted factorisation
  mod `p^k`).

Pairings span the Hensel-lift bench targets only — the conversion operations
(`runModPChecksum`, `runLiftToZChecksum`, `runReduceModPowChecksum`) and the
ordered linear product (`runPolyProductChecksum`) are not Hensel-lift work and
have no comparable FLINT entry point.

Hex's lifted factors are reduced via `reduceModPow` to non-negative residues in
`[0, p^k)`; the FLINT driver returns centred residues in `(-p^k/2, p^k/2]`. The
two checksum streams therefore diverge by representation choice and are
recorded independently for stability — the informational verdict tracks wall
times only.
-/

namespace Hex
namespace HenselBench

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

instance : Hashable ZPoly where
  hash p := hash p.toArray

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (FpPoly p) where
  hash f := hash f.toArray

/-- Prepared input for the conversion-operation benchmarks. -/
structure BridgeInput where
  zpoly : ZPoly
  fpoly : FpPoly 5
  deriving Hashable

/-- Prepared input for one linear Hensel step and the iterative wrapper. -/
structure LinearInput where
  k : Nat := 3
  f : ZPoly
  g : ZPoly
  h : ZPoly
  s : FpPoly 5
  t : FpPoly 5
  deriving Hashable

/-- Prepared input for one quadratic Hensel step. -/
structure QuadraticInput where
  f : ZPoly
  g : ZPoly
  h : ZPoly
  s : ZPoly
  t : ZPoly
  deriving Hashable

/-- Prepared input for ordered multifactor helpers. -/
structure MultifactorInput where
  k : Nat := 3
  f : ZPoly
  factors : Array ZPoly
  deriving Hashable

/-- Encoding scale for benchmark parameters that vary both degree `n` and precision `k`. -/
def liftParamScale : Nat :=
  1000

/-- Encode a degree/precision pair as the single `Nat` parameter accepted by lean-bench. -/
def encodeLiftParam (n k : Nat) : Nat :=
  n * liftParamScale + k

/-- Decode the degree component from an encoded lift benchmark parameter. -/
def liftBenchDegree (param : Nat) : Nat :=
  param / liftParamScale

/-- Decode the requested precision component from an encoded lift benchmark parameter. -/
def liftBenchPrecision (param : Nat) : Nat :=
  param % liftParamScale

/-- Textbook cost model for linear lifting over encoded `(n, k)` parameters. -/
def liftLinearComplexity (param : Nat) : Nat :=
  let n := liftBenchDegree param
  let k := liftBenchPrecision param
  n * n * k

/-- Textbook cost model for quadratic lifting over encoded `(n, k)` parameters. -/
def liftQuadraticComplexity (param : Nat) : Nat :=
  let n := liftBenchDegree param
  let k := liftBenchPrecision param
  n * n * Nat.log2 (k + 1)

/-- Deterministic integer coefficient generator keyed by size, index, and salt. -/
def zCoeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 3) * (salt + 19) + (i + 1) * (i + 5) * 11 + n * 37) % 997
  let value := Int.ofNat (raw + 1)
  if (i + salt) % 2 = 0 then value else -value

/-- Deterministic `F_5` coefficient generator keyed by size, index, and salt. -/
def fpCoeffValue (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 7) + (i + 5) * (i + 9) * 3 + n * 13) % 5

/-- Deterministic dense integer polynomial with `n` generated coefficients. -/
def denseZPoly (n salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => zCoeffValue n i salt

/-- Deterministic dense `F_5` polynomial with `n` generated coefficients. -/
def denseFpPoly (n salt : Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i => fpCoeffValue n i salt

/-- Deterministic monic integer linear factor. -/
def linearZFactor (salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs #[Int.ofNat ((salt % 4) + 1), 1]

/-- Deterministic monic `F_5` linear factor. -/
def linearFpFactor (salt : Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs #[fpCoeffValue 1 0 salt, 1]

/-- Stable checksum for integer-polynomial benchmark results. -/
def checksumZPoly (f : ZPoly) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for finite-field-polynomial benchmark results. -/
def checksumFpPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for an ordered array of integer polynomials. -/
def checksumZPolyArray (polys : Array ZPoly) : UInt64 :=
  polys.foldl (fun acc f => mixHash acc (checksumZPoly f)) 0

/-- Per-parameter fixture for conversion operations. -/
def prepBridgeInput (n : Nat) : BridgeInput :=
  { zpoly := denseZPoly n 17
    fpoly := denseFpPoly n 23 }

/-- Per-parameter fixture for linear Hensel operations.

The factor error is built as a multiple of `5`, so the correction path is
nontrivial while staying deterministic. The Bezout pair is computed via
`normalizedXGCD` so that `s * gMod + t * hMod ≡ 1 (mod 5)`; the iterative
linear lift relies on this precondition to keep the corrected `h` factor
bounded in degree across all `k` steps. The shared salts `59 / 62 / 67`
match `prepMultifactorLiftInput`, which already verifies coprimeness on
the full scientific `n` ladder including `n = 192`.
-/
def prepLinearInput (n : Nat) : LinearInput :=
  let g := linearZFactor 59
  let h := denseZPoly (n + 1) 62
  let e := denseZPoly (n + 1) 67
  let f := g * h + DensePoly.scale (5 : Int) e
  let xgcd := ZPoly.normalizedXGCD 5 g h
  { f := f
    g := g
    h := h
    s := xgcd.left
    t := xgcd.right }

/-- Encoded `(n, k)` fixture for iterative linear Hensel lift benchmarks. -/
def prepLinearLiftInput (param : Nat) : LinearInput :=
  { prepLinearInput (liftBenchDegree param) with
    k := liftBenchPrecision param }

/-- Per-parameter fixture for quadratic Hensel operations. -/
def prepQuadraticInput (n : Nat) : QuadraticInput :=
  let g := linearZFactor 43
  let h := denseZPoly (n + 1) 47
  let e := denseZPoly (n + 1) 53
  let f := g * h + DensePoly.scale (5 : Int) e
  { f := f
    g := g
    h := h
    s := 0
    t := 1 }

/-- Per-parameter fixture for the ordered product of many small factors. -/
def prepProductInput (n : Nat) : MultifactorInput :=
  let factors := (Array.range n).map linearZFactor
  { f := Array.polyProduct factors
    factors := factors }

/-- Per-parameter fixture for the two-factor multifactor lifting path. -/
def prepMultifactorLiftInput (n : Nat) : MultifactorInput :=
  let g := linearZFactor 59
  -- Salt 62 keeps `h` coprime to `g` modulo 5 across the scientific ladder.
  let h := denseZPoly (n + 1) 62
  let factors := #[g, h]
  let e := denseZPoly (n + 1) 67
  { f := Array.polyProduct factors + DensePoly.scale (5 : Int) e
    factors := factors }

/-- Encoded `(n, k)` fixture for iterative multifactor lift benchmarks. -/
def prepMultifactorLiftPrecisionInput (param : Nat) : MultifactorInput :=
  { prepMultifactorLiftInput (liftBenchDegree param) with
    k := liftBenchPrecision param }

/-- Benchmark target: reduce integer coefficients modulo `5`. -/
def runModPChecksum (input : BridgeInput) : UInt64 :=
  checksumFpPoly <| ZPoly.modP 5 input.zpoly

/-- Benchmark target: lift `F_5` coefficients to canonical integer representatives. -/
def runLiftToZChecksum (input : BridgeInput) : UInt64 :=
  checksumZPoly <| FpPoly.liftToZ input.fpoly

/-- Benchmark target: reduce integer coefficients modulo `5^3`. -/
def runReduceModPowChecksum (input : BridgeInput) : UInt64 :=
  checksumZPoly <| ZPoly.reduceModPow input.zpoly 5 3

/-- Benchmark target: one linear Hensel correction step. -/
def runLinearHenselStepChecksum (input : LinearInput) : UInt64 :=
  let r := ZPoly.linearHenselStep 5 1 input.f input.g input.h input.s input.t
  mixHash (checksumZPoly r.g) (checksumZPoly r.h)

/-- Benchmark target: fixed-precision iterative linear Hensel lift. -/
def runHenselLiftChecksum (input : LinearInput) : UInt64 :=
  let r := ZPoly.henselLift 5 input.k input.f input.g input.h input.s input.t
  mixHash (checksumZPoly r.g) (checksumZPoly r.h)

/-- Benchmark target: one quadratic Hensel correction step. -/
def runQuadraticHenselStepChecksum (input : QuadraticInput) : UInt64 :=
  let r := ZPoly.quadraticHenselStep 5 input.f input.g input.h input.s input.t
  mixHash (mixHash (checksumZPoly r.g) (checksumZPoly r.h))
    (mixHash (checksumZPoly r.s) (checksumZPoly r.t))

/-- Benchmark target: ordered product of prepared integer-polynomial factors. -/
def runPolyProductChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPoly <| Array.polyProduct input.factors

/-- Benchmark target: ordered multifactor lift of two prepared factors. -/
def runMultifactorLiftChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPolyArray <| ZPoly.multifactorLift 5 input.k input.f input.factors

/-- Benchmark target: production quadratic ordered multifactor lift. -/
def runMultifactorLiftQuadraticChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPolyArray <| ZPoly.multifactorLiftQuadratic 5 input.k input.f input.factors

/-! ## FLINT `nmod_poly_hensel_lift_*` informational comparator surfaces

Each of the five Hensel-lift Hex targets is paired with a corresponding
call into the shared persistent-subprocess python-flint driver
(`scripts/oracle/flint_bench_driver.py`, HO-20) via
`Hex.BenchOracle.Flint.runOp` on the `nmod_poly_hensel` family. Hex normalises
lifted factors to non-negative residues in `[0, p^k)` while the driver returns
centred residues in `(-p^k/2, p^k/2]`; the comparator checksum is computed
directly on the FLINT-returned coefficient list and is therefore not expected
to equal the Hex-side checksum at the same rung. The comparator is
`informational` per `SPEC/Libraries/hex-hensel.md §"External comparators"`,
so the headline report records wall-times only. -/

/-- Stable checksum over an integer coefficient list returned by FLINT. The
list is consumed in the order the driver supplies. -/
def checksumIntCoeffs (coeffs : List Int) : UInt64 :=
  coeffs.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Encode a `ZPoly` as a JSON coefficient list (ascending degree). -/
def zPolyToFlintJson (p : ZPoly) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson p.toArray.toList

/-- Encode an `FpPoly 5` as a JSON coefficient list (ascending degree) over
non-negative integer representatives in `[0, 5)`. -/
def fpPolyFiveToFlintJson (f : FpPoly 5) : Lean.Json :=
  Hex.BenchOracle.Flint.intsToJson <|
    f.toArray.toList.map fun coeff => Int.ofNat coeff.toNat

/-- Read the FLINT `lift_once` / `lift` reply object `{G, H, ...}` and return
a stable checksum over the centred-residue coefficient lists `G` then `H`. -/
def checksumFlintLiftReply (reply : Lean.Json) : IO UInt64 := do
  let gJson ←
    match reply.getObjVal? "G" with
    | Except.ok v => pure v
    | Except.error msg => throw <| IO.userError s!"FLINT lift reply missing G: {msg}"
  let hJson ←
    match reply.getObjVal? "H" with
    | Except.ok v => pure v
    | Except.error msg => throw <| IO.userError s!"FLINT lift reply missing H: {msg}"
  let gCoeffs ← Hex.BenchOracle.Flint.jsonToInts gJson
  let hCoeffs ← Hex.BenchOracle.Flint.jsonToInts hJson
  return mixHash (checksumIntCoeffs gCoeffs) (checksumIntCoeffs hCoeffs)

/-- FLINT comparator: `nmod_poly_hensel.lift_once` for one linear Hensel
step over `p = 5`, `k = 1`. The Hex side performs one linear lift from
`mod 5` to `mod 5^2`; FLINT's `lift_once` is a single Newton-style
doubling, reaching the same `mod 5^2` modulus. Hex provides a Bezout pair
satisfying `s*g + t*h ≡ 1 (mod 5)` via `normalizedXGCD`; the same pair is
forwarded so neither side recomputes it. -/
def runFlintLinearHenselStepChecksum (input : LinearInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly_hensel" "lift_once"
    #[("p", (5 : Lean.Json)), ("k", (1 : Lean.Json)),
      ("f", zPolyToFlintJson input.f),
      ("g", zPolyToFlintJson input.g),
      ("h", zPolyToFlintJson input.h),
      ("s", fpPolyFiveToFlintJson input.s),
      ("t", fpPolyFiveToFlintJson input.t)]
  checksumFlintLiftReply result

/-- FLINT comparator: `nmod_poly_hensel.lift` to `target_k = input.k`. The
Hex side runs `input.k` linear iterations starting from `mod 5`; FLINT
reaches the same `mod 5^k` modulus via `⌈log₂ input.k⌉` quadratic
doublings. -/
def runFlintHenselLiftChecksum (input : LinearInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly_hensel" "lift"
    #[("p", (5 : Lean.Json)), ("k", (1 : Lean.Json)),
      ("target_k", (Lean.Json.num (Lean.JsonNumber.fromNat input.k))),
      ("f", zPolyToFlintJson input.f),
      ("g", zPolyToFlintJson input.g),
      ("h", zPolyToFlintJson input.h),
      ("s", fpPolyFiveToFlintJson input.s),
      ("t", fpPolyFiveToFlintJson input.t)]
  checksumFlintLiftReply result

/-- FLINT comparator: `nmod_poly_hensel.lift_once` for one quadratic step
over `p = 5`, `k = 1`. The Hex `runQuadraticHenselStepChecksum` fixture
seeds `(s, t) = (0, 1)`, which does not satisfy `s*g + t*h ≡ 1 (mod 5)`;
omitting `s`/`t` lets the driver compute a valid Bezout pair internally
via `_bezout_mod_p`, mirroring the Bezout setup work Hex performs from
its degenerate seed. -/
def runFlintQuadraticHenselStepChecksum (input : QuadraticInput) : IO UInt64 := do
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly_hensel" "lift_once"
    #[("p", (5 : Lean.Json)), ("k", (1 : Lean.Json)),
      ("f", zPolyToFlintJson input.f),
      ("g", zPolyToFlintJson input.g),
      ("h", zPolyToFlintJson input.h)]
  checksumFlintLiftReply result

/-- FLINT comparator: `nmod_poly_hensel.lift` for the two-factor linear
multifactor lift. The `MultifactorInput` fixture always carries
`#[g, h]`, so the driver's two-factor lift API matches the Hex
registration exactly. -/
def runFlintMultifactorLiftChecksum (input : MultifactorInput) : IO UInt64 := do
  let (g, h) ←
    match input.factors with
    | #[g, h] => pure (g, h)
    | _ =>
        throw <| IO.userError s!"FLINT multifactor lift expects two factors, got {input.factors.size}"
  let result ← Hex.BenchOracle.Flint.runOp "nmod_poly_hensel" "lift"
    #[("p", (5 : Lean.Json)), ("k", (1 : Lean.Json)),
      ("target_k", (Lean.Json.num (Lean.JsonNumber.fromNat input.k))),
      ("f", zPolyToFlintJson input.f),
      ("g", zPolyToFlintJson g),
      ("h", zPolyToFlintJson h)]
  checksumFlintLiftReply result

/-- FLINT comparator for the production quadratic multifactor lifter. Both
Hex multifactor targets reach the same `mod p^k` factorisation on the
same fixture, so the FLINT call is identical to
`runFlintMultifactorLiftChecksum`; the pair is recorded separately so the
two Hex strategies can each report their own ratio against the FLINT
reference. -/
def runFlintMultifactorLiftQuadraticChecksum
    (input : MultifactorInput) : IO UInt64 :=
  runFlintMultifactorLiftChecksum input

/-! Per-rung wrappers for paired fixed-benchmark registrations. Each
`runFooAt n` (or `param`) calls the Hex target on the prepared fixture;
each `runFlintFooAt` calls the FLINT comparator on the same fixture so
wall-times are comparable in the same harness. -/

def runLinearHenselStepChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runLinearHenselStepChecksum (prepLinearInput n)
def runFlintLinearHenselStepChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintLinearHenselStepChecksum (prepLinearInput n)

def runHenselLiftChecksumAt (param : Nat) : Unit → IO UInt64 := fun _ =>
  return runHenselLiftChecksum (prepLinearLiftInput param)
def runFlintHenselLiftChecksumAt (param : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintHenselLiftChecksum (prepLinearLiftInput param)

def runQuadraticHenselStepChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  return runQuadraticHenselStepChecksum (prepQuadraticInput n)
def runFlintQuadraticHenselStepChecksumAt (n : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintQuadraticHenselStepChecksum (prepQuadraticInput n)

def runMultifactorLiftChecksumAt (param : Nat) : Unit → IO UInt64 := fun _ =>
  return runMultifactorLiftChecksum (prepMultifactorLiftPrecisionInput param)
def runFlintMultifactorLiftChecksumAt (param : Nat) : Unit → IO UInt64 := fun _ =>
  runFlintMultifactorLiftChecksum (prepMultifactorLiftPrecisionInput param)

def runMultifactorLiftQuadraticChecksumAt (param : Nat) : Unit → IO UInt64 :=
    fun _ =>
  return runMultifactorLiftQuadraticChecksum (prepMultifactorLiftPrecisionInput param)
def runFlintMultifactorLiftQuadraticChecksumAt (param : Nat) :
    Unit → IO UInt64 := fun _ =>
  runFlintMultifactorLiftQuadraticChecksum (prepMultifactorLiftPrecisionInput param)

/-! Per-rung concrete bindings used by `setup_fixed_benchmark`. The rung
ladders pick six points inside each Hex registration's eligible
parameter range so the headline report records the ratio's shape
across the range. -/

-- Linear Hensel step: `n` in `[64, 512]`, six rungs.
def runLinearHenselStep64 : Unit → IO UInt64 := runLinearHenselStepChecksumAt 64
def runFlintLinearHenselStep64 : Unit → IO UInt64 := runFlintLinearHenselStepChecksumAt 64
def runLinearHenselStep128 : Unit → IO UInt64 := runLinearHenselStepChecksumAt 128
def runFlintLinearHenselStep128 : Unit → IO UInt64 := runFlintLinearHenselStepChecksumAt 128
def runLinearHenselStep192 : Unit → IO UInt64 := runLinearHenselStepChecksumAt 192
def runFlintLinearHenselStep192 : Unit → IO UInt64 := runFlintLinearHenselStepChecksumAt 192
def runLinearHenselStep256 : Unit → IO UInt64 := runLinearHenselStepChecksumAt 256
def runFlintLinearHenselStep256 : Unit → IO UInt64 := runFlintLinearHenselStepChecksumAt 256
def runLinearHenselStep384 : Unit → IO UInt64 := runLinearHenselStepChecksumAt 384
def runFlintLinearHenselStep384 : Unit → IO UInt64 := runFlintLinearHenselStepChecksumAt 384
def runLinearHenselStep512 : Unit → IO UInt64 := runLinearHenselStepChecksumAt 512
def runFlintLinearHenselStep512 : Unit → IO UInt64 := runFlintLinearHenselStepChecksumAt 512

-- Quadratic Hensel step: `n` in `[64, 512]`, six rungs.
def runQuadraticHenselStep64 : Unit → IO UInt64 := runQuadraticHenselStepChecksumAt 64
def runFlintQuadraticHenselStep64 : Unit → IO UInt64 := runFlintQuadraticHenselStepChecksumAt 64
-- n = 128 is skipped: the QuadraticInput fixture at that size has
-- `gcd(g, h) ≠ 1 (mod 5)`, which violates the FLINT Hensel-lift Bezout
-- precondition the driver checks. The closest n above 128 with coprime
-- fixture is n = 160.
def runQuadraticHenselStep160 : Unit → IO UInt64 := runQuadraticHenselStepChecksumAt 160
def runFlintQuadraticHenselStep160 : Unit → IO UInt64 := runFlintQuadraticHenselStepChecksumAt 160
def runQuadraticHenselStep192 : Unit → IO UInt64 := runQuadraticHenselStepChecksumAt 192
def runFlintQuadraticHenselStep192 : Unit → IO UInt64 := runFlintQuadraticHenselStepChecksumAt 192
def runQuadraticHenselStep256 : Unit → IO UInt64 := runQuadraticHenselStepChecksumAt 256
def runFlintQuadraticHenselStep256 : Unit → IO UInt64 := runFlintQuadraticHenselStepChecksumAt 256
def runQuadraticHenselStep384 : Unit → IO UInt64 := runQuadraticHenselStepChecksumAt 384
def runFlintQuadraticHenselStep384 : Unit → IO UInt64 := runFlintQuadraticHenselStepChecksumAt 384
def runQuadraticHenselStep512 : Unit → IO UInt64 := runQuadraticHenselStepChecksumAt 512
def runFlintQuadraticHenselStep512 : Unit → IO UInt64 := runFlintQuadraticHenselStepChecksumAt 512

-- Encoded `(n, k)` parameters reused across the iterative linear lift and the
-- two-factor multifactor lifters. The python-flint driver emulates the Hensel
-- lift via `fmpz_poly` arithmetic (HO-20 wiring, see
-- `scripts/oracle/flint_bench_driver.py` docstring); coefficient size doubles
-- per Newton step, so intermediate `fmpz_poly` operands blow up dramatically
-- once `target_k ≥ 12` at moderate `n`. Empirical measurement (carica, Apple M2
-- Ultra, fresh driver per call) shows the driver process consuming > 1 GB at
-- `(n = 32, k = 16)` and > 10 GB at `(n = 128, k = 16)`; the matching Hex
-- scientific parametric ladder runs to `(192, 64)` because Hex's coefficient
-- representation stays bounded. The FLINT comparator pair therefore cannot
-- mirror the full Hex schedule; the six paired rungs sit at `k = 8` with `n`
-- varying so the iterated-lift trend can be read against the per-call FLINT
-- driver floor.
def encLift32_8 : Nat := encodeLiftParam 32 8
def encLift64_8 : Nat := encodeLiftParam 64 8
def encLift96_8 : Nat := encodeLiftParam 96 8
def encLift128_8 : Nat := encodeLiftParam 128 8
def encLift192_8 : Nat := encodeLiftParam 192 8
def encLift256_8 : Nat := encodeLiftParam 256 8

-- Iterative linear Hensel lift: six rungs at `k = 8` with `n` varying.
def runHenselLift_n32_k8 : Unit → IO UInt64 := runHenselLiftChecksumAt encLift32_8
def runFlintHenselLift_n32_k8 : Unit → IO UInt64 := runFlintHenselLiftChecksumAt encLift32_8
def runHenselLift_n64_k8 : Unit → IO UInt64 := runHenselLiftChecksumAt encLift64_8
def runFlintHenselLift_n64_k8 : Unit → IO UInt64 := runFlintHenselLiftChecksumAt encLift64_8
def runHenselLift_n96_k8 : Unit → IO UInt64 := runHenselLiftChecksumAt encLift96_8
def runFlintHenselLift_n96_k8 : Unit → IO UInt64 := runFlintHenselLiftChecksumAt encLift96_8
def runHenselLift_n128_k8 : Unit → IO UInt64 := runHenselLiftChecksumAt encLift128_8
def runFlintHenselLift_n128_k8 : Unit → IO UInt64 := runFlintHenselLiftChecksumAt encLift128_8
def runHenselLift_n192_k8 : Unit → IO UInt64 := runHenselLiftChecksumAt encLift192_8
def runFlintHenselLift_n192_k8 : Unit → IO UInt64 := runFlintHenselLiftChecksumAt encLift192_8
def runHenselLift_n256_k8 : Unit → IO UInt64 := runHenselLiftChecksumAt encLift256_8
def runFlintHenselLift_n256_k8 : Unit → IO UInt64 := runFlintHenselLiftChecksumAt encLift256_8

-- Two-factor linear multifactor lift: same six rungs as the iterative linear
-- target.
def runMultiLift_n32_k8 : Unit → IO UInt64 := runMultifactorLiftChecksumAt encLift32_8
def runFlintMultiLift_n32_k8 : Unit → IO UInt64 := runFlintMultifactorLiftChecksumAt encLift32_8
def runMultiLift_n64_k8 : Unit → IO UInt64 := runMultifactorLiftChecksumAt encLift64_8
def runFlintMultiLift_n64_k8 : Unit → IO UInt64 := runFlintMultifactorLiftChecksumAt encLift64_8
def runMultiLift_n96_k8 : Unit → IO UInt64 := runMultifactorLiftChecksumAt encLift96_8
def runFlintMultiLift_n96_k8 : Unit → IO UInt64 := runFlintMultifactorLiftChecksumAt encLift96_8
def runMultiLift_n128_k8 : Unit → IO UInt64 := runMultifactorLiftChecksumAt encLift128_8
def runFlintMultiLift_n128_k8 : Unit → IO UInt64 := runFlintMultifactorLiftChecksumAt encLift128_8
def runMultiLift_n192_k8 : Unit → IO UInt64 := runMultifactorLiftChecksumAt encLift192_8
def runFlintMultiLift_n192_k8 : Unit → IO UInt64 := runFlintMultifactorLiftChecksumAt encLift192_8
def runMultiLift_n256_k8 : Unit → IO UInt64 := runMultifactorLiftChecksumAt encLift256_8
def runFlintMultiLift_n256_k8 : Unit → IO UInt64 := runFlintMultifactorLiftChecksumAt encLift256_8

-- Production quadratic multifactor lift: same six rungs.
def runMultiLiftQ_n32_k8 : Unit → IO UInt64 := runMultifactorLiftQuadraticChecksumAt encLift32_8
def runFlintMultiLiftQ_n32_k8 : Unit → IO UInt64 := runFlintMultifactorLiftQuadraticChecksumAt encLift32_8
def runMultiLiftQ_n64_k8 : Unit → IO UInt64 := runMultifactorLiftQuadraticChecksumAt encLift64_8
def runFlintMultiLiftQ_n64_k8 : Unit → IO UInt64 := runFlintMultifactorLiftQuadraticChecksumAt encLift64_8
def runMultiLiftQ_n96_k8 : Unit → IO UInt64 := runMultifactorLiftQuadraticChecksumAt encLift96_8
def runFlintMultiLiftQ_n96_k8 : Unit → IO UInt64 := runFlintMultifactorLiftQuadraticChecksumAt encLift96_8
def runMultiLiftQ_n128_k8 : Unit → IO UInt64 := runMultifactorLiftQuadraticChecksumAt encLift128_8
def runFlintMultiLiftQ_n128_k8 : Unit → IO UInt64 := runFlintMultifactorLiftQuadraticChecksumAt encLift128_8
def runMultiLiftQ_n192_k8 : Unit → IO UInt64 := runMultifactorLiftQuadraticChecksumAt encLift192_8
def runFlintMultiLiftQ_n192_k8 : Unit → IO UInt64 := runFlintMultifactorLiftQuadraticChecksumAt encLift192_8
def runMultiLiftQ_n256_k8 : Unit → IO UInt64 := runMultifactorLiftQuadraticChecksumAt encLift256_8
def runFlintMultiLiftQ_n256_k8 : Unit → IO UInt64 := runFlintMultifactorLiftQuadraticChecksumAt encLift256_8

/-
Coefficient reduction maps each of the `n` dense integer coefficients once and
then normalizes the result, so the conversion operation has linear cost.
-/
setup_benchmark runModPChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Canonical lifting maps each of the `n` finite-field coefficients to its
integer representative and normalizes the dense result, giving linear cost.
-/
setup_benchmark runLiftToZChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Reduction modulo a fixed power `5^3` performs one bounded integer reduction per
dense coefficient followed by normalization, so the model is linear in `n`.
-/
setup_benchmark runReduceModPowChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The linear step performs dense arithmetic against degree-`n` inputs, including
a correction product whose operands both grow linearly with the fixture size.
-/
setup_benchmark runLinearHenselStepChecksum n => n * n
  with prep := prepLinearInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The wrapper performs `k` linear correction steps over degree-`n` dense inputs;
the single lean-bench parameter encodes `(n, k)` as `n * 1000 + k`, including
Mignotte-sized precisions such as `42` on the scientific schedule.
-/
setup_benchmark runHenselLiftChecksum param => liftLinearComplexity param
  with prep := prepLinearLiftInput
  where {
    paramFloor := encodeLiftParam 32 4
    paramCeiling := encodeLiftParam 192 64
    paramSchedule := .custom #[
      encodeLiftParam 32 4,
      encodeLiftParam 32 16,
      encodeLiftParam 32 42,
      encodeLiftParam 64 16,
      encodeLiftParam 64 42,
      encodeLiftParam 96 42,
      encodeLiftParam 128 64,
      encodeLiftParam 192 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The quadratic step performs dense factor and Bezout correction products over
degree-`n` fixtures while the requested modulus size is fixed.
-/
setup_benchmark runQuadraticHenselStepChecksum n => n * n
  with prep := prepQuadraticInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Left-folding `n` linear factors grows the accumulator degree one step at a
time, giving a quadratic total number of coefficient operations.
-/
setup_benchmark runPolyProductChecksum n => n * n
  with prep := prepProductInput
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This two-factor fixture exercises the public ordered lift helper over encoded
`(n, k)` parameters; the linear delegated Hensel lift repeats a quadratic
dense-polynomial correction `k` times.
-/
setup_benchmark runMultifactorLiftChecksum param => liftLinearComplexity param
  with prep := prepMultifactorLiftPrecisionInput
  where {
    paramFloor := encodeLiftParam 32 4
    paramCeiling := encodeLiftParam 192 64
    paramSchedule := .custom #[
      encodeLiftParam 32 4,
      encodeLiftParam 32 16,
      encodeLiftParam 32 42,
      encodeLiftParam 64 16,
      encodeLiftParam 64 42,
      encodeLiftParam 96 42,
      encodeLiftParam 128 64,
      encodeLiftParam 192 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The production path shares the encoded `(n, k)` fixture with the linear lifter,
but its binary lift uses only `ceil(log₂ k)` quadratic-doubling steps; the
factor/Bezout correction products dominate each step.
-/
setup_benchmark runMultifactorLiftQuadraticChecksum param => liftQuadraticComplexity param
  with prep := prepMultifactorLiftPrecisionInput
  where {
    paramFloor := encodeLiftParam 32 4
    paramCeiling := encodeLiftParam 192 64
    paramSchedule := .custom #[
      encodeLiftParam 32 4,
      encodeLiftParam 32 16,
      encodeLiftParam 32 42,
      encodeLiftParam 64 16,
      encodeLiftParam 64 42,
      encodeLiftParam 96 42,
      encodeLiftParam 128 64,
      encodeLiftParam 192 64]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-! ## FLINT `nmod_poly_hensel_lift_*` informational comparator fixed registrations

Each Hensel-lift Lean target is paired with the matching FLINT
`nmod_poly_hensel` op via the shared persistent-subprocess driver. The pairs
are registered as `setup_fixed_benchmark` rungs at the same parameter inside
the existing eligible parametric range, six rungs per pair, so the headline
report records raw and overhead-adjusted ratios at each rung and a trend
across the ladder. The comparator is `informational` per
`SPEC/Libraries/hex-hensel.md §"External comparators"`. -/

setup_fixed_benchmark runLinearHenselStep64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintLinearHenselStep64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runLinearHenselStep128 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintLinearHenselStep128 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runLinearHenselStep192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintLinearHenselStep192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runLinearHenselStep256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintLinearHenselStep256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runLinearHenselStep384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintLinearHenselStep384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runLinearHenselStep512 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintLinearHenselStep512 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runQuadraticHenselStep64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintQuadraticHenselStep64 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runQuadraticHenselStep160 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintQuadraticHenselStep160 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runQuadraticHenselStep192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintQuadraticHenselStep192 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runQuadraticHenselStep256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintQuadraticHenselStep256 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runQuadraticHenselStep384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintQuadraticHenselStep384 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runQuadraticHenselStep512 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintQuadraticHenselStep512 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runHenselLift_n32_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintHenselLift_n32_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runHenselLift_n64_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintHenselLift_n64_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runHenselLift_n96_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintHenselLift_n96_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runHenselLift_n128_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintHenselLift_n128_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runHenselLift_n192_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintHenselLift_n192_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runHenselLift_n256_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintHenselLift_n256_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runMultiLift_n32_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLift_n32_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLift_n64_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLift_n64_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLift_n96_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLift_n96_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLift_n128_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLift_n128_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLift_n192_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLift_n192_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLift_n256_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLift_n256_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }

setup_fixed_benchmark runMultiLiftQ_n32_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLiftQ_n32_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLiftQ_n64_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLiftQ_n64_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLiftQ_n96_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLiftQ_n96_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLiftQ_n128_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLiftQ_n128_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLiftQ_n192_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLiftQ_n192_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runMultiLiftQ_n256_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }
setup_fixed_benchmark runFlintMultiLiftQ_n256_k8 where { repeats := 5, maxSecondsPerCall := 6.0 }

end HenselBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
