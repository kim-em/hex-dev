/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRoots
import LeanBench

/-!
Phase 4 benchmark registrations for `hex-roots`.

This module is the Phase 4 benchmark root for the certified complex-root
isolation API. It covers the exact Gaussian-dyadic primitives (`taylor`, the
two atom-witness checks, the speculative Newton step), the separation-precision
helper (`mahlerPrec`), the refinement primitives (`Component.refine1`,
`Component.certify?`), the end-to-end drivers (`isolateAll?`, `isolate`), the
refined-threading operation (`DyadicRootIsolation.refineTo?`), and the
root-identity test (`RefinedIsolation.sameRoot`). It also registers the
dual-route atom-certificate experiment on one shared canonical input, joined
on a strategy-invariant projection of the isolation output.

The deterministic inputs include:

* `seededPoly d` — a dense integer polynomial with coefficients in `[-10, 10]`
  drawn from the same seed-`0xC0FFEE` LCG the conformance ci-tier fixtures use
  (`conformance/HexRoots/EmitFixtures.lean`). Its roots are generically
  irrational and distinct, so isolation exercises subdivision to the separation
  depth rather than short-circuiting. Used by `mahlerPrec` and canonical
  Taylor/witness fixtures.
* `linProdPoly d = ∏_{j=1}^{d} (X − j)` — a Wilkinson-shaped product of distinct
  monic linear factors with the integer roots `1, …, d`. Newton recentres onto
  an integer root exactly, so the certified centres are exact integers; this is
  what makes the strategy regressions' invariant hash agree across the
  three strategies (the atoms' stored squares differ, but the integer-grid
  projection of their centres does not).
* `separatedPoly d = ∏(2X−(2j+1))` — uniformly separated half-integer roots,
  used by canonical fixed `isolate`/`isolateAll?`/`refine1` cases and the
  historical unregistered isolation diagnostic ladder.
* `boundedRootPoly 128` — bounded-height with exact root `1`, used by the
  canonical witness, Newton, and pinned-NK certification cases.

The declared complexity models are *wall-time* models: the textbook
exact-dyadic-operation count from `HexRoots/SPEC/hex-roots.md § Complexity
contract` multiplied by the family's working-bit-length growth
`B = prec + n·log‖p‖∞` where that growth is asymptotically significant on the
registered schedule (the reconciliation each derivation comment records). A
family whose operands stay in the flat, allocation-dominated GMP band across
its schedule keeps the op-count model unchanged (the bit-growth sits in the
constant); a family whose precision or coefficient bit-length grows with the
parameter folds the growth into the exponent. Each registration's comment
states which case it is and why. The `verify` smoke gate only exercises each
registration at parameters `0` and `1`.

Only `runMahlerPrec` is a parametric consistency gate. All other operations
use canonical fixed registrations: their reachable inputs sit
in a genuine GMP transition band where no honest scalar wall model has a flat
constant. Fixed timings retain regression coverage without asserting such a
model; the evidence and lean-bench#67 follow-up are recorded in the report.

Registrations (operation-count derivations remain documented adjacent to each
canonical or parametric case):

* `runTaylor` — fixed exact Taylor shift at seeded degree 128 and unit centre.
* `runWitnessCheck`, `runNkWitnessCheck` — Pellet and Newton-Kantorovich atom
  witnesses, `O(n²)` (Taylor shift dominates; integer centre, sub-word
  operands, flat band).
* `runMahlerPrec` — separation precision, `O(n · log‖p‖∞)`, word-size integer
  arithmetic (no bit-growth).
* `runNewtonSquare` — speculative Newton step, `O(n²)` (integer-centre Taylor
  shift dominates, flat band).
* `runRefine1` — one subdivision round on a fixed-separation mid-refinement
  component; `runCertify` — one pinned-NK certification attempt on the
  bounded-root fixture. Both are fixed `O(n²)` operation shapes.
* `runIsolateAll` — fixed `isolateAll?` at target `32` on separated degree 12.
* `runIsolate` — fixed `isolate` to the `separationDepth` floor on separated
  degree 8.
* `runRefineTo` — fixed at achieved precision 131077.
* `runSameRoot` — `RefinedIsolation.sameRoot`, a single dyadic comparison
  (fixed nanosecond-scale benchmark).
* `runIsolateNk`, `runIsolatePellet`, `runIsolateNkThenPellet` — fixed on the
  shared `linProdPoly 10`; all three must agree on the invariant hash.

External comparator (`informational`, per
`libraries.yml: HexRoots.phase4.comparators`):

* **python-flint** `fmpz_poly.complex_roots()` (the SPEC's ci-tier oracle,
  which returns certified Arb balls with multiplicities) is timed as a
  process-call comparator on the historical unregistered fixed-separation
  diagnostic ladder at degrees `4..10`, which includes canonical `runIsolate`
  degree 8, plus canonical `runIsolateAll` degree 12; the ratios are recorded in
  `reports/hex-roots-performance.md`. It is
  `informational`, not gating: FLINT's `complex_roots` is a multiprecision
  ball-arithmetic engine, structurally different from this library's
  decidable exact-integer Pellet / Newton-Kantorovich certificates, so the
  SPEC's time budgets — not a constant-factor `1×` goal — are the yardstick.
  Reproduce with `scripts/bench/hexroots_flint_compare.py` under a
  `python-flint ≥ 0.9.0` virtualenv (subprocess, wall clock, per-call
  overhead measured on a trivial input). MPSolve remains a local correctness
  oracle, not a Phase-4 performance comparator.
-/

namespace Hex.RootsBench

open Hex

/-! ### Deterministic input families -/

/-- The LCG step from `conformance/HexRoots/EmitFixtures.lean`
(`6364136223846793005·s + 1442695040888963407 mod 2^64`, realised as `UInt64`
wraparound). -/
def lcgNext (s : UInt64) : UInt64 := 6364136223846793005 * s + 1442695040888963407

/-- The seed-`0xC0FFEE` coefficient stream: `degree + 1` coefficients in
`[-10, 10]` (constant term first), with the leading coefficient forced nonzero
so the polynomial has the requested degree. Matches the ci-tier fixture
generator. -/
def seededCoeffs (degree : Nat) : Array Int := Id.run do
  let mut s : UInt64 := 0xC0FFEE
  let mut out : Array Int := Array.mkEmpty (degree + 1)
  for _ in [0:degree + 1] do
    s := lcgNext s
    out := out.push (Int.ofNat (s.toNat % 21) - 10)
  if out[degree]! == 0 then
    out := out.set! degree 1
  return out

/-- A dense integer polynomial of degree `degree` with bounded pseudo-random
coefficients (see `seededCoeffs`). -/
def seededPoly (degree : Nat) : ZPoly := DensePoly.ofCoeffs (seededCoeffs degree)

/-- The monic linear factor `X − root`. -/
def linearFactor (root : Int) : ZPoly := DensePoly.ofCoeffs #[-root, 1]

/-- `∏_{j=1}^{degree} (X − j)`, a Wilkinson-shaped polynomial with the distinct
integer roots `1, …, degree`. Empty product `1` at `degree = 0`. -/
def linProdPoly (degree : Nat) : ZPoly :=
  (Array.range degree).foldl
    (fun acc i => acc * linearFactor (Int.ofNat (i + 1)))
    (1 : ZPoly)

/-- A smooth driver family with roots `1/2, 3/2, …, degree-1/2`. -/
def separatedPoly (degree : Nat) : ZPoly :=
  (Array.range degree).foldl
    (fun acc i => acc * DensePoly.ofCoeffs #[-(2 * (Int.ofNat i) + 1), 2])
    (1 : ZPoly)

/-- A bounded-height degree-`degree` family with exact root `1`. -/
def boundedRootPoly (degree : Nat) : ZPoly :=
  if degree = 0 then 1 else linearFactor 1 * seededPoly (degree - 1)

/-- The fixed integer Gaussian-dyadic centre `1` used by the `taylor`
benchmark.  It exercises every synthetic-division pass while avoiding the
fractional-centre transition band identified by the Phase-4 audit. -/
def taylorCentre : GaussDyadic := (Dyadic.ofInt 1, Dyadic.ofInt 0)

/-- A square of half-width `2^{−12}` centred on the integer root `1` of
`boundedRootPoly 128`, used by the witness-check and Newton-step benchmarks.
At this radius the square remains well inside the witness's firing threshold
for the canonical input. -/
def rootSquare : DyadicSquare := ⟨Dyadic.ofInt 1, 0, 12⟩

/-! ### Result checksums (stable observables) -/

/-- Stable observable for a dyadic number: its exact reduced rational. -/
def dyadicChecksum (d : Dyadic) : UInt64 :=
  let q := d.toRat
  mixHash (hash q.num) (hash (q.den : Int))

/-- Stable observable for a Gaussian dyadic. -/
def gaussChecksum (z : GaussDyadic) : UInt64 :=
  mixHash (dyadicChecksum z.1) (dyadicChecksum z.2)

/-- Stable observable for an array of Gaussian dyadics (the `taylor` output). -/
def gaussArrayChecksum (zs : Array GaussDyadic) : UInt64 :=
  zs.foldl (fun acc z => mixHash acc (gaussChecksum z)) (hash zs.size)

/-- Stable observable for a dyadic square. -/
def squareChecksum (s : DyadicSquare) : UInt64 :=
  mixHash (mixHash (dyadicChecksum s.re) (dyadicChecksum s.im)) (hash s.prec)

/-- Stable observable for a certification result: its stored square plus the
atom/cluster tag and root count. -/
def certifiedChecksum {p : ZPoly} (c : Certified p) : UInt64 :=
  let tag : Nat := match c with | .atom _ => 1 | .cluster cl => cl.k
  mixHash (squareChecksum c.square) (hash tag)

/-- Stable observable for an optional certification result. -/
def optionCertifiedChecksum {p : ZPoly} : Option (Certified p) → UInt64
  | none => 0
  | some c => mixHash 1 (certifiedChecksum c)

/-- Stable observable for an array of certification results. -/
def certifiedArrayChecksum {p : ZPoly} (rs : Array (Certified p)) : UInt64 :=
  rs.foldl (fun acc c => mixHash acc (certifiedChecksum c)) (hash rs.size)

/-- Stable observable for an array of components (the `refine1` output). -/
def componentsChecksum (cs : Array Component) : UInt64 :=
  cs.foldl (fun acc c => mixHash acc (c.squares.foldl
    (fun a s => mixHash a (squareChecksum s)) (hash c.candidateK))) (hash cs.size)

/-! ### `Hashable` instances for benchmark input types

`setup_benchmark` records a hash of the prepared input alongside each JSONL row.
`ZPoly`, `DyadicSquare`, `Component`, and `DyadicRootIsolation` carry no derived
`Hashable`, so the instances below route through the exact-rational observables
above; product and option inputs then derive automatically. -/

instance : Hashable ZPoly where hash p := hash p.toArray

instance : Hashable DyadicSquare where hash := squareChecksum

instance : Hashable Component where
  hash c := c.squares.foldl (fun a s => mixHash a (squareChecksum s)) (hash c.candidateK)

instance {p : ZPoly} : Hashable (DyadicRootIsolation p) where
  hash iso := squareChecksum iso.square

/-! ### Strategy-invariant projection for the `compare` group

The three strategies isolate the same integer roots but store different squares
(different precisions, sometimes off-by-one levels). The projection below is
invariant across strategies on `linProdPoly`: it records the atom count and the
multiset of atom centres rounded to the NEAREST INTEGER. The compare family's
roots are integers and every strategy's certified centre lies within the
stored square's radius of its root, far below `1/2`, so the rounding is
robust to the strategies' differing squares and precisions (a finer grid
would put bucket boundaries near non-integer centres and break invariance;
this digest is only meaningful for integer-root families). The `compare`
gate is exactly that agreement. -/

/-- Round a dyadic to the nearest integer (`⌊x⌉`). -/
def gridBucket (d : Dyadic) : Int := (d.toRat + (1 : Rat) / 2).floor

/-- Lexicographic order on integer-grid buckets, for a deterministic multiset
digest. -/
def bucketLe (a b : Int × Int) : Bool :=
  if a.1 = b.1 then a.2 ≤ b.2 else a.1 < b.1

/-- Strategy-invariant digest of an isolation output: the atom count mixed with
the sorted multiset of integer-grid centre buckets. -/
def rootsDigest {p : ZPoly} (atoms : Array (DyadicRootIsolation p)) : UInt64 :=
  let buckets := (atoms.map fun iso =>
    (gridBucket iso.square.re, gridBucket iso.square.im)).qsort bucketLe
  buckets.foldl (fun acc b => mixHash (mixHash acc (hash b.1)) (hash b.2))
    (hash atoms.size)

/-! ### Mid-refinement component fixture -/

/-- A representative mid-refinement component of `seededPoly degree`: two
`refine1` rounds down from `Component.cauchy`, keeping the first surviving
component (a subdivided region localised near a root). Falls back to the Cauchy
square when the degree is degenerate or every child was `T₀`-discarded. -/
def midComponent (degree : Nat) : ZPoly × Component :=
  let p := seededPoly degree
  if h : 0 < p.degree?.getD 0 then
    let start := Component.cauchy p h
    let round1 := start.refine1 p
    let round2 := round1.flatMap (·.refine1 p)
    (p, (round2[0]?.orElse fun _ => round1[0]?).getD start)
  else
    (p, ⟨#[⟨0, 0, 0⟩], 0⟩)

/-- A mid-refinement component on the smooth fixed-separation family. -/
def separatedMidComponent (degree : Nat) : ZPoly × Component :=
  let p := separatedPoly degree
  if h : 0 < p.degree?.getD 0 then
    let start := Component.cauchy p h
    let round1 := start.refine1 p
    let round2 := round1.flatMap (·.refine1 p)
    (p, (round2[0]?.orElse fun _ => round1[0]?).getD start)
  else
    (p, ⟨#[⟨0, 0, 0⟩], 0⟩)

/-! ### Refined-atom fixture for `refineTo?` and `sameRoot` -/

/-- A small fixed polynomial with distinct simple roots for the refined-atom
fixtures: `(x−1)(x−2)(x+3)`. -/
def refinePoly : ZPoly := DensePoly.ofCoeffs #[6, -7, 0, 1]

/-- One atom of `refinePoly`, isolated to (at least) the separation depth. The
`refineTo?` benchmark sharpens this atom; the `sameRoot` benchmark compares its
refined form against itself. `none` never occurs for this squarefree fixture. -/
def refineAtom? : Option (DyadicRootIsolation refinePoly) :=
  if h : HasOnlySimpleRoots refinePoly then
    match isolate refinePoly h 0 with
    | some atoms => atoms[0]?
    | none => none
  else none

/-- The refined-isolation form of `refineAtom?`, meeting the separation
precision required by `RefinedIsolation`. -/
def refinedAtom? : Option (RefinedIsolation refinePoly) :=
  refineAtom?.bind DyadicRootIsolation.toRefined?

/-! ### Benchmark targets -/

/-- Benchmark target: exact Gaussian-dyadic Taylor shift at the fixed centre. -/
def taylorChecksum (p : ZPoly) : UInt64 :=
  gaussArrayChecksum (taylor p taylorCentre)

/-- Benchmark target: Pellet atom witness (`k = 1`) on the root-centred square. -/
def witnessChecksum (p : ZPoly) : UInt64 :=
  hash (witnessCheck p rootSquare 1)

/-- Benchmark target: Newton-Kantorovich atom witness on the root-centred square. -/
def nkWitnessChecksum (p : ZPoly) : UInt64 :=
  hash (nkWitnessCheck p rootSquare)

/-- Benchmark target: closed-form separation precision. -/
def runMahlerPrec (p : ZPoly) : UInt64 :=
  hash (mahlerPrec p)

/-- Benchmark target: one speculative Newton step from the root-centred square. -/
def newtonChecksum (p : ZPoly) : UInt64 :=
  squareChecksum (newtonSquare p rootSquare 1)

/-- Benchmark target: one subdivision round on a mid-refinement component. -/
def refine1Checksum (pc : ZPoly × Component) : UInt64 :=
  componentsChecksum (pc.2.refine1 pc.1)

/-- Benchmark target: one certification attempt on a mid-refinement component. -/
def certifyChecksum (pc : ZPoly × Component) : UInt64 :=
  optionCertifiedChecksum (Component.certify? pc.1 .nkThenPellet pc.2)

/-- Benchmark target: `isolateAll?` at target precision `32`. -/
def isolateAllChecksum (p : ZPoly) : UInt64 :=
  if h : 0 < p.degree?.getD 0 then
    match isolateAll? p 32 #[Component.cauchy p h] with
    | some rs => certifiedArrayChecksum rs
    | none => 0
  else 0

/-- Isolate `p` under `strategy` and digest the output with the
strategy-invariant projection; `0` for non-squarefree or degenerate inputs. -/
def isolateDigest (strategy : AtomStrategy) (p : ZPoly) : UInt64 :=
  if h : HasOnlySimpleRoots p then
    match isolate p h 0 strategy with
    | some atoms => rootsDigest atoms
    | none => 0
  else 0

/-- Benchmark target: `isolate` to the `separationDepth` floor (`atom_prec = 0`). -/
def runIsolateParam (p : ZPoly) : UInt64 :=
  isolateDigest .nkThenPellet p

/-- Compare-group target: `isolate` under the Newton-Kantorovich-only strategy. -/
def isolateNkChecksum (p : ZPoly) : UInt64 :=
  isolateDigest .nk p

/-- Compare-group target: `isolate` under the Pellet-only strategy. -/
def isolatePelletChecksum (p : ZPoly) : UInt64 :=
  isolateDigest .pellet p

/-- Compare-group target: `isolate` under the default `nkThenPellet` strategy. -/
def isolateNkThenPelletChecksum (p : ZPoly) : UInt64 :=
  isolateDigest .nkThenPellet p

/-- Benchmark target: sharpen a fixed `≈32`-precision atom to a parametric
target precision. The prepared `σ` carries the fixed atom and the requested
target so the atom construction stays out of the timed loop. -/
def refineToChecksum (input : Option (DyadicRootIsolation refinePoly) × Int) : UInt64 :=
  match input.1 with
  | some iso =>
    match iso.refineTo? input.2 with
    | some iso' => squareChecksum iso'.square
    | none => 0
  | none => 0

/-- Per-parameter fixture for `runRefineTo`: the fixed refined atom paired with
the target precision the parameter encodes. -/
def prepRefineTo (target : Nat) : Option (DyadicRootIsolation refinePoly) × Int :=
  (refineAtom?, (target : Int))

/-! ### Canonical fixed inputs -/

initialize taylorRef : IO.Ref (Option ZPoly) ← IO.mkRef (some (seededPoly 128))
initialize witnessRef : IO.Ref (Option ZPoly) ← IO.mkRef (some (boundedRootPoly 128))
initialize refine1Ref : IO.Ref (Option (ZPoly × Component)) ←
  IO.mkRef (some (separatedMidComponent 8))
initialize refineToRef : IO.Ref (Option (DyadicRootIsolation refinePoly) × Int) ←
  IO.mkRef (prepRefineTo 131077)
initialize isolateAllRef : IO.Ref (Option ZPoly) ← IO.mkRef (some (separatedPoly 12))
initialize compareRef : IO.Ref (Option ZPoly) ← IO.mkRef (some (linProdPoly 10))

/-- Canonical degree-128 certification fixture pinned to the NK branch. -/
def pinnedCertify? : Option (ZPoly × Component) :=
  let p := boundedRootPoly 128
  if nkWitnessCheck p rootSquare.doubled = true then some (p, ⟨#[rootSquare], 1⟩) else none

initialize certifyRef : IO.Ref (Option (ZPoly × Component)) ← IO.mkRef pinnedCertify?

def runTaylor : Unit → IO UInt64 := fun _ => do return (← taylorRef.get).map taylorChecksum |>.getD 0
def runWitnessCheck : Unit → IO UInt64 := fun _ => do return (← witnessRef.get).map witnessChecksum |>.getD 0
def runNkWitnessCheck : Unit → IO UInt64 := fun _ => do return (← witnessRef.get).map nkWitnessChecksum |>.getD 0
def runNewtonSquare : Unit → IO UInt64 := fun _ => do return (← witnessRef.get).map newtonChecksum |>.getD 0
def runRefine1 : Unit → IO UInt64 := fun _ => do return (← refine1Ref.get).map refine1Checksum |>.getD 0
def runCertify : Unit → IO UInt64 := fun _ => do return (← certifyRef.get).map certifyChecksum |>.getD 0
def runRefineTo : Unit → IO UInt64 := fun _ => do return refineToChecksum (← refineToRef.get)
initialize isolateFixedRef : IO.Ref (Option ZPoly) ← IO.mkRef (some (separatedPoly 8))

def runIsolate : Unit → IO UInt64 := fun _ => do
  return ((← isolateFixedRef.get).map runIsolateParam).getD 0

def runIsolateAll : Unit → IO UInt64 := fun _ => do return (← isolateAllRef.get).map isolateAllChecksum |>.getD 0
def runIsolateNk : Unit → IO UInt64 := fun _ => do return (← compareRef.get).map isolateNkChecksum |>.getD 0
def runIsolatePellet : Unit → IO UInt64 := fun _ => do return (← compareRef.get).map isolatePelletChecksum |>.getD 0
def runIsolateNkThenPellet : Unit → IO UInt64 := fun _ => do return (← compareRef.get).map isolateNkThenPelletChecksum |>.getD 0

/-! ### `taylor` / `mahlerPrec` : dense seeded family -/

/-
Cost model. `taylor` produces `p(X + z) = Σ cₖ Xᵏ` by repeated synthetic
division: the `k`-indexed outer pass runs an inner Horner sweep of length
`n − 1 − k`, so the total is `Σ_k (n − 1 − k) = O(n²)` exact Gaussian-dyadic
multiply/adds. The canonical degree-128 case uses the integer centre `z = 1`:
there is no denominator growth, but binomial output magnitudes still grow
linearly in bits. The reachable GMP transition does not admit a stable scalar
wall model, so this is fixed for regression tracking with an expected hash.
-/
setup_fixed_benchmark runTaylor where {
  repeats := 5, maxSecondsPerCall := 4.0, expectedHash := some 0x9917b7b230496af4 }

/-
Cost model. `mahlerPrec` evaluates the closed-form Mahler/Landau separation
bound: the `coeffAbsMax` scan is `O(n)` `Nat.max` steps, plus a fixed number
of `ceilLog2` calls and word-size integer multiplies forming `t`. The SPEC
contract is `O(n · log‖p‖∞)`; the seeded family holds `‖p‖∞ ≤ 10` fixed, so
`log‖p‖∞` is constant and the op count reduces to linear in `n`. Bit-growth:
every operand (the coefficients `≤ 10`, the degree `n`, the `ceilLog2` results,
the sum `t = O(n)`) fits in a single machine word across `16..256`, so `B` is
constant and the wall model equals the op count `n`.
-/
setup_benchmark runMahlerPrec n => n
  with prep := seededPoly
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-! ### witness checks / Newton step : root-centred `linProdPoly` -/

/-
Cost model. `witnessCheck` computes the exact Taylor coefficients at the
square's centre (the `O(n²)` shift, which dominates) and then, for each of the
three test radii, a single `O(n)` fold over the coefficients, so the op count
is `n²`. The canonical input is `boundedRootPoly 128`, centred on its exact
integer root `1`; its bounded-height coefficients avoid Wilkinson expansion,
while the Taylor output still crosses GMP limbs. It is fixed with an expected
hash because that reachable transition has no stable scalar wall model.
-/
setup_fixed_benchmark runWitnessCheck where {
  repeats := 5, maxSecondsPerCall := 4.0, expectedHash := some 0xb }

/-
Cost model. `nkWitnessCheck` has the same `O(n²)` Taylor-shift-dominated shape
as `witnessCheck`, plus one `invFloor` reciprocal and a single `O(n)`
radial-Lipschitz fold, so the op count is `n²`. It uses the same canonical
bounded-height degree-128 input and fixed-regression rationale as
`runWitnessCheck`.
-/
setup_fixed_benchmark runNkWitnessCheck where {
  repeats := 5, maxSecondsPerCall := 4.0, expectedHash := some 0xb }

/-
Cost model. `newtonSquare` computes the Taylor coefficients at the centre (the
`O(n²)` shift), reads `c₀, c₁`, and does one `Dyadic.invAtPrec` reciprocal plus
a constant amount of Gaussian-dyadic arithmetic. The Taylor shift dominates, so
the op count is `n²`. It uses the same bounded-height degree-128 input; the
fixed-precision reciprocal is lower order. The fixed registration tracks the
GMP-transition case without asserting a scalar asymptotic fit.
-/
setup_fixed_benchmark runNewtonSquare where {
  repeats := 5, maxSecondsPerCall := 4.0, expectedHash := some 0x450307c7dcbe905c }

/-! ### refinement primitives : canonical fixed fixtures -/

/-
Cost model. `refine1` subdivides each square of the component four ways and
runs the `T₀` `rootFree` exclusion — one Taylor shift, `O(n²)` — on each child,
then glues the survivors. For a component of a bounded number of squares this
is a bounded number of `O(n²)` shifts, so the op count is `n²` in the degree
`n`. The canonical fixture is the degree-8 fixed-separation product, refined
two rounds below its Cauchy component. It is fixed because its parametric
smooth-family calibration drifted in the reachable transition band.
-/
setup_fixed_benchmark runRefine1 where {
  repeats := 5, maxSecondsPerCall := 4.0, expectedHash := some 0x6dd99fc71c5233ae }

/-
Cost model. `certify?` under the default `nkThenPellet` strategy first tries
the Newton-Kantorovich witness on the doubled enclosing square: one
`nkWitnessCheck` (`O(n²)`) and one speculative `newtonSquare` (`O(n²)`). On a
canonical bounded-height degree-128 component is pinned by checking
`nkWitnessCheck p rootSquare.doubled = true` during initialization, so this NK
path always fires and the op count is `n²`. Fixed rather than parametric
because the certification path is Taylor-shift dominated and the shift's
`Θ(n)`-bit output growth places every reachable schedule in the `n²..n³`
GMP transition band (issue #8750, rounds one to three: pure powers and the
limb model all showed drifting constants). The fixed expected hash makes a
fixture-path or semantic regression visible.
-/
setup_fixed_benchmark runCertify where {
  repeats := 5, maxSecondsPerCall := 6.0, expectedHash := some 0x1698ec123da6112f }

/-! ### whole-polynomial drivers -/

/-
Cost model. `isolateAll?` refines the Cauchy component to disjoint certified
atoms at target precision `32`. The op count is `n³`: up to `O(n)` components,
each driven through `O(n)` subdivision levels of `O(n²)`-per-witness work
amortised by the speculative Newton jumps. Bit-growth is asymptotically
significant here: the working bit-length reaches `B = prec + n·log‖p‖∞ = Θ(n)`
(precision `~32` at the certifying level, plus coefficient growth, and
the Taylor coefficients' `Θ(prec·n)` denominator growth), and the
growing-precision dyadic arithmetic (notably the `invAtPrec` reciprocal) is
schoolbook `O(B²)`. The SPEC heuristic `O(n³·B²)` with `B = Θ(n)` gives the
wall model `n⁵`. The canonical fixed case is the degree-12 uniformly
separated half-integer product; it tracks the full driver without asserting a
slope after its quiet-machine sweep remained transitional.
-/
-- Fixed rather than parametric: the quiet-machine sweep stayed in the GMP
-- transition band at every reachable schedule (issue #8750, round four), so
-- no scalar wall model has a flat constant; the shared canonical input keeps
-- the cross-strategy `compare` agreement gate as a regression check.
setup_fixed_benchmark runIsolateAll where {
  repeats := 5, maxSecondsPerCall := 20.0, expectedHash := some 0x9fa00d70361d4394 }

/-
Cost model. `isolate` runs `isolateAll?` from the Cauchy component to
`max atom_prec (separationDepth p)` and requires every result to be an atom.
With `atom_prec = 0` the target is the `separationDepth` floor, which grows
with the degree, so this is the deeper of the two whole-polynomial drivers.
Same `n³` op count as `isolateAll?`, but on this family the floor is steep:
`separatedPoly n` has `log ‖p‖∞ = Θ(n·log n)` (the `2^n` leading factor and
the double-factorial constant term), so
`separationDepth = O(n·log‖p‖∞) = Θ(n²·log n)`, the emission-level working
bit-length is `B = Θ(n²·log n)`, and the honestly derived wall from the SPEC
`O(n³·B²)` contract is `~n⁷` (polylogs suppressed per house convention). That
asymptote is far beyond the 30 s/call band (an earlier `n⁵` registration fit
the 4..10 rungs, but only as a transition-band artifact; the adjacent
derivation could not support it, so per the no-fitting rule it was withdrawn:
issue #8750). Canonical fixed case at the mid-schedule degree 8; regression
tracking without an asymptotic claim.
-/
setup_fixed_benchmark runIsolate where {
    repeats := 5, maxSecondsPerCall := 30.0, expectedHash := some 0x16c307fd2a36d31e }

/-
Cost model. `refineTo?` sharpens a fixed degree-3 atom from precision `≈32` to
the canonical achieved precision `131077`. Speculative Newton doubles precision
per accepted jump, so the final witness dominates: a fixed number
(`O(deg²) = O(1)` at degree `3`) of Taylor multiplies on `B ≈ t`-bit dyadics,
each a schoolbook `t × t` product costing `O(t²)`, so the wall model is `t²`
in the achieved precision. The discrete Newton ladder and GMP crossover make
the reachable sweep unsuitable for one scalar model, so the expected-hash
fixed case tracks the high-precision regression directly.
-/
setup_fixed_benchmark runRefineTo where {
  repeats := 5, maxSecondsPerCall := 4.0, expectedHash := some 0x8dd3e4ee56489bf8 }

/-! ### `compare` group : dual-route atom-certificate experiment

`runIsolateNk`, `runIsolatePellet`, and `runIsolateNkThenPellet` isolate the
same `linProdPoly` inputs under the three `AtomStrategy` values and digest the
output with the strategy-invariant `rootsDigest`. On this integer-root family
all three agree, so `compare runIsolateNk runIsolatePellet runIsolateNkThenPellet`
reports `allAgreed`; a divergence would be a cross-strategy conformance failure.
The wall model is `n⁵` (each is an `isolate` run), matching the drivers. -/

/-
Cost model: one `isolate` run over `linProdPoly n`; `n³` op count (n
subdivision/adoption rounds of O(n) witness checks at O(n) ops each), and the
separation target's working bit-length `B = Θ(n log n)` enters the
growing-precision arithmetic as a schoolbook `O(B²)` per-op factor, so
`O(n³·B²)` gives the `n⁵` wall model; the NK-only strategy certifies each atom
on its doubled square.
-/
-- Fixed rather than parametric: the quiet-machine sweep stayed in the GMP
-- transition band at every reachable schedule (issue #8750, round four), so
-- no scalar wall model has a flat constant; the shared canonical input keeps
-- the cross-strategy `compare` agreement gate as a regression check.
setup_fixed_benchmark runIsolateNk where {
  repeats := 5, maxSecondsPerCall := 8.0, expectedHash := some 0xda631bdf13415a4f }

/-
Cost model: one `isolate` run over `linProdPoly n`; `n³` op count (n
subdivision/adoption rounds of O(n) witness checks at O(n) ops each), and the
separation target's working bit-length `B = Θ(n log n)` enters the
growing-precision arithmetic as a schoolbook `O(B²)` per-op factor, so
`O(n³·B²)` gives the `n⁵` wall model; the Pellet-only strategy runs the
three-radius test per k candidate.
-/
-- Fixed rather than parametric: the quiet-machine sweep stayed in the GMP
-- transition band at every reachable schedule (issue #8750, round four), so
-- no scalar wall model has a flat constant; the shared canonical input keeps
-- the cross-strategy `compare` agreement gate as a regression check.
setup_fixed_benchmark runIsolatePellet where {
  repeats := 5, maxSecondsPerCall := 8.0, expectedHash := some 0xda631bdf13415a4f }

/-
Cost model: one `isolate` run over `linProdPoly n`; `n³` op count (n
subdivision/adoption rounds of O(n) witness checks at O(n) ops each), and the
separation target's working bit-length `B = Θ(n log n)` enters the
growing-precision arithmetic as a schoolbook `O(B²)` per-op factor, so
`O(n³·B²)` gives the `n⁵` wall model; the default strategy tries NK first,
Pellet as fallback.
-/
-- Fixed rather than parametric: the quiet-machine sweep stayed in the GMP
-- transition band at every reachable schedule (issue #8750, round four), so
-- no scalar wall model has a flat constant; the shared canonical input keeps
-- the cross-strategy `compare` agreement gate as a regression check.
setup_fixed_benchmark runIsolateNkThenPellet where {
  repeats := 5, maxSecondsPerCall := 8.0, expectedHash := some 0xda631bdf13415a4f }

/-! ### `sameRoot` : fixed microsecond benchmark -/

/-- The prebuilt refined-atom pair for the `sameRoot` benchmark, threaded through
an `IO.Ref` so the single dyadic comparison is not constant-folded away. -/
initialize sameRootRef :
    IO.Ref (Option (RefinedIsolation refinePoly × RefinedIsolation refinePoly)) ←
  IO.mkRef (refinedAtom?.map fun r => (r, r))

/-
`RefinedIsolation.sameRoot` is a single `DyadicSquare.discsMeet` comparison — a
handful of exact-dyadic multiplies and one `≤` — so it is a microsecond-scale
fixed benchmark rather than a parametric sweep. The atoms come from the `IO.Ref`
above so the harness measures the comparison, not a folded constant.
-/
def runSameRoot : Unit → IO UInt64 := fun () => do
  match ← sameRootRef.get with
  | some (a, b) => return hash (RefinedIsolation.sameRoot a b)
  | none => return 0

setup_fixed_benchmark runSameRoot where {
    repeats := 5
    expectedHash := some 0xb
  }

end Hex.RootsBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
