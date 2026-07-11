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
dual-route atom-certificate experiment as a `compare` group: `isolate` under
`.nk`, `.pellet`, and `.nkThenPellet` on one shared deterministic domain,
joined on a strategy-invariant projection of the isolation output.

Two deterministic input families are used, each keyed by the benchmark
parameter (its degree):

* `seededPoly d` — a dense integer polynomial with coefficients in `[-10, 10]`
  drawn from the same seed-`0xC0FFEE` LCG the conformance ci-tier fixtures use
  (`conformance/HexRoots/EmitFixtures.lean`). Its roots are generically
  irrational and distinct, so isolation exercises subdivision to the separation
  depth rather than short-circuiting. Used by `taylor`, `mahlerPrec`, the
  refinement primitives, and the two whole-polynomial drivers.
* `linProdPoly d = ∏_{j=1}^{d} (X − j)` — a Wilkinson-shaped product of distinct
  monic linear factors with the integer roots `1, …, d`. Newton recentres onto
  an integer root exactly, so the certified centres are exact integers; this is
  what makes the `compare` group's strategy-invariant hash agree across the
  three strategies (the atoms' stored squares differ, but the integer-grid
  projection of their centres does not). Also used for the witness-check and
  Newton-step registrations, whose squares are centred on the integer root `1`
  of the family.

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

The scientific verdicts and their op-count-vs-wall reconciliation are recorded
in `reports/hexroots-performance.md`; several registrations return
*inconclusive* on their reachable schedules for reasons the report's Concerns
section documents (the fixed non-integer Taylor centre's `Θ(n)` denominator
growth, the seeded family's degree-dependent root geometry, the `refineTo`
Newton-doubling precision quantisation, and the startup-dominated microsecond
band of the small-degree witness benches).

Registrations (each with an adjacent cost-model derivation comment):

* `runTaylor` — exact Taylor shift, `O(n²)` exact-dyadic operations (the
  fixed non-integer centre's `Θ(n)`-bit denominator growth stays in the
  allocation-dominated band on the schedule).
* `runWitnessCheck`, `runNkWitnessCheck` — Pellet and Newton-Kantorovich atom
  witnesses, `O(n²)` (Taylor shift dominates; integer centre, sub-word
  operands, flat band).
* `runMahlerPrec` — separation precision, `O(n · log‖p‖∞)`, word-size integer
  arithmetic (no bit-growth).
* `runNewtonSquare` — speculative Newton step, `O(n²)` (integer-centre Taylor
  shift dominates, flat band).
* `runRefine1`, `runCertify` — one subdivision round and one certification
  attempt on a mid-refinement component, `O(n²)` (low-precision centres,
  sub-word operands, flat band).
* `runIsolateAll` — `isolateAll?` at target `32`, `O(n³·B²) = O(n⁵)` with the
  working bit-length `B = Θ(n)`.
* `runIsolate` — `isolate` to the `separationDepth` floor, `O(n³·B²) = O(n⁵)`.
* `runRefineTo` — `DyadicRootIsolation.refineTo?` from `≈32` to a parametric
  target precision `t`, `O(t²)` schoolbook bit-cost at fixed degree.
* `runSameRoot` — `RefinedIsolation.sameRoot`, a single dyadic comparison
  (fixed benchmark, microseconds).
* `runIsolateNk`, `runIsolatePellet`, `runIsolateNkThenPellet` — the `compare`
  group over `linProdPoly`, `O(n³·B²) = O(n⁵)`; all three must agree on the
  strategy-invariant hash.

External comparators (both `informational`, per
`libraries.yml: HexRoots.phase4.comparators`):

* **python-flint** `fmpz_poly.complex_roots()` (the SPEC's ci-tier oracle,
  which returns certified Arb balls with multiplicities) is timed as a
  process-call comparator on the same seeded degree ladder the
  whole-polynomial drivers use; the ratio `hex isolateAll?@32 / flint` per
  degree is recorded in `reports/hexroots-performance.md`. It is
  `informational`, not gating: FLINT's `complex_roots` is a multiprecision
  ball-arithmetic engine, structurally different from this library's
  decidable exact-integer Pellet / Newton-Kantorovich certificates, so the
  SPEC's time budgets — not a constant-factor `1×` goal — are the yardstick.
  Reproduce with `scripts/bench/hexroots_flint_compare.py` under a
  `python-flint ≥ 0.9.0` virtualenv (subprocess, wall clock, per-call
  overhead measured on a trivial input).
* **MPSolve** (Bini–Fiorentino `mpsolve`, the SPEC's local-tier and Phase-4
  external performance comparator) is classified `informational` and
  **scheduled-only**: it is not wired in this PR. Required environment: the
  `mpsolve` CLI (`unisa-cs/mpsolve`, built with GMP) on `PATH`, driven on the
  same seeded ladder via its `-au -Gi` isolate-mode output. Rationale for the
  informational class: MPSolve is a multiprecision-float C library computing
  approximate root inclusions, structurally different from this library's
  integer-certified Lean witnesses, so its ratio orients but does not gate.
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

/-- The fixed Gaussian-dyadic centre `1/4 + (1/8)·i` used by the `taylor`
benchmark: a nonzero dyadic point so the shift exercises every synthetic-
division pass. -/
def taylorCentre : GaussDyadic := (Dyadic.ofIntWithPrec 1 2, Dyadic.ofIntWithPrec 1 3)

/-- A square of half-width `2^{−12}` centred on the integer root `1` of
`linProdPoly`, used by the witness-check and Newton-step benchmarks. At this
radius the isolation ratio to the nearest sibling root (distance `1`) is far
inside the witness's firing threshold for every scheduled degree. -/
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
def runTaylor (p : ZPoly) : UInt64 :=
  gaussArrayChecksum (taylor p taylorCentre)

/-- Benchmark target: Pellet atom witness (`k = 1`) on the root-centred square. -/
def runWitnessCheck (p : ZPoly) : UInt64 :=
  hash (witnessCheck p rootSquare 1)

/-- Benchmark target: Newton-Kantorovich atom witness on the root-centred square. -/
def runNkWitnessCheck (p : ZPoly) : UInt64 :=
  hash (nkWitnessCheck p rootSquare)

/-- Benchmark target: closed-form separation precision. -/
def runMahlerPrec (p : ZPoly) : UInt64 :=
  hash (mahlerPrec p)

/-- Benchmark target: one speculative Newton step from the root-centred square. -/
def runNewtonSquare (p : ZPoly) : UInt64 :=
  squareChecksum (newtonSquare p rootSquare 1)

/-- Benchmark target: one subdivision round on a mid-refinement component. -/
def runRefine1 (pc : ZPoly × Component) : UInt64 :=
  componentsChecksum (pc.2.refine1 pc.1)

/-- Benchmark target: one certification attempt on a mid-refinement component. -/
def runCertify (pc : ZPoly × Component) : UInt64 :=
  optionCertifiedChecksum (Component.certify? pc.1 .nkThenPellet pc.2)

/-- Benchmark target: `isolateAll?` at target precision `32`. -/
def runIsolateAll (p : ZPoly) : UInt64 :=
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
def runIsolate (p : ZPoly) : UInt64 :=
  isolateDigest .nkThenPellet p

/-- Compare-group target: `isolate` under the Newton-Kantorovich-only strategy. -/
def runIsolateNk (p : ZPoly) : UInt64 :=
  isolateDigest .nk p

/-- Compare-group target: `isolate` under the Pellet-only strategy. -/
def runIsolatePellet (p : ZPoly) : UInt64 :=
  isolateDigest .pellet p

/-- Compare-group target: `isolate` under the default `nkThenPellet` strategy. -/
def runIsolateNkThenPellet (p : ZPoly) : UInt64 :=
  isolateDigest .nkThenPellet p

/-- Benchmark target: sharpen a fixed `≈32`-precision atom to a parametric
target precision. The prepared `σ` carries the fixed atom and the requested
target so the atom construction stays out of the timed loop. -/
def runRefineTo (input : Option (DyadicRootIsolation refinePoly) × Int) : UInt64 :=
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

/-! ### `taylor` / `mahlerPrec` : dense seeded family -/

/-
Cost model. `taylor` produces `p(X + z) = Σ cₖ Xᵏ` by repeated synthetic
division: the `k`-indexed outer pass runs an inner Horner sweep of length
`n − 1 − k`, so the total is `Σ_k (n − 1 − k) = O(n²)` exact Gaussian-dyadic
multiply/adds (degree `n` is the parameter). Bit-growth: the fixed centre
`z = 1/4 + i/8 = 2^{−3}(2 + i)` is a *non-integer* dyadic, so `z^{j−k}` carries
denominator `2^{3(j−k)}` and the coefficient `cₖ` reaches working bit-length
`B = Θ(n)` (the `2^{3n}` denominator dominates the `binomial ~ 2^n` numerator).
Each inner op multiplies a `B`-bit operand by the fixed `3`-bit centre, a
schoolbook `O(B)` cost, so the wall bit-cost is `O(n²·B) = O(n³)` in the
multiplication-bound limit. On the registered `16..256` schedule the operands
are `≤ 12` GMP words, still in the allocation-dominated transition where wall
tracks the `O(n²)` operation count with a sub-linear residual (measured
`~n^{2.25}`, short of the `n³` asymptote); the op-count `n²` is the declared
wall model per the SPEC contract, with the transition residual reported as a
Concern. This is the same Taylor-shift shape as hex-real-roots'
`runMobiusTransform` but with a non-integer centre, whose denominator growth
is what keeps it out of the flat band that made that one consistent at `n²`.
-/
setup_benchmark runTaylor n => n * n
  with prep := seededPoly
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

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
is `n²`. Bit-growth: the square is centred on the *integer* root `1` of
`linProdPoly`, so the centre `z = (1, 0)` has precision `0` and `z^{j−k}`
introduces no denominator; the Taylor coefficients are the (integer)
elementary-symmetric coefficients of `p(X+1)`, of bit-length `~log(n!) =
O(n log n)`, which stays under one GMP word (`≤ 44` bits at `n = 16`) across
the `2..16` schedule. Operands are sub-word, per-op cost flat, so the wall
model is the op count `n²`.
-/
setup_benchmark runWitnessCheck n => n * n
  with prep := linProdPoly
  where {
    paramFloor := 2
    paramCeiling := 16
    paramSchedule := .custom #[2, 4, 6, 8, 10, 12, 16]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model. `nkWitnessCheck` has the same `O(n²)` Taylor-shift-dominated shape
as `witnessCheck`, plus one `invFloor` reciprocal and a single `O(n)`
radial-Lipschitz fold, so the op count is `n²`. Bit-growth: identical to
`witnessCheck` — integer centre `(1, 0)`, no denominator, integer Taylor
coefficients of `O(n log n)` bits staying sub-word (`≤ 44` bits) across
`2..16`, so operands are flat and the wall model is the op count `n²`.
-/
setup_benchmark runNkWitnessCheck n => n * n
  with prep := linProdPoly
  where {
    paramFloor := 2
    paramCeiling := 16
    paramSchedule := .custom #[2, 4, 6, 8, 10, 12, 16]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model. `newtonSquare` computes the Taylor coefficients at the centre (the
`O(n²)` shift), reads `c₀, c₁`, and does one `Dyadic.invAtPrec` reciprocal plus
a constant amount of Gaussian-dyadic arithmetic. The Taylor shift dominates, so
the op count is `n²`. Bit-growth: integer centre `(1, 0)` on `linProdPoly`, no
denominator, integer Taylor coefficients of `O(n log n)` bits staying sub-word
across `2..16`; the reciprocal is at precision `~2·prec = 24` bits, also
sub-word. Operands flat, so the wall model is the op count `n²`.
-/
setup_benchmark runNewtonSquare n => n * n
  with prep := linProdPoly
  where {
    paramFloor := 2
    paramCeiling := 16
    paramSchedule := .custom #[2, 4, 6, 8, 10, 12, 16]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-! ### refinement primitives : mid-refinement component of the seeded family -/

/-
Cost model. `refine1` subdivides each square of the component four ways and
runs the `T₀` `rootFree` exclusion — one Taylor shift, `O(n²)` — on each child,
then glues the survivors. For a component of a bounded number of squares this
is a bounded number of `O(n²)` shifts, so the op count is `n²` in the degree
`n`. Bit-growth: the mid-refinement component sits two levels below `cauchy`,
so its square centres have low precision (`~cauchy.prec + 2`, a few bits) and
the seeded coefficients are `≤ 10`; the Taylor coefficients reach only `O(n)`
bits (dominated by `|z|^n` with `|z|` near the root bound `~11`), which stays
sub-word (`≤ 42` bits at `n = 12`) across the `4..12` schedule. Operands flat,
so the wall model is the op count `n²`.
-/
setup_benchmark runRefine1 n => n * n
  with prep := midComponent
  where {
    paramFloor := 4
    paramCeiling := 12
    paramSchedule := .custom #[4, 6, 8, 10, 12]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model. `certify?` under the default `nkThenPellet` strategy first tries
the Newton-Kantorovich witness on the doubled enclosing square: one
`nkWitnessCheck` (`O(n²)`) and one speculative `newtonSquare` (`O(n²)`). On a
mid-refinement component localised near a root this NK path fires, so the op
count is `n²`. (The Pellet fallback, taken only when NK does not fire, loops
over `k ≤ deg p` and is `O(n³)`; it is not the path this fixture measures.)
Bit-growth: same low-precision seeded mid-refinement component as `refine1` —
`O(n)`-bit Taylor coefficients staying sub-word across `4..12` — so operands
are flat and the wall model is the op count `n²`.
-/
setup_benchmark runCertify n => n * n
  with prep := midComponent
  where {
    paramFloor := 4
    paramCeiling := 12
    paramSchedule := .custom #[4, 6, 8, 10, 12]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-! ### whole-polynomial drivers : dense seeded family -/

/-
Cost model. `isolateAll?` refines the Cauchy component to disjoint certified
atoms at target precision `32`. The op count is `n³`: up to `O(n)` components,
each driven through `O(n)` subdivision levels of `O(n²)`-per-witness work
amortised by the speculative Newton jumps. Bit-growth is asymptotically
significant here: the working bit-length reaches `B = prec + n·log‖p‖∞ = Θ(n)`
(precision `~32` at the certifying level, plus the seeded `n·log 10` term, and
the Taylor coefficients' `Θ(prec·n)` denominator growth), and the
growing-precision dyadic arithmetic (notably the `invAtPrec` reciprocal) is
schoolbook `O(B²)`. The SPEC heuristic `O(n³·B²)` with `B = Θ(n)` gives the
wall model `n⁵`. The seeded family's distinct irrational roots force genuine
subdivision, but their *degree-dependent* root geometry (some degrees have
much closer roots than neighbours) makes the wall time non-monotonic in `n`,
which the report's Concerns section flags as a fit-quality limitation.
-/
-- Polylog factors (a strict B = Θ(n log n) reading gives n^5·log²n) are
-- suppressed in the declared model per house convention: the harness fits a
-- log-log slope, and the sibling Phase-4 reports (hex-real-roots) declare
-- plain powers for the same reason.
setup_benchmark runIsolateAll n => n * n * n * n * n
  with prep := seededPoly
  where {
    paramFloor := 4
    paramCeiling := 20
    paramSchedule := .custom #[4, 6, 8, 10, 12, 14, 16, 18, 20]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model. `isolate` runs `isolateAll?` from the Cauchy component to
`max atom_prec (separationDepth p)` and requires every result to be an atom.
With `atom_prec = 0` the target is the `separationDepth` floor, which grows
with the degree, so this is the deeper of the two whole-polynomial drivers.
Same `n³` op count as `isolateAll?`. Bit-growth: the target precision is now
`separationDepth p = mahlerPrec p + O(log n) = O(n·log‖p‖∞)`, so `B = Θ(n)` is
even more firmly in the multiplication-bound regime; `O(n³·B²)` with
`B = Θ(n)` gives the wall model `n⁵`. The schedule caps lower (degree `16`)
because the separation-depth target keeps one full-ladder pass practical there.
Same seeded-family non-monotonicity caveat as `isolateAll?`.
-/
-- Polylog factors (a strict B = Θ(n log n) reading gives n^5·log²n) are
-- suppressed in the declared model per house convention: the harness fits a
-- log-log slope, and the sibling Phase-4 reports (hex-real-roots) declare
-- plain powers for the same reason.
setup_benchmark runIsolate n => n * n * n * n * n
  with prep := seededPoly
  where {
    paramFloor := 4
    paramCeiling := 16
    paramSchedule := .custom #[4, 6, 8, 10, 12, 14, 16]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model. `refineTo?` sharpens a fixed degree-3 atom from precision `≈32` to
the parametric target `t`. Speculative Newton doubles the precision per
accepted jump, so the final witness at precision `t` dominates: a fixed number
(`O(deg²) = O(1)` at degree `3`) of Taylor multiplies on `B ≈ t`-bit dyadics,
each a schoolbook `t × t` product costing `O(t²)`, so the wall model is `t²`
in the target precision. Caveat: Newton doubling reaches a *discrete* precision
ladder, so the per-call work is a step function of `t` rather than smooth in it
(targets in the same doubling interval do equal work); the report's Concerns
section flags this quantisation as the reason the verdict is inconclusive on
the `64..256` schedule.
-/
setup_benchmark runRefineTo t => t * t
  with prep := prepRefineTo
  where {
    paramFloor := 64
    paramCeiling := 256
    paramSchedule := .custom #[64, 96, 128, 192, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

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
-- Polylog factors (a strict B = Θ(n log n) reading gives n^5·log²n) are
-- suppressed in the declared model per house convention: the harness fits a
-- log-log slope, and the sibling Phase-4 reports (hex-real-roots) declare
-- plain powers for the same reason.
setup_benchmark runIsolateNk n => n * n * n * n * n
  with prep := linProdPoly
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 5, 6]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model: one `isolate` run over `linProdPoly n`; `n³` op count (n
subdivision/adoption rounds of O(n) witness checks at O(n) ops each), and the
separation target's working bit-length `B = Θ(n log n)` enters the
growing-precision arithmetic as a schoolbook `O(B²)` per-op factor, so
`O(n³·B²)` gives the `n⁵` wall model; the Pellet-only strategy runs the
three-radius test per k candidate.
-/
-- Polylog factors (a strict B = Θ(n log n) reading gives n^5·log²n) are
-- suppressed in the declared model per house convention: the harness fits a
-- log-log slope, and the sibling Phase-4 reports (hex-real-roots) declare
-- plain powers for the same reason.
setup_benchmark runIsolatePellet n => n * n * n * n * n
  with prep := linProdPoly
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 5, 6]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/-
Cost model: one `isolate` run over `linProdPoly n`; `n³` op count (n
subdivision/adoption rounds of O(n) witness checks at O(n) ops each), and the
separation target's working bit-length `B = Θ(n log n)` enters the
growing-precision arithmetic as a schoolbook `O(B²)` per-op factor, so
`O(n³·B²)` gives the `n⁵` wall model; the default strategy tries NK first,
Pellet as fallback.
-/
-- Polylog factors (a strict B = Θ(n log n) reading gives n^5·log²n) are
-- suppressed in the declared model per house convention: the harness fits a
-- log-log slope, and the sibling Phase-4 reports (hex-real-roots) declare
-- plain powers for the same reason.
setup_benchmark runIsolateNkThenPellet n => n * n * n * n * n
  with prep := linProdPoly
  where {
    paramFloor := 2
    paramCeiling := 6
    paramSchedule := .custom #[2, 3, 4, 5, 6]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

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
