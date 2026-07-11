/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealRoots
import LeanBench

/-!
Benchmark registrations for `hex-real-roots`.

This Phase 4 slice measures the certified real-root isolation surface: the
two isolation engines through the public `isolate?`/`isolateSturm?` drivers,
the Sturm-chain and sign-variation primitives, the Möbius transform, the
`rootBound`/`sepPrec` closed forms, and the `refineTo` refinement loop.

Every timed target returns a compact integer checksum built from the dyadic
endpoints of the isolation output (`dyadicKey`), the chain coefficients, or
the scalar result, so the harness's hash column doubles as a
cross-implementation conformance check.

Input families (per `SPEC/Libraries/hex-real-roots.md` §"Time budgets" and the
conformance §"local" tier). `isolate?` is deliberately exercised on three
structurally different families, never a single happy-path shape:

* `well-separated-products`: `∏_{k=1}^{n} (x − k)`, `n` unit-separated integer
  roots. The Descartes engine's easy regime; resolves in `O(n + log(bound/gap))`
  bisection levels.
* `chebyshev-clustered`: the degree-`n` Chebyshev polynomial `T_n` built from
  the integer recurrence `T_{k+1} = 2x·T_k − T_{k-1}`. Its `n` real roots
  cluster near `±1` with gaps `~ 1/n²`, so bisection must descend deeper.
* `mignotte-worst-case`: `xⁿ − (a·x − 1)²` with `a = 1000`, the textbook
  Descartes worst case — a close real root pair that keeps Descartes variation
  counts at their maximum until the interval width shrinks to the order of the
  separation. This is the family that realises the SPEC's worst-case
  `O(n²·(h + log n))` Möbius-transform bound.

`compare runIsolateDescartesFirst runIsolateSturm` (shared
`well-separated-products` domain) is the intentional cross-engine equivalence
check: `isolate?` runs Descartes-first, `isolateSturm?` is the certified
fallback, and both must hash-agree on the isolation endpoints at every common
degree.

External comparator: SageMath `real_roots` / python-flint (the SPEC's oracle
role list) is `informational`, structurally different (approximate/native
vs the certified exact-integer engine), and scheduled-only — not wired in this
PR. See `libraries.yml: HexRealRoots.phase4.comparators`.
-/

namespace Hex.RealRootsBench

open Hex

/-- Hashable for the integer-polynomial fixture type, so `with prep := …`
targets can hoist a `ZPoly` fixture. -/
instance : Hashable ZPoly where
  hash p := hash p.toArray

/-- Ceiling base-2 logarithm, `⌈log₂ n⌉`, clamped to `1` for `n ≤ 1`. Used to
express the `log n` factor of the SPEC complexity contract inside the
`Nat → Nat` cost models. -/
def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 1 else (n - 1).log2 + 1

/-- The Mignotte parameter `a`. Fixed at `1000` per the SPEC's local-tier
worst-case fixture; large runs at `a = 10⁶` belong to the scheduled profile,
not to `verify`. -/
def mignotteA : Int := 1000

/-- `∏_{k=1}^{n} (x − k)`: `n` unit-separated integer roots. Built by iterated
multiplication of the linear factors `(x − k)`. For `n = 0` this is the
constant `1` (no roots). -/
def wellSepPoly (n : Nat) : ZPoly :=
  (List.range n).foldl
    (fun acc k => acc * DensePoly.ofCoeffs #[-(Int.ofNat (k + 1)), 1])
    (DensePoly.ofCoeffs #[(1 : Int)])

/-- The degree-`n` Chebyshev polynomial `T_n` with integer coefficients, from
the recurrence `T_0 = 1`, `T_1 = x`, `T_{k+1} = 2x·T_k − T_{k-1}`. Its `n`
distinct real roots cluster near `±1`. -/
def chebyshevPoly (n : Nat) : ZPoly :=
  let twoX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 2]
  let rec go : Nat → ZPoly → ZPoly → ZPoly
    | 0, prev, _ => prev
    | k + 1, prev, cur => go k cur (twoX * cur - prev)
  match n with
  | 0 => DensePoly.ofCoeffs #[(1 : Int)]
  | m + 1 => go m (DensePoly.ofCoeffs #[(1 : Int)]) (DensePoly.ofCoeffs #[(0 : Int), 1])

/-- The Mignotte polynomial `xⁿ − (a·x − 1)² = xⁿ − a²x² + 2a·x − 1` with
`a = mignotteA`. The Descartes worst case: a close real root pair near `1/a`.
The `xⁿ` term and the low-degree `(a·x − 1)²` block are disjoint for `n ≥ 3`;
for smaller `n` the ascending assembly still produces a valid nonzero
polynomial (used only at `verify` params). -/
def mignottePoly (n : Nat) : ZPoly :=
  let a := mignotteA
  DensePoly.ofCoeffs <| (Array.range (n + 1)).map fun i =>
    let leading : Int := if i = n then 1 else 0
    let square : Int :=
      if i = 0 then -1
      else if i = 1 then 2 * a
      else if i = 2 then -(a * a)
      else 0
    leading + square

/-- Deterministic bounded-coefficient integer polynomial of degree `n + 2`,
used for the lower-level Sturm/Möbius/bound primitives where the SPEC
complexity is a function of `n` at bounded coefficient bit-length `h`.

Shape `xᵈ + (Σ_{i<d} cᵢ xⁱ) − x − 1` with small `cᵢ ∈ {−1, 0, 1}` and a forced
`−x − 1` tail: the tail makes the polynomial reliably squarefree (so its Sturm
chain attains full length `d`, scaling smoothly with the parameter), while the
coefficients stay in a fixed band so `h` is held roughly constant across the
ladder. -/
def denseCoeff (i : Nat) : Int :=
  Int.ofNat ((i * 2654435761) % 3) - 1

def densePoly (n : Nat) : ZPoly :=
  let d := n + 2
  DensePoly.ofCoeffs <| (Array.range (d + 1)).map fun i =>
    if i = d then 1
    else if i = 0 then -1
    else if i = 1 then -1
    else denseCoeff i

/-- A stable integer key for a dyadic value: `ofOdd n k` maps to `n·C + k`,
zero to `0`. The odd numerator and the power-of-two exponent are exact, so
this is a faithful fingerprint of the endpoint. -/
def dyadicKey : Dyadic → Int
  | .zero => 0
  | .ofOdd n k _ => n * 1_000_003 + k

/-- Stable checksum of an isolation run: fold `dyadicKey` over every interval
endpoint. `none` (engine decline) maps to `-1`, distinct from any real run. -/
def isolationsChecksum {p : ZPoly} (r : Option (RealRootIsolations p)) : Int :=
  match r with
  | none => -1
  | some rs =>
    rs.isolations.foldl
      (fun acc iso =>
        acc * 65_537 + dyadicKey iso.interval.lower * 257 + dyadicKey iso.interval.upper)
      17

/-- Stable checksum of a Sturm chain: fold over every coefficient of every
element. -/
def chainChecksum (chain : Array ZPoly) : Int :=
  chain.foldl
    (fun acc q => q.toArray.foldl (fun a c => a * 131 + c) (acc * 65_537))
    0

/-- Prepared chain plus a fixed evaluation point for the `sturmVarAt`
benchmark: the chain is built in `prep` so the timed body measures only the
per-point Horner evaluation. -/
structure VarInput where
  /-- The Sturm chain, hoisted out of the timing loop. -/
  chain : Array ZPoly
  /-- A fixed dyadic evaluation point. -/
  point : Dyadic

instance : Hashable VarInput where
  hash inp := hash (inp.chain, dyadicKey inp.point)

/-- A fixed half-open dyadic interval `(−1, 1]` for the Möbius-transform
benchmark, independent of the parameter. -/
def mobiusI : DyadicInterval :=
  ⟨Dyadic.ofInt (-1), Dyadic.ofInt 1, by decide⟩

/-- Fixed linear polynomial `x − 5` for the refinement benchmark: `refineTo`
rebuilds the (tiny) chain per step, so the loop's cost is dominated by the
bisection depth the escalating target demands, not by the chain. -/
def refineP : ZPoly := DensePoly.ofCoeffs #[(-5 : Int), 1]

/-! ### Timed targets. -/

/-- `isolate?` on the well-separated integer-root product. -/
def runIsolateWellSep (p : ZPoly) : Int := isolationsChecksum (isolate? p)

/-- `isolate?` on the Chebyshev-clustered polynomial. -/
def runIsolateChebyshev (p : ZPoly) : Int := isolationsChecksum (isolate? p)

/-- `isolate?` on the Mignotte worst-case polynomial. -/
def runIsolateMignotte (p : ZPoly) : Int := isolationsChecksum (isolate? p)

/-- `isolate?` (Descartes-first) on the shared compare domain. -/
def runIsolateDescartesFirst (p : ZPoly) : Int := isolationsChecksum (isolate? p)

/-- `isolateSturm?` (certified engine) on the shared compare domain. -/
def runIsolateSturm (p : ZPoly) : Int := isolationsChecksum (isolateSturm? p)

/-- Build the Sturm chain of the dense fixture and checksum it. -/
def runSturmChain (p : ZPoly) : Int := chainChecksum (ZPoly.sturmChain p)

/-- Prepare a hoisted Sturm chain and a fixed nontrivial dyadic evaluation
point `3/2`, so the per-element Horner accumulator grows geometrically and the
timed body measures genuine dyadic multiplication rather than a degenerate
sum-of-coefficients at `x = 1`. -/
def prepVarInput (n : Nat) : VarInput :=
  { chain := ZPoly.sturmChain (densePoly n), point := (Dyadic.ofInt 3) >>> (1 : Int) }

/-- Evaluate the hoisted chain's sign variations at the fixed point. -/
def runSturmVarAt (inp : VarInput) : Int := Int.ofNat (sturmVarAt inp.chain inp.point)

/-- One integer Möbius transform of the dense fixture over `(−1, 1]`. -/
def runMobiusTransform (p : ZPoly) : Int := chainChecksum #[mobiusTransform p mobiusI]

/-- The Cauchy root-bound closed form of the dense fixture. -/
def runRootBound (p : ZPoly) : Int := dyadicKey (rootBound p)

/-- The separation-precision closed form of the dense fixture. -/
def runSepPrec (p : ZPoly) : Int := Int.ofNat (sepPrec p)

/-- Refine the first isolation of `x − 5` to precision `8·(n + 1)`; the
escalating target drives a bisection depth linear in `n`. -/
def runRefineTo (n : Nat) : Int :=
  match isolate? refineP with
  | none => -1
  | some rs =>
    match rs.isolations[0]? with
    | none => -2
    | some iso =>
      let refined := Hex.RealRootIsolation.refineTo iso (Int.ofNat (8 * (n + 1)))
      dyadicKey refined.interval.lower * 257 + dyadicKey refined.interval.upper

/-! ### Registrations.

Each `setup_benchmark` carries a cost-model derivation naming the dominant
step and how the fixture parameter maps onto that step's input size, per
`SPEC/benchmarking.md`.
-/

/- `isolate?` on `∏(x−k)`. SPEC §"Complexity contract": well-separated roots
resolve in `O(n + log(rootBound/gap))` bisection levels; with `O(n)` unresolved
intervals per level that is `O(n²)` Möbius transforms, each an `O(n²)` integer
Taylor shift, so `O(n⁴)` integer operations. Coefficient growth of `∏(x−k)`
(`h ~ n log n` bits) is an additional bignum factor carried by the constant. -/
-- Declared cost-model: worst-case O(n^4) integer operations, textbook Descartes bisection.
setup_benchmark runIsolateWellSep n => n ^ 4
  with prep := wellSepPoly
  where {
    paramFloor := 4
    paramCeiling := 24
    paramSchedule := .custom #[4, 8, 12, 16, 20, 24]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `isolate?` on `T_n`. The clustered roots near `±1` (gaps `~1/n²`) force
`O(log n)` extra bisection levels versus the well-separated family, but the
dominant asymptotic is still `O(n²)` Möbius transforms of `O(n²)` cost each,
i.e. `O(n⁴)`; coefficient magnitude `~2^n` (`h ~ n`) is the bignum factor. -/
-- Declared cost-model: worst-case O(n^4) integer operations, textbook Descartes bisection.
setup_benchmark runIsolateChebyshev n => n ^ 4
  with prep := chebyshevPoly
  where {
    paramFloor := 4
    paramCeiling := 20
    paramSchedule := .custom #[4, 8, 12, 16, 20]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `isolate?` on the Mignotte worst case. SPEC §"Complexity contract": bisection
depth is `O(n·(h + log n))` and each node is one `O(n²)` Möbius transform. The
Mignotte polynomial has `O(1)` real roots (the close pair), so the bisection
tree width is `O(1)` and the node count is `O(depth) = O(n)` at fixed `a`
(`h = O(log a)` constant), giving `O(n³)` integer operations. The SPEC's wider
`O(n²·(h + log n))` transform bound needs `Θ(n)` simultaneously-clustered roots
(the Chebyshev family); the Mignotte pair stresses transform depth and the
large-`a` coefficient magnitude rather than transform count. -/
-- Declared cost-model: O(n^3) integer operations, O(n)-depth Descartes bisection of the close pair.
setup_benchmark runIsolateMignotte n => n ^ 3
  with prep := mignottePoly
  where {
    paramFloor := 4
    paramCeiling := 20
    paramSchedule := .custom #[4, 8, 12, 16, 20]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Compare leg (Descartes-first `isolate?`). Shared `well-separated-products`
domain with `runIsolateSturm`; same `O(n⁴)` textbook model as
`runIsolateWellSep` since it is the same driver on the same inputs. -/
-- Declared cost-model: worst-case O(n^4) integer operations, textbook Descartes bisection.
setup_benchmark runIsolateDescartesFirst n => n ^ 4
  with prep := wellSepPoly
  where {
    paramFloor := 4
    paramCeiling := 20
    paramSchedule := .custom #[4, 8, 12, 16, 20]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- Compare leg (certified Sturm engine). Same shared domain. Each of the
`O(n²)` bisection nodes evaluates the *whole* Sturm chain — `O(n)` elements of
total degree `O(n²)` — and the primitive chain's coefficients grow to `O(n·h)`
bits (SPEC §"Complexity contract"), so each node's bignum evaluation carries an
extra factor of `O(n)` over the Descartes engine's bounded-coefficient Möbius
transform: `O(n²)` nodes × `O(n²)` Horner × `O(n)` bit-growth = `O(n⁵)`. This
super-`O(n⁴)` cost is exactly why `isolate?` runs Descartes first; the compare's
relative-timing summary makes the gap concrete. -/
-- Declared cost-model: O(n^5) bit-operations, full-chain-per-node Sturm bisection with O(n·h) coefficient growth.
setup_benchmark runIsolateSturm n => n ^ 5
  with prep := wellSepPoly
  where {
    paramFloor := 4
    paramCeiling := 20
    paramSchedule := .custom #[4, 8, 12, 16, 20]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `sturmChain`. The SPEC bounds each of the `O(n)` pseudo-divisions by
`O(n²)`, but the primitive polynomial-remainder sequence is Euclidean-like:
each `spem` drops the degree by one at `O(n)` cost, so the chain telescopes to
`O(n²)` coefficient operations total (BPR §8.3, signed remainder sequence). The
content gcds and the `O(n·h)` primitive-chain coefficient growth are carried by
the constant. -/
-- Declared cost-model: O(n^2) coefficient operations, telescoping primitive-remainder sequence.
setup_benchmark runSturmChain n => n ^ 2
  with prep := densePoly
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `sturmVarAt`. SPEC §"Complexity contract": one exact Horner evaluation per
chain element, `O(n²)` dyadic operations per queried point. The chain is
hoisted through `prep`, so the timed body is exactly the per-point evaluation. -/
-- Declared cost-model: O(n^2) dyadic operations, one Horner pass per chain element.
setup_benchmark runSturmVarAt n => n ^ 2
  with prep := prepVarInput
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `mobiusTransform`. SPEC §"Complexity contract": `O(n²)` integer operations
per node (Taylor-shift pipeline, no rational arithmetic). -/
-- Declared cost-model: O(n^2) integer operations, Taylor-shift Möbius pipeline.
setup_benchmark runMobiusTransform n => n ^ 2
  with prep := densePoly
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 32, 64, 128, 256]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `rootBound`. SPEC §"Complexity contract": `O(n·h)` integer operations. The
bounded-coefficient dense fixture holds `h` roughly constant, so the model
reduces to the linear coefficient scan `O(n)`. -/
-- Declared cost-model: O(n·h) integer operations; linear O(n) at bounded coefficient bit-length h.
setup_benchmark runRootBound n => n
  with prep := densePoly
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 48, 96, 160, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `sepPrec`. SPEC §"Complexity contract": `O(n·h)` integer operations,
dominated by the `coeffL2NormBound` coefficient scan; linear `O(n)` at bounded
coefficient bit-length. -/
-- Declared cost-model: O(n·h) integer operations; linear O(n) at bounded coefficient bit-length h.
setup_benchmark runSepPrec n => n
  with prep := densePoly
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 48, 96, 160, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

/- `refineTo` at escalating precision targets. Each `refine1` halves the
interval width by one bisection step; refining `x − 5`'s isolation to precision
`8·(n + 1)` performs `Θ(n)` halvings, each a constant-cost chain evaluation on
the degree-one fixture, so the loop is `O(n)` in the target parameter. -/
-- Declared cost-model: O(n) refinement steps, linear in the escalating precision target.
setup_benchmark runRefineTo n => n
  where {
    paramFloor := 16
    paramCeiling := 256
    paramSchedule := .custom #[16, 48, 96, 160, 256]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1.0
  }

end Hex.RealRootsBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
