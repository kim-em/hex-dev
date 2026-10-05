/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSturm
import LeanBench

/-! Prepared query, count, replay and literal-transport costs on `T_n`,
query one and endpoints (-2,2). The head-degree ladder is 128 through 1024;
its coefficients and accumulators have growing binary size. Preparations,
supplied certificates and cache validation remain outside timed bodies.
See `reports/sturm-bit-cost-models.md` for the independently derived models.
-/
namespace Hex.SturmFrontendBench
open Hex DensePoly

def head (n : Nat) : ZPoly :=
  let twoX : ZPoly := ofCoeffs #[0, 2]
  let rec go : Nat → ZPoly → ZPoly → ZPoly
    | 0, prev, _ => prev
    | k + 1, prev, cur => go k cur (twoX * cur - prev)
  go n 1 (ofCoeffs #[0, 1])

def interval : DyadicInterval := ⟨Dyadic.ofInt (-2), Dyadic.ofInt 2, by decide⟩

structure Input where
  p : DensePoly Rat
  bounds : DyadicInterval := interval
  domain : Option (Sturm.PreparedDomain Rat)
  cert : Option (TarskiCertificate Rat Rat Unit)
  integer : Option IntTarskiCertificate
  cache : Option (TarskiCertificate.Domain.Checked (Ctx := Unit)
    (Sturm.orderSign : Rat → Int) (EndpointSigns.ofSign Sturm.orderSign))

instance : Inhabited Input := ⟨{ p := 0, domain := none, cert := none, integer := none, cache := none }⟩

instance : Hashable Input where
  hash i := hash i.p.toArray

def fromHead (z : ZPoly) (bounds : DyadicInterval := interval) : Input :=
  let p := ZPoly.toRatPoly z
  let a := bounds.lower.toRat
  let b := bounds.upper.toRat
  let cert := Sturm.certify Sturm.orderSign () p 1 (.finite a) (.finite b)
  let i : Input := {
    p := p
    bounds := bounds
    domain := Sturm.prepare Sturm.orderSign p (.finite a) (.finite b)
    cert := cert
    integer := IntTarskiCertificate.certify z 1 bounds
    cache := cert.bind fun c => TarskiCertificate.Domain.replay? Sturm.orderSign
      (EndpointSigns.ofSign Sturm.orderSign) c.domain }
  if i.cert.any (fun c => i.cache.any (fun d =>
      d.data.binds () p (.finite a) (.finite b) c.squarefree)) then i
  else panic! "benchmark fixture must exercise a checked-cache hit"

def prepare (n : Nat) : Input := fromHead (head n)

-- Consume all translated chain coefficients and scales, not just the answer.
def chainHash (c : SignedRemainderChain Rat) : UInt64 :=
  hash (c.chain.map DensePoly.toArray, c.degrees,
    c.initial.leftScale, c.initial.quotient.toArray, c.initial.rightScale,
    c.steps.map (fun s => (s.leftScale, s.quotient.toArray, s.rightScale)),
    c.terminal.map fun (u, q) => (u, q.toArray))

def certHash (c : TarskiCertificate Rat Rat Unit) : UInt64 :=
  hash (chainHash c.squarefree, chainHash c.remainders,
    c.lowerSigns, c.upperSigns, c.value)

def integerHash (c : IntTarskiCertificate) : UInt64 :=
  hash (c.squarefree.chain.map DensePoly.toArray, c.remainders.chain.map DensePoly.toArray,
    c.remainders.initial.quotient.toArray,
    c.remainders.steps.map (fun s => (s.leftScale, s.quotient.toArray, s.rightScale)),
    c.lowerSigns, c.upperSigns, c.value)

def runPrepared (i : Input) : Option Int :=
  i.domain.map fun d => Sturm.queryPrepared d 1

def runRetarget (i : Input) : Option Bool :=
  i.domain.map fun d => (d.withEndpoints? (.finite (-3)) (.finite 3)).isSome

def runCount (i : Input) : Option Nat :=
  Sturm.rootCount Sturm.orderSign i.p (.finite i.bounds.lower.toRat) (.finite i.bounds.upper.toRat)

def runPreparedCount (i : Input) : Option Int :=
  i.domain.map Sturm.countPrepared

def runCertificate (i : Input) : Option UInt64 :=
  (Sturm.certify Sturm.orderSign () i.p 1 (.finite i.bounds.lower.toRat) (.finite i.bounds.upper.toRat)).map certHash

def runPreparedCertificate (i : Input) : Option UInt64 :=
  i.domain.map fun d => certHash (Sturm.certifyPrepared () d 1)

def runCountCertificate (i : Input) : Option UInt64 :=
  i.domain.map fun d => certHash (Sturm.certifyCountPrepared () d)

def runFieldReplay (i : Input) : Bool :=
  match i.cert with
  | none => false
  | some c => Sturm.check Sturm.orderSign () i.p 1 (.finite i.bounds.lower.toRat) (.finite i.bounds.upper.toRat) c.value c

def runCachedReplay (i : Input) : Bool :=
  match i.cert with
  | none => false
  | some c => Sturm.checkCached Sturm.orderSign () i.p 1 (.finite i.bounds.lower.toRat) (.finite i.bounds.upper.toRat) c.value i.cache c

def runClear (i : Input) : Option UInt64 :=
  i.cert.map fun c => integerHash (c.clearDenominators i.p 1 i.bounds)

def runEmbed (i : Input) : Option UInt64 := i.integer.map fun c => certHash c.toRat

/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runPrepared n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Cost-model derivation: two-sided. Two integer-endpoint Horner passes
visit n coefficients and O(n)-bit accumulators, multiplying by fixed ±3.
This is Θ(n²) big-by-small bit work on the all-bignum ladder. -/
setup_benchmark runRetarget n => n ^ 2
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runCount n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Cost-model derivation: two-sided. Prepared counting only evaluates the
stored monic U-chain. There are Θ(n²) coefficients with Θ(n) total-width
progression per entry; adjacent dyadic denominators differ by word-size
factors on this ladder. Horner at ±2 and power-of-two gcd normalization take
linear limb work, giving Θ(n³), without rebuilding a chain. -/
setup_benchmark runPreparedCount n => n ^ 3
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runCertificate n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runPreparedCertificate n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runCountCertificate n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runFieldReplay n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runCachedReplay n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runClear n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Retired upper-bound hypothesis: the Chebyshev profile does not exercise
the cited general arithmetic as a dominant phase. This registration is
diagnostic and does not attest Phase 4. Not a unit-cost claim. The normal
Chebyshev chain has O(n²) coefficient operations on O(n)-bit scalars. GMP's
published schoolbook multiplication and classical quadratic gcd upper bounds
cover Rat normalization and literal replay, hence O(n⁴) bit work. The mixed
allocation/limb costs and algorithm thresholds prevent a uniform tight power
model on the finite ladder. See reports/sturm-bit-cost-models.md. -/
setup_benchmark runEmbed n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

def runInfinite (i : Input) : Option Int :=
  Sturm.query Sturm.orderSign i.p 1 .negInf .posInf

/- Retired upper-bound hypothesis, not Phase-4 evidence: the same
degree-descending O(n²) normal chain as finite
querying; infinity signs read leading coefficients and degrees, adding O(n)
work instead of endpoint Horner passes. This exercises whole-line domains. -/
setup_benchmark runInfinite n => n ^ 4
  with prep := prepare
  where {
    paramSchedule := .custom #[128, 256, 512, 1024]
    paramFloor := 128
    paramCeiling := 1024
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

structure QueryInput where
  domain : Option (Sturm.PreparedDomain Rat)
  q : DensePoly Rat

instance : Hashable QueryInput where
  hash i := hash i.q.toArray

def prepareQuery (m : Nat) : QueryInput :=
  let p : DensePoly Rat := ofCoeffs #[-2, 0, 1]
  let q : DensePoly Rat := ofCoeffs ((Array.replicate (m + 1) (0 : Rat)).set! 0 1 |>.set! m 1)
  ⟨Sturm.prepare Sturm.orderSign p (.finite (-2)) (.finite 2), q⟩

def runPreparedHigh (i : QueryInput) : Option Int :=
  i.domain.map fun d => Sturm.queryPrepared d i.q

def runPreparedCertificateHigh (i : QueryInput) : Option UInt64 :=
  i.domain.map fun d => certHash (Sturm.certifyPrepared () d i.q)

/- Cost model: for P=X²-2, F=X^m+1, division by the fixed monic
quadratic stores Θ(m) quotient coefficients with Θ(m)-bit total-width
progression, hence Θ(m²) big-by-small bit work. Remaining chains have fixed
degree. This is the same derived initial-reduction family as runRationalHigh;
prepared querying removes the fixed head/domain work, not that reduction.
The chosen ladder is its retained signal-valid range, not a new fitted model. -/
setup_benchmark runPreparedHigh m => m ^ 2
  with prep := prepareQuery
  where {
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    paramFloor := 131072
    paramCeiling := 1048576
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }
/- Cost model: the same Θ(m²) reduction, plus linear traversal of its
Θ(m²)-bit quotient to consume the literal certificate. No new head chain is
constructed in this prepared frontend. -/
setup_benchmark runPreparedCertificateHigh m => m ^ 2
  with prep := prepareQuery
  where {
    paramSchedule := .custom #[131072, 262144, 524288, 1048576]
    paramFloor := 131072
    paramCeiling := 1048576
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

instance : Inhabited DyadicInterval := ⟨interval⟩

structure AxisInput where
  p : ZPoly
  interval : DyadicInterval

instance : Inhabited AxisInput := ⟨⟨0, interval⟩⟩

instance : Hashable AxisInput where
  hash i := hash (i.p.toArray, i.interval.lower.toRat, i.interval.upper.toRat)

/-- Deterministic unrelated odd mantissas. The top bit and low bit are set;
LCG words fill the interior rather than creating a power-of-two shortcut. -/
def oddMantissa (bits seed : Nat) : Int :=
  let b := max bits 2
  let (_, value) := (List.range ((b + 63) / 64)).foldl
    (fun (state, value) _ =>
      let next : UInt64 := state * 6364136223846793005 + 1442695040888963407
      (next, value * 2 ^ (64 : Nat) + next.toNat)) ((UInt64.ofNat seed), 0)
  let value := value % 2 ^ (b - 1)
  Int.ofNat (2 ^ (b - 1) + value / 2 * 2 + 1)

def coefficientInput (bits : Nat) : AxisInput :=
  let b := max bits 16
  -- B² < 3AC, A,C > 0: the derivative is positive on the real line.
  -- A dominates the other coefficients at ±2, so this squarefree cubic
  -- has exactly one root there. Nonreal repeated roots would force degree ≥4.
  ⟨ofCoeffs #[-oddMantissa (b - 1) 41, oddMantissa (b - 1) 23,
      oddMantissa (b - 2) 9, oddMantissa b 1], interval⟩

def endpointBounds (bits : Nat) (fractional : Bool := false) : DyadicInterval :=
  let b := max bits 16
  let u := oddMantissa b 17
  let prec : Int := if fractional then (b / 2 : Nat) else 0
  let a := Dyadic.ofIntWithPrec (-u) prec
  let c := Dyadic.ofIntWithPrec u prec
  if h : a < c then ⟨a, c, h⟩
  else panic! "endpoint-size fixture must be ordered"

def endpointInput (bits : Nat) : AxisInput := ⟨head 8, endpointBounds bits⟩
def fractionalInput (bits : Nat) : AxisInput := ⟨head 8, endpointBounds bits true⟩

def runCoefficientBits (i : AxisInput) : Option Int := ZPoly.tarskiQuery i.p 1 i.interval
def runEndpointBits (i : AxisInput) : Option Int := ZPoly.tarskiQuery i.p 1 i.interval
def runFractionalBits (i : AxisInput) : Option Int := ZPoly.tarskiQuery i.p 1 i.interval

/- Cost-model derivation, cited upper bound: fixed degree bounds the number of scalar operations; operand and
intermediate widths are O(bits). GMP's published quadratic multiplication/gcd
bounds give O(bits²). Binary normalization, allocation and GMP crossover
thresholds prevent a uniform tight monomial for the whole pipeline. -/
setup_benchmark runCoefficientBits bits => bits ^ 2
  with prep := coefficientInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, cited upper bound: eight fixed Horner steps per fixed chain entry perform arithmetic
on O(bits)-wide dyadic accumulators. The same published GMP upper bounds
cover their scalar products. This is an endpoint-size axis, not a head- or
query-degree axis. No fitted arithmetic-regime exponent is used. -/
setup_benchmark runEndpointBits bits => bits ^ 2
  with prep := endpointInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

structure RetargetInput where
  p : DensePoly Rat
  domain : Option (Sturm.PreparedDomain Rat)

instance : Hashable RetargetInput where
  hash i := hash i.p.toArray

def retargetInput (n : Nat) : RetargetInput :=
  let p : DensePoly Rat := ofCoeffs
    ((Array.replicate (max n 2 + 1) (0 : Rat)).set! 0 (-2) |>.set! (max n 2) 1)
  ⟨p, Sturm.prepare Sturm.orderSign p (.finite (-1)) (.finite 1)⟩

def runRetargetWide (i : RetargetInput) : Bool :=
  i.domain.any fun d => (d.withEndpoints? (.finite (-3)) (.finite 3)).isSome

/- Cost-model derivation, two-sided: X^n−2 has a short derivative chain, so preparation needs only
linear storage. Retargeting at ±3 performs n big-by-small Horner products
with Θ(n)-bit accumulators. Θ(n²) bit work dominates the Θ(n) dispatch term
on the preregistered 1600..13000-limb regime. The original Chebyshev attempt
and its faster-than-declared failure are retained. -/
setup_benchmark runRetargetWide n => n ^ 2
  with prep := retargetInput
  where {
    paramSchedule := .custom #[65536, 131072, 262144, 524288]
    paramFloor := 65536
    paramCeiling := 524288
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound pending a profile check: unlike the withdrawn power-of-two endpoint family, odd b-bit
mantissas make each nontrivial fixed-degree Horner product growing-by-growing.
Both integral and fractional endpoints exercise GMP multiplication. -/
setup_benchmark runFractionalBits bits => bits ^ 2
  with prep := fractionalInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

def translatedInput (bits : Nat) : Input :=
  let z := oddMantissa bits 29
  let p := (head 8).compose (ofCoeffs #[-z, 1])
  let a := Dyadic.ofInt (z - 2)
  let b := Dyadic.ofInt (z + 2)
  if h : a < b then fromHead p ⟨a, b, h⟩
  else panic! "translated fixture must be ordered"

-- Independent names preserve the failed head-degree registrations.
def runPreparedBits := runPrepared
def runCountBits := runCount
def runPreparedCountBits := runPreparedCount
def runCertificateBits := runCertificate
def runPreparedCertificateBits := runPreparedCertificate
def runCountCertificateBits := runCountCertificate
def runFieldReplayBits := runFieldReplay
def runCachedReplayBits := runCachedReplay
def runClearBits := runClear
def runInfiniteBits := runInfinite

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runPreparedBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runCountBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runPreparedCountBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runCertificateBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runPreparedCertificateBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runCountCertificateBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runFieldReplayBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runCachedReplayBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runClearBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, candidate cited upper bound: T_8(X−z), with odd b-bit z and endpoints z±2, has a fixed
normal chain with Θ(b)-bit coefficients. Its linear quotients contain −z;
chain products and endpoint Horner multiply two growing operands. GMP's
published quadratic product/gcd bounds apply only if those phases dominate, which the
retained profiles do not establish. Size thresholds
prevent a single tight monomial across the registered limb regimes. -/
setup_benchmark runInfiniteBits bits => bits ^ 2
  with prep := translatedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

structure IntegerInput where
  cert : Option IntTarskiCertificate

instance : Hashable IntegerInput where
  hash i := hash (i.cert.map integerHash)

def embedInput (n : Nat) : IntegerInput :=
  let p : ZPoly := ofCoeffs
    ((Array.replicate (max n 2 + 1) (0 : Int)).set! 0 (-2) |>.set! (max n 2) 1)
  let bounds : DyadicInterval := ⟨Dyadic.ofInt (-1), Dyadic.ofInt 1, by decide⟩
  ⟨IntTarskiCertificate.certify p 1 bounds⟩

def runEmbedSparse (i : IntegerInput) : Option UInt64 :=
  i.cert.map fun c => certHash c.toRat

/- Cost-model derivation, two-sided: embedding is a literal coefficient/scale cast, not arithmetic on
coefficient magnitudes. X^n−2 has a short chain containing Θ(n) word-size
entries. Every cast and scalar hash is constant word work; output traversal
and array allocation are Θ(n). The old long-chain bit-volume hypothesis is
retained as failed evidence rather than a performance claim. -/
setup_benchmark runEmbedSparse n => n
  with prep := embedInput
  where {
    paramSchedule := .custom #[2048, 4096, 8192, 16384, 32768]
    paramFloor := 2048
    paramCeiling := 32768
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/-- A short-chain degree family with two real roots at every even rung. -/
structure SparseInput where
  head : ZPoly
  frontend : Input

instance : Inhabited SparseInput := ⟨⟨0, default⟩⟩

instance : Hashable SparseInput where
  hash i := hash i.head.toArray

def sparseInput (degree : Nat) : SparseInput :=
  let n := max degree 2
  let p : ZPoly := ofCoeffs
    ((Array.replicate (n + 1) (0 : Int)).set! 0 (-1) |>.set! n 2)
  let bounds : DyadicInterval := ⟨Dyadic.ofInt (-1), Dyadic.ofInt 1, by decide⟩
  let i := fromHead p bounds
  let expected : Int := if n % 2 = 0 then 2 else 1
  if ZPoly.tarskiQuery p 1 bounds == some expected &&
      Sturm.query Sturm.orderSign i.p 1 (.finite (-1)) (.finite 1) == some expected &&
      i.domain.any (fun d => d.squarefree.chain.size == 3) then
    ⟨p, i⟩
  else panic! "short-chain fixture failed its degree/count/chain checks"

def runSparseDomain (i : SparseInput) : Bool :=
  (Sturm.prepare Sturm.orderSign i.frontend.p (.finite (-1)) (.finite 1)).isSome

def runSparseQuery (i : SparseInput) : Option Int :=
  Sturm.query Sturm.orderSign i.frontend.p 1 (.finite (-1)) (.finite 1)

def runSparseInteger (i : SparseInput) : Option Int :=
  ZPoly.tarskiQuery i.head 1 i.frontend.bounds

def runSparsePrepared (i : SparseInput) : Option Int := runPrepared i.frontend

def runSparseCount (i : SparseInput) : Option Nat := runCount i.frontend

def runSparsePreparedCount (i : SparseInput) : Option Int := runPreparedCount i.frontend

def runSparseCertificate (i : SparseInput) : Option UInt64 := runCertificate i.frontend

def runSparsePreparedCertificate (i : SparseInput) : Option UInt64 :=
  runPreparedCertificate i.frontend

def runSparseCountCertificate (i : SparseInput) : Option UInt64 := runCountCertificate i.frontend

def runSparseReplay (i : SparseInput) : Bool := runFieldReplay i.frontend

def runSparseCachedReplay (i : SparseInput) : Bool := runCachedReplay i.frontend

def runSparseClear (i : SparseInput) : Option UInt64 := runClear i.frontend

def runSparseEmbed (i : SparseInput) : Option UInt64 := runEmbed i.frontend

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseDomain n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseQuery n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseInteger n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparsePrepared n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseCount n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparsePreparedCount n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseCertificate n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparsePreparedCertificate n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseCountCertificate n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseReplay n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseCachedReplay n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseClear n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

/- Cost-model derivation, two-sided: P=2X^n−1, F=1 and endpoints ±1.
The normalized chain is P,X^(n−1),1. Its divisions have d=2 or m=0,
so the dynamic recurrence has Θ(n) word-size work. Horner at ±1,
literal identities, denominator clearing and full output hashes traverse
Θ(n) entries. The single 2n normalization factor is word-size on this
fixed ladder. Preparation and checked-cache validation are outside timing.
This short-chain family does not cover growing chain length or bit height. -/
setup_benchmark runSparseEmbed n => n
  with prep := sparseInput
  where {
    paramSchedule := .custom #[16384, 32768, 65536, 131072]
    paramFloor := 16384
    paramCeiling := 131072
    outerTrials := 4
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 600
  }

end Hex.SturmFrontendBench
