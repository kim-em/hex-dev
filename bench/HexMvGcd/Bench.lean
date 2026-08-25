/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexMvGcd
import HexMvPolyCorpus
import HexMvGcdFlint
import LeanBench

/-!
Native benchmark registrations for `hex-mv-gcd`.

This first benchmark layer covers the public executable API and the seven
input families named by the SPEC. Input construction is outside the timed
region. Timed functions return structural checksums, so the benchmark runner
must traverse the result and can compare repeated runs for exact agreement.

The route benchmarks deliberately separate the public dispatcher from the
deterministic PRS fallback. This makes a regression in coprime detection,
Brown interpolation, or coefficient swell attributable to one registration.

Each parametric child batch autotunes warm in-process repetitions. The
executable's startup floor is larger than those batches on the scheduled host,
so `signalFloorMultiplier := 1.0` retains the child-side measurements without
changing their scientific ladders or wallclock caps.
-/

namespace Hex.MvGcdBench

open Hex
open Hex.MvPoly
open Hex.MvPolyBench.Corpus

abbrev P2 (R : Type) [Zero R] := MvPoly 2 R Mono.lex
abbrev P3 (R : Type) [Zero R] := MvPoly 3 R Mono.lex
abbrev P8 (R : Type) [Zero R] := MvPoly 8 R Mono.lex

/-- Stable structural hash of a canonical sparse polynomial. -/
def checksum [Zero R] [Hashable R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n R cmp) : UInt64 :=
  p.termsList.foldl
    (fun acc term =>
      mixHash (mixHash acc (hash term.1.toList)) (hash term.2))
    0

instance [Zero R] [Hashable R]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    Hashable (MvPoly n R cmp) where
  hash := checksum

/-- Dense bivariate coefficient box. -/
def denseBox2 [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [NatCast R]
    (degree : Nat) : P2 R :=
  ofTerms <| (List.range (degree + 1)).flatMap fun xExponent =>
    (List.range (degree + 1)).map fun yExponent =>
      (Hex.Vector.ofFn' fun i =>
        if i.val = 0 then xExponent else yExponent, 1)

/-- Dense trivariate box used by the Brown family. -/
def denseBox3 (degree : Nat) : P3 Int :=
  ofTerms <| (List.range (degree + 1)).flatMap fun xExponent =>
    (List.range (degree + 1)).flatMap fun yExponent =>
      (List.range (degree + 1)).map fun zExponent =>
        (Hex.Vector.ofFn' fun i =>
          if i.val = 0 then xExponent
          else if i.val = 1 then yExponent
          else zExponent, 1)

/-- High-degree, low-support polynomial in eight variables. -/
def sparse8 (degree salt : Nat) : P8 Int :=
  ofTerms <| (Mono.zero, 1) :: (List.finRange 8).map fun axis =>
    (Hex.Vector.ofFn' fun i => if i = axis then degree else 0,
      Int.ofNat (axis.val + salt + 1))

structure PublicInput where
  left : P2 Int
  right : P2 Int
  product : P2 Int
  deriving Hashable, Nonempty

structure SupportInput where
  polynomial : P2 Int
  deriving Hashable

/-- Exactly `count` supported terms with bounded coefficients. -/
def prepSupport (count : Nat) : SupportInput :=
  { polynomial := ofTerms <| intTerms count 79 fun exponent =>
      Hex.Vector.ofFn' fun i =>
        if i.val = 0 then exponent else count - exponent }

def prepPublic (degree : Nat) : PublicInput :=
  let x : P2 Int := X 0
  let y : P2 Int := X 1
  let common := x + y + 1
  let leftCofactor := denseBox2 degree + x + 2
  let rightCofactor := denseBox2 degree + y + 3
  { left := common * leftCofactor
    right := common * rightCofactor
    product := common ^ 3 * leftCofactor ^ 2 * rightCofactor }

def runMonoContent (input : SupportInput) : UInt64 :=
  hash (monoContent input.polynomial).toList

def runContent (input : SupportInput) : UInt64 :=
  hash (content input.polynomial)

def runPrimPart (input : SupportInput) : UInt64 :=
  checksum (primPart input.polynomial)

def runScalarContent (input : SupportInput) : UInt64 :=
  hash (scalarContent input.polynomial)

def runPolyNormalize (input : SupportInput) : UInt64 :=
  checksum (polyNormalize input.polynomial)

def runPolyIsUnit (input : SupportInput) : UInt64 :=
  hash (polyIsUnit input.polynomial)

def runToUnivariate (input : SupportInput) : UInt64 :=
  let view := toUnivariate (0 : Fin 2) Mono.lex input.polynomial
  view.toArray.foldl (fun acc coefficient =>
    mixHash acc (checksum coefficient)) 0

def runContentIn (input : PublicInput) : UInt64 :=
  checksum (contentIn (0 : Fin 2) Mono.lex input.product)

def runPrimPartIn (input : PublicInput) : UInt64 :=
  checksum (primPartIn (0 : Fin 2) Mono.lex input.product)

def runDivExact (input : PublicInput) : UInt64 :=
  match divExact? input.left (X 0 + X 1 + 1) with
  | none => 0
  | some quotient => checksum quotient

def runGcd (input : PublicInput) : UInt64 :=
  checksum (gcd input.left input.right)

def runCofactors (input : PublicInput) : UInt64 :=
  let result := cofactors input.left input.right
  mixHash (checksum result.1) (checksum result.2)

def runIsCoprime (input : PublicInput) : UInt64 :=
  hash (isCoprime input.left input.right)

def runGcdList (input : PublicInput) : UInt64 :=
  checksum (gcdList [input.left, input.right, input.product])

def runLcm (input : PublicInput) : UInt64 :=
  checksum (lcm input.left input.right)

def runSqfDecomp (input : PublicInput) : UInt64 :=
  let decomp := sqfDecomp input.product
  decomp.factors.foldl
    (fun acc factor =>
      mixHash (mixHash acc (checksum factor.factor))
        (hash factor.multiplicity))
    (hash decomp.content)

def runRadical (input : PublicInput) : UInt64 :=
  checksum (radical input.product)

def runIsSquarefree (input : PublicInput) : UInt64 :=
  hash (isSquarefree input.product)

initialize public2 : IO.Ref PublicInput ← IO.mkRef (prepPublic 2)

def runContentInFixed (_ : Unit) : IO UInt64 := do
  return runContentIn (← public2.get)

def runPrimPartInFixed (_ : Unit) : IO UInt64 := do
  return runPrimPartIn (← public2.get)

def runGcdFixed (_ : Unit) : IO UInt64 := do
  return runGcd (← public2.get)

def runCofactorsFixed (_ : Unit) : IO UInt64 := do
  return runCofactors (← public2.get)

def runIsCoprimeFixed (_ : Unit) : IO UInt64 := do
  return runIsCoprime (← public2.get)

def runGcdListFixed (_ : Unit) : IO UInt64 := do
  return runGcdList (← public2.get)

def runLcmFixed (_ : Unit) : IO UInt64 := do
  return runLcm (← public2.get)

def runSqfDecompFixed (_ : Unit) : IO UInt64 := do
  return runSqfDecomp (← public2.get)

def runRadicalFixed (_ : Unit) : IO UInt64 := do
  return runRadical (← public2.get)

def runIsSquarefreeFixed (_ : Unit) : IO UInt64 := do
  return runIsSquarefree (← public2.get)

def runDivExactFixed (_ : Unit) : IO UInt64 := do
  return runDivExact (← public2.get)

structure CoprimeInput where
  left : P2 Int
  right : P2 Int
  deriving Hashable, Nonempty

def prepCoprime (degree : Nat) : CoprimeInput :=
  let x : P2 Int := X 0
  let y : P2 Int := X 1
  { left := x ^ (degree + 1) + y + 1
    right := y ^ (degree + 1) + x + 2 }

def runCoprime (input : CoprimeInput) : UInt64 :=
  mixHash (checksum (gcd input.left input.right))
    (hash (isCoprime input.left input.right))

initialize coprime1 : IO.Ref CoprimeInput ← IO.mkRef (prepCoprime 1)

def runCoprimeFamilyFixed (_ : Unit) : IO UInt64 := do
  return runCoprime (← coprime1.get)

structure DenseInput where
  left : P3 Int
  right : P3 Int
  deriving Hashable, Nonempty

def prepDense (degree : Nat) : DenseInput :=
  let x : P3 Int := X 0
  let y : P3 Int := X 1
  let z : P3 Int := X 2
  let common := x + y + z + 1
  let box := denseBox3 degree
  { left := common * (box + x + 2)
    right := common * (box + y + 3) }

def runDense (input : DenseInput) : UInt64 :=
  checksum (gcd input.left input.right)

initialize dense0 : IO.Ref DenseInput ← IO.mkRef (prepDense 0)

def runDenseFixed (_ : Unit) : IO UInt64 := do
  return runDense (← dense0.get)

structure SparseInput where
  left : P8 Int
  right : P8 Int
  deriving Hashable, Nonempty

def prepSparse (degree : Nat) : SparseInput :=
  let common : P8 Int := X 0 + X 7 + 1
  { left := common * sparse8 degree 1
    right := common * sparse8 (degree + 1) 3 }

def runSparse (input : SparseInput) : UInt64 :=
  checksum (gcd input.left input.right)

initialize sparse1 : IO.Ref SparseInput ← IO.mkRef (prepSparse 1)

def runSparseFixed (_ : Unit) : IO UInt64 := do
  return runSparse (← sparse1.get)

structure SwellInput where
  left : P2 Int
  right : P2 Int
  deriving Hashable, Nonempty

def prepSwell (degree : Nat) : SwellInput :=
  let x : P2 Int := X 0
  let y : P2 Int := X 1
  let common := C 2 * x + y + 1
  { left := common * (x ^ degree + C 37 * y + 1)
    right := common * (x ^ (degree + 1) - C 41 * y + 2) }

def runSwell (input : SwellInput) : UInt64 :=
  checksum (prsCert input.left input.right).gcd

initialize swell3 : IO.Ref SwellInput ← IO.mkRef (prepSwell 3)
initialize swell4 : IO.Ref SwellInput ← IO.mkRef (prepSwell 4)
initialize swell5 : IO.Ref SwellInput ← IO.mkRef (prepSwell 5)

def runSwell3 (_ : Unit) : IO UInt64 := do
  return runSwell (← swell3.get)

def runSwell4 (_ : Unit) : IO UInt64 := do
  return runSwell (← swell4.get)

def runSwell5 (_ : Unit) : IO UInt64 := do
  return runSwell (← swell5.get)

structure RationalInput where
  left : P2 Rat
  right : P2 Rat
  deriving Hashable, Nonempty

def prepRational (degree : Nat) : RationalInput :=
  let x : P2 Rat := X 0
  let y : P2 Rat := X 1
  let common := C ((1 : Rat) / 2) * x + C ((1 : Rat) / 3) * y + 1
  let box := denseBox2 degree
  { left := common * (box + C ((1 : Rat) / 5) * x + 1)
    right := common * (box + C ((1 : Rat) / 7) * y + 2) }

def runRational (input : RationalInput) : UInt64 :=
  checksum (gcd input.left input.right)

initialize rational0 : IO.Ref RationalInput ← IO.mkRef (prepRational 0)

def runRationalFixed (_ : Unit) : IO UInt64 := do
  return runRational (← rational0.get)

structure SquarefreeInput where
  polynomial : P2 Int
  deriving Hashable, Nonempty

def prepSquarefree (multiplicity : Nat) : SquarefreeInput :=
  let x : P2 Int := X 0
  let y : P2 Int := X 1
  { polynomial :=
      (x + y + 1) ^ multiplicity *
        (x + C 2 * y + 3) ^ (multiplicity + 1) }

def runSquarefree (input : SquarefreeInput) : UInt64 :=
  let decomp := sqfDecomp input.polynomial
  decomp.factors.foldl
    (fun acc factor =>
      mixHash (mixHash acc (checksum factor.factor))
        (hash factor.multiplicity))
    (hash decomp.content)

initialize squarefree1 : IO.Ref SquarefreeInput ←
  IO.mkRef (prepSquarefree 1)

def runSquarefreeFixed (_ : Unit) : IO UInt64 := do
  return runSquarefree (← squarefree1.get)

structure CofactorInput where
  dividend : P2 Int
  divisor : P2 Int
  deriving Hashable

def prepCofactor (degree : Nat) : CofactorInput :=
  let x : P2 Int := X 0
  let y : P2 Int := X 1
  let divisor := x + y + 1
  { dividend := divisor * (denseBox2 degree + x * y + 2)
    divisor := divisor }

def runCofactor (input : CofactorInput) : UInt64 :=
  match divExact? input.dividend input.divisor with
  | none => 0
  | some quotient => checksum quotient

/- The support fold visits each of the `n` terms once and compares fixed-arity
exponent vectors, so the term-count model is linear. -/
setup_benchmark runMonoContent n => n
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Coefficient content is one bounded-coefficient gcd per supported term, so
the `n`-term ladder has linear cost. -/
setup_benchmark runContent n => n
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Primitive part performs the linear content fold and one scalar traversal
over the same `n` terms. -/
setup_benchmark runPrimPart n => n
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Scalar content is the same bounded-coefficient gcd fold, hence linear in
the exact support size `n`. -/
setup_benchmark runScalarContent n => n
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Normalization reads the leading term and scales each of the `n` terms by a
unit, giving a linear support traversal. -/
setup_benchmark runPolyNormalize n => n
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Unit recognition inspects the canonical support and its sole coefficient;
the nonunit ladder still returns a checksum after the linear support-size
query, so the declared bound is linear. -/
setup_benchmark runPolyIsUnit n => n
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Recursive-view construction partitions `n` terms into a canonical map;
each insertion is logarithmic in the number of occupied coefficients. -/
setup_benchmark runToUnivariate n => n * Nat.log2 (n + 1)
  with prep := prepSupport
  where {
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384, 32768]
    signalFloorMultiplier := 1.0
  }

/- Named content and primitive part invoke recursive gcd production, for which
the SPEC gives probe counts rather than a full runtime model. They therefore
use canonical fixed registrations instead of invented asymptotics. -/
setup_fixed_benchmark runContentInFixed where {
  expectedHash := some 0xd1f9ea943ea7ea73
}
setup_fixed_benchmark runPrimPartInFixed where {
  expectedHash := some 0x358b5704b57e7de5
}

/- The public exact-division entry point is covered here on the same canonical
input as the other wrappers. The cofactor-heavy family below carries its
machine-operation model without constructing unrelated public results. -/
setup_fixed_benchmark runDivExactFixed where {
  expectedHash := some 0xeeadb45fd4afbeef
}

/- The public dispatcher, cofactor wrappers, list/lcm wrappers, and squarefree
operations are route-dependent. Canonical fixed registrations cover their API
surface; the isolated families below carry the scientific ladders. -/
setup_fixed_benchmark runGcdFixed where {
  expectedHash := some 0x01a55d7eea73bbb3
}
setup_fixed_benchmark runCofactorsFixed where {
  expectedHash := some 0x0cc3e4fb6781af05
}
setup_fixed_benchmark runIsCoprimeFixed where {
  expectedHash := some 0x000000000000000d
}
setup_fixed_benchmark runGcdListFixed where {
  expectedHash := some 0x01a55d7eea73bbb3
}
setup_fixed_benchmark runLcmFixed where {
  expectedHash := some 0x45d39921edcf59e0
}
setup_fixed_benchmark runSqfDecompFixed where {
  expectedHash := some 0xc2c56dd345ace7ce
}
setup_fixed_benchmark runRadicalFixed where {
  expectedHash := some 0x45d39921edcf59e0
}
setup_fixed_benchmark runIsSquarefreeFixed where {
  expectedHash := some 0x000000000000000d
}

/- The SPEC gives image-gcd probe counts, not full runtime models, for the
route-dependent families. Canonical fixed cases record their costs without
inventing asymptotics from degree alone. Phase 4 expands these representatives
across the full arity and shape matrix named by the SPEC. -/
setup_fixed_benchmark runCoprimeFamilyFixed where {
  expectedHash := some 0x42905229134041e6
}
setup_fixed_benchmark runDenseFixed where {
  expectedHash := some 0x78ec2b32b48ac34
}
setup_fixed_benchmark runSparseFixed where {
  expectedHash := some 0xb45fffc66bacdc5f
}

/- The extended PRS has no useful asymptotic bound in the SPEC. Fixed rungs
record coefficient swell without asserting a false scaling model. -/
setup_fixed_benchmark runSwell3 where {
  expectedHash := some 0x9fac850485b60c86
}
setup_fixed_benchmark runSwell4 where {
  expectedHash := some 0x9fac850485b60c86
}
setup_fixed_benchmark runSwell5 where {
  expectedHash := some 0x9fac850485b60c86
}

/- Denominator clearing and Yun's loop likewise inherit dispatcher-dependent
gcd costs. Their fixed cases exercise the rational lift and repeated-factor
paths without treating probe counts as machine-operation models. -/
setup_fixed_benchmark runRationalFixed where {
  expectedHash := some 0xf6040a6b74bc3ff1
}
setup_fixed_benchmark runSquarefreeFixed where {
  expectedHash := some 0x5262547c4fa35a9e
}

/-! # Informational FLINT comparator registrations

The pair returns the same canonical sparse term list, so `compare` also checks
cross-system agreement. The FLINT registration is scheduled-only;
python-flint must be installed in that environment. -/

setup_fixed_benchmark Flint.runFlintMpolyOverhead where
  Flint.flintCompareConfig 0x0000000000000007

setup_fixed_benchmark Flint.runLeanCoprime2 where
  Flint.leanCompareConfig 0x227808efbc4a0df6
setup_fixed_benchmark Flint.runFlintCoprime2 where
  Flint.flintCompareConfig 0x227808efbc4a0df6

/- With a three-term divisor and a dense quotient, exact division visits each
quotient/divisor term pair and performs logarithmic support updates. -/
setup_benchmark runCofactor n => n * n * Nat.log2 (n + 1)
  with prep := prepCofactor
  where {
    paramSchedule := .custom #[16, 32, 64, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    outerTrials := 3
  }

end Hex.MvGcdBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
