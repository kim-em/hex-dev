/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn
import LeanBench
import HexRationalFn.Scaling
import HexRationalFn.Families
import HexRationalFn.Workloads
import HexRationalFn.Fixtures

/-!
Fixed-workload latency measurements, not fitted asymptotic claims: rational
coefficient growth is an independent variable. Prepared operands and certificates
are shared by competing algorithms. Every returned polynomial is hashed in full.
-/

namespace Hex.RationalFnBench
open Hex DensePoly RationalFn

private def digest (f : RationalFn Rat) : UInt64 :=
  mixHash (hash f.num.toArray) (hash f.den.toArray)

private instance : Inhabited (RationalFn Rat) := ⟨0⟩

private def fraction (p q : DensePoly Rat) : RationalFn Rat :=
  if h : q ≠ 0 then normalize p q h else panic! "benchmark denominator is zero"

structure Input where
  p : DensePoly Rat
  q : DensePoly Rat
  f : RationalFn Rat
  g : RationalFn Rat
  different : RationalFn Rat
  pole : RationalFn Rat
  cert : Cert Rat
  invalid : Cert Rat
  enlarged : Cert Rat

private def prepare (n cancellation bits : Nat) : Input :=
  let a : DensePoly Rat := ofList ((List.range (n + 1)).map fun i =>
    (if i = n then 1 else ((i % 3 + 1 : Nat) : Rat)))
  let b := a + 1
  let h : DensePoly Rat := monomial cancellation 1 + 1
  let scalar : Rat := (2 ^ bits + 1 : Nat) / (2 ^ bits + 3 : Nat)
  let p := scale scalar (a * h)
  let q := scale (-2) (b * h)
  let f := fraction a b
  let g := fraction b a
  let cert := if hq : q ≠ 0 then certifyWith defaultPlan p q hq
    else ⟨0, 1, 0, 1⟩
  let t : DensePoly Rat := monomial 32 1 + 1
  ⟨p, q, f, g, ofPoly (f.num + 1), fraction 1 #p[0, 1],
    cert, { cert with s := cert.s + 1 },
    { cert with s := cert.s + t * cert.den, t := cert.t - t * cert.num }⟩

initialize inputs : IO.Ref (Array Input) ← IO.mkRef <|
  (#[(4, 0, 1), (4, 4, 1), (12, 2, 1), (12, 12, 1),
     (4, 2, 16), (4, 2, 64), (4, 2, 256)].map fun (n, c, b) => prepare n c b)

private def collect (op : Input → UInt64) : IO UInt64 := do
  return (← inputs.get).foldl (fun h i => mixHash h (op i)) 0

def runNormalization (_ : Unit) : IO UInt64 :=
  collect fun i => digest (fraction i.p i.q)

def runAddition (_ : Unit) : IO UInt64 :=
  collect fun i => [i.f + i.g, i.f + i.f, i.f + (-i.f),
    i.f + fraction 1 (i.f.den * #p[1, 1])].foldl
      (fun h f => mixHash h (digest f)) 0

def runMultiplication (_ : Unit) : IO UInt64 :=
  collect fun i => mixHash (digest (i.f * i.g)) (digest (i.f * i.f))

private def naiveMul (f g : RationalFn Rat) : RationalFn Rat :=
  fraction (defaultPlan.mul f.num g.num) (defaultPlan.mul f.den g.den)

def runMultiplyNormalize (_ : Unit) : IO UInt64 :=
  collect fun i => mixHash (digest (naiveMul i.f i.g)) (digest (naiveMul i.f i.f))

def runHeight (_ : Unit) : IO UInt64 :=
  collect fun i => digest ((fraction i.p i.q) ^ (3 : Nat))

def runQueries (_ : Unit) : IO UInt64 :=
  collect fun i => mixHash (digest i.f⁻¹)
    (hash (i.f == i.f, ofPoly i.f.num == i.different, eval? i.f 2, eval? i.pole 0))

def runCalculus (_ : Unit) : IO UInt64 :=
  collect fun i =>
    let (p, r) := split (i.f ^ (3 : Nat))
    mixHash (mixHash (digest (derivative i.f)) (digest (derivative (i.f ^ (3 : Nat)))))
      (mixHash (hash p.toArray) (mixHash (digest r) (digest (i.f ^ (3 : Nat)))))

private def certHash (c : Cert Rat) : UInt64 :=
  mixHash (hash c.num.toArray) (mixHash (hash c.den.toArray)
    (mixHash (hash c.s.toArray) (hash c.t.toArray)))

def runGenerate (_ : Unit) : IO UInt64 :=
  collect fun i => if h : i.q ≠ 0 then certHash (certifyWith defaultPlan i.p i.q h) else 0

def runReplay (_ : Unit) : IO UInt64 :=
  collect fun i =>
    hash (check i.p i.q i.cert, check i.p i.q i.invalid, check i.p i.q i.enlarged)

initialize products : IO.Ref (Array (DensePoly Rat × DensePoly Rat)) ← IO.mkRef <|
  (#[16, 32, 64, 128].map fun n =>
    (ofList ((List.range n).map fun i => ((i % 7 + 1 : Nat) : Rat)),
     ofList ((List.range n).map fun i => ((i % 5 + 2 : Nat) : Rat))))

def runPlan (plan : MulPlan Rat) : IO UInt64 := do
  return (← products.get).foldl
    (fun h (p, q) => mixHash h (hash (plan.mul p q).toArray)) 0

def runSchoolbook (_ : Unit) : IO UInt64 := runPlan schoolbookPlan
def runKaratsuba1 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 1)
def runKaratsuba2 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 2)
def runKaratsuba4 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 4)
def runKaratsuba8 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 8)
def runKaratsuba16 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 16)
def runKaratsuba32 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 32)
def runKaratsuba64 (_ : Unit) : IO UInt64 := runPlan (karatsubaPlan 64)

/-- Fixed latency canaries deliberately make no rational bit-complexity claim. -/
def config : LeanBench.FixedBenchmarkConfig :=
  { repeats := 3, maxSecondsPerCall := 5.0, minTotalSeconds := 0.01 }

setup_fixed_benchmark runNormalization where { config with expectedHash := some 0xf08ce7f457ff8542 }
setup_fixed_benchmark runAddition where { config with expectedHash := some 0x11e29f67437451f7 }
setup_fixed_benchmark runMultiplication where { config with expectedHash := some 0x39fe48e581013f90 }
setup_fixed_benchmark runMultiplyNormalize where { config with expectedHash := some 0x39fe48e581013f90 }
setup_fixed_benchmark runHeight where { config with expectedHash := some 0x949f85f4efa83f9f }
setup_fixed_benchmark runQueries where { config with expectedHash := some 0xe9cda1597b0d8cf1 }
setup_fixed_benchmark runCalculus where { config with expectedHash := some 0xf22425efd6f4b137 }
setup_fixed_benchmark runGenerate where { config with expectedHash := some 0xcdcd8edb10154fa7 }
setup_fixed_benchmark runReplay where { config with expectedHash := some 0xb4b34400f0686b27 }
setup_fixed_benchmark runSchoolbook where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba1 where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba2 where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba4 where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba8 where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba16 where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba32 where { config with expectedHash := some 0x1260c30ce6946c8a }
setup_fixed_benchmark runKaratsuba64 where { config with expectedHash := some 0x1260c30ce6946c8a }


/-- Individual crossover rungs use the same prepared dense polynomials. -/
def runProduct (plan : MulPlan Rat) (index : Nat) : IO UInt64 := do
  let pairs ← products.get
  if h : index < pairs.size then
    let (p, q) := pairs[index]
    return hash (plan.mul p q).toArray
  throw (IO.userError "invalid crossover input")

def runSchoolbook16 (_ : Unit) : IO UInt64 := runProduct schoolbookPlan 0
setup_fixed_benchmark runSchoolbook16 where { config with expectedHash := some 0xcd839a69b2fb358a }
def runKaratsubaAt16 (_ : Unit) : IO UInt64 := runProduct defaultPlan 0
setup_fixed_benchmark runKaratsubaAt16 where { config with expectedHash := some 0xcd839a69b2fb358a }
def runSchoolbook32 (_ : Unit) : IO UInt64 := runProduct schoolbookPlan 1
setup_fixed_benchmark runSchoolbook32 where { config with expectedHash := some 0x2800282abbf42580 }
def runKaratsubaAt32 (_ : Unit) : IO UInt64 := runProduct defaultPlan 1
setup_fixed_benchmark runKaratsubaAt32 where { config with expectedHash := some 0x2800282abbf42580 }
def runSchoolbook64 (_ : Unit) : IO UInt64 := runProduct schoolbookPlan 2
setup_fixed_benchmark runSchoolbook64 where { config with expectedHash := some 0x54dc53949de9d9d5 }
def runKaratsubaAt64 (_ : Unit) : IO UInt64 := runProduct defaultPlan 2
setup_fixed_benchmark runKaratsubaAt64 where { config with expectedHash := some 0x54dc53949de9d9d5 }
def runSchoolbook128 (_ : Unit) : IO UInt64 := runProduct schoolbookPlan 3
setup_fixed_benchmark runSchoolbook128 where { config with expectedHash := some 0x418d85c40c381422 }
def runKaratsubaAt128 (_ : Unit) : IO UInt64 := runProduct defaultPlan 3
setup_fixed_benchmark runKaratsubaAt128 where { config with expectedHash := some 0x418d85c40c381422 }

initialize cancellationInputs : IO.Ref (Array Input) ← IO.mkRef <|
  (#[1, 2, 4, 8, 16].map fun n => prepare n 0 1)

def runCancel (index : Nat) (naive : Bool) : IO UInt64 := do
  let pairs ← cancellationInputs.get
  if h : index < pairs.size then
    let i := pairs[index]
    return digest (if naive then naiveMul i.f i.g
      else i.f * i.g)
  throw (IO.userError "invalid cancellation input")

def runCancel1 (_ : Unit) : IO UInt64 := runCancel 0 false
setup_fixed_benchmark runCancel1 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runNaive1 (_ : Unit) : IO UInt64 := runCancel 0 true
setup_fixed_benchmark runNaive1 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runCancel2 (_ : Unit) : IO UInt64 := runCancel 1 false
setup_fixed_benchmark runCancel2 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runNaive2 (_ : Unit) : IO UInt64 := runCancel 1 true
setup_fixed_benchmark runNaive2 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runCancel4 (_ : Unit) : IO UInt64 := runCancel 2 false
setup_fixed_benchmark runCancel4 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runNaive4 (_ : Unit) : IO UInt64 := runCancel 2 true
setup_fixed_benchmark runNaive4 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runCancel8 (_ : Unit) : IO UInt64 := runCancel 3 false
setup_fixed_benchmark runCancel8 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runNaive8 (_ : Unit) : IO UInt64 := runCancel 3 true
setup_fixed_benchmark runNaive8 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runCancel16 (_ : Unit) : IO UInt64 := runCancel 4 false
setup_fixed_benchmark runCancel16 where { config with expectedHash := some 0x2785d1bb85a2c29d }
def runNaive16 (_ : Unit) : IO UInt64 := runCancel 4 true
setup_fixed_benchmark runNaive16 where { config with expectedHash := some 0x2785d1bb85a2c29d }

/-- Full output agreement and representation-size diagnostics outside timing. -/
def validate : IO Unit := do
  for i in ← inputs.get do
    unless i.f * i.g == naiveMul i.f i.g do
      throw (IO.userError "cross-cancellation disagreement")
    unless check i.p i.q i.cert do throw (IO.userError "certificate rejected")
    unless check i.p i.q i.enlarged && !(check i.p i.q i.invalid) do
      throw (IO.userError "certificate mutation disagreement")
    let result := i.f * i.g
    let raw := i.f.num * i.g.num
    let bits := fun (p : DensePoly Rat) => p.toArray.foldl
      (fun n c => max n (max c.num.natAbs.log2 c.den.log2 + 1)) 0
    IO.println s!"input lengths={i.p.size}/{i.q.size}, coefficient bits={bits i.p}/{bits i.q}; multiplication raw lengths={raw.size}/{(i.f.den * i.g.den).size}, canonical={result.num.size}/{result.den.size}, raw bits={bits raw}, canonical bits={bits result.num}"
    let canonical := fraction i.p i.q
    let powered := canonical ^ (3 : Nat)
    IO.println s!"height canonical lengths={canonical.num.size}/{canonical.den.size}, bits={bits canonical.num}/{bits canonical.den}; cubed lengths={powered.num.size}/{powered.den.size}, bits={bits powered.num}/{bits powered.den}"
  for (p, q) in ← products.get do
    for cutoff in [16, 32, 64] do
      unless (karatsubaPlan cutoff).mul p q == p * q do
        throw (IO.userError "multiplication plan disagreement")

end Hex.RationalFnBench

def main (args : List String) : IO UInt32 := do
  if args == ["emit-workloads"] then
    Hex.RationalFnFixtures.emitFixtures
    return 0
  if args == ["emit-scaling"] then
    Hex.RationalFnScaling.emitFixtures
    return 0
  if args == ["sizes"] then
    Hex.RationalFnBench.validate
    Hex.RationalFnScaling.validate
    return 0
  LeanBench.Cli.dispatch args
