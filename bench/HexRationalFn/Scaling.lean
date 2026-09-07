/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn
import LeanBench

/-!
Operation-specific degree ladders over bounded rational coefficients. Preparation
does not normalize: the consecutive-polynomial pair has a literal Bezout proof.
Each returned polynomial is hashed in full. These registrations cover queries
and witness-size replay, not the library's remaining Phase-4 families.
-/

namespace Hex.RationalFnScaling
open DensePoly RationalFn

private instance : Inhabited (RationalFn Rat) := ⟨0⟩

/-- Dense monic inputs of degree `n`, with small positive integer coefficients. -/
def dense (n : Nat) : DensePoly Rat :=
  ofList ((List.range (n + 1)).map fun i =>
    if i = n then 1 else ((i % 3 + 1 : Nat) : Rat))

/-- Consecutive polynomials are coprime without any Euclidean computation. -/
def consecutive (p : DensePoly Rat) : RationalFn Rat :=
  let q := p + 1
  if h : q.leadingCoeff = 1 then
    ofCoprime p q h ⟨-1, 1, by dsimp [q]; grind⟩
  else panic! "nonmonic benchmark denominator"

/-- Full canonical output; array hashing is linear in the stored coefficient count. -/
def output (f : RationalFn Rat) : Array Rat × Array Rat := (f.num.toArray, f.den.toArray)

private instance : Hashable (RationalFn Rat) := ⟨fun f => hash (output f)⟩

structure QueryInput where
  f : RationalFn Rat
  equal : RationalFn Rat
  different : RationalFn Rat
  deriving Hashable

/-- Equal inputs have independently rebuilt arrays. Array equality visits high
indices first, so the constant coefficient is the last compared coefficient. -/
def prepQuery (n : Nat) : QueryInput :=
  -- The smoke runner probes zero; scientific parameters are all at least 128.
  let n := max n 1
  let p := dense n
  let copy := ofList p.toArray.reverse.toList.reverse
  ⟨consecutive p, consecutive copy,
    ofPoly (p + 1)⟩

def equal (i : QueryInput) : Bool := i.f == i.equal
def different (i : QueryInput) : Bool := i.f == i.different
def inverse (i : QueryInput) : Array Rat × Array Rat := output i.f⁻¹
def negate (i : QueryInput) : Array Rat × Array Rat := output (-i.f)
def evaluate (i : QueryInput) : Option Rat := eval? i.f (-1)

/-- The pole denominator is dense and vanishes at one. Its numerator is one,
so no pole disappears during canonicalization. -/
def prepPole (n : Nat) : RationalFn Rat :=
  let q : DensePoly Rat := (dense n) * #p[-1, 1]
  if h : q.leadingCoeff = 1 then ofCoprime 1 q h (Coprime.one_right q).symm
  else panic! "nonmonic pole denominator"

def evaluatePole (f : RationalFn Rat) : Option Rat := eval? f 1

def queryConfig : LeanBench.BenchmarkConfig :=
  { paramSchedule := .custom #[128, 256, 512, 1024, 2048, 4096, 8192, 16384],
    targetInnerNanos := 2000000000, maxSecondsPerCall := 10, outerTrials := 3 }

-- Linear two-sided model: equal independently allocated canonical arrays require Θ(n)
-- coefficient comparisons; all coefficients have bounded word-size values.
setup_benchmark equal n => n with prep := prepQuery where queryConfig
-- Linear two-sided model: array comparison visits n down to 0; the only
-- difference is at coefficient 0, after Θ(n) bounded-word comparisons.
setup_benchmark different n => n with prep := prepQuery where queryConfig
-- Linear two-sided model: monic-numerator inversion shares the swapped arrays;
-- the harness's complete output hash still requires Θ(n) bounded-word work.
setup_benchmark inverse n => n with prep := prepQuery where queryConfig
-- Linear two-sided model: negation traverses the degree-n numerator; full output hashing is
-- also Θ(n). Negation does not run a gcd or change coefficient bit lengths.
setup_benchmark negate n => n with prep := prepQuery where queryConfig
-- Linear two-sided model: Horner at -1 visits both arrays. Alternating partial sums of the
-- periodic coefficients are bounded, so rational arithmetic remains word-size.
setup_benchmark evaluate n => n with prep := prepQuery where queryConfig
-- Linear two-sided model: the dense denominator's Horner walk at 1 has Θ(n) bounded partial
-- sums (telescoping coefficients); numerator evaluation is skipped at the pole.
setup_benchmark evaluatePole n => n with prep := prepPole where queryConfig

structure ReplayInput where
  p : DensePoly Rat
  q : DensePoly Rat
  cert : Cert Rat

private instance : Hashable ReplayInput := ⟨fun i =>
  hash (i.p.toArray, i.q.toArray, i.cert.num.toArray, i.cert.den.toArray,
    i.cert.s.toArray, i.cert.t.toArray)⟩

/-- Hold the canonical degree at one and vary only a dense Bezout multiplier:
`s = -1 + h*q`, `t = 1 - h*p`. Validation still exercises the last identity. -/
def prepWitness (n : Nat) : ReplayInput :=
  let p : DensePoly Rat := #p[1, 1]
  let q : DensePoly Rat := #p[2, 1]
  let h := dense n
  ⟨p, q, ⟨p, q, -1 + h * q, 1 - h * p⟩⟩

def replay (i : ReplayInput) : Bool := check i.p i.q i.cert

/-- Reject only in the last Bezout identity, after traversing the witnesses. -/
def prepRejected (n : Nat) : ReplayInput :=
  let i := prepWitness n
  { i with cert := { i.cert with s := i.cert.s + 1 } }

def reject (i : ReplayInput) : Bool := check i.p i.q i.cert

-- Linear two-sided model: two dense degree-n witnesses multiply fixed linear polynomials
-- by schoolbook multiplication, then are added and compared. Θ(n) bounded
-- coefficient operations; this is a witness-size model, not a degree-gcd model.
setup_benchmark replay n => n with prep := prepWitness where queryConfig
-- Linear two-sided model: rejection occurs only after the same Θ(n) witness arithmetic.
setup_benchmark reject n => n with prep := prepRejected where queryConfig

/-- Fail on fixture drift independently of the benchmark result hashes. -/
def validate : IO Unit := do
  for n in [1, 2, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] do
    let i := prepQuery n
    unless i.f.num.size == n + 1 && i.f.den.size == n + 1 do
      throw (IO.userError s!"query degree mismatch at {n}")
    unless equal i && !(different i) do
      throw (IO.userError s!"equality fixture mismatch at {n}")
    unless i.f.num.size == i.different.num.size &&
        i.f.num.toArray.extract 1 (n + 1) == i.different.num.toArray.extract 1 (n + 1) &&
        i.f.num.coeff 0 != i.different.num.coeff 0 do
      throw (IO.userError s!"late-mismatch location drift at {n}")
    unless evaluate i == some (i.f.num.eval (-1) / i.f.den.eval (-1)) do
      throw (IO.userError s!"regular evaluation fixture mismatch at {n}")
    unless evaluatePole (prepPole n) == none do
      throw (IO.userError s!"pole fixture mismatch at {n}")
    unless replay (prepWitness n) && !(reject (prepRejected n)) do
      throw (IO.userError s!"witness fixture mismatch at {n}")
  IO.println "PASS: query and witness scaling fixtures"

private def ratJson (c : Rat) : Lean.Json := Lean.toJson (c.num, c.den)

private def polyJson (p : DensePoly Rat) : Lean.Json :=
  Lean.Json.arr (p.toArray.map ratJson)

private def fractionJson (f : RationalFn Rat) : Lean.Json :=
  Lean.Json.mkObj [("num", polyJson f.num), ("den", polyJson f.den)]

/-- Complete matched-input QQ fixtures for the persistent FLINT driver. The
zero parameter is a trivial-input timing control, not a scientific rung. -/
def emitFixtures : IO Unit := do
  for n in [0, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] do
    let i := prepQuery n
    let pole := prepPole n
    let optionJson := fun v => match v with
      | some r => ratJson r
      | none => Lean.Json.null
    for (name, op, operands, expected, point) in
        [("equal", "equal", #[i.f, i.equal], Lean.toJson (equal i), (-1 : Rat)),
         ("different", "equal", #[i.f, i.different], Lean.toJson (different i), -1),
         ("inverse", "inv", #[i.f], fractionJson i.f⁻¹, -1),
         ("negate", "neg", #[i.f], fractionJson (-i.f), -1),
         ("evaluate", "eval", #[i.f], optionJson (evaluate i), -1),
         ("evaluatePole", "eval", #[pole], optionJson (evaluatePole pole), 1)] do
      IO.println (Lean.Json.mkObj [
        ("schema_version", Lean.toJson (1 : Nat)), ("domain", Lean.toJson "QQ"),
        ("parameter", Lean.toJson n), ("benchmark", Lean.toJson s!"Hex.RationalFnScaling.{name}"),
        ("operation", Lean.toJson op), ("operands", Lean.Json.arr (operands.map fractionJson)),
        ("point", ratJson point), ("expected", expected)]).compress

end Hex.RationalFnScaling
