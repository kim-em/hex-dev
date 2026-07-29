/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly

@[expose] public section

/-!
Deterministic input generators shared by the native `HexMvPoly` benchmark and
the external CompPoly and Mathlib `MvSparsePoly` comparator adapters.

This file deliberately does not import LeanBench or Mathlib. Comparator drivers
translate the returned term lists into their own representations, so every
implementation receives the same monomials and coefficients.
-/

namespace Hex.MvPolyBench.Corpus

open Hex
open Hex.MvPoly

/-- Deterministic nonzero signed benchmark coefficient. -/
def coeffValue (size i salt : Nat) : Int :=
  let magnitude : Int :=
    Int.ofNat (((i + 3) * (salt + 11) + size * 17 + i * i * 5) % 251 + 1)
  if (i + salt) % 2 = 0 then magnitude else -magnitude

/-- Monomial supported on one coordinate. -/
def axisMono {arity : Nat} (axis : Fin arity) (exponent : Nat) : Mono arity :=
  Hex.Vector.ofFn' fun i => if i.val = axis then exponent else 0

/-- A genuinely multivariate monomial whose first coordinate keeps sources
duplicate-free. In a square, the first two coordinate sums `(i+j, i²+j²)`
uniquely determine the unordered source pair, so the output support is
quadratic rather than a modular-collision artifact. The third coordinate keeps
the different salted SOS inputs disjoint. -/
def patternedMono (_size i salt : Nat) : Mono 4 :=
  Hex.Vector.ofFn' fun j =>
    if j.val = 0 then i
    else if j.val = 1 then i * i + salt
    else if j.val = 2 then (i + 1) * (salt + 2)
    else (i * i + i + 1) * (salt + 3)

/-- A duplicate-free source monomial designed to collide after even variables
are erased or the four variables are paired into two targets. -/
def collisionMono (size i : Nat) : Mono 4 :=
  Hex.Vector.ofFn' fun j =>
    if j.val = 0 then i
    else if j.val = 1 then i % 8
    else if j.val = 2 then size - i
    else i % 8

/-- A duplicate-free source monomial for partial evaluation. The two evaluated
coordinates encode `i < 1024` in base 32, so their exponents stay bounded while
the two surviving coordinates deliberately collapse to eight destination
keys. -/
def partialEvalMono (i : Nat) : Mono 4 :=
  Hex.Vector.ofFn' fun j =>
    if j.val = 0 then i % 32
    else if j.val = 1 then i % 8
    else if j.val = 2 then (i / 32) % 32
    else i % 8

/-- Integer terms for a deterministic sparse support. -/
def intTerms {arity : Nat} (size salt : Nat) (key : Nat → Mono arity) :
    List (Mono arity × Int) :=
  (List.range size).map fun i => (key i, coeffValue size i salt)

/-- Integral-valued rational terms matching `intTerms` coefficient-for-
coefficient, retained as a controlled representation-overhead input for
external comparator adapters. -/
def ratTerms {arity : Nat} (size salt : Nat) (key : Nat → Mono arity) :
    List (Mono arity × Rat) :=
  (List.range size).map fun i => (key i, Rat.ofInt (coeffValue size i salt))

/-- Rational terms with genuine but bounded non-unit denominators. Cycling
through small primes exercises normalization without making coefficient
bit-size, rather than sparse structure, the benchmark parameter. -/
def fracTerms {arity : Nat} (size salt : Nat) (key : Nat → Mono arity) :
    List (Mono arity × Rat) :=
  (List.range size).map fun i =>
    let den : Int :=
      match (i + salt) % 5 with
      | 0 => 2
      | 1 => 3
      | 2 => 5
      | 3 => 7
      | _ => 11
    let numerator := coeffValue size i salt
    let coprimeNumerator :=
      if numerator % den = 0 then numerator + 1 else numerator
    (key i, Rat.divInt coprimeNumerator den)

/- The comparator adapters rely on duplicate-free sources. Keep representative
largest-rung checks beside the generators so a corpus edit cannot silently
change `ofTerms` from insertion into coefficient summation. -/
#guard ((intTerms 256 3 (axisMono (0 : Fin 4))).map Prod.fst).Nodup
#guard ((intTerms 4096 13 (patternedMono 4096 · 1)).map Prod.fst).Nodup
#guard ((intTerms 1024 53 (collisionMono 1024)).map Prod.fst).Nodup
#guard ((intTerms 1024 71 partialEvalMono).map Prod.fst).Nodup
#guard (fracTerms 64 29 (axisMono (0 : Fin 4))).all (·.2.den != 1)

end Hex.MvPolyBench.Corpus
