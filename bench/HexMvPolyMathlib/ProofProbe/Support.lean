/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib
public import HexMvPolyBench.Corpus

@[expose] public section

/-!
Shared inputs and the proof-probe-only sorted-list comparator for the
`HexMvPoly` kernel-reduction measurements.

The sorted form follows the computational shape of the open Mathlib
`MvSparsePoly` work: canonical ordered terms, single-pass addition, and
translated multiplication rows. Rows are merged in balanced rounds so the
comparison does not accidentally benchmark repeated linear insertion.
-/

namespace HexMvPolyMathlib.ProofProbe

open Hex
open Hex.MvPoly
open Hex.MvPolyBench.Corpus

namespace Sorted

/-- Proof-probe-only canonical sorted-list representation. Operations below
are the only constructors used by the probes, and maintain increasing
comparator order while removing zero coefficients. -/
structure Poly (n : Nat) (R : Type)
    (cmp : Mono n → Mono n → Ordering := Mono.lex) where
  terms : List (Mono n × R)
  deriving BEq, DecidableEq

variable {cmp : Mono n → Mono n → Ordering}
  {targetCmp : Mono k → Mono k → Ordering}

/-- Merge two increasing canonical term lists, combining equal monomials. -/
def merge [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    List (Mono n × R) → List (Mono n × R) → List (Mono n × R)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      match cmp x.1 y.1 with
      | .lt => x :: merge cmp xs (y :: ys)
      | .gt => y :: merge cmp (x :: xs) ys
      | .eq =>
          let coefficient := x.2 + y.2
          if coefficient = 0 then merge cmp xs ys
          else (x.1, coefficient) :: merge cmp xs ys
termination_by xs ys => xs.length + ys.length

/-- Insert one term through the same merge path used by addition. -/
def insert [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex)
    (terms : List (Mono n × R)) (term : Mono n × R) :
    List (Mono n × R) :=
  if term.2 = 0 then terms else merge cmp terms [term]

/-- Canonicalize an arbitrary term stream. Input construction is deliberately
outside the timed representation operations in the fresh-module probes. -/
def ofTerms [Zero R] [Add R] [DecidableEq R]
    (terms : List (Mono n × R))
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  ⟨terms.foldl (insert cmp) []⟩

instance [Zero R] : Zero (Poly n R cmp) where
  zero := ⟨[]⟩

instance [Zero R] [One R] [DecidableEq R] : One (Poly n R cmp) where
  one := if (1 : R) = 0 then ⟨[]⟩ else ⟨[(Mono.zero, 1)]⟩

/-- Single-pass canonical sparse addition. -/
def add [Zero R] [Add R] [DecidableEq R]
    (p q : Poly n R cmp) : Poly n R cmp :=
  ⟨merge cmp p.terms q.terms⟩

instance [Zero R] [Add R] [DecidableEq R] : Add (Poly n R cmp) where
  add := add

/-- Negate coefficients without changing the ordered support. -/
def neg [Neg R] (p : Poly n R cmp) : Poly n R cmp :=
  ⟨p.terms.map fun term => (term.1, -term.2)⟩

instance [Neg R] : Neg (Poly n R cmp) where
  neg := neg

/-- Sparse subtraction through merge addition. -/
def sub [Zero R] [Add R] [Neg R] [DecidableEq R]
    (p q : Poly n R cmp) : Poly n R cmp :=
  add p (neg q)

instance [Zero R] [Add R] [Neg R] [DecidableEq R] :
    Sub (Poly n R cmp) where
  sub := sub

/-- Merge adjacent translated rows once. -/
def mergeRound [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    List (List (Mono n × R)) → List (List (Mono n × R))
  | [] => []
  | [row] => [row]
  | first :: second :: rest =>
      merge cmp first second :: mergeRound cmp rest

/-- Repeated balanced merge rounds. The fuel is initialized to the row count;
each nontrivial round at least halves that count. -/
def mergeRows [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    Nat → List (List (Mono n × R)) → List (Mono n × R)
  | _, [] => []
  | _, [row] => row
  | 0, rows => rows.foldl (merge cmp) []
  | fuel + 1, rows => mergeRows cmp fuel (mergeRound cmp rows)

/-- Produce sorted translated rows and combine them in balanced merge rounds. -/
def mul [Zero R] [Add R] [Mul R] [DecidableEq R]
    (p q : Poly n R cmp) : Poly n R cmp :=
  let rows :=
    p.terms.map fun left =>
      q.terms.map fun right =>
        (Mono.mul left.1 right.1, left.2 * right.2)
  ⟨mergeRows cmp rows.length rows⟩

instance [Zero R] [Add R] [Mul R] [DecidableEq R] : Mul (Poly n R cmp) where
  mul := mul

/-- Linear-power helper used only by the structural substitution probe. -/
def pow [Zero R] [One R] [Add R] [Mul R] [DecidableEq R]
    (p : Poly n R cmp) : Nat → Poly n R cmp
  | 0 => 1
  | exponent + 1 => p * pow p exponent

/-- Constant polynomial. -/
def C [Zero R] [DecidableEq R] (coefficient : R)
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  if coefficient = 0 then 0 else ⟨[(Mono.zero, coefficient)]⟩

/-- Variable polynomial. -/
def X [Zero R] [One R] [DecidableEq R] (i : Fin n)
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  ⟨[(Mono.unit i, 1)]⟩

/-- Rename variables, canonicalizing collisions. -/
def rename [Zero R] [Add R] [DecidableEq R]
    (f : Fin n → Fin k) (p : Poly n R cmp)
    (targetCmp : Mono k → Mono k → Ordering := Mono.lex) : Poly k R targetCmp :=
  ofTerms (p.terms.map fun term => (Mono.rename f term.1, term.2)) targetCmp

/-- Evaluate one source monomial under a polynomial substitution. -/
def substMonomial [Zero R] [One R] [Add R] [Mul R] [DecidableEq R]
    (g : Fin n → Poly k R targetCmp) (m : Mono n) (coefficient : R) :
    Poly k R targetCmp :=
  (List.finRange n).foldl
    (fun acc i =>
      acc * pow (cmp := targetCmp) (g i) (Mono.degreeOf i m))
    (C coefficient targetCmp)

/-- Polynomial substitution for the collision probe. -/
def subst [Zero R] [One R] [Add R] [Mul R] [DecidableEq R]
    (g : Fin n → Poly k R targetCmp) (p : Poly n R cmp) : Poly k R targetCmp :=
  p.terms.foldl
    (fun acc term =>
      acc + substMonomial (targetCmp := targetCmp) g term.1 term.2)
    0

end Sorted

abbrev HexInt := MvPoly 4 Int Mono.lex
abbrev HexRat := MvPoly 4 Rat Mono.lex
abbrev SortedInt := Sorted.Poly 4 Int Mono.lex
abbrev SortedRat := Sorted.Poly 4 Rat Mono.lex

namespace Grevlex8

abbrev HexInt := MvPoly 8 Int Mono.grevlex
abbrev HexRat := MvPoly 8 Rat Mono.grevlex
abbrev SortedInt := Sorted.Poly 8 Int Mono.grevlex
abbrev SortedRat := Sorted.Poly 8 Rat Mono.grevlex

end Grevlex8

/-- Deterministic sparse eight-variable support. The first exponent makes the
source duplicate-free; the remaining exponents exercise genuinely
multivariate comparisons in a pseudo-random-looking but reproducible order. -/
def scatteredMono8 (i : Nat) : Mono 8 :=
  Hex.Vector.ofFn' fun j =>
    if j.val = 0 then i
    else ((i + 3 * j.val + 1) * (i + 5 * j.val + 7)) %
      (11 + 2 * j.val)

/-- Shared integer axis-support input in the production representation. -/
def hexAxisInt (size : Nat) (axis : Fin 4) (salt : Nat) : HexInt :=
  ofTerms (intTerms size salt (axisMono axis))

/-- Shared rational axis-support input in the production representation. -/
def hexAxisRat (size : Nat) (axis : Fin 4) (salt : Nat) : HexRat :=
  ofTerms (fracTerms size salt (axisMono axis))

/-- The same integer axis-support input in the sorted comparator. -/
def sortedAxisInt (size : Nat) (axis : Fin 4) (salt : Nat) : SortedInt :=
  Sorted.ofTerms (intTerms size salt (axisMono axis))

/-- The same rational axis-support input in the sorted comparator. -/
def sortedAxisRat (size : Nat) (axis : Fin 4) (salt : Nat) : SortedRat :=
  Sorted.ofTerms (fracTerms size salt (axisMono axis))

/-- A lexicographic addition workload covering separated and interleaved
supports in the production representation. -/
def hexAdditionLex (size : Nat) : Prop :=
  let separatedLeft : HexInt :=
    ofTerms (intTerms size 73 fun i => axisMono 0 i)
  let separatedRight : HexInt :=
    ofTerms (intTerms size 79 fun i => axisMono 0 (size + i))
  let interleavedLeft : HexInt :=
    ofTerms (intTerms size 83 fun i => axisMono 1 (2 * i))
  let interleavedRight : HexInt :=
    ofTerms (intTerms size 89 fun i => axisMono 1 (2 * i + 1))
  separatedLeft + separatedRight = separatedRight + separatedLeft ∧
    interleavedLeft + interleavedRight =
      interleavedRight + interleavedLeft

/-- The matching lexicographic addition workload in the sorted comparator. -/
def sortedAdditionLex (size : Nat) : Prop :=
  let separatedLeft : SortedInt :=
    Sorted.ofTerms (intTerms size 73 fun i => axisMono 0 i)
  let separatedRight : SortedInt :=
    Sorted.ofTerms (intTerms size 79 fun i => axisMono 0 (size + i))
  let interleavedLeft : SortedInt :=
    Sorted.ofTerms (intTerms size 83 fun i => axisMono 1 (2 * i))
  let interleavedRight : SortedInt :=
    Sorted.ofTerms (intTerms size 89 fun i => axisMono 1 (2 * i + 1))
  separatedLeft + separatedRight = separatedRight + separatedLeft ∧
    interleavedLeft + interleavedRight =
      interleavedRight + interleavedLeft

/-- A greater-arity grevlex addition workload on deterministic scattered
support in the production representation. -/
def hexAdditionGrevlex (size : Nat) : Prop :=
  let p : Grevlex8.HexInt :=
    ofTerms (intTerms size 97 scatteredMono8)
  let q : Grevlex8.HexInt :=
    ofTerms (intTerms size 101 fun i => scatteredMono8 (size + i))
  p + q = q + p

/-- The matching greater-arity grevlex addition workload in the sorted
comparator. -/
def sortedAdditionGrevlex (size : Nat) : Prop :=
  let p : Grevlex8.SortedInt :=
    Sorted.ofTerms (intTerms size 97 scatteredMono8) Mono.grevlex
  let q : Grevlex8.SortedInt :=
    Sorted.ofTerms
      (intTerms size 101 fun i => scatteredMono8 (size + i)) Mono.grevlex
  p + q = q + p

/-- Low-collision genuinely multivariate multiplication in the production
representation. -/
def hexMulSparse (size : Nat) : Prop :=
  let p : HexInt := ofTerms (intTerms size 103 (patternedMono size · 3))
  let q : HexInt := ofTerms (intTerms size 107 (patternedMono size · 5))
  p * q = q * p

/-- The matching low-collision multiplication in the sorted comparator. -/
def sortedMulSparse (size : Nat) : Prop :=
  let p : SortedInt :=
    Sorted.ofTerms (intTerms size 103 (patternedMono size · 3))
  let q : SortedInt :=
    Sorted.ofTerms (intTerms size 107 (patternedMono size · 5))
  p * q = q * p

/-- High-collision rational multiplication at arity eight under grevlex in the
production representation. -/
def hexMulCollide (size : Nat) : Prop :=
  let p : Grevlex8.HexRat :=
    ofTerms (fracTerms size 109 (axisMono (0 : Fin 8)))
  let q : Grevlex8.HexRat :=
    ofTerms (fracTerms size 113 (axisMono (0 : Fin 8)))
  p * q = q * p

/-- The matching high-collision rational multiplication in the sorted
comparator. -/
def sortedMulCollide (size : Nat) : Prop :=
  let p : Grevlex8.SortedRat :=
    Sorted.ofTerms
      (fracTerms size 109 (axisMono (0 : Fin 8))) Mono.grevlex
  let q : Grevlex8.SortedRat :=
    Sorted.ofTerms
      (fracTerms size 113 (axisMono (0 : Fin 8))) Mono.grevlex
  p * q = q * p

/-- Cancellation-heavy integer identity in the production representation. -/
def hexCancellationInt (size : Nat) : Prop :=
  let p := hexAxisInt size 0 37
  let q := hexAxisInt size 1 41
  (p + q) * (p + q) - (p * p + q * q) = p * q + q * p

/-- Cancellation-heavy rational identity in the production representation. -/
def hexCancellationRat (size : Nat) : Prop :=
  let p := hexAxisRat size 0 43
  let q := hexAxisRat size 1 47
  (p + q) * (p + q) - (p * p + q * q) = p * q + q * p

/-- The integer cancellation identity in the sorted comparator. -/
def sortedCancellationInt (size : Nat) : Prop :=
  let p := sortedAxisInt size 0 37
  let q := sortedAxisInt size 1 41
  (p + q) * (p + q) - (p * p + q * q) = p * q + q * p

/-- The rational cancellation identity in the sorted comparator. -/
def sortedCancellationRat (size : Nat) : Prop :=
  let p := sortedAxisRat size 0 43
  let q := sortedAxisRat size 1 47
  (p + q) * (p + q) - (p * p + q * q) = p * q + q * p

/-- Three-polynomial square expansion used as a representative SOS
certificate identity in the production representation. -/
def hexSos (size : Nat) : Prop :=
  let p := hexAxisInt size 0 59
  let q := hexAxisInt size 1 61
  let r := hexAxisInt size 2 67
  (p + q + r) * (p + q + r) =
    p * p + p * q + p * r +
    (q * p + q * q + q * r) +
    (r * p + r * q + r * r)

/-- The same representative SOS identity in the sorted comparator. -/
def sortedSos (size : Nat) : Prop :=
  let p := sortedAxisInt size 0 59
  let q := sortedAxisInt size 1 61
  let r := sortedAxisInt size 2 67
  (p + q + r) * (p + q + r) =
    p * p + p * q + p * r +
    (q * p + q * q + q * r) +
    (r * p + r * q + r * r)

/-- Collision-heavy four-variable input in the production representation. -/
def hexStructuralInput (size : Nat) : HexInt :=
  ofTerms (intTerms size 53 (collisionMono size))

/-- The same collision-heavy input in the sorted comparator. -/
def sortedStructuralInput (size : Nat) : SortedInt :=
  Sorted.ofTerms (intTerms size 53 (collisionMono size))

/-- Renaming to variables agrees with substitution by those variables in the
production representation. -/
def hexStructural (size : Nat) : Prop :=
  let f : Fin 4 → Fin 2 := fun i => if i.val % 2 = 0 then 0 else 1
  rename Mono.lex f (hexStructuralInput size) =
    subst (targetCmp := Mono.lex) (fun i => X (f i)) (hexStructuralInput size)

/-- The matching collision identity in the sorted comparator. -/
def sortedStructural (size : Nat) : Prop :=
  let f : Fin 4 → Fin 2 := fun i => if i.val % 2 = 0 then 0 else 1
  Sorted.rename f (sortedStructuralInput size) =
    Sorted.subst (fun i => Sorted.X (f i)) (sortedStructuralInput size)

end HexMvPolyMathlib.ProofProbe
