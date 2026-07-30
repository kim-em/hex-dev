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

/-- Merge two increasing canonical term lists, combining equal monomials.

The worker is structurally recursive on fuel rather than using a generated
well-founded recursion theorem. The public entry point supplies exactly the
sum of the input lengths, so the exhausted-fuel branch is unreachable for
canonical calls. This keeps kernel reduction focused on the list merge itself.
-/
def merge [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex)
    (left right : List (Mono n × R)) : List (Mono n × R) :=
  go (left.length + right.length) left right
where
  go : Nat → List (Mono n × R) → List (Mono n × R) → List (Mono n × R)
    | _, [], ys => ys
    | _, xs, [] => xs
    | 0, xs, ys => xs ++ ys
    | fuel + 1, x :: xs, y :: ys =>
        match cmp x.1 y.1 with
        | .lt => x :: go fuel xs (y :: ys)
        | .gt => y :: go fuel (x :: xs) ys
        | .eq =>
            let coefficient := x.2 + y.2
            if coefficient = 0 then go fuel xs ys
            else (x.1, coefficient) :: go fuel xs ys

/-- Insert one term through the same merge path used by addition. -/
def insert [Zero R] [Add R] [DecidableEq R]
    (cmp : Mono n → Mono n → Ordering := Mono.lex)
    (terms : List (Mono n × R)) (term : Mono n × R) :
    List (Mono n × R) :=
  if term.2 = 0 then terms else merge cmp terms [term]

/-- Canonicalize an arbitrary term stream by repeated insertion. -/
def ofTerms [Zero R] [Add R] [DecidableEq R]
    (terms : List (Mono n × R))
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  ⟨terms.foldl (insert cmp) []⟩

/-- Whether a term stream has strictly increasing, hence distinct, keys. -/
def strictlyOrdered
    (cmp : Mono n → Mono n → Ordering := Mono.lex) :
    List (Mono n × R) → Bool
  | [] | [_] => true
  | first :: second :: rest =>
      cmp first.1 second.1 == .lt &&
        strictlyOrdered cmp (second :: rest)

/-- Use the linear construction path for an already sorted term stream.

Zero coefficients are discarded first. A checked fallback through `ofTerms`
keeps the proxy canonical if a benchmark corpus ever violates its advertised
strict-order precondition. -/
def ofSortedTerms [Zero R] [Add R] [DecidableEq R]
    (terms : List (Mono n × R))
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  let filtered := terms.filter fun term => term.2 != 0
  if strictlyOrdered cmp filtered then
    ⟨filtered⟩
  else
    ofTerms filtered cmp

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

/-- Produce sorted translated rows and combine them in balanced merge rounds.
Translation preserves row order because `cmp` is a monomial order. -/
def mul [Zero R] [Add R] [Mul R] [DecidableEq R] [IsMonomialOrder cmp]
    (p q : Poly n R cmp) : Poly n R cmp :=
  let rows :=
    p.terms.map fun left =>
      q.terms.map fun right =>
        (Mono.mul left.1 right.1, left.2 * right.2)
  ⟨mergeRows cmp rows.length rows⟩

instance [Zero R] [Add R] [Mul R] [DecidableEq R] [IsMonomialOrder cmp] :
    Mul (Poly n R cmp) where
  mul := mul

/-- Linear-power helper used only by the structural substitution probe. -/
def pow [Zero R] [One R] [Add R] [Mul R] [DecidableEq R]
    [IsMonomialOrder cmp]
    (p : Poly n R cmp) : Nat → Poly n R cmp
  | 0 => 1
  | exponent + 1 =>
      let q := pow p ((exponent + 1) / 2)
      let q2 := q * q
      if (exponent + 1) % 2 = 0 then q2 else q2 * p
termination_by exponent => exponent
decreasing_by omega

/-- Constant polynomial. -/
def C [Zero R] [DecidableEq R] (coefficient : R)
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  if coefficient = 0 then 0 else ⟨[(Mono.zero, coefficient)]⟩

/-- Variable polynomial. -/
def X [Zero R] [One R] [DecidableEq R] (i : Fin n)
    (cmp : Mono n → Mono n → Ordering := Mono.lex) : Poly n R cmp :=
  if (1 : R) = 0 then 0 else ⟨[(Mono.unit i, 1)]⟩

/-- Rename variables, canonicalizing collisions. -/
def rename [Zero R] [Add R] [DecidableEq R]
    (f : Fin n → Fin k) (p : Poly n R cmp)
    (targetCmp : Mono k → Mono k → Ordering := Mono.lex) : Poly k R targetCmp :=
  ofTerms (p.terms.map fun term => (Mono.rename f term.1, term.2)) targetCmp

/-- Evaluate one source monomial under a polynomial substitution. -/
def substMonomial [Zero R] [One R] [Add R] [Mul R] [DecidableEq R]
    [IsMonomialOrder targetCmp]
    (g : Fin n → Poly k R targetCmp) (m : Mono n) (coefficient : R) :
    Poly k R targetCmp :=
  (List.finRange n).foldl
    (fun acc i =>
      acc * pow (cmp := targetCmp) (g i) (Mono.degreeOf i m))
    (C coefficient targetCmp)

/-- Polynomial substitution for the collision probe. -/
def subst [Zero R] [One R] [Add R] [Mul R] [DecidableEq R]
    [IsMonomialOrder targetCmp]
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

namespace Grlex4

abbrev HexInt := MvPoly 4 Int Mono.grlex
abbrev SortedInt := Sorted.Poly 4 Int Mono.grlex

end Grlex4

namespace Grlex8

abbrev HexInt := MvPoly 8 Int Mono.grlex
abbrev SortedInt := Sorted.Poly 8 Int Mono.grlex

end Grlex8

namespace Grevlex2

abbrev HexInt := MvPoly 2 Int Mono.grevlex
abbrev SortedInt := Sorted.Poly 2 Int Mono.grevlex

end Grevlex2

namespace Grevlex4

abbrev HexInt := MvPoly 4 Int Mono.grevlex
abbrev SortedInt := Sorted.Poly 4 Int Mono.grevlex

end Grevlex4

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
    if j.val = 0 then 256 * i
    else ((i + 3 * j.val + 1) * (i + 5 * j.val + 7)) %
      (11 + 2 * j.val)

/-- Embed the shared four-variable patterned support in arity eight. -/
def patternedMono8 (size i salt : Nat) : Mono 8 :=
  Hex.Vector.ofFn' fun j =>
    if h : j.val < 4 then
      let j4 : Fin 4 := ⟨j.val, h⟩
      (patternedMono size i salt)[j4]
    else 0

/-! Every proof-probe stream takes the intended linear sorted-input path. -/

example : Sorted.strictlyOrdered Mono.lex
    (intTerms 32 73 fun i => axisMono (0 : Fin 4) i) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.lex
    (intTerms 32 79 fun i => axisMono (0 : Fin 4) (32 + i)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.lex
    (intTerms 32 83 fun i => axisMono (1 : Fin 4) (2 * i)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.lex
    (intTerms 32 89 fun i => axisMono (1 : Fin 4) (2 * i + 1)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 32 97 scatteredMono8) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 32 101 fun i => scatteredMono8 (32 + i)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grlex
    (intTerms 6 103 (patternedMono8 6 · 3)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grlex
    (intTerms 6 107 (patternedMono8 6 · 5)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (fracTerms 8 109 (axisMono (0 : Fin 8))) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (fracTerms 8 113 (axisMono (0 : Fin 8))) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.lex
    (intTerms 6 37 (axisMono (0 : Fin 4))) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.lex
    (fracTerms 6 43 (axisMono (0 : Fin 4))) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 4 59 (patternedMono 4 · 3)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 4 61 (patternedMono 4 · 7)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 4 67 (patternedMono 4 · 11)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 3 59 (patternedMono 3 · 3)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 3 61 (patternedMono 3 · 7)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grevlex
    (intTerms 3 67 (patternedMono 3 · 11)) := by
  decide +kernel
example : Sorted.strictlyOrdered Mono.grlex
    (intTerms 8 53 (collisionMono 8)) := by
  decide +kernel
example :
    let f : Fin 4 → Fin 2 :=
      fun j => if j.val % 2 = 0 then 0 else 1
    Mono.rename f (collisionMono 8 0) =
        Mono.rename f (collisionMono 8 1) ∧
      Mono.rename f (collisionMono 8 2) =
        Mono.rename f (collisionMono 8 3) ∧
      Mono.rename f (collisionMono 8 4) =
        Mono.rename f (collisionMono 8 5) ∧
      Mono.rename f (collisionMono 8 6) =
        Mono.rename f (collisionMono 8 7) := by
  decide +kernel

/-- Shared integer axis-support input in the production representation. -/
def hexAxisInt (size : Nat) (axis : Fin 4) (salt : Nat) : HexInt :=
  ofTerms (intTerms size salt (axisMono axis))

/-- Shared rational axis-support input in the production representation. -/
def hexAxisRat (size : Nat) (axis : Fin 4) (salt : Nat) : HexRat :=
  ofTerms (fracTerms size salt (axisMono axis))

/-- The same integer axis-support input in the sorted comparator. -/
def sortedAxisInt (size : Nat) (axis : Fin 4) (salt : Nat) : SortedInt :=
  Sorted.ofSortedTerms (intTerms size salt (axisMono axis))

/-- The same rational axis-support input in the sorted comparator. -/
def sortedAxisRat (size : Nat) (axis : Fin 4) (salt : Nat) : SortedRat :=
  Sorted.ofSortedTerms (fracTerms size salt (axisMono axis))

/-- Four inputs for the separated and interleaved addition cases. -/
structure AdditionInputs (P : Type) where
  separatedLeft : P
  separatedRight : P
  interleavedLeft : P
  interleavedRight : P

/-- Lexicographic production inputs, shared by construction and arithmetic
probes so their construction cost can be measured separately. -/
def hexAdditionLexInputs (size : Nat) : AdditionInputs HexInt where
  separatedLeft :=
    ofTerms (intTerms size 73 fun i => axisMono 0 i)
  separatedRight :=
    ofTerms (intTerms size 79 fun i => axisMono 0 (size + i))
  interleavedLeft :=
    ofTerms (intTerms size 83 fun i => axisMono 1 (2 * i))
  interleavedRight :=
    ofTerms (intTerms size 89 fun i => axisMono 1 (2 * i + 1))

/-- Matching lexicographic sorted-list inputs. -/
def sortedAdditionLexInputs (size : Nat) : AdditionInputs SortedInt where
  separatedLeft :=
    Sorted.ofSortedTerms (intTerms size 73 fun i => axisMono 0 i)
  separatedRight :=
    Sorted.ofSortedTerms (intTerms size 79 fun i => axisMono 0 (size + i))
  interleavedLeft :=
    Sorted.ofSortedTerms (intTerms size 83 fun i => axisMono 1 (2 * i))
  interleavedRight :=
    Sorted.ofSortedTerms (intTerms size 89 fun i => axisMono 1 (2 * i + 1))

/-- Greater-arity grevlex production inputs. -/
def hexAdditionGrevlexInputs (size : Nat) :
    Grevlex8.HexInt × Grevlex8.HexInt :=
  (ofTerms (intTerms size 97 scatteredMono8),
    ofTerms (intTerms size 101 fun i => scatteredMono8 (size + i)))

/-- Matching greater-arity grevlex sorted-list inputs. -/
def sortedAdditionGrevlexInputs (size : Nat) :
    Grevlex8.SortedInt × Grevlex8.SortedInt :=
  (Sorted.ofSortedTerms
      (intTerms size 97 scatteredMono8) Mono.grevlex,
    Sorted.ofSortedTerms
      (intTerms size 101 fun i => scatteredMono8 (size + i))
      Mono.grevlex)

/-- A lexicographic addition workload covering separated and interleaved
supports in the production representation. -/
def hexAdditionLex (size : Nat) : Prop :=
  let input := hexAdditionLexInputs size
  input.separatedLeft + input.separatedRight =
      input.separatedRight + input.separatedLeft ∧
    input.interleavedLeft + input.interleavedRight =
      input.interleavedRight + input.interleavedLeft

/-- The matching lexicographic addition workload in the sorted comparator. -/
def sortedAdditionLex (size : Nat) : Prop :=
  let input := sortedAdditionLexInputs size
  input.separatedLeft + input.separatedRight =
      input.separatedRight + input.separatedLeft ∧
    input.interleavedLeft + input.interleavedRight =
      input.interleavedRight + input.interleavedLeft

/-- A greater-arity grevlex addition workload on deterministic scattered
support in the production representation. -/
def hexAdditionGrevlex (size : Nat) : Prop :=
  let input := hexAdditionGrevlexInputs size
  input.1 + input.2 = input.2 + input.1

/-- The matching greater-arity grevlex addition workload in the sorted
comparator. -/
def sortedAdditionGrevlex (size : Nat) : Prop :=
  let input := sortedAdditionGrevlexInputs size
  input.1 + input.2 = input.2 + input.1

/-- Construction-only production workload matched to `hexAdditionLex` and
`hexAdditionGrevlex`. -/
def hexAdditionInputs (size : Nat) : Prop :=
  let lex := hexAdditionLexInputs size
  let grevlex := hexAdditionGrevlexInputs size
  lex.separatedLeft.termCount = size ∧
    lex.separatedRight.termCount = size ∧
    lex.interleavedLeft.termCount = size ∧
    lex.interleavedRight.termCount = size ∧
    grevlex.1.termCount = size ∧
    grevlex.2.termCount = size

/-- Construction-only sorted-list workload matched to the addition
candidate. -/
def sortedAdditionInputs (size : Nat) : Prop :=
  let lex := sortedAdditionLexInputs size
  let grevlex := sortedAdditionGrevlexInputs size
  lex.separatedLeft.terms.length = size ∧
    lex.separatedRight.terms.length = size ∧
    lex.interleavedLeft.terms.length = size ∧
    lex.interleavedRight.terms.length = size ∧
    grevlex.1.terms.length = size ∧
    grevlex.2.terms.length = size

/-- Low-collision genuinely multivariate multiplication in the production
representation. -/
def hexMulSparse (size : Nat) : Prop :=
  let p : Grlex8.HexInt :=
    ofTerms (intTerms size 103 (patternedMono8 size · 3))
  let q : Grlex8.HexInt :=
    ofTerms (intTerms size 107 (patternedMono8 size · 5))
  p * q = q * p

/-- The matching low-collision multiplication in the sorted comparator. -/
def sortedMulSparse (size : Nat) : Prop :=
  let p : Grlex8.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 103 (patternedMono8 size · 3))
      Mono.grlex
  let q : Grlex8.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 107 (patternedMono8 size · 5))
      Mono.grlex
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
    Sorted.ofSortedTerms
      (fracTerms size 109 (axisMono (0 : Fin 8))) Mono.grevlex
  let q : Grevlex8.SortedRat :=
    Sorted.ofSortedTerms
      (fracTerms size 113 (axisMono (0 : Fin 8))) Mono.grevlex
  p * q = q * p

/-- Construction-only production workload matched to high-collision
multiplication. -/
def hexMulCollideInputs (size : Nat) : Prop :=
  let p : Grevlex8.HexRat :=
    ofTerms (fracTerms size 109 (axisMono (0 : Fin 8)))
  let q : Grevlex8.HexRat :=
    ofTerms (fracTerms size 113 (axisMono (0 : Fin 8)))
  p.termCount = size ∧ q.termCount = size

/-- Matching construction-only sorted-list multiplication workload. -/
def sortedMulCollideInputs (size : Nat) : Prop :=
  let p : Grevlex8.SortedRat :=
    Sorted.ofSortedTerms
      (fracTerms size 109 (axisMono (0 : Fin 8))) Mono.grevlex
  let q : Grevlex8.SortedRat :=
    Sorted.ofSortedTerms
      (fracTerms size 113 (axisMono (0 : Fin 8))) Mono.grevlex
  p.terms.length = size ∧ q.terms.length = size

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

/-- Construction-only production workload matched to the integer and rational
cancellation identities. -/
def hexCancellationInputs (size : Nat) : Prop :=
  let intLeft := hexAxisInt size 0 37
  let intRight := hexAxisInt size 1 41
  let ratLeft := hexAxisRat size 0 43
  let ratRight := hexAxisRat size 1 47
  intLeft.termCount = size ∧
    intRight.termCount = size ∧
    ratLeft.termCount = size ∧
    ratRight.termCount = size

/-- Matching construction-only sorted-list cancellation workload. -/
def sortedCancellationInputs (size : Nat) : Prop :=
  let intLeft := sortedAxisInt size 0 37
  let intRight := sortedAxisInt size 1 41
  let ratLeft := sortedAxisRat size 0 43
  let ratRight := sortedAxisRat size 1 47
  intLeft.terms.length = size ∧
    intRight.terms.length = size ∧
    ratLeft.terms.length = size ∧
    ratRight.terms.length = size

/-- Three-polynomial square expansion used as a representative SOS
certificate identity in the production representation. -/
def hexSos (size : Nat) : Prop :=
  let p : Grevlex4.HexInt :=
    ofTerms (intTerms size 59 (patternedMono size · 3))
  let q : Grevlex4.HexInt :=
    ofTerms (intTerms size 61 (patternedMono size · 7))
  let r : Grevlex4.HexInt :=
    ofTerms (intTerms size 67 (patternedMono size · 11))
  (p + q + r) * (p + q + r) =
    p * p + p * q + p * r +
    (q * p + q * q + q * r) +
    (r * p + r * q + r * r)

/-- The same representative SOS identity in the sorted comparator. -/
def sortedSos (size : Nat) : Prop :=
  let p : Grevlex4.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 59 (patternedMono size · 3)) Mono.grevlex
  let q : Grevlex4.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 61 (patternedMono size · 7)) Mono.grevlex
  let r : Grevlex4.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 67 (patternedMono size · 11)) Mono.grevlex
  (p + q + r) * (p + q + r) =
    p * p + p * q + p * r +
    (q * p + q * q + q * r) +
    (r * p + r * q + r * r)

/-- Construction-only production workload matched to the SOS identity. -/
def hexSosInputs (size : Nat) : Prop :=
  let p : Grevlex4.HexInt :=
    ofTerms (intTerms size 59 (patternedMono size · 3))
  let q : Grevlex4.HexInt :=
    ofTerms (intTerms size 61 (patternedMono size · 7))
  let r : Grevlex4.HexInt :=
    ofTerms (intTerms size 67 (patternedMono size · 11))
  p.termCount = size ∧ q.termCount = size ∧ r.termCount = size

/-- Matching construction-only sorted-list SOS workload. -/
def sortedSosInputs (size : Nat) : Prop :=
  let p : Grevlex4.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 59 (patternedMono size · 3)) Mono.grevlex
  let q : Grevlex4.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 61 (patternedMono size · 7)) Mono.grevlex
  let r : Grevlex4.SortedInt :=
    Sorted.ofSortedTerms
      (intTerms size 67 (patternedMono size · 11)) Mono.grevlex
  p.terms.length = size ∧
    q.terms.length = size ∧
    r.terms.length = size

/-- Collision-heavy four-variable input in the production representation. -/
def hexStructuralInput (size : Nat) : Grlex4.HexInt :=
  ofTerms (intTerms size 53 (collisionMono size))

/-- The same collision-heavy input in the sorted comparator. -/
def sortedStructuralInput (size : Nat) : Grlex4.SortedInt :=
  Sorted.ofSortedTerms
    (intTerms size 53 (collisionMono size)) Mono.grlex

/-- Construction-only production workload matched to the structural
collision identity. -/
def hexStructuralInputs (size : Nat) : Prop :=
  (hexStructuralInput size).termCount = size

/-- Matching construction-only sorted-list structural workload. -/
def sortedStructuralInputs (size : Nat) : Prop :=
  (sortedStructuralInput size).terms.length = size

/-- Renaming to variables agrees with substitution by those variables in the
production representation. -/
def hexStructural (size : Nat) : Prop :=
  let f : Fin 4 → Fin 2 := fun i => if i.val % 2 = 0 then 0 else 1
  rename Mono.grevlex f (hexStructuralInput size) =
    subst (targetCmp := Mono.grevlex)
      (fun i => X (cmp := Mono.grevlex) (f i))
      (hexStructuralInput size)

/-- The matching collision identity in the sorted comparator. -/
def sortedStructural (size : Nat) : Prop :=
  let f : Fin 4 → Fin 2 := fun i => if i.val % 2 = 0 then 0 else 1
  Sorted.rename f (sortedStructuralInput size) Mono.grevlex =
    Sorted.subst
      (fun i => Sorted.X (cmp := Mono.grevlex) (f i))
      (sortedStructuralInput size)

end HexMvPolyMathlib.ProofProbe
