/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Uni

@[expose] public section

/-!
The recursive multivariate diophantine solver used by the Hensel stage loop.

At one recursion level, `sliceVar y 0` sets the selected non-main variable to
zero.  After solving that smaller problem, the solver corrects one power of
`y` at a time.  The coefficient at each power is again a problem in one fewer
active variable, and the recursion bottoms out in `solveUni`.

Every partial operation is represented by `Option`: unequal tuples are never
zipped or truncated, and a univariate right-hand side outside the degree range
of the partial-fraction map stops the computation.
-/

namespace Hex.MvHensel

open Hex
open Hex.MvPoly

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-! # Slicing and embedding -/

/-- The coefficient of `x_j ^ e`, kept in the original arity with `x_j`
removed from every retained monomial. -/
def sliceVar (j : Fin (n + 1)) (e : Nat)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  p.foldTerms
    (fun acc m c =>
      if Mono.degreeOf j m = e then
        acc.addMonomial (MvPoly.insertVar j 0 (MvPoly.removeVar j m)) c
      else acc)
    0

/-- Multiply a coefficient slice by the power which places it back at its
original coordinate. -/
def embedPower (j : Fin (n + 1)) (e : Nat)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  p * X j ^ e

/-- Embed an integer univariate polynomial in the selected main variable. -/
def embedUni (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (f : ZPoly) : MvPoly (n + 1) Int cmp :=
  MvPoly.ofUnivariate (cmp := cmp) i cmp'
    (DensePoly.ofCoeffs (f.toArray.map fun c => MvPoly.C c))

/-! # Checked tuple arithmetic -/

/-- Add two polynomial tuples, rejecting unequal lengths. -/
def tupleAdd? :
    List (MvPoly (n + 1) Int cmp) →
      List (MvPoly (n + 1) Int cmp) →
        Option (List (MvPoly (n + 1) Int cmp))
  | [], [] => some []
  | a :: as, b :: bs => do
      let tail ← tupleAdd? as bs
      some ((a + b) :: tail)
  | _, _ => none

/-- Form `Σ_j coefficients[j] * bases[j]`, rejecting unequal lengths. -/
def mvCombination? :
    List (MvPoly (n + 1) Int cmp) →
      List (MvPoly (n + 1) Int cmp) →
        Option (MvPoly (n + 1) Int cmp)
  | [], [] => some 0
  | a :: as, b :: bs => do
      let tail ← mvCombination? as bs
      some (a * b + tail)
  | _, _ => none

/-- Whether a reduced univariate right-hand side lies in the image of the
degree-bounded partial-fraction map.  The zero polynomial is below every
degree; a zero product has no usable degree bound. -/
def uniRange (q : Nat) (images : List ZPoly) (c : ZPoly) : Bool :=
  match (uniProduct images).degree? with
  | none => false
  | some bound =>
      match (reduceUni q c).degree? with
      | none => true
      | some degree => degree < bound

/-- The base solve, including the degree-range and tuple-length checks which
turn the total `solveUni` primitive into the partial public operation needed
by the multivariate recursion. -/
def solveUniChecked? (q : Nat) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (count : Nat) (images witness : List ZPoly) (c : ZPoly) :
    Option (List (MvPoly (n + 1) Int cmp)) :=
  if images.length != count || witness.length != count then none
  else if !uniRange q images c then none
  else
    let answer := solveUni q images witness c
    if answer.length != count then none
    else some (answer.map (embedUni (cmp := cmp) i cmp'))

/-! # Variable recursion -/

/-- Recursive worker.  `active` lists the non-main variables still present.
The public entry point supplies every remaining variable exactly once. -/
def diophantineAux (q : Nat) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (d : Fin n → Nat) (images witness : List ZPoly) :
    List (Fin n) → List (MvPoly (n + 1) Int cmp) →
      MvPoly (n + 1) Int cmp →
        Option (List (MvPoly (n + 1) Int cmp))
  | [], bs, c =>
      solveUniChecked? q i cmp' bs.length images witness
        (imageAt i cmp' (fun _ => 0) c)
  | y :: ys, bs, c => do
      let selected := remainingVar i y
      let lowerBs := bs.map (sliceVar selected 0)
      let initial ← diophantineAux q i cmp' d images witness ys lowerBs
        (sliceVar selected 0 c)
      (List.range (d y)).foldlM
        (fun current k => do
          let sum ← mvCombination? current bs
          let rhs := sliceVar selected (k + 1) (c - sum)
          let correction ←
            diophantineAux q i cmp' d images witness ys lowerBs rhs
          let raised := correction.map (embedPower selected (k + 1))
          tupleAdd? current raised)
        initial
termination_by active => active.length

/-- Check the main-variable degree bounds of a candidate tuple. -/
def mvDegreeBounded (i : Fin (n + 1)) (images : List ZPoly)
    (answer : List (MvPoly (n + 1) Int cmp)) : Bool :=
  images.length == answer.length &&
    (List.range images.length).all fun j =>
      MvPoly.degreeOf i (answer.getD j 0) <
        (images.getD j 0).degree?.getD 0

/-- Check the computed equation throughout the requested truncation box. -/
def checkDiophantine (q : Nat) (i : Fin (n + 1)) (d : Fin n → Nat)
    (bs answer : List (MvPoly (n + 1) Int cmp))
    (c : MvPoly (n + 1) Int cmp) : Bool :=
  match mvCombination? answer bs with
  | none => false
  | some sum => reduceMod q (truncate i d (sum - c)) == 0

/-- Solve `Σ_j Δ_j b_j ≡ c (mod q)` by recursing through the first `count`
non-main variables, then check the result inside the full degree box `d`.
Callers may omit a future-variable suffix known not to occur in the bases or
right-hand side; the unchanged final checker rejects an incorrect omission. -/
def diophantinePrefix (q : Nat) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (count : Nat) (d : Fin n → Nat)
    (bs : List (MvPoly (n + 1) Int cmp))
    (images witness : List ZPoly) (c : MvPoly (n + 1) Int cmp) :
    Option (List (MvPoly (n + 1) Int cmp)) := do
  if q ≤ 1 || images.isEmpty || images.length != witness.length ||
      images.length != bs.length then none else pure ()
  let answer ← diophantineAux q i cmp' d images witness
    ((List.finRange n).take count) bs c
  if !mvDegreeBounded i images answer then none
  else if !checkDiophantine q i d bs answer c then none
  else some answer

/-- Solve `Σ_j Δ_j b_j ≡ c (mod q)` inside the non-main degree box `d`,
with `deg_i Δ_j < deg images[j]`.  A malformed tuple, an out-of-range
recursive right-hand side, or a failed final equation returns `none`. -/
def diophantine (q : Nat) (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (d : Fin n → Nat) (bs : List (MvPoly (n + 1) Int cmp))
    (images witness : List ZPoly) (c : MvPoly (n + 1) Int cmp) :
    Option (List (MvPoly (n + 1) Int cmp)) :=
  diophantinePrefix q i cmp' n d bs images witness c

/-! # Mathematical contract -/

/-- Under the partial-fraction hypotheses and the load-bearing degree bound
on the multivariate bases, the recursive solve succeeds, satisfies the box
equation, and preserves each factor's main-variable degree bound. -/
theorem diophantine_spec {q : Nat} {i : Fin (n + 1)}
    {d : Fin n → Nat} {bs : List (MvPoly (n + 1) Int cmp)}
    {images witness : List ZPoly} {c : MvPoly (n + 1) Int cmp}
    (huni : UniValid q images witness)
    (hbs : bs.length = images.length)
    (hc : MvPoly.degreeOf i c < (uniProduct images).degree?.getD 0)
    (hb : ∀ j, j < bs.length →
      imageAt i cmp' (fun _ => 0) (bs.getD j 0) =
        (complements images).getD j 0)
    (hbdeg : ∀ j, j < bs.length →
      MvPoly.degreeOf i (bs.getD j 0) +
          (images.getD j 0).degree?.getD 0 ≤
        (uniProduct images).degree?.getD 0) :
    ∃ answer sum,
      diophantine q i cmp' d bs images witness c = some answer ∧
      mvCombination? answer bs = some sum ∧
      BoxCongr i d q sum c ∧
      ∀ j, j < images.length →
        MvPoly.degreeOf i (answer.getD j 0) <
          (images.getD j 0).degree?.getD 0 := by
  sorry

end Hex.MvHensel
