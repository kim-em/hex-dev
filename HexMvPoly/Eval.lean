/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Query

@[expose] public section

/-!
Direct, fixed-variable-order Horner, and partial evaluation for
`Hex.MvPoly`.
-/

namespace Hex.MvPoly

universe u v

variable {n : Nat} {R : Type u} {S : Type v}
  {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Evaluate coefficients through `f` and variables through `x`. Powers are
computed by repeated squaring in `Mono.prod`. -/
def eval₂ [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) : S :=
  p.foldTerms (fun acc m c => acc + f c * Mono.prod x m) 0

/-- Evaluate a polynomial at `x`. -/
def eval [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) : R :=
  eval₂ id x p

/-- A term whose coefficient has already been mapped into the target
semiring. -/
abbrev HornerTerm (n : Nat) (S : Type v) := Mono n × S

/-- Terms sharing one exponent in the variable currently being evaluated. -/
abbrev HornerGroup (n : Nat) (S : Type v) := Nat × List (HornerTerm n S)

/-- Read an exponent using a natural variable index, returning zero when the
index is out of range. -/
def hornerExponent (k : Nat) (m : Mono n) : Nat :=
  if h : k < n then m[(⟨k, h⟩ : Fin n)] else 0

/-- Add a term to an association list keyed by one variable exponent. -/
def insertHornerTerm (exponent : Nat) (term : HornerTerm n S) :
    List (HornerGroup n S) → List (HornerGroup n S)
  | [] => [(exponent, [term])]
  | group :: groups =>
      if group.1 = exponent then
        (group.1, term :: group.2) :: groups
      else
        group :: insertHornerTerm exponent term groups

/-- Insert an exponent group into descending exponent order. -/
def insertHornerGroupDesc (group : HornerGroup n S) :
    List (HornerGroup n S) → List (HornerGroup n S)
  | [] => [group]
  | group' :: groups =>
      if group'.1 < group.1 then
        group :: group' :: groups
      else
        group' :: insertHornerGroupDesc group groups

/-- Collect terms into groups keyed by their exponent at variable `k`. -/
def collectHornerGroups (k : Nat) (terms : List (HornerTerm n S)) :
    List (HornerGroup n S) :=
  terms.foldl
    (fun groups term => insertHornerTerm (hornerExponent k term.1) term groups) []

/-- Sort exponent groups from high exponent to low exponent. -/
def sortHornerGroups (groups : List (HornerGroup n S)) :
    List (HornerGroup n S) :=
  groups.foldl (fun sorted group => insertHornerGroupDesc group sorted) []

/-- Group terms by one variable exponent, ordered from high to low. -/
def hornerGroups (k : Nat) (terms : List (HornerTerm n S)) :
    List (HornerGroup n S) :=
  sortHornerGroups (collectHornerGroups k terms)

/-- Sparse Horner fold over already-evaluated coefficient groups. Missing
exponents are skipped with repeated-squaring powers. -/
def evalSparseHornerGroups [Lean.Grind.Semiring S]
    (x : S) : List (Nat × S) → S
  | [] => 0
  | group :: groups =>
      let state := groups.foldl
        (fun state group =>
          let previousExponent := state.1
          let acc := state.2
          let exponent := group.1
          (exponent, acc * Mono.powBySq x (previousExponent - exponent) + group.2))
        group
      state.2 * Mono.powBySq x state.1

/-- Evaluate sparse terms by fixed-order Horner in variables
`0, 1, ..., n - 1`. `fuel` is the number of variables left. -/
def eval₂HornerTerms [Lean.Grind.Semiring S]
    (xs : Nat → S) : Nat → Nat → List (HornerTerm n S) → S
  | 0, _, terms => terms.foldl (fun acc term => acc + term.2) 0
  | fuel + 1, k, terms =>
      let groups := hornerGroups k terms
      let evaluatedGroups := groups.map fun group =>
        (group.1, eval₂HornerTerms xs fuel (k + 1) group.2)
      evalSparseHornerGroups (xs k) evaluatedGroups

/-- Evaluate using fixed-variable-order sparse Horner evaluation. -/
def eval₂Horner [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) : S :=
  let xs : Nat → S := fun k => if h : k < n then x ⟨k, h⟩ else 0
  let terms := p.termsList.map fun term => (term.1, f term.2)
  eval₂HornerTerms xs n 0 terms

/-- Evaluate at `x` using fixed-variable-order sparse Horner evaluation. -/
def evalHorner [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) : R :=
  eval₂Horner id x p

/-- Erase the exponents of variables assigned by `s`. -/
def eraseAssigned (s : Fin n → Option R) (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun i => if (s i).isSome then 0 else m[i]

/-- Evaluate the variables assigned by `s`, leaving all other variables in
the same ambient polynomial ring. Terms that collide are combined. -/
def partialEval [Lean.Grind.Semiring R] [DecidableEq R]
    (s : Fin n → Option R) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc m c =>
      let assigned := Mono.prod (fun i => (s i).getD 1) m
      acc.addMonomial (eraseAssigned s m) (c * assigned))
    0

theorem eval₂_eq [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) :
    eval₂ f x p =
      p.termsList.foldl (fun acc term => acc + f term.2 * Mono.prod x term.1) 0 := by
  unfold eval₂ foldTerms termsList
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]

theorem eval_eq [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    eval x p =
      p.termsList.foldl (fun acc term => acc + term.2 * Mono.prod x term.1) 0 := by
  unfold eval
  simpa using eval₂_eq id x p

theorem eval₂Horner_eq [Zero R] [Lean.Grind.Semiring S]
    (f : R → S) (x : Fin n → S) (p : MvPoly n R cmp) :
    eval₂Horner f x p = eval₂ f x p := by
  sorry

theorem evalHorner_eq [Lean.Grind.Semiring R]
    (x : Fin n → R) (p : MvPoly n R cmp) :
    evalHorner x p = eval x p := by
  sorry

end Hex.MvPoly
