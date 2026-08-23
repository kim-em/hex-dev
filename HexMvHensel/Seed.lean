/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Diophantine

@[expose] public section

/-!
Input data and leading-coefficient preparation for multivariate Hensel
lifting.  `Setup` remains in `Uni`; this module extends that stable object
with the full checked input contract.
-/

namespace Hex.MvHensel

open Hex
open Hex.MvPoly

/-- The starting data for one multivariate lift. -/
structure Input (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp] [IsMonomialOrder cmp'] where
  setup : Setup n
  target : MvPoly (n + 1) Int cmp
  images : List ZPoly
  leading : List (MvPoly n Int cmp')
  witness : List ZPoly

/-- Failures retain the distinction between malformed input, an unsuitable
point or prime, and failure to reconstruct at the available modulus. -/
inductive Failure where
  | arity
  | degreeDrop
  | imageProduct
  | leadingProduct
  | leadingImage (j : Nat)
  | primeDividesLc (j : Nat)
  | notCoprime
  | witnessDegree (j : Nat)
  | reconstruct (modulus : Nat)
  deriving BEq, DecidableEq, Repr

/-- Retry policy for reconstruction failures. -/
structure Config where
  doublings : Nat
  deriving BEq, DecidableEq, Repr

namespace Config

/-- Six exponent doublings after the initial attempt. -/
def default : Config := { doublings := 6 }

end Config

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-- Ordered product of multivariate polynomials. -/
def mvProduct {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] (fs : List (MvPoly k Int order)) :
    MvPoly k Int order :=
  fs.foldl (· * ·) 1

/-- Replace the coefficient at the main-variable degree of `p` by `L`. -/
def setLc (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (p : MvPoly (n + 1) Int cmp) :
    MvPoly (n + 1) Int cmp :=
  let q := MvPoly.toUnivariate i cmp' p
  let degree := MvPoly.degreeOf i p
  let size := max q.size (degree + 1)
  let coefficients := Array.ofFn (n := size) fun k =>
    if k.val = degree then L else q.coeff k.val
  MvPoly.ofUnivariate (cmp := cmp) i cmp'
    (DensePoly.ofCoeffs coefficients)

/-- Embed a univariate image and replace its leading coefficient by `L`. -/
def seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (F : ZPoly) :
    MvPoly (n + 1) Int cmp :=
  if F.size = 0 then 0
  else
    let coefficients := Array.ofFn (n := F.size) fun k =>
      if k.val + 1 = F.size then L else MvPoly.C (F.coeff k.val)
    MvPoly.ofUnivariate (cmp := cmp) i cmp'
      (DensePoly.ofCoeffs coefficients)

/-- Keep only variables whose indices are below `count`; this is evaluation
of every later variable at zero without changing the arity. -/
def prefixVars {k : Nat} {order : Mono k → Mono k → Ordering}
    [IsMonomialOrder order] (count : Nat) (p : MvPoly k Int order) :
    MvPoly k Int order :=
  p.restrictBy fun m =>
    decide (∀ j : Fin k, count ≤ j.val → Mono.degreeOf j m = 0)

/-- Keep the main variable and the first `count` remaining variables, setting
all later remaining variables to zero. -/
def prefixNonMain (i : Fin (n + 1)) (count : Nat)
    (p : MvPoly (n + 1) Int cmp) : MvPoly (n + 1) Int cmp :=
  p.restrictBy fun m =>
    decide (∀ j : Fin n, count ≤ j.val →
      Mono.degreeOf (remainingVar i j) m = 0)

/-- Build all seeds without any default indexing or prefix truncation. -/
def seedTuple? (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp'] :
    List ZPoly → List (MvPoly n Int cmp') →
      Option (List (MvPoly (n + 1) Int cmp))
  | [], [] => some []
  | F :: Fs, L :: Ls => do
      let tail ← seedTuple? i cmp' Fs Ls
      some (seed i cmp' (prefixVars 0 L) F :: tail)
  | _, _ => none

/-! The elementary seed laws are Phase-1 proof obligations. -/

theorem imageAt_seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (a : Fin n → Int) (L : MvPoly n Int cmp') (F : ZPoly)
    (h : MvPoly.eval a L = F.leadingCoeff) :
    imageAt i cmp' a (seed (cmp := cmp) i cmp' L F) = F := by
  sorry

theorem lcIn_seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (F : ZPoly) (hF : F.size ≠ 0) (hL : L ≠ 0) :
    lcIn i cmp' (seed (cmp := cmp) i cmp' L F) = L := by
  sorry

theorem degreeOf_seed (i : Fin (n + 1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (L : MvPoly n Int cmp') (F : ZPoly) (hL : L ≠ 0) :
    MvPoly.degreeOf i (seed (cmp := cmp) i cmp' L F) =
      F.degree?.getD 0 := by
  sorry

end Hex.MvHensel
