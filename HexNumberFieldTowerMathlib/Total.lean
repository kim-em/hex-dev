/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Flatten

public section

/-!
Total forms of the tower operations.

Each `Option`-valued tower operation has a completeness theorem showing it
never returns `none`. These definitions unwrap the option with that proof, so
users who import the companion can write `adjoin` instead of
`(adjoin? ..).get!`. Each is `Option.get` applied to the operation it names
and adds no computation of its own; the `Option`-valued operations remain the
conformance and performance owners.
-/

namespace Hex.NumberTower

/-- Adjoin a root to a tower; total by `adjoin?_isSome`. -/
def adjoin (T : NumberTower) (a : AlgebraicRoot) : Extension T :=
  (T.adjoin? a).get (adjoin?_isSome T a)

/-- Factor a polynomial over a tower; total by `factor?_isSome`. -/
def factor (T : NumberTower) (f : Poly T) : Factorization T f :=
  (T.factor? f).get (factor?_isSome T f)

/-- Split a polynomial over a tower; total by `split?_isSome`. -/
def split (T : NumberTower) (f : Poly T) : Splitting T f :=
  (T.split? f).get (split?_isSome T f)

/-- Flatten a tower to a primitive element; total by `flatten?_isSome`. -/
def flatten (T : NumberTower) : Flattening T :=
  T.flatten?.get (flatten?_isSome T)

@[simp] theorem adjoin?_eq_some (T : NumberTower) (a : AlgebraicRoot) :
    T.adjoin? a = some (T.adjoin a) :=
  (Option.some_get (adjoin?_isSome T a)).symm

@[simp] theorem factor?_eq_some (T : NumberTower) (f : Poly T) :
    T.factor? f = some (T.factor f) :=
  (Option.some_get (factor?_isSome T f)).symm

@[simp] theorem split?_eq_some (T : NumberTower) (f : Poly T) :
    T.split? f = some (T.split f) :=
  (Option.some_get (split?_isSome T f)).symm

@[simp] theorem flatten?_eq_some (T : NumberTower) :
    T.flatten? = some T.flatten :=
  (Option.some_get (flatten?_isSome T)).symm

end Hex.NumberTower
