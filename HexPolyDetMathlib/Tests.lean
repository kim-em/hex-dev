/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import HexPolyDetMathlib.NoFallbackTests
import HexPolyDetMathlib.Bird.Audit

open Lean

open Matrix

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1; 1, x] = (det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) R)).value :=
  (det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) R)).proof

example {R : Type} [CommRing R] (x : R) :
    Matrix.det (fun i j : Fin 2 => if i = j then x else 1) =
      (det% ((fun i j : Fin 2 => if i = j then x else 1) : Matrix (Fin 2) (Fin 2) R)).value :=
  (det% ((fun i j : Fin 2 => if i = j then x else 1) : Matrix (Fin 2) (Fin 2) R)).proof

example {R : Type} [CommRing R] (x : R) :
    Matrix.det (Matrix.ofArray #[x, 1, 1, x] (by rfl) : Matrix (Fin 2) (Fin 2) R) =
      (det% (Matrix.ofArray #[x, 1, 1, x] (by rfl) : Matrix (Fin 2) (Fin 2) R)).value :=
  (det% (Matrix.ofArray #[x, 1, 1, x] (by rfl) : Matrix (Fin 2) (Fin 2) R)).proof

example {R : Type} [CommRing R] (x : R) :
    Matrix.det (Matrix.of ![![x, 1], ![1, x]]) = x*x - 1 := by
  det

example {R : Type} [CommRing R] (x : R) : Matrix.det !![x, 1; 1, x] = x * x - 1 := by
  det

example {R : Type} [CommRing R] (x : R) : x * x - 1 = Matrix.det !![x, 1; 1, x] := by
  det

example {R : Type} [CommRing R] (x : R) : True := by
  det (maxRelationWork := 100) (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) R) with d hd
  have : Matrix.det !![x, 1; 1, x] = d := hd
  trivial

example {R : Type} [CommRing R] (x : R) : Matrix.det !![x, 1; 1, x] = x * x - 1 := by
  simp only [Hex.normPolyDet]
  ring

example (x : Int) : Matrix.det (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) = x - x - 2 := by
  det

example (a b : ZMod 3) : Matrix.det !![a, 0; 0, b] = a*b + 3*a*b := by
  det

example (x : ZMod 2) : Matrix.det !![-2*x, 0, 0; 0, x, 0; 0, 0, x] = 0 := by
  det

example (a b : ZMod 4) : Matrix.det !![a, 0; 0, b] = a*b + 4*a*b := by
  det

example {R : Type} [CommRing R] [CharP R 4] (a b : R) :
    Matrix.det !![a, 0; 0, b] = a*b + 4*a*b := by
  det

example : True := by
  det (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) with d hd
  have : d = -2 := by rfl
  have : Matrix.det !![(1 : Int), 2; 3, 4] = d := hd
  trivial

example (x : ZMod 2) :
    (det% (!![-2*x, 0, 0; 0, x, 0; 0, 0, x] : Matrix (Fin 3) (Fin 3) (ZMod 2))).value = 0 := by
  rfl

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1; 1, x] = (det% !![x, 1; 1, x]).value :=
  (det% !![x, 1; 1, x]).proof

example {R : Type} [CommRing R] (x : R) : True := by
  det !![x, 1; 1, x] with d hd
  trivial

example (x : Int) : Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by
  fail_if_success det (maxRelationWork := 0)
  fail_if_success det (maxHeartbeats := 0)
  det

example : Matrix.det (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) = -2 := by
  det -packing

example {R : Type} [CommRing R] [CharP R (2 + 2)] (a b : R) :
    Matrix.det !![a, 0; 0, b] = a*b + 4*a*b := by
  det

example (x y : Rat) :
    Matrix.det !![x/y, 1; 1, x/y] = (x/y)^2 - 1 := by
  det

example (x y : Rat) :
    Matrix.det !![(x/y)/(x/y), 1; 1, (x/y)/(x/y)] =
      ((x/y)/(x/y))^2 - 1 := by
  det

example (x : Rat) : Matrix.det !![x/0, 1; 1, x] = -1 := by
  det

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1; 1, x] + 1 = x*x := by
  simp only [Hex.normPolyDet]
  ring

example {R : Type} [CommRing R] (x y : R)
    (h : Matrix.det !![x, 1; 1, x] = y) : y = x*x - 1 := by
  simp only [Hex.normPolyDet] at h
  calc
    y = -1 + x ^ 2 := h.symm
    _ = x*x - 1 := by ring

example {R : Type} [CommRing R] (x y : R)
    (h : Matrix.det !![x, 1; 1, x] = y) :
    Matrix.det !![x, 1; 1, x] = y := by
  fail_if_success det
  exact h

example {R : Type} [CommRing R] (x : R) :
    (det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) R)).value = -1 + x ^ 2 := by
  rfl

example (x : Int) :
    (det% (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int)).value =
      x ^ 3 - 2 * x := by
  ring

example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      x ^ 4 - 3 * x ^ 2 + 1 := by
  det

example : HexMatrixMathlib.Certified Matrix.det
    (!![(1 : Rat), 2; 3, 4] : Matrix (Fin 2) (Fin 2) Rat) :=
  det% !![1, 2; 3, 4]

example {R : Type} [CommRing R] (x : R) :
    Matrix.det (fun i j : Fin 2 => if i = j then x else 1) = x ^ 2 - 1 := by
  det

example {R : Type} [CommRing R] (x : R) : True := by
  let xs : Array R := #[x, 1, 1, x]
  det (Matrix.ofArray xs (by rfl) : Matrix (Fin 2) (Fin 2) R) with d hd
  have : d = -1 + x ^ 2 := by rfl
  trivial

example {R : Type} [Field R] (a b c d u v w x : R) :
    Matrix.det !![a/u, b/v; c/w, d/x] = a*d/(u*x)-b*c/(v*w) := by
  det

example {R : Type} [Field R] (a b c d u v : R) :
    Matrix.det !![a*c/u, a*d/u; b*c/v, b*d/v] = 0 := by
  det

example {R : Type} [Field R] (a b c d : R) :
    Matrix.det !![a/b*(c/d)-a/d*(c/b), 0; a, b] = 0 := by
  det

example {R : Type} [Field R] (a : R)
    (h : Matrix.det !![a/a] = 1) : Matrix.det !![a/a] = 1 := by
  fail_if_success det
  exact h

example {R : Type} [CommRing R] :
    Matrix.det (Matrix.ofArray #[] (by rfl) : Matrix (Fin 0) (Fin 0) R) = 1 := by
  det

example {R : Type} [CommRing R] (x : R) : Matrix.det !![x] = x := by
  det

example (x : Rat) :
    (det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Rat)).value = -1 + x ^ 2 := by
  rfl

example {R : Type} [CommRing R] (x y : R) :
    Matrix.det !![x + y, 0; 0, 1] = x + y := by
  det
