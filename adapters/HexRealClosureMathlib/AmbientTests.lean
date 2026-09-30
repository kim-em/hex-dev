/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Ambient
public import HexRealClosureMathlib.Deflation

public section

open Hex.RealClosure
open scoped Hex.OrderedFn.Infinitesimal

example : ∃ s : (Ambient.infinitesimal Rat).Carrier,
    0 < s ∧ s ^ 2 = Ambient.nativeHom HexRationalFnMathlib.ratField_eq
      (Ambient.infinitesimal Rat) (Hex.RationalFn.X : Hex.RationalFn Rat) ∧
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat)
      (Hex.RationalFn.X : Hex.RationalFn Rat) < s ∧ s < 1 := by
  simp only [Ambient.nativeHom_X]
  exact Ambient.exists_sqrt_X (Ambient.infinitesimal Rat)

example (f : Hex.RationalFn Rat) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f =
      (SignType.sign (Ambient.nativeHom HexRationalFnMathlib.ratField_eq
        (Ambient.infinitesimal Rat) f) : Int) :=
  Ambient.nativeHom_sign HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f

example (a : Rat) :
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat)
      (Hex.RationalFn.C a : Hex.RationalFn Rat) =
      (Ambient.infinitesimal Rat).inclusion
        (@Hex.RationalFn.C Rat (Field.toGrindField (K := Rat)) inferInstance a) :=
  Ambient.nativeHom_C HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) a

example (f h : Hex.RationalFn Rat) :
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) (f + h) =
      Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f +
        Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) h :=
  (Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat)).map_add f h

example (f : Hex.RationalFn Rat) :
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f = 0 ↔
      f = 0 :=
  Ambient.nativeHom_zero HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f

example (f : Hex.RationalFn Rat) :
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f⁻¹ =
      (Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f)⁻¹ :=
  Ambient.nativeHom_inv HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f

example (f h : Hex.RationalFn Rat) :
    Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) (f / h) =
      Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f /
        Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) h :=
  Ambient.nativeHom_div HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) f h

/-- The native interpretation supplies the actual deflation bridge hypotheses. -/
example (root : Hex.RationalFn Rat) :
    HexPolyMathlib.Interpret.interpret
      (Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat))
      (Ambient.nativeHom_zero HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat))
      (linearFactor root) = Polynomial.X - Polynomial.C
        (Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat) root) := by
  letI : Field (Hex.RationalFn Rat) := HexPolyMathlib.fieldOfGrind
  let hom := Ambient.nativeHom HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat)
  exact interpret_linearFactor hom
    (Ambient.nativeHom_zero HexRationalFnMathlib.ratField_eq (Ambient.infinitesimal Rat))
    hom.map_one (fun a b => map_sub hom a b) root
