/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Ambient
public import Mathlib.RingTheory.Algebraic.Integral

public section

namespace Hex.RealClosure

attribute [local instance] Polynomial.algebra
attribute [local instance 2000] Field.toGrindField
open scoped Hex.OrderedFn.Infinitesimal

private noncomputable abbrev ratFuncAlgebra (B R : Type*) [Field B] [Field R]
    [Algebra B R] : Algebra (RatFunc B) (RatFunc R) := by
  letI : FaithfulSMul B R :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr
      (RingHom.injective (algebraMap B R))
  exact RatFunc.liftAlgebra B (RatFunc R)

private theorem ratFunc_algebraic (B R : Type*) [Field B] [Field R]
    [Algebra B R] [Algebra.IsAlgebraic B R] :
    letI : Algebra (RatFunc B) (RatFunc R) := ratFuncAlgebra B R
    Algebra.IsAlgebraic (RatFunc B) (RatFunc R) := by
  letI : FaithfulSMul B R :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr
      (RingHom.injective (algebraMap B R))
  letI : Algebra (RatFunc B) (RatFunc R) := ratFuncAlgebra B R
  letI : IsScalarTower (Polynomial B) (RatFunc B) (RatFunc R) :=
    RatFunc.isScalarTower_liftAlgebra B (RatFunc R)
  have hfrac : Algebra.IsAlgebraic (Polynomial R) (RatFunc R) :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := Polynomial R) (K := RatFunc R) (C := RatFunc R)).mpr inferInstance
  letI : Algebra.IsAlgebraic (Polynomial R) (RatFunc R) := hfrac
  have hpoly : Algebra.IsAlgebraic (Polynomial B) (Polynomial R) := inferInstance
  letI : Algebra.IsAlgebraic (Polynomial B) (Polynomial R) := hpoly
  have h : Algebra.IsAlgebraic (Polynomial B) (RatFunc R) :=
    Algebra.IsAlgebraic.trans (Polynomial B) (Polynomial R) (RatFunc R)
  exact (IsFractionRing.comap_isAlgebraic_iff
    (A := Polynomial B) (K := RatFunc B) (C := RatFunc R)).mp h

private theorem ratFuncAlgebra_eq_map (B R : Type*) [Field B] [Field R]
    [Algebra B R] :
    letI : Algebra (RatFunc B) (RatFunc R) := ratFuncAlgebra B R
    algebraMap (RatFunc B) (RatFunc R) =
      RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap B R))
        (HexRationalFnMathlib.map_nonzero (algebraMap B R)) := by
  letI : Algebra (RatFunc B) (RatFunc R) := ratFuncAlgebra B R
  letI : FaithfulSMul B R :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr
      (RingHom.injective (algebraMap B R))
  letI : IsScalarTower (Polynomial B) (RatFunc B) (RatFunc R) :=
    RatFunc.isScalarTower_liftAlgebra B (RatFunc R)
  apply IsFractionRing.ringHom_ext (A := Polynomial B)
  intro p
  rw [← IsScalarTower.algebraMap_apply (Polynomial B) (RatFunc B) (RatFunc R) p]
  change (algebraMap (Polynomial R) (RatFunc R))
    (Polynomial.map (algebraMap B R) p) = _
  simpa only [RatFunc.coe_mapRingHom_eq_coe_map, map_one, div_one,
    Polynomial.coe_mapRingHom] using
    (RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap B R))
      (HexRationalFnMathlib.map_nonzero (algebraMap B R)) p 1).symm

private abbrev hexAlgebra (B R : Type*) [Field B] [Field R]
    [DecidableEq B] [DecidableEq R] [Algebra B R] :
    Algebra (Hex.RationalFn B) (Hex.RationalFn R) :=
  RingHom.toAlgebra (HexRationalFnMathlib.mapHom (algebraMap B R))

private theorem hex_algebraic (B R : Type*) [Field B] [Field R]
    [DecidableEq B] [DecidableEq R] [Algebra B R]
    [Algebra.IsAlgebraic B R] :
    letI : Algebra (Hex.RationalFn B) (Hex.RationalFn R) := hexAlgebra B R
    Algebra.IsAlgebraic (Hex.RationalFn B) (Hex.RationalFn R) := by
  letI : Algebra (Hex.RationalFn B) (Hex.RationalFn R) := hexAlgebra B R
  letI : Algebra (RatFunc B) (RatFunc R) := ratFuncAlgebra B R
  have h : RingHom.comp (algebraMap (RatFunc B) (RatFunc R))
        (HexRationalFnMathlib.equiv (K := B)).toRingHom =
      RingHom.comp (HexRationalFnMathlib.equiv (K := R)).toRingHom
        (algebraMap (Hex.RationalFn B) (Hex.RationalFn R)) := by
    ext q
    change (algebraMap (RatFunc B) (RatFunc R)) (HexRationalFnMathlib.toRatFunc q) =
      HexRationalFnMathlib.toRatFunc
        (HexRationalFnMathlib.mapHom (algebraMap B R) q)
    rw [ratFuncAlgebra_eq_map B R, HexRationalFnMathlib.toRatFunc_mapHom]
  have alg := ratFunc_algebraic B R
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (HexRationalFnMathlib.equiv (K := B))
    (HexRationalFnMathlib.equiv (K := R)) h).mp alg

namespace Ambient

/-- If the old coefficient field is algebraic over the base, the enlarged
real closure is algebraic over the mapped infinitesimal base. -/
theorem mapped_algebraic (B R : Type*) [Field B] [Field R]
    [DecidableEq B] [DecidableEq R] [LinearOrder R] [IsStrictOrderedRing R]
    [Algebra B R] [Algebra.IsAlgebraic B R]
    (ambient : Ambient (Hex.RationalFn R)) :
    letI : Algebra (Hex.RationalFn B) ambient.Carrier :=
      (mappedHom (algebraMap B R) ambient).toAlgebra
    Algebra.IsAlgebraic (Hex.RationalFn B) ambient.Carrier := by
  letI : Algebra (Hex.RationalFn B) (Hex.RationalFn R) := hexAlgebra B R
  letI : Algebra (Hex.RationalFn R) ambient.Carrier := ambient.inclusion.toAlgebra
  letI : Algebra (Hex.RationalFn B) ambient.Carrier :=
    (mappedHom (algebraMap B R) ambient).toAlgebra
  letI : IsScalarTower (Hex.RationalFn B) (Hex.RationalFn R) ambient.Carrier :=
    IsScalarTower.of_algebraMap_eq
      (R := Hex.RationalFn B) (S := Hex.RationalFn R) (A := ambient.Carrier)
      (fun _ => rfl)
  letI : Algebra.IsAlgebraic (Hex.RationalFn B) (Hex.RationalFn R) :=
    hex_algebraic B R
  letI : Algebra.IsAlgebraic (Hex.RationalFn R) ambient.Carrier :=
    ⟨fun x => ambient.algebraic x⟩
  exact Algebra.IsAlgebraic.trans (Hex.RationalFn B) (Hex.RationalFn R) ambient.Carrier

end Ambient

end Hex.RealClosure

/-- info: 'Hex.RealClosure.Ambient.mapped_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Ambient.mapped_algebraic
