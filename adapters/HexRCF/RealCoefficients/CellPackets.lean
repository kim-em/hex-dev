/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RowOperations
public import HexRealClosure.RootReplay
public section
namespace Hex.RCF.RealCoefficients.CellPackets
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [one : One E] [add : Add E] [sub : Sub E] [mul : Mul E] [nat : NatCast E]

/-- The same checked linear-head binding and complete selected row, with the
coefficient operations explicit in the type. -/
structure Point (sign : E → Int) (binding : Ctx) (point : E)
    (queries : List (DensePoly E)) where
  root : Descriptor E Ctx sign binding
  bound : (root.raw.head - Isolation.pointQuery point).isZero = true
  signs : SelectedSigns root queries

/-- Existing adjacent-root evidence, independent of the full table wrapper. -/
structure Bounds (sign : E → Int) (binding : Ctx)
    (roots : List (Descriptor E Ctx sign binding)) (cut : Fin (roots.length+1)) where
  point : E
  left : (h : 0 < cut.val) → SelectedSigns
    (roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) [Isolation.pointQuery point]
  leftSign : ∀ h, (left h).value = -1
  right : (h : cut.val < roots.length) → SelectedSigns
    (roots.get ⟨cut.val, h⟩) [Isolation.pointQuery point]
  rightSign : ∀ h, (right h).value = 1

structure Sector (sign : E → Int) (binding : Ctx)
    (roots : List (Descriptor E Ctx sign binding)) (cut : Fin (roots.length+1))
    (queries : List (DensePoly E)) where
  sector : Bounds sign binding roots cut
  row : Point sign binding sector.point queries

@[expose] def Point.changeOps (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E)
    (otherMul : Mul E) (otherNat : NatCast E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub)
    (hm : otherMul = mul) (hn : otherNat = nat)
    (sign : E → Int) (binding : Ctx) (point : E) (queries : List (DensePoly E))
    (source : @Point E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding point queries) :
    @Point E Ctx _ _ _ one add sub mul nat sign binding point queries :=
  let root := @Point.root E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding point queries source
  let bound := @Point.bound E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding point queries source
  let signs := @Point.signs E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding point queries source
  @Point.mk E Ctx _ _ _ one add sub mul nat sign binding point queries
    (@Descriptor.changeOps E Ctx _ _ _ one add sub mul nat otherOne otherAdd otherSub otherMul otherNat
      ho ha hs hm hn sign binding root)
    (by
      cases ho; cases ha; cases hs; cases hm; cases hn
      simpa only [Descriptor.changeOps_self] using bound)
    (@RowOperations.changeOps E Ctx _ _ _ one add sub mul nat otherOne otherAdd otherSub otherMul otherNat
      ho ha hs hm hn sign binding root queries signs)

@[expose] def Bounds.reindex (sign : E → Int) (binding : Ctx)
    {first second : List (Descriptor E Ctx sign binding)} (same : first = second)
    (cut : Fin (first.length+1)) (source : Bounds sign binding first cut) :
    Bounds sign binding second (Fin.cast (congrArg (fun roots => roots.length+1) same) cut) := by
  cases same
  exact source

@[expose] def Bounds.changeOps (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E)
    (otherMul : Mul E) (otherNat : NatCast E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub)
    (hm : otherMul = mul) (hn : otherNat = nat)
    (sign : E → Int) (binding : Ctx)
    (roots : List (@Descriptor E Ctx _ _ otherOne otherAdd otherSub otherMul otherNat _ sign binding))
    (cut : Fin (roots.length+1))
    (source : @Bounds E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut) :
    @Bounds E Ctx _ _ _ one add sub mul nat sign binding
      (roots.map (@Descriptor.changeOps E Ctx _ _ _ one add sub mul nat
        otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn sign binding))
      (Fin.cast (by simp only [List.length_map]) cut) := by
  cases ho; cases ha; cases hs; cases hm; cases hn
  have same : roots.map (Descriptor.changeOps one add sub mul nat rfl rfl rfl rfl rfl sign binding) = roots :=
    List.map_id'' (fun root => Descriptor.changeOps_self sign binding root) roots
  exact Bounds.reindex sign binding same.symm cut source

end Hex.RCF.RealCoefficients.CellPackets
