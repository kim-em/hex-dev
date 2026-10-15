/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellPackets
public section
namespace Hex.RCF.RealCoefficients.CellPackets
open Hex Hex.RealClosure Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [one : One E] [add : Add E] [sub : Sub E] [mul : Mul E] [nat : NatCast E]

theorem Bounds.reindex_point (sign : E → Int) (binding : Ctx)
    {first second : List (Descriptor E Ctx sign binding)} (same : first = second)
    (cut : Fin (first.length+1)) (source : Bounds sign binding first cut) :
    (Bounds.reindex sign binding same cut source).point = source.point := by
  cases same
  rfl

theorem Bounds.changeOps_point (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E)
    (otherMul : Mul E) (otherNat : NatCast E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub)
    (hm : otherMul = mul) (hn : otherNat = nat)
    (sign : E → Int) (binding : Ctx)
    (roots : List (@Descriptor E Ctx _ _ otherOne otherAdd otherSub otherMul otherNat _ sign binding))
    (cut : Fin (roots.length+1))
    (source : @Bounds E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut) :
    @Bounds.point E Ctx _ _ _ one add sub mul nat sign binding _ _
      (@Bounds.changeOps E Ctx _ _ _ one add sub mul nat
        otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn
        sign binding roots cut source) =
    @Bounds.point E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut source := by
  cases ho; cases ha; cases hs; cases hm; cases hn
  dsimp only [Bounds.changeOps]
  exact Bounds.reindex_point sign binding _ cut source

@[expose] def Point.repoint (sign : E → Int) (binding : Ctx) {first second : E}
    (same : first = second) (queries : List (DensePoly E))
    (source : Point sign binding first queries) : Point sign binding second queries :=
  ⟨source.root, by rw [← same]; exact source.bound, source.signs⟩

theorem Point.repoint_values (sign : E → Int) (binding : Ctx) {first second : E}
    (same : first = second) (queries : List (DensePoly E))
    (source : Point sign binding first queries) :
    (Point.repoint sign binding same queries source).signs.values = source.signs.values := rfl

@[expose] def Point.changeQueries (sign : E → Int) (binding : Ctx) (point : E)
    {first second : List (DensePoly E)} (same : first = second)
    (source : Point sign binding point first) : Point sign binding point second :=
  ⟨source.root, source.bound,
    ⟨source.signs.values.cast (congrArg List.length same), source.signs.evidence, by
      cases same
      exact source.signs.accepted⟩⟩

theorem Point.changeQueries_values (sign : E → Int) (binding : Ctx) (point : E)
    {first second : List (DensePoly E)} (same : first = second)
    (source : Point sign binding point first) :
    (Point.changeQueries sign binding point same source).signs.values.toList = source.signs.values.toList := rfl
@[expose] def Sector.changeOps (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E)
    (otherMul : Mul E) (otherNat : NatCast E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub)
    (hm : otherMul = mul) (hn : otherNat = nat)
    (sign : E → Int) (binding : Ctx)
    (roots : List (@Descriptor E Ctx _ _ otherOne otherAdd otherSub otherMul otherNat _ sign binding))
    (cut : Fin (roots.length+1)) (queries : List (DensePoly E))
    (source : @Sector E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut queries) :
    @Sector E Ctx _ _ _ one add sub mul nat sign binding
      (roots.map (@Descriptor.changeOps E Ctx _ _ _ one add sub mul nat
        otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn sign binding))
      (Fin.cast (by simp only [List.length_map]) cut) queries :=
  let bounds := @Sector.sector E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut queries source
  let point := @Bounds.point E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut bounds
  let row := @Sector.row E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut queries source
  let changed := @Bounds.changeOps E Ctx _ _ _ one add sub mul nat
    otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn sign binding roots cut bounds
  let same := @Bounds.changeOps_point E Ctx _ _ _ one add sub mul nat
    otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn sign binding roots cut bounds
  let row := @Point.changeOps E Ctx _ _ _ one add sub mul nat
    otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn sign binding point queries row
  @Sector.mk E Ctx _ _ _ one add sub mul nat sign binding _ _ queries changed
    (@Point.repoint E Ctx _ _ _ one add sub mul nat sign binding point _ same.symm queries row)

@[expose] def Sector.values (sign : E → Int) (binding : Ctx)
    {roots : List (Descriptor E Ctx sign binding)} {cut : Fin (roots.length+1)}
    {queries : List (DensePoly E)} (source : Sector sign binding roots cut queries) : List Int :=
  source.row.signs.values.toList

theorem Sector.changeOps_values (otherOne : One E) (otherAdd : Add E) (otherSub : Sub E)
    (otherMul : Mul E) (otherNat : NatCast E)
    (ho : otherOne = one) (ha : otherAdd = add) (hs : otherSub = sub)
    (hm : otherMul = mul) (hn : otherNat = nat)
    (sign : E → Int) (binding : Ctx)
    (roots : List (@Descriptor E Ctx _ _ otherOne otherAdd otherSub otherMul otherNat _ sign binding))
    (cut : Fin (roots.length+1)) (queries : List (DensePoly E))
    (source : @Sector E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding roots cut queries) :
    @Sector.values E Ctx _ _ _ one add sub mul nat sign binding _ _ _
      (@Sector.changeOps E Ctx _ _ _ one add sub mul nat
        otherOne otherAdd otherSub otherMul otherNat ho ha hs hm hn sign binding roots cut queries source) =
    @Sector.values E Ctx _ _ _ otherOne otherAdd otherSub otherMul otherNat sign binding _ _ _ source := rfl

@[expose] def Sector.changeQueries (sign : E → Int) (binding : Ctx)
    {roots : List (Descriptor E Ctx sign binding)} {cut : Fin (roots.length+1)}
    {first second : List (DensePoly E)} (same : first = second)
    (source : Sector sign binding roots cut first) : Sector sign binding roots cut second :=
  ⟨source.sector, Point.changeQueries sign binding source.sector.point same source.row⟩

theorem Sector.changeQueries_values (sign : E → Int) (binding : Ctx)
    {roots : List (Descriptor E Ctx sign binding)} {cut : Fin (roots.length+1)}
    {first second : List (DensePoly E)} (same : first = second)
    (source : Sector sign binding roots cut first) :
    (Sector.changeQueries sign binding same source).values sign binding = source.values sign binding := rfl

end Hex.RCF.RealCoefficients.CellPackets
