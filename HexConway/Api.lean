/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekamp.RabinSoundness
import HexGFqRing.Basic
import HexConway.Certificates

/-!
Coefficient-list transport of the irreducibility/monic facts, the
aggregate `luebeckConwayPolynomial?_irreducible`/`_monic` dispatch
theorems, and the public `SupportedEntry` / `conwayPoly` API.
-/
namespace Hex

namespace Conway
/-- The coefficient-list constructor for the committed `C(2, 1)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_1
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) =
    some luebeckConwayPolynomial_2_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1] =
      luebeckConwayPolynomial_2_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_1_irreducible

/-- The coefficient-list constructor for the committed `C(2, 2)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_2
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) =
    some luebeckConwayPolynomial_2_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1] =
      luebeckConwayPolynomial_2_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_2_irreducible

/-- The coefficient-list constructor for the committed `C(2, 3)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_3
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) =
    some luebeckConwayPolynomial_2_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1] =
      luebeckConwayPolynomial_2_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_3_irreducible

/-- The coefficient-list constructor for the committed `C(2, 4)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_4
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) =
    some luebeckConwayPolynomial_2_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1] =
      luebeckConwayPolynomial_2_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_4_irreducible

/-- The coefficient-list constructor for the committed `C(2, 5)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_5
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) =
    some luebeckConwayPolynomial_2_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1] =
      luebeckConwayPolynomial_2_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_5_irreducible

/-- The coefficient-list constructor for the committed `C(2, 6)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_6
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) =
    some luebeckConwayPolynomial_2_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1] =
      luebeckConwayPolynomial_2_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_6_irreducible

/-- The coefficient-list constructor for the committed `C(3, 1)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_1
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) =
    some luebeckConwayPolynomial_3_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 1] =
      luebeckConwayPolynomial_3_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_1_irreducible

/-- The coefficient-list constructor for the committed `C(3, 2)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_2
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) =
    some luebeckConwayPolynomial_3_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1] =
      luebeckConwayPolynomial_3_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_2_irreducible

/-- The coefficient-list constructor for the committed `C(3, 3)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_3
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) =
    some luebeckConwayPolynomial_3_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1] =
      luebeckConwayPolynomial_3_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_3_irreducible

/-- The coefficient-list constructor for the committed `C(3, 4)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_4
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) =
    some luebeckConwayPolynomial_3_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1] =
      luebeckConwayPolynomial_3_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_4_irreducible

/-- The coefficient-list constructor for the committed `C(3, 5)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_5
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_3_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1] =
      luebeckConwayPolynomial_3_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_5_irreducible

/-- The coefficient-list constructor for the committed `C(3, 6)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_6
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) =
    some luebeckConwayPolynomial_3_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1] =
      luebeckConwayPolynomial_3_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_6_irreducible

/-- The coefficient-list constructor for the committed `C(5, 1)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_1
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) =
    some luebeckConwayPolynomial_5_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 1] =
      luebeckConwayPolynomial_5_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_1_irreducible

/-- The coefficient-list constructor for the committed `C(5, 2)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_2
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) =
    some luebeckConwayPolynomial_5_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1] =
      luebeckConwayPolynomial_5_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_2_irreducible

/-- The coefficient-list constructor for the committed `C(5, 3)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_3
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) =
    some luebeckConwayPolynomial_5_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1] =
      luebeckConwayPolynomial_5_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_3_irreducible

/-- The coefficient-list constructor for the committed `C(5, 4)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_4
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) =
    some luebeckConwayPolynomial_5_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1] =
      luebeckConwayPolynomial_5_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_4_irreducible

/-- The coefficient-list constructor for the committed `C(5, 5)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_5
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_5_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1] =
      luebeckConwayPolynomial_5_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_5_irreducible

/-- The coefficient-list constructor for the committed `C(5, 6)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_6
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) =
    some luebeckConwayPolynomial_5_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1] =
      luebeckConwayPolynomial_5_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_6_irreducible

/-- The coefficient-list constructor for the committed `C(7, 1)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_1
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) =
    some luebeckConwayPolynomial_7_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 1] =
      luebeckConwayPolynomial_7_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_1_irreducible

/-- The coefficient-list constructor for the committed `C(7, 2)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_2
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) =
    some luebeckConwayPolynomial_7_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1] =
      luebeckConwayPolynomial_7_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_2_irreducible

/-- The coefficient-list constructor for the committed `C(7, 3)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_3
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) =
    some luebeckConwayPolynomial_7_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1] =
      luebeckConwayPolynomial_7_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_3_irreducible

/-- The coefficient-list constructor for the committed `C(7, 4)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_4
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) =
    some luebeckConwayPolynomial_7_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1] =
      luebeckConwayPolynomial_7_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_4_irreducible

/-- The coefficient-list constructor for the committed `C(7, 5)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_5
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_7_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1] =
      luebeckConwayPolynomial_7_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_5_irreducible

/-- The coefficient-list constructor for the committed `C(7, 6)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_6
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) =
    some luebeckConwayPolynomial_7_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1] =
      luebeckConwayPolynomial_7_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_6_irreducible

/-- The coefficient-list constructor for the committed `C(11, 1)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_1
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) =
    some luebeckConwayPolynomial_11_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 1] =
      luebeckConwayPolynomial_11_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_1_irreducible

/-- The coefficient-list constructor for the committed `C(11, 2)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_2
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) =
    some luebeckConwayPolynomial_11_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1] =
      luebeckConwayPolynomial_11_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_2_irreducible

/-- The coefficient-list constructor for the committed `C(11, 3)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_3
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) =
    some luebeckConwayPolynomial_11_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1] =
      luebeckConwayPolynomial_11_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_3_irreducible

/-- The coefficient-list constructor for the committed `C(11, 4)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_4
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) =
    some luebeckConwayPolynomial_11_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1] =
      luebeckConwayPolynomial_11_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_4_irreducible

/-- The coefficient-list constructor for the committed `C(11, 5)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_5
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) =
    some luebeckConwayPolynomial_11_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1] =
      luebeckConwayPolynomial_11_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_5_irreducible

/-- The coefficient-list constructor for the committed `C(11, 6)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_6
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) =
    some luebeckConwayPolynomial_11_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1] =
      luebeckConwayPolynomial_11_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_6_irreducible

/-- The coefficient-list constructor for the committed `C(13, 1)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_1_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_1
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) =
    some luebeckConwayPolynomial_13_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 1] =
      luebeckConwayPolynomial_13_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_1_irreducible

/-- The coefficient-list constructor for the committed `C(13, 2)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_2_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_2
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) =
    some luebeckConwayPolynomial_13_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1] =
      luebeckConwayPolynomial_13_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_2_irreducible

/-- The coefficient-list constructor for the committed `C(13, 3)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_3_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_3
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) =
    some luebeckConwayPolynomial_13_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1] =
      luebeckConwayPolynomial_13_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_3_irreducible

/-- The coefficient-list constructor for the committed `C(13, 4)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_4_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_4
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) =
    some luebeckConwayPolynomial_13_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1] =
      luebeckConwayPolynomial_13_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_4_irreducible

/-- The coefficient-list constructor for the committed `C(13, 5)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_5_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_5
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_13_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1] =
      luebeckConwayPolynomial_13_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_5_irreducible

/-- The coefficient-list constructor for the committed `C(13, 6)` Conway entry
yields an irreducible `FpPoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's irreducibility proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_6_irreducible :
    FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_6
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) =
    some luebeckConwayPolynomial_13_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1] =
      luebeckConwayPolynomial_13_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_6_irreducible

/-- The coefficient-list constructor for the committed `C(2, 1)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_1_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_1
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1]) =
    some luebeckConwayPolynomial_2_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1] =
      luebeckConwayPolynomial_2_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_1_monic

/-- The coefficient-list constructor for the committed `C(2, 2)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_2_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_2
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1]) =
    some luebeckConwayPolynomial_2_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 1] =
      luebeckConwayPolynomial_2_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_2_monic

/-- The coefficient-list constructor for the committed `C(2, 3)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_3_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_3
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1]) =
    some luebeckConwayPolynomial_2_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1] =
      luebeckConwayPolynomial_2_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_3_monic

/-- The coefficient-list constructor for the committed `C(2, 4)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_4_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_4
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1]) =
    some luebeckConwayPolynomial_2_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 0, 1] =
      luebeckConwayPolynomial_2_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_4_monic

/-- The coefficient-list constructor for the committed `C(2, 5)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_5_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_5
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1]) =
    some luebeckConwayPolynomial_2_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 0, 1, 0, 0, 1] =
      luebeckConwayPolynomial_2_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_5_monic

/-- The coefficient-list constructor for the committed `C(2, 6)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_2_6_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_2_6
  change some (luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1]) =
    some luebeckConwayPolynomial_2_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 2 [1, 1, 0, 1, 1, 0, 1] =
      luebeckConwayPolynomial_2_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_2_6_monic

/-- The coefficient-list constructor for the committed `C(3, 1)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_1_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_1
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 1]) =
    some luebeckConwayPolynomial_3_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 1] =
      luebeckConwayPolynomial_3_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_1_monic

/-- The coefficient-list constructor for the committed `C(3, 2)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_2_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_2
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1]) =
    some luebeckConwayPolynomial_3_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1] =
      luebeckConwayPolynomial_3_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_2_monic

/-- The coefficient-list constructor for the committed `C(3, 3)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_3_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_3
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1]) =
    some luebeckConwayPolynomial_3_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 1] =
      luebeckConwayPolynomial_3_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_3_monic

/-- The coefficient-list constructor for the committed `C(3, 4)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_4_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_4
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1]) =
    some luebeckConwayPolynomial_3_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 0, 0, 2, 1] =
      luebeckConwayPolynomial_3_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_4_monic

/-- The coefficient-list constructor for the committed `C(3, 5)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_5_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_5
  change some (luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_3_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [1, 2, 0, 0, 0, 1] =
      luebeckConwayPolynomial_3_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_5_monic

/-- The coefficient-list constructor for the committed `C(3, 6)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and the
literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_3_6_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_3_6
  change some (luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1]) =
    some luebeckConwayPolynomial_3_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 3 [2, 2, 1, 0, 2, 0, 1] =
      luebeckConwayPolynomial_3_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_3_6_monic

/-- The coefficient-list constructor for the committed `C(5, 1)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_1_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_1
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 1]) =
    some luebeckConwayPolynomial_5_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 1] =
      luebeckConwayPolynomial_5_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_1_monic

/-- The coefficient-list constructor for the committed `C(5, 2)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_2_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_2
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1]) =
    some luebeckConwayPolynomial_5_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 4, 1] =
      luebeckConwayPolynomial_5_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_2_monic

/-- The coefficient-list constructor for the committed `C(5, 3)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_3_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_3
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1]) =
    some luebeckConwayPolynomial_5_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 3, 0, 1] =
      luebeckConwayPolynomial_5_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_3_monic

/-- The coefficient-list constructor for the committed `C(5, 4)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_4_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_4
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1]) =
    some luebeckConwayPolynomial_5_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 4, 4, 0, 1] =
      luebeckConwayPolynomial_5_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_4_monic

/-- The coefficient-list constructor for the committed `C(5, 5)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_5_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_5
  change some (luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_5_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [3, 4, 0, 0, 0, 1] =
      luebeckConwayPolynomial_5_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_5_monic

/-- The coefficient-list constructor for the committed `C(5, 6)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_5_6_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_5_6
  change some (luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1]) =
    some luebeckConwayPolynomial_5_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 5 [2, 0, 1, 4, 1, 0, 1] =
      luebeckConwayPolynomial_5_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_5_6_monic

/-- The coefficient-list constructor for the committed `C(7, 1)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_1_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_1
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 1]) =
    some luebeckConwayPolynomial_7_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 1] =
      luebeckConwayPolynomial_7_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_1_monic

/-- The coefficient-list constructor for the committed `C(7, 2)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_2_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_2
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1]) =
    some luebeckConwayPolynomial_7_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 6, 1] =
      luebeckConwayPolynomial_7_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_2_monic

/-- The coefficient-list constructor for the committed `C(7, 3)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_3_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_3
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1]) =
    some luebeckConwayPolynomial_7_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 0, 6, 1] =
      luebeckConwayPolynomial_7_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_3_monic

/-- The coefficient-list constructor for the committed `C(7, 4)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_4_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_4
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1]) =
    some luebeckConwayPolynomial_7_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 4, 5, 0, 1] =
      luebeckConwayPolynomial_7_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_4_monic

/-- The coefficient-list constructor for the committed `C(7, 5)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_5_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_5
  change some (luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_7_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [4, 1, 0, 0, 0, 1] =
      luebeckConwayPolynomial_7_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_5_monic

/-- The coefficient-list constructor for the committed `C(7, 6)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's monicity proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_7_6_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_7_6
  change some (luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1]) =
    some luebeckConwayPolynomial_7_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 7 [3, 6, 4, 5, 1, 0, 1] =
      luebeckConwayPolynomial_7_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_7_6_monic

/-- The coefficient-list constructor for the committed `C(11, 1)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_1_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_1
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 1]) =
    some luebeckConwayPolynomial_11_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 1] =
      luebeckConwayPolynomial_11_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_1_monic

/-- The coefficient-list constructor for the committed `C(11, 2)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_2_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_2
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1]) =
    some luebeckConwayPolynomial_11_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 7, 1] =
      luebeckConwayPolynomial_11_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_2_monic

/-- The coefficient-list constructor for the committed `C(11, 3)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_3_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_3
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1]) =
    some luebeckConwayPolynomial_11_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 2, 0, 1] =
      luebeckConwayPolynomial_11_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_3_monic

/-- The coefficient-list constructor for the committed `C(11, 4)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_4_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_4
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1]) =
    some luebeckConwayPolynomial_11_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 10, 8, 0, 1] =
      luebeckConwayPolynomial_11_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_4_monic

/-- The coefficient-list constructor for the committed `C(11, 5)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_5_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_5
  change some (luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1]) =
    some luebeckConwayPolynomial_11_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [9, 0, 10, 0, 0, 1] =
      luebeckConwayPolynomial_11_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_5_monic

/-- The coefficient-list constructor for the committed `C(11, 6)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_11_6_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_11_6
  change some (luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1]) =
    some luebeckConwayPolynomial_11_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 11 [2, 7, 6, 4, 3, 0, 1] =
      luebeckConwayPolynomial_11_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_11_6_monic

/-- The coefficient-list constructor for the committed `C(13, 1)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_1_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_1
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 1]) =
    some luebeckConwayPolynomial_13_1 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 1] =
      luebeckConwayPolynomial_13_1 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_1_monic

/-- The coefficient-list constructor for the committed `C(13, 2)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_2_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_2
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1]) =
    some luebeckConwayPolynomial_13_2 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 12, 1] =
      luebeckConwayPolynomial_13_2 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_2_monic

/-- The coefficient-list constructor for the committed `C(13, 3)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_3_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_3
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1]) =
    some luebeckConwayPolynomial_13_3 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 2, 0, 1] =
      luebeckConwayPolynomial_13_3 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_3_monic

/-- The coefficient-list constructor for the committed `C(13, 4)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_4_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_4
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1]) =
    some luebeckConwayPolynomial_13_4 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 12, 3, 0, 1] =
      luebeckConwayPolynomial_13_4 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_4_monic

/-- The coefficient-list constructor for the committed `C(13, 5)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_5_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_5
  change some (luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1]) =
    some luebeckConwayPolynomial_13_5 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [11, 4, 0, 0, 0, 1] =
      luebeckConwayPolynomial_13_5 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_5_monic

/-- The coefficient-list constructor for the committed `C(13, 6)` Conway entry
yields a monic `DensePoly`, via the `luebeckConwayPolynomial?` table hit and
the literal's `_monic` proof. -/
private theorem luebeckConwayPolynomialOfCoeffs_13_6_monic :
    DensePoly.Monic (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) := by
  have hhit := luebeckConwayPolynomial?_hit_13_6
  change some (luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1]) =
    some luebeckConwayPolynomial_13_6 at hhit
  have hpoly : luebeckConwayPolynomialOfCoeffs 13 [2, 11, 11, 10, 0, 0, 1] =
      luebeckConwayPolynomial_13_6 :=
    Option.some.inj hhit
  rw [hpoly]
  exact luebeckConwayPolynomial_13_6_monic

/-- Every committed imported entry in the current Tier 1 slice comes with
an irreducibility witness. -/
@[grind →] theorem luebeckConwayPolynomial?_irreducible
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    FpPoly.Irreducible f := by
  unfold luebeckConwayPolynomial? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨coeffs, hcoeffs, hf⟩ := h
  subst hf
  unfold luebeckConwayCoeffs? at hcoeffs
  split at hcoeffs
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_6_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_1_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_2_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_3_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_4_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_5_irreducible
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_6_irreducible
  · cases hcoeffs

/-- Every committed Tier 1 Conway entry in the current table is monic. -/
@[simp, grind →] theorem luebeckConwayPolynomial?_monic
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    DensePoly.Monic f := by
  unfold luebeckConwayPolynomial? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨coeffs, hcoeffs, hf⟩ := h
  subst hf
  unfold luebeckConwayCoeffs? at hcoeffs
  split at hcoeffs
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_1_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_2_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_3_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_4_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_5_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_2_6_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_1_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_2_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_3_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_4_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_5_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_3_6_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_1_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_2_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_3_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_4_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_5_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_5_6_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_1_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_2_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_3_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_4_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_5_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_7_6_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_1_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_2_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_3_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_4_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_5_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_11_6_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_1_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_2_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_3_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_4_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_5_monic
  · cases hcoeffs
    exact luebeckConwayPolynomialOfCoeffs_13_6_monic
  · cases hcoeffs

/-- A committed Conway entry packages the current Tier 1 lookup hit for a
supported `(p, n)` pair. -/
structure SupportedEntry (p n : Nat) [ZMod64.Bounds p] where
  poly : FpPoly p
  prime : Hex.Nat.Prime p
  isSupported : luebeckConwayPolynomial? p n = some poly

/-- The current committed table supports `C(2, 1)`. -/
def supportedEntry_2_1 : SupportedEntry 2 1 :=
  ⟨luebeckConwayPolynomial_2_1, prime_two, luebeckConwayPolynomial?_hit_2_1⟩

/-- The current committed table supports `C(2, 2)`. -/
def supportedEntry_2_2 : SupportedEntry 2 2 :=
  ⟨luebeckConwayPolynomial_2_2,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_2⟩

/-- The current committed table supports `C(2, 3)`. -/
def supportedEntry_2_3 : SupportedEntry 2 3 :=
  ⟨luebeckConwayPolynomial_2_3,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_3⟩

/-- The current committed table supports `C(2, 4)`. -/
def supportedEntry_2_4 : SupportedEntry 2 4 :=
  ⟨luebeckConwayPolynomial_2_4,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_4⟩

/-- The current committed table supports `C(2, 5)`. -/
def supportedEntry_2_5 : SupportedEntry 2 5 :=
  ⟨luebeckConwayPolynomial_2_5,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_5⟩

/-- The current committed table supports `C(2, 6)`. -/
def supportedEntry_2_6 : SupportedEntry 2 6 :=
  ⟨luebeckConwayPolynomial_2_6,
    supportedEntry_2_1.prime,
    luebeckConwayPolynomial?_hit_2_6⟩

/-- The current committed table supports `C(3, 1)`. -/
def supportedEntry_3_1 : SupportedEntry 3 1 :=
  ⟨luebeckConwayPolynomial_3_1, prime_three, luebeckConwayPolynomial?_hit_3_1⟩

/-- The current committed table supports `C(3, 2)`. -/
def supportedEntry_3_2 : SupportedEntry 3 2 :=
  ⟨luebeckConwayPolynomial_3_2,
    supportedEntry_3_1.prime,
    luebeckConwayPolynomial?_hit_3_2⟩

/-- The current committed table supports `C(3, 3)`. -/
def supportedEntry_3_3 : SupportedEntry 3 3 :=
  ⟨luebeckConwayPolynomial_3_3,
    supportedEntry_3_1.prime,
    luebeckConwayPolynomial?_hit_3_3⟩

/-- The current committed table supports `C(3, 4)`. -/
def supportedEntry_3_4 : SupportedEntry 3 4 :=
  ⟨luebeckConwayPolynomial_3_4,
    supportedEntry_3_1.prime,
    luebeckConwayPolynomial?_hit_3_4⟩

/-- The current committed table supports `C(3, 5)`. -/
def supportedEntry_3_5 : SupportedEntry 3 5 :=
  ⟨luebeckConwayPolynomial_3_5,
    supportedEntry_3_1.prime,
    luebeckConwayPolynomial?_hit_3_5⟩

/-- The current committed table supports `C(3, 6)`. -/
def supportedEntry_3_6 : SupportedEntry 3 6 :=
  ⟨luebeckConwayPolynomial_3_6,
    supportedEntry_3_1.prime,
    luebeckConwayPolynomial?_hit_3_6⟩

/-- The current committed table supports `C(5, 1)`. -/
def supportedEntry_5_1 : SupportedEntry 5 1 :=
  ⟨luebeckConwayPolynomial_5_1, prime_five, luebeckConwayPolynomial?_hit_5_1⟩

/-- The current committed table supports `C(5, 2)`. -/
def supportedEntry_5_2 : SupportedEntry 5 2 :=
  ⟨luebeckConwayPolynomial_5_2,
    supportedEntry_5_1.prime,
    luebeckConwayPolynomial?_hit_5_2⟩

/-- The current committed table supports `C(5, 3)`. -/
def supportedEntry_5_3 : SupportedEntry 5 3 :=
  ⟨luebeckConwayPolynomial_5_3,
    supportedEntry_5_1.prime,
    luebeckConwayPolynomial?_hit_5_3⟩

/-- The current committed table supports `C(5, 4)`. -/
def supportedEntry_5_4 : SupportedEntry 5 4 :=
  ⟨luebeckConwayPolynomial_5_4,
    supportedEntry_5_1.prime,
    luebeckConwayPolynomial?_hit_5_4⟩

/-- The current committed table supports `C(5, 5)`. -/
def supportedEntry_5_5 : SupportedEntry 5 5 :=
  ⟨luebeckConwayPolynomial_5_5,
    supportedEntry_5_1.prime,
    luebeckConwayPolynomial?_hit_5_5⟩

/-- The current committed table supports `C(5, 6)`. -/
def supportedEntry_5_6 : SupportedEntry 5 6 :=
  ⟨luebeckConwayPolynomial_5_6,
    supportedEntry_5_1.prime,
    luebeckConwayPolynomial?_hit_5_6⟩

/-- The current committed table supports `C(7, 1)`. -/
def supportedEntry_7_1 : SupportedEntry 7 1 :=
  ⟨luebeckConwayPolynomial_7_1, prime_seven, luebeckConwayPolynomial?_hit_7_1⟩

/-- The current committed table supports `C(7, 2)`. -/
def supportedEntry_7_2 : SupportedEntry 7 2 :=
  ⟨luebeckConwayPolynomial_7_2,
    supportedEntry_7_1.prime,
    luebeckConwayPolynomial?_hit_7_2⟩

/-- The current committed table supports `C(7, 3)`. -/
def supportedEntry_7_3 : SupportedEntry 7 3 :=
  ⟨luebeckConwayPolynomial_7_3,
    supportedEntry_7_1.prime,
    luebeckConwayPolynomial?_hit_7_3⟩

/-- The current committed table supports `C(7, 4)`. -/
def supportedEntry_7_4 : SupportedEntry 7 4 :=
  ⟨luebeckConwayPolynomial_7_4,
    supportedEntry_7_1.prime,
    luebeckConwayPolynomial?_hit_7_4⟩

/-- The current committed table supports `C(7, 5)`. -/
def supportedEntry_7_5 : SupportedEntry 7 5 :=
  ⟨luebeckConwayPolynomial_7_5,
    supportedEntry_7_1.prime,
    luebeckConwayPolynomial?_hit_7_5⟩

/-- The current committed table supports `C(7, 6)`. -/
def supportedEntry_7_6 : SupportedEntry 7 6 :=
  ⟨luebeckConwayPolynomial_7_6,
    supportedEntry_7_1.prime,
    luebeckConwayPolynomial?_hit_7_6⟩

/-- The current committed table supports `C(11, 1)`. -/
def supportedEntry_11_1 : SupportedEntry 11 1 :=
  ⟨luebeckConwayPolynomial_11_1, prime_eleven, luebeckConwayPolynomial?_hit_11_1⟩

/-- The current committed table supports `C(11, 2)`. -/
def supportedEntry_11_2 : SupportedEntry 11 2 :=
  ⟨luebeckConwayPolynomial_11_2,
    supportedEntry_11_1.prime,
    luebeckConwayPolynomial?_hit_11_2⟩

/-- The current committed table supports `C(11, 3)`. -/
def supportedEntry_11_3 : SupportedEntry 11 3 :=
  ⟨luebeckConwayPolynomial_11_3,
    supportedEntry_11_1.prime,
    luebeckConwayPolynomial?_hit_11_3⟩

/-- The current committed table supports `C(11, 4)`. -/
def supportedEntry_11_4 : SupportedEntry 11 4 :=
  ⟨luebeckConwayPolynomial_11_4,
    supportedEntry_11_1.prime,
    luebeckConwayPolynomial?_hit_11_4⟩

/-- The current committed table supports `C(11, 5)`. -/
def supportedEntry_11_5 : SupportedEntry 11 5 :=
  ⟨luebeckConwayPolynomial_11_5,
    supportedEntry_11_1.prime,
    luebeckConwayPolynomial?_hit_11_5⟩

/-- The current committed table supports `C(11, 6)`. -/
def supportedEntry_11_6 : SupportedEntry 11 6 :=
  ⟨luebeckConwayPolynomial_11_6,
    supportedEntry_11_1.prime,
    luebeckConwayPolynomial?_hit_11_6⟩

/-- The current committed table supports `C(13, 1)`. -/
def supportedEntry_13_1 : SupportedEntry 13 1 :=
  ⟨luebeckConwayPolynomial_13_1, prime_thirteen, luebeckConwayPolynomial?_hit_13_1⟩

/-- The current committed table supports `C(13, 2)`. -/
def supportedEntry_13_2 : SupportedEntry 13 2 :=
  ⟨luebeckConwayPolynomial_13_2,
    supportedEntry_13_1.prime,
    luebeckConwayPolynomial?_hit_13_2⟩

/-- The current committed table supports `C(13, 3)`. -/
def supportedEntry_13_3 : SupportedEntry 13 3 :=
  ⟨luebeckConwayPolynomial_13_3,
    supportedEntry_13_1.prime,
    luebeckConwayPolynomial?_hit_13_3⟩

/-- The current committed table supports `C(13, 4)`. -/
def supportedEntry_13_4 : SupportedEntry 13 4 :=
  ⟨luebeckConwayPolynomial_13_4,
    supportedEntry_13_1.prime,
    luebeckConwayPolynomial?_hit_13_4⟩

/-- The current committed table supports `C(13, 5)`. -/
def supportedEntry_13_5 : SupportedEntry 13 5 :=
  ⟨luebeckConwayPolynomial_13_5,
    supportedEntry_13_1.prime,
    luebeckConwayPolynomial?_hit_13_5⟩

/-- The current committed table supports `C(13, 6)`. -/
def supportedEntry_13_6 : SupportedEntry 13 6 :=
  ⟨luebeckConwayPolynomial_13_6,
    supportedEntry_13_1.prime,
    luebeckConwayPolynomial?_hit_13_6⟩

/-- Recover the committed Conway modulus for a supported entry. -/
def conwayPoly (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) : FpPoly p :=
  h.poly

/-- A `SupportedEntry` packages the lookup hit for the committed Tier 1 Conway
table entry selected by `conwayPoly`. -/
@[simp, grind =>] theorem luebeckConwayPolynomial?_conwayPoly
    {p n : Nat} [ZMod64.Bounds p] (h : SupportedEntry p n) :
    luebeckConwayPolynomial? p n = some (conwayPoly p n h) :=
  h.isSupported

grind_pattern luebeckConwayPolynomial?_conwayPoly => conwayPoly p n h

/-- In `ZMod64 p`, `1` is nonzero when the modulus is greater than one; this
feeds the committed Conway-table leading-coefficient checks. -/
private theorem zmod64_one_ne_zero_of_one_lt
    {p : Nat} [ZMod64.Bounds p] (hp : 1 < p) : (1 : ZMod64 p) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := p) 1 0).mp h
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hp] at hm
  exact Nat.one_ne_zero hm

/-- A coefficient array of size at least two with nonzero last entry gives a
positive degree for `DensePoly.ofCoeffs`, as used by
`luebeckConwayPolynomial?_degree_pos`. -/
private theorem ofCoeffs_degree_pos_of_back_ne_zero
    {R : Type u} [Zero R] [DecidableEq R]
    (arr : Array R) (hsize : 2 ≤ arr.size)
    (hback : arr[arr.size - 1]'(by omega) ≠ Zero.zero) :
    0 < (DensePoly.ofCoeffs arr).degree?.getD 0 := by
  have hgetd_eq :
      arr.getD (arr.size - 1) (Zero.zero : R) = arr[arr.size - 1]'(by omega) :=
    (Array.getElem_eq_getD (Zero.zero : R)).symm
  have hcoeff_ne : (DensePoly.ofCoeffs arr).coeff (arr.size - 1) ≠ Zero.zero := by
    rw [DensePoly.coeff_ofCoeffs, hgetd_eq]; exact hback
  have hpoly_size : arr.size - 1 < (DensePoly.ofCoeffs arr).size := by
    rcases Nat.lt_or_ge (arr.size - 1) (DensePoly.ofCoeffs arr).size with hlt | hge
    · exact hlt
    · exact False.elim (hcoeff_ne (DensePoly.coeff_eq_zero_of_size_le _ hge))
  rw [show (DensePoly.ofCoeffs arr).degree? =
        if _h : (DensePoly.ofCoeffs arr).size = 0 then none
        else some ((DensePoly.ofCoeffs arr).size - 1) from rfl]
  rw [dif_neg (by omega : (DensePoly.ofCoeffs arr).size ≠ 0)]
  simp only [Option.getD_some]
  omega

/-- Every committed Tier 1 Conway entry in the current table is nonconstant. -/
@[simp, grind →] theorem luebeckConwayPolynomial?_degree_pos
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    0 < FpPoly.degree f := by
  unfold luebeckConwayPolynomial? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨coeffs, hcoeffs, hf⟩ := h
  subst hf
  unfold luebeckConwayCoeffs? at hcoeffs
  split at hcoeffs
  all_goals
    (cases hcoeffs
     all_goals
       (refine ofCoeffs_degree_pos_of_back_ne_zero _ ?_ ?_
        · simp
        · intro hzero
          simp at hzero
          exact absurd hzero (zmod64_one_ne_zero_of_one_lt (by decide))))

/-- A polynomial with a nonzero coefficient at `n` and no storage beyond `n`
has degree exactly `n`. -/
private theorem degree_eq_of_coeff_ne_zero_of_size_le
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (hcoeff : f.coeff n ≠ 0) (hsize : f.size ≤ n + 1) :
    FpPoly.degree f = n := by
  have hnlt : n < f.size := by
    by_cases hlt : n < f.size
    · exact hlt
    · exact False.elim
        (hcoeff (DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hlt)))
  change f.degree?.getD 0 = n
  rw [DensePoly.degree?_eq_some_of_pos_size f (by omega)]
  simp only [Option.getD_some]
  omega

/-- Every committed Tier 1 Conway entry has the degree requested by its lookup key. -/
@[simp, grind →] theorem luebeckConwayPolynomial?_degree_eq
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    FpPoly.degree f = n := by
  unfold luebeckConwayPolynomial? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨coeffs, hcoeffs, hf⟩ := h
  subst hf
  unfold luebeckConwayCoeffs? at hcoeffs
  split at hcoeffs
  all_goals
    cases hcoeffs <;>
      (apply degree_eq_of_coeff_ne_zero_of_size_le
       · simp [luebeckConwayPolynomialOfCoeffs]
         exact zmod64_one_ne_zero_of_one_lt (by decide)
       · unfold luebeckConwayPolynomialOfCoeffs
         refine Nat.le_trans (DensePoly.size_ofCoeffs_le _) ?_
         simp)

/-- Supported Conway entries produce nonconstant moduli. -/
@[simp, grind =>] theorem conwayPoly_nonconstant
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    0 < FpPoly.degree (conwayPoly p n h) := by
  grind

grind_pattern conwayPoly_nonconstant => conwayPoly p n h

/-- Supported Conway entries carry the imported irreducibility witness. -/
@[grind =>]
theorem conwayPoly_irreducible
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    FpPoly.Irreducible (conwayPoly p n h) := by
  grind

grind_pattern conwayPoly_irreducible => conwayPoly p n h

/-- Supported Conway entries carry the imported monicity witness. -/
@[simp, grind =>] theorem conwayPoly_monic
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    DensePoly.Monic (conwayPoly p n h) := by
  grind

grind_pattern conwayPoly_monic => conwayPoly p n h


end Conway

end Hex
