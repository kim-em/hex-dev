import HexGF2Mathlib.Basic
import HexGFqField
import Mathlib.Data.Fintype.Card

/-!
Identification definitions between the packed `HexGF2` extension-field
wrappers and the generic quotient-ring finite-field construction.

This module reuses the packed-polynomial conversion layer from
`HexGF2Mathlib.Basic` to package both the single-word `GF2n` surface and the
arbitrary-degree `GF2nPoly` surface as project-local ring equivalences with the
generic `Hex.GFqField.FiniteField` model over `Hex.FpPoly 2`.
-/

namespace HexGF2Mathlib

open Hex

namespace TypeEquiv

/-- Convert the project-local equivalence record to Mathlib's `Equiv`. -/
def toEquiv {α : Type u} {β : Type v} (e : TypeEquiv α β) : α ≃ β where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv

end TypeEquiv

namespace GF2n

instance : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem prime_two : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

variable {n : Nat} {irr : UInt64}
variable {hn : 0 < n} {hn64 : n < 64}
variable {hirr : Hex.GF2Poly.Irreducible (Hex.GF2Poly.ofUInt64Monic irr n)}

/-- The packed irreducible modulus viewed inside the generic `FpPoly 2`
representation. -/
def modulusFpPoly : Hex.FpPoly 2 :=
  HexGF2Mathlib.GF2Poly.toFpPoly (Hex.GF2Poly.ofUInt64Monic irr n)

include hn hn64 in
/-- The generic `FpPoly 2` modulus inherits positive degree from the packed
single-word modulus, whose degree is the fixed extension degree `n > 0`. -/
theorem modulusFpPoly_degree_pos : 0 < Hex.FpPoly.degree (modulusFpPoly (n := n) (irr := irr)) := by
  unfold Hex.FpPoly.degree modulusFpPoly
  rw [HexGF2Mathlib.GF2Poly.degree?_toFpPoly,
    Hex.GF2Poly.degree?_ofUInt64Monic_of_lt_64 irr hn64]
  simpa using hn

include hirr in
/-- Packed irreducibility transports across the `GF2Poly ≃+* FpPoly 2`
conversion layer. -/
theorem modulusFpPoly_irreducible :
    Hex.FpPoly.Irreducible (modulusFpPoly (n := n) (irr := irr)) :=
  HexGF2Mathlib.GF2Poly.irreducible_toFpPoly hirr

include hn hn64 hirr in
/-- The generic finite-field model corresponding to the packed single-word
`GF(2^n)` wrapper. -/
abbrev GenericFiniteField :=
  Hex.GFqField.FiniteField
    (modulusFpPoly (n := n) (irr := irr))
    (modulusFpPoly_degree_pos (n := n) (irr := irr) (hn := hn) (hn64 := hn64))
    prime_two
    (modulusFpPoly_irreducible (n := n) (irr := irr) (hirr := hirr))

/-- Interpret a packed single-word field element inside the generic quotient
field model. -/
def toGeneric (x : Hex.GF2n n irr hn hn64 hirr) :
    GenericFiniteField (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) :=
  Hex.GFqField.ofPoly
    (modulusFpPoly (n := n) (irr := irr))
    (modulusFpPoly_degree_pos (n := n) (irr := irr) (hn := hn) (hn64 := hn64))
    prime_two
    (modulusFpPoly_irreducible (n := n) (irr := irr) (hirr := hirr))
    (HexGF2Mathlib.GF2Poly.toFpPoly (Hex.GF2n.toPolyWord x.val))

/-- Repack the canonical representative of a generic quotient-field element as a
single-word `GF(2^n)` element. -/
def ofGeneric
    (x : GenericFiniteField (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)) :
    Hex.GF2n n irr hn hn64 hirr :=
  Hex.GF2n.reduce
    (n := n) (irr := irr)
    ((((HexGF2Mathlib.GF2Poly.ofFpPoly (Hex.GFqField.repr x)).toWords).getD 0 0))

@[simp]
theorem ofGeneric_toGeneric (x : Hex.GF2n n irr hn hn64 hirr) :
    ofGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)
        (toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) x) = x := by
  sorry

@[simp]
theorem toGeneric_ofGeneric
    (x : GenericFiniteField (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)) :
    toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)
        (ofGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) x) = x := by
  sorry

@[simp]
theorem toGeneric_add (x y : Hex.GF2n n irr hn hn64 hirr) :
    toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) (x + y) =
      (toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) x +
        toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) y) := by
  sorry

@[simp]
theorem toGeneric_mul (x y : Hex.GF2n n irr hn hn64 hirr) :
    toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) (x * y) =
      (toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) x *
        toGeneric (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) y) := by
  sorry

/-- The packed single-word field wrapper is ring-equivalent to the generic
finite-field construction over the transported modulus. -/
def equiv : Hex.GF2n n irr hn hn64 hirr ≃+*
    GenericFiniteField (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) where
  toFun := toGeneric
  invFun := ofGeneric
  left_inv := ofGeneric_toGeneric
  right_inv := toGeneric_ofGeneric
  map_mul' := toGeneric_mul
  map_add' := toGeneric_add

/-- Single-word packed field elements are indexed by their bounded canonical
word representatives. -/
def finEquiv : Hex.GF2n n irr hn hn64 hirr ≃ Fin (2 ^ n) where
  toFun x := ⟨x.val.toNat, x.val_lt⟩
  invFun i :=
    ⟨UInt64.ofNatLT i.1
        (Nat.lt_of_lt_of_le i.2
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hn64))),
      by simp⟩
  left_inv := by
    intro x
    cases x
    simp
  right_inv := by
    intro i
    cases i
    simp

noncomputable instance : Fintype (Hex.GF2n n irr hn hn64 hirr) :=
  Fintype.ofEquiv (Fin (2 ^ n)) (finEquiv (n := n) (irr := irr)
    (hn := hn) (hn64 := hn64) (hirr := hirr)).symm

theorem fintype_card :
    Fintype.card (Hex.GF2n n irr hn hn64 hirr) = 2 ^ n := by
  simpa using Fintype.card_congr (finEquiv (n := n) (irr := irr)
    (hn := hn) (hn64 := hn64) (hirr := hirr))

end GF2n

namespace GF2nPoly

instance : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem prime_two : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

variable {f : Hex.GF2Poly} {hirr : Hex.GF2Poly.Irreducible f}
variable {hdeg : 0 < f.degree}

/-- Reduced packed representatives modulo `f`, isolated from the field wrapper
so Mathlib-side finite support can be transported before the final public
`GF2nPoly` cardinality statements are proved. -/
abbrev ReducedPackedRep (f : Hex.GF2Poly) : Type :=
  { p : Hex.GF2Poly // p.IsZero ∨ p.degree < f.degree }

/-- The executable packed quotient wrapper is exactly the reduced-representative
subtype used for finite support. -/
def reducedPackedRepEquiv : TypeEquiv (Hex.GF2nPoly f hirr) (ReducedPackedRep f) where
  toFun x := ⟨x.val, x.val_reduced⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- Encode a reduced packed representative as a bounded binary index. -/
def reducedPackedRepIndex (x : ReducedPackedRep f) : Fin (2 ^ f.degree) :=
  ⟨HexGF2Mathlib.GF2Poly.toNat x.1, HexGF2Mathlib.GF2Poly.toNat_lt_of_degree_lt x.2⟩

/-- Decode a bounded binary index into the corresponding reduced packed
representative. -/
def reducedPackedRepOfIndex (i : Fin (2 ^ f.degree)) : ReducedPackedRep f :=
  ⟨HexGF2Mathlib.GF2Poly.ofNatBelowDegree f.degree i.1,
    HexGF2Mathlib.GF2Poly.ofNatBelowDegree_reduced f.degree i⟩

@[simp]
theorem reducedPackedRepIndex_ofIndex (i : Fin (2 ^ f.degree)) :
    reducedPackedRepIndex (f := f) (reducedPackedRepOfIndex (f := f) i) = i := by
  apply Fin.ext
  exact HexGF2Mathlib.GF2Poly.toNat_ofNatBelowDegree f.degree i

@[simp]
theorem reducedPackedRepOfIndex_index (x : ReducedPackedRep f) :
    reducedPackedRepOfIndex (f := f) (reducedPackedRepIndex (f := f) x) = x := by
  cases x with
  | mk p hp =>
      apply Subtype.ext
      exact HexGF2Mathlib.GF2Poly.ofNatBelowDegree_toNat hp

/-- Reduced packed representatives are equivalent to the finite binary index
space determined by the modulus degree. -/
def reducedPackedRepFinEquiv : TypeEquiv (ReducedPackedRep f) (Fin (2 ^ f.degree)) where
  toFun := reducedPackedRepIndex (f := f)
  invFun := reducedPackedRepOfIndex (f := f)
  left_inv := reducedPackedRepOfIndex_index (f := f)
  right_inv := reducedPackedRepIndex_ofIndex (f := f)

/-- The packed irreducible modulus viewed inside the generic `FpPoly 2`
representation. -/
def modulusFpPoly : Hex.FpPoly 2 :=
  HexGF2Mathlib.GF2Poly.toFpPoly f

include hdeg in
/-- The generic `FpPoly 2` modulus inherits positive degree from the packed
modulus, which carries it as the explicit hypothesis `hdeg : 0 < f.degree`.

This positivity is *not* derivable from `hirr` alone: `Hex.GF2Poly.Irreducible`
(`HexGF2/Euclid.lean:57`) is `f ≠ 0 ∧ ∀ a b, a * b = f → a.degree = 0 ∨
b.degree = 0`, which admits the unit `f = 1` (its only factorisations
`1 = 1 * 1` have both factors of degree 0), and `toFpPoly 1 = 1` has degree `0`.
Throughout `HexGF2`, positive degree is taken from a separate hypothesis, never
from irreducibility. So the arbitrary-degree wrapper requires `0 < f.degree`
exactly as the single-word `GF2n` wrapper requires `hn : 0 < n` above; the
`toFpPoly` transport preserves it via `degree?_toFpPoly`. -/
theorem modulusFpPoly_degree_pos : 0 < Hex.FpPoly.degree (modulusFpPoly (f := f)) := by
  unfold Hex.FpPoly.degree modulusFpPoly
  rw [HexGF2Mathlib.GF2Poly.degree?_toFpPoly]
  exact hdeg

include hirr in
/-- Packed irreducibility transports across the `GF2Poly ≃+* FpPoly 2`
conversion layer. -/
theorem modulusFpPoly_irreducible :
    Hex.FpPoly.Irreducible (modulusFpPoly (f := f)) :=
  HexGF2Mathlib.GF2Poly.irreducible_toFpPoly hirr

include hirr hdeg in
/-- The generic finite-field model corresponding to the packed arbitrary-degree
`GF(2^n)` wrapper. -/
abbrev GenericFiniteField :=
  Hex.GFqField.FiniteField
    (modulusFpPoly (f := f))
    (modulusFpPoly_degree_pos (f := f) (hdeg := hdeg))
    prime_two
    (modulusFpPoly_irreducible (f := f) (hirr := hirr))

/-- Interpret a packed quotient-field element inside the generic quotient field
model. -/
def toGeneric (x : Hex.GF2nPoly f hirr) :
    GenericFiniteField (f := f) (hirr := hirr) (hdeg := hdeg) :=
  Hex.GFqField.ofPoly
    (modulusFpPoly (f := f))
    (modulusFpPoly_degree_pos (f := f) (hdeg := hdeg))
    prime_two
    (modulusFpPoly_irreducible (f := f) (hirr := hirr))
    (HexGF2Mathlib.GF2Poly.toFpPoly x.val)

/-- Repack the canonical representative of a generic quotient-field element as a
packed `GF(2^n)` residue. -/
def ofGeneric (x : GenericFiniteField (f := f) (hirr := hirr) (hdeg := hdeg)) :
    Hex.GF2nPoly f hirr :=
  Hex.GF2nPoly.reducePoly (f := f) (HexGF2Mathlib.GF2Poly.ofFpPoly (Hex.GFqField.repr x))

/-- `FpPoly.degree` of a transported packed polynomial equals its packed degree. -/
theorem degree_toFpPoly (q : Hex.GF2Poly) :
    Hex.FpPoly.degree (HexGF2Mathlib.GF2Poly.toFpPoly q) = q.degree := by
  unfold Hex.FpPoly.degree Hex.GF2Poly.degree
  rw [HexGF2Mathlib.GF2Poly.degree?_toFpPoly]

/-- **Reduction-compatibility bridge.** Packed remainder reduction modulo `f`
transports across the `GF2Poly ≃+* FpPoly 2` conversion layer to the generic
quotient-ring reduction `GFqRing.reduceMod`. This is the missing transport that
lets the `GF2nPoly` quotient round-trip / add / mul obligations follow from the
already-proved packed-level ring equivalence. -/
theorem toFpPoly_reduceMod (p g : Hex.GF2Poly) (hgdeg : 0 < g.degree) :
    HexGF2Mathlib.GF2Poly.toFpPoly (p % g) =
      Hex.GFqRing.reduceMod (HexGF2Mathlib.GF2Poly.toFpPoly g)
        (HexGF2Mathlib.GF2Poly.toFpPoly p) := by
  letI : Hex.ZMod64.PrimeModulus 2 := Hex.ZMod64.primeModulusOfPrime GF2n.prime_two
  have hgne : g ≠ 0 := by
    intro h; rw [h] at hgdeg; simp [Hex.GF2Poly.degree, Hex.GF2Poly.degree?] at hgdeg
  have hgdeg' : 0 < Hex.FpPoly.degree (HexGF2Mathlib.GF2Poly.toFpPoly g) := by
    rw [degree_toFpPoly]; exact hgdeg
  have hdeglt :
      Hex.FpPoly.degree (HexGF2Mathlib.GF2Poly.toFpPoly (p % g)) <
        Hex.FpPoly.degree (HexGF2Mathlib.GF2Poly.toFpPoly g) := by
    rw [degree_toFpPoly, degree_toFpPoly]
    rcases Hex.GF2Poly.mod_degree_lt p g hgne with hz | hlt
    · rw [Hex.GF2Poly.eq_zero_of_isZero hz]
      simpa [Hex.GF2Poly.degree, Hex.GF2Poly.degree?] using hgdeg
    · exact hlt
  have heucl :
      HexGF2Mathlib.GF2Poly.toFpPoly p =
        HexGF2Mathlib.GF2Poly.toFpPoly (p % g) +
          HexGF2Mathlib.GF2Poly.toFpPoly (p / g) * HexGF2Mathlib.GF2Poly.toFpPoly g := by
    conv_lhs => rw [← Hex.GF2Poly.div_mul_add_mod p g]
    rw [HexGF2Mathlib.GF2Poly.toFpPoly_add, HexGF2Mathlib.GF2Poly.toFpPoly_mul,
      Hex.FpPoly.add_comm]
  rw [heucl, Hex.GFqRing.reduceMod_add_mul_self_right _ hgdeg']
  exact (Hex.GFqRing.reduceMod_eq_self_of_degree_lt _ _ hdeglt).symm

/-- Equality of generic finite-field elements from equality of canonical
representatives. -/
theorem eq_of_repr_eq
    {x y : GenericFiniteField (f := f) (hirr := hirr) (hdeg := hdeg)}
    (h : Hex.GFqField.repr x = Hex.GFqField.repr y) : x = y := by
  apply Hex.GFqField.ext
  exact Subtype.ext h

/-- The canonical representative of a packed element embedded into the generic
model is simply its packed value, transported to `FpPoly 2`. -/
theorem repr_toGeneric (x : Hex.GF2nPoly f hirr) :
    Hex.GFqField.repr (toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) x) =
      HexGF2Mathlib.GF2Poly.toFpPoly x.val := by
  letI : Hex.ZMod64.PrimeModulus 2 := Hex.ZMod64.primeModulusOfPrime GF2n.prime_two
  unfold toGeneric
  rw [Hex.GFqField.repr_ofPoly]
  apply Hex.GFqRing.reduceMod_eq_self_of_degree_lt
  rw [degree_toFpPoly]
  show Hex.FpPoly.degree (modulusFpPoly (f := f)) > x.val.degree
  rw [show modulusFpPoly (f := f) = HexGF2Mathlib.GF2Poly.toFpPoly f from rfl, degree_toFpPoly]
  rcases x.val_reduced with hz | hlt
  · rw [Hex.GF2Poly.eq_zero_of_isZero hz]
    simpa [Hex.GF2Poly.degree, Hex.GF2Poly.degree?] using hdeg
  · exact hlt

@[simp]
theorem ofGeneric_toGeneric (x : Hex.GF2nPoly f hirr) :
    ofGeneric (f := f) (hirr := hirr) (hdeg := hdeg)
      (toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) x) = x := by
  unfold ofGeneric
  rw [repr_toGeneric, HexGF2Mathlib.GF2Poly.ofFpPoly_toFpPoly]
  apply Hex.GF2nPoly.eq_of_val_eq
  rw [Hex.GF2nPoly.reducePoly_val_eq_mod]
  exact Hex.GF2Poly.mod_eq_self_of_reduced x.val f x.val_reduced

@[simp]
theorem toGeneric_ofGeneric (x : GenericFiniteField (f := f) (hirr := hirr) (hdeg := hdeg)) :
    toGeneric (f := f) (hirr := hirr) (hdeg := hdeg)
      (ofGeneric (f := f) (hirr := hirr) (hdeg := hdeg) x) = x := by
  letI : Hex.ZMod64.PrimeModulus 2 := Hex.ZMod64.primeModulusOfPrime GF2n.prime_two
  apply eq_of_repr_eq
  rw [repr_toGeneric]
  unfold ofGeneric
  rw [Hex.GF2nPoly.reducePoly_val_eq_mod,
    toFpPoly_reduceMod _ _ hdeg, HexGF2Mathlib.GF2Poly.toFpPoly_ofFpPoly]
  exact Hex.GFqRing.reduceMod_eq_self_of_degree_lt _ _
    (Hex.GFqField.degree_repr_lt_degree x)

@[simp]
theorem toGeneric_add (x y : Hex.GF2nPoly f hirr) :
    toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) (x + y) =
      (toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) x +
        toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) y) := by
  apply eq_of_repr_eq
  rw [Hex.GFqField.repr_add, repr_toGeneric, repr_toGeneric, repr_toGeneric,
    Hex.GF2nPoly.add_val, toFpPoly_reduceMod _ _ hdeg, HexGF2Mathlib.GF2Poly.toFpPoly_add,
    show modulusFpPoly (f := f) = HexGF2Mathlib.GF2Poly.toFpPoly f from rfl]

@[simp]
theorem toGeneric_mul (x y : Hex.GF2nPoly f hirr) :
    toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) (x * y) =
      (toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) x *
        toGeneric (f := f) (hirr := hirr) (hdeg := hdeg) y) := by
  apply eq_of_repr_eq
  rw [Hex.GFqField.repr_mul, repr_toGeneric, repr_toGeneric, repr_toGeneric,
    Hex.GF2nPoly.mul_val, toFpPoly_reduceMod _ _ hdeg, HexGF2Mathlib.GF2Poly.toFpPoly_mul,
    show modulusFpPoly (f := f) = HexGF2Mathlib.GF2Poly.toFpPoly f from rfl]

include hdeg in
/-- The packed arbitrary-degree field wrapper is ring-equivalent to the generic
finite-field construction over the transported modulus. -/
def equiv : Hex.GF2nPoly f hirr ≃+* GenericFiniteField (f := f) (hirr := hirr) (hdeg := hdeg) where
  toFun := toGeneric
  invFun := ofGeneric
  left_inv := ofGeneric_toGeneric
  right_inv := toGeneric_ofGeneric
  map_mul' := toGeneric_mul
  map_add' := toGeneric_add

/-- Packed arbitrary-degree field elements are indexed by reduced packed
representatives below the modulus degree. -/
def finEquiv : Hex.GF2nPoly f hirr ≃ Fin (2 ^ f.degree) :=
  TypeEquiv.toEquiv <|
    TypeEquiv.trans
      (reducedPackedRepEquiv (f := f) (hirr := hirr))
      (reducedPackedRepFinEquiv (f := f))

noncomputable instance : Fintype (Hex.GF2nPoly f hirr) :=
  Fintype.ofEquiv (Fin (2 ^ f.degree)) (finEquiv (f := f) (hirr := hirr)).symm

theorem fintype_card :
    Fintype.card (Hex.GF2nPoly f hirr) = 2 ^ f.degree := by
  simpa using Fintype.card_congr (finEquiv (f := f) (hirr := hirr))

end GF2nPoly

end HexGF2Mathlib
