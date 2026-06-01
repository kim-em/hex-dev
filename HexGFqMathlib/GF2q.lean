import HexGFqMathlib.Basic
import HexGF2Mathlib.Field
import Mathlib.Algebra.Ring.Equiv

/-!
Mathlib-side correspondence between the optimized binary Conway field and the
generic canonical Conway field.
-/

namespace Hex

namespace GF2q

variable {n : Nat} [h : Conway.PackedGF2Entry n]

instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem cast_symm_cast {α β : Type u} (h : α = β) (x : α) :
    cast h.symm (cast h x) = x := by
  cases h
  rfl

private theorem cast_cast_symm {α β : Type u} (h : α = β) (x : β) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

private theorem cast_mul {α β : Type u} [Mul α] [Mul β] (h : α = β) (x y : α) :
    cast h (x * y) = cast h x * cast h y := by
  sorry

private theorem cast_add {α β : Type u} [Add α] [Add β] (h : α = β) (x y : α) :
    cast h (x + y) = cast h x + cast h y := by
  sorry

/-- The packed `GF2n` modulus, transported to `FpPoly 2`, is the Conway
polynomial selected for the same committed packed entry. -/
theorem modulusFpPoly_eq_conway :
    HexGF2Mathlib.GF2n.modulusFpPoly (n := n) (irr := h.lower) =
      GFq.modulus h.entry := by
  sorry

/-- The generic finite-field target of the packed correspondence is
definitionally the same field type as `GFq 2 n` after identifying the
transported packed modulus with the Conway modulus. -/
private theorem genericField_eq_conway :
    HexGF2Mathlib.GF2n.GenericFiniteField
      (n := n) (irr := h.lower) =
      GFq 2 n h.entry := by
  sorry

/-- Reindex the generic finite-field target of the packed `GF2n` correspondence
to the canonical Conway-field target used by `GFq 2 n`. -/
private def genericEquivGFq :
    RingEquiv
      (HexGF2Mathlib.GF2n.GenericFiniteField
        (n := n) (irr := h.lower))
      (GFq 2 n h.entry) where
  toFun x := cast (genericField_eq_conway (n := n)) x
  invFun x := cast (genericField_eq_conway (n := n)).symm x
  left_inv := by
    intro x
    exact cast_symm_cast (genericField_eq_conway (n := n)) x
  right_inv := by
    intro x
    exact cast_cast_symm (genericField_eq_conway (n := n)) x
  map_mul' := by
    intro x y
    exact cast_mul (genericField_eq_conway (n := n)) x y
  map_add' := by
    intro x y
    exact cast_add (genericField_eq_conway (n := n)) x y

set_option maxHeartbeats 800000

/-- The optimized packed binary Conway field is ring-equivalent to the generic
canonical Conway field over `p = 2`. -/
def equivGFq : RingEquiv (GF2q n) (GFq 2 n h.entry) := by
  let lower := h.lower
  let hn := h.degree_pos
  let hn64 := h.degree_lt_word
  let hirr := h.packed_irreducible
  change RingEquiv
    (GF2n n lower hn hn64 hirr)
    (GFq 2 n h.entry)
  let e :=
    HexGF2Mathlib.GF2n.equiv
      (n := n) (irr := lower)
      (hn := hn) (hn64 := hn64)
      (hirr := hirr)
  let g := genericEquivGFq (n := n)
  exact
    { toFun := fun x => g (e x)
      invFun := fun x => e.symm (g.symm x)
      left_inv := by
        intro x
        sorry
      right_inv := by
        intro x
        sorry
      map_mul' := by
        intro x y
        sorry
      map_add' := by
        intro x y
        sorry }

end GF2q

end Hex
