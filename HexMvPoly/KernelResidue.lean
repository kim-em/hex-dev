/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.KernelMap
public import HexModArith.Ring

@[expose] public section

/-! Positive-characteristic certificate arithmetic on ordinary natural-number
residues. The local operation dictionaries below carry no ring-law instances.
The producer and denotation conversions are separate from certificate replay. -/

namespace Hex.MvPoly.Kernel

open CoeffMap

/-- Modular addition of coefficients. -/
def residueAdd (p a b : Nat) : Nat := Nat.mod (Nat.add a b) p

/-- Modular multiplication of coefficients. -/
def residueMul (p a b : Nat) : Nat := Nat.mod (Nat.mul a b) p

/-- Negation by multiplication by the residue of `-1`. Pattern matching on the
modulus keeps the coefficient path within natural addition, multiplication,
modulus, and structural recursion. -/
def residueNeg (p a : Nat) : Nat :=
  match p with
  | 0 => 0
  | k + 1 => residueMul p k a

/-- Merge canonical residue lists, reducing every coefficient collision. -/
def addMod (p : Nat) (a b : PolyList Nat) : PolyList Nat :=
  letI : Add Nat := ⟨residueAdd p⟩
  add a b

/-- Multiply translated rows with modular products and balanced modular merges. -/
def mulMod (p : Nat) (a b : PolyList Nat) : PolyList Nat :=
  letI : Add Nat := ⟨residueAdd p⟩
  letI : Mul Nat := ⟨residueMul p⟩
  mul a b

/-- Negate residue coefficients and remove zero results. -/
def negMod (p : Nat) (a : PolyList Nat) : PolyList Nat :=
  mapCoeffs (residueNeg p) a

/-- Multiply by an arbitrary natural-number scalar modulo the modulus. -/
def smulMod (p c : Nat) (a : PolyList Nat) : PolyList Nat :=
  mapCoeffs (residueMul p c) a

/-- Subtraction of canonical residue lists. -/
def subMod (p : Nat) (a b : PolyList Nat) : PolyList Nat :=
  addMod p a (negMod p b)

/-- Canonical exponents and nonzero coefficients strictly below the modulus. -/
def CanonicalMod (p n : Nat) (a : PolyList Nat) : Prop :=
  Canonical n a ∧ ∀ t ∈ a, t.2 < p

/-- Check canonical form and the residue bound on untrusted certificate data. -/
def isCanonicalMod (p n : Nat) (a : PolyList Nat) : Bool :=
  isCanonical n a && a.all (fun t => Nat.blt t.2 p)

/-- The Boolean check is equivalent to canonical residue form. -/
theorem isCanonicalMod_iff {p n : Nat} {a : PolyList Nat} :
    isCanonicalMod p n a = true ↔ CanonicalMod p n a := by
  simp [isCanonicalMod, CanonicalMod, isCanonical_iff, List.all_eq_true, Nat.blt_eq]

section Conversion
variable (p : Nat) [Hex.ZMod64.Bounds p]

/-- Producer-side conversion from machine-word residues to quoted naturals. -/
def ofResidues (a : PolyList (Hex.ZMod64 p)) : PolyList Nat :=
  map Hex.ZMod64.toNat a

/-- Interpret natural coefficients as residues. This is a semantic conversion,
never part of the closed Boolean certificate computation. -/
def toResidues (a : PolyList Nat) : PolyList (Hex.ZMod64 p) :=
  map (fun c => Hex.ZMod64.ofNat p c) a

private theorem residue_zero (a : Hex.ZMod64 p) : a.toNat = 0 ↔ a = 0 := by
  rw [Hex.ZMod64.eq_iff_toNat_eq]
  rfl

/-- Reading back producer residues is exact, with no support assumptions. -/
@[simp] theorem toResidues_ofResidues (a : PolyList (Hex.ZMod64 p)) :
    toResidues p (ofResidues p a) = a := by
  unfold toResidues ofResidues
  rw [map_map]
  unfold map
  apply List.map_id''
  intro t
  simp only [Hex.ZMod64.ofNat_toNat]

/-- Reading and quoting a bounded natural coefficient leaves it unchanged. -/
theorem ofResidues_toResidues {a : PolyList Nat} (ha : ∀ t ∈ a, t.2 < p) :
    ofResidues p (toResidues p a) = a := by
  unfold toResidues ofResidues
  rw [map_map]
  unfold map
  refine (List.map_congr_left (g := id) ?_).trans (List.map_id _)
  intro t ht
  apply Prod.ext
  · rfl
  · change (Hex.ZMod64.ofNat p t.2).toNat = t.2
    rw [Hex.ZMod64.toNat_ofNat]
    exact Nat.mod_eq_of_lt (ha t ht)

/-- The encoding is injective on the executable coefficient carrier. -/
theorem ofResidues_injective : Function.Injective (ofResidues p) :=
  map_injective _ (fun _ _ h => Hex.ZMod64.ext_toNat h)

/-- Executable canonical lists quote to canonical residue lists. -/
theorem ofResidues_canonical {n : Nat} {a : PolyList (Hex.ZMod64 p)} :
    CanonicalMod p n (ofResidues p a) ↔ Canonical n a := by
  simp only [CanonicalMod, ofResidues, canonical_map _ (residue_zero p)]
  have h : ∀ t ∈ map Hex.ZMod64.toNat a, t.2 < p := by
    simpa only [map, List.forall_mem_map] using
      (fun (t : Term (Hex.ZMod64 p)) (_ : t ∈ a) => t.2.toNat_lt)
  exact and_iff_left h

/-- Canonical natural residues have canonical executable denotation lists. -/
theorem toResidues_canonical {n : Nat} {a : PolyList Nat}
    (ha : CanonicalMod p n a) : Canonical n (toResidues p a) := by
  apply (ofResidues_canonical p).mp
  rwa [ofResidues_toResidues p ha.2]

/-- Quoting commutes with modular addition. -/
theorem ofResidues_add (a b : PolyList (Hex.ZMod64 p)) :
    ofResidues p (add a b) = addMod p (ofResidues p a) (ofResidues p b) := by
  letI : Add Nat := ⟨residueAdd p⟩
  exact map_add _ (residue_zero p) Hex.ZMod64.toNat_add a b

/-- Quoting commutes with modular multiplication. -/
theorem ofResidues_mul (a b : PolyList (Hex.ZMod64 p)) :
    ofResidues p (mul a b) = mulMod p (ofResidues p a) (ofResidues p b) := by
  letI : Add Nat := ⟨residueAdd p⟩
  letI : Mul Nat := ⟨residueMul p⟩
  exact map_mul _ (residue_zero p) Hex.ZMod64.toNat_add Hex.ZMod64.toNat_mul a b

/-- Quoting commutes with scalar multiplication. -/
theorem ofResidues_smul (c : Hex.ZMod64 p) (a : PolyList (Hex.ZMod64 p)) :
    ofResidues p (smul c a) = smulMod p c.toNat (ofResidues p a) := by
  exact map_mapCoeffs _ (residue_zero p) _ _ (Hex.ZMod64.toNat_mul c) a

private theorem residue_neg (a : Hex.ZMod64 p) :
    (-a).toNat = residueNeg p a.toNat := by
  have hp := Hex.ZMod64.Bounds.pPos (p := p)
  cases p with
  | zero => omega
  | succ k =>
    have hk : (k : Hex.ZMod64 (k + 1)) = -1 := by
      have h := Hex.ZMod64.natCast_self (p := k + 1)
      rw [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_one] at h
      grind
    have hmul : -a = (k : Hex.ZMod64 (k + 1)) * a := by rw [hk]; grind
    rw [hmul]
    change (Hex.ZMod64.mul _ _).toNat = _
    rw [Hex.ZMod64.toNat_mul]
    change (k % (k + 1) * a.toNat) % (k + 1) = _
    simp only [residueNeg, residueMul, Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
    rfl

/-- Quoting commutes with negation. -/
theorem ofResidues_neg (a : PolyList (Hex.ZMod64 p)) :
    ofResidues p (neg a) = negMod p (ofResidues p a) := by
  exact map_mapCoeffs _ (residue_zero p) _ _ (residue_neg p) a

/-- Natural scalars may be unreduced; multiplication reduces them modulo `p`. -/
theorem ofResidues_smul_nat (c : Nat) (a : PolyList (Hex.ZMod64 p)) :
    ofResidues p (smul (Hex.ZMod64.ofNat p c) a) =
      smulMod p c (ofResidues p a) := by
  apply map_mapCoeffs _ (residue_zero p)
  intro x
  change (Hex.ZMod64.mul _ x).toNat = _
  rw [Hex.ZMod64.toNat_mul, Hex.ZMod64.toNat_ofNat]
  change (c % p * x.toNat) % p = (c * x.toNat) % p
  simp [Nat.mul_mod]

/-- Reading modular addition agrees with executable addition on bounded inputs. -/
theorem toResidues_addMod {a b : PolyList Nat}
    (ha : ∀ t ∈ a, t.2 < p) (hb : ∀ t ∈ b, t.2 < p) :
    toResidues p (addMod p a b) = add (toResidues p a) (toResidues p b) := by
  have h := ofResidues_add p (toResidues p a) (toResidues p b)
  rw [ofResidues_toResidues p ha, ofResidues_toResidues p hb] at h
  rw [← h, toResidues_ofResidues]

/-- Reading modular multiplication agrees with executable multiplication. -/
theorem toResidues_mulMod {a b : PolyList Nat}
    (ha : ∀ t ∈ a, t.2 < p) (hb : ∀ t ∈ b, t.2 < p) :
    toResidues p (mulMod p a b) = mul (toResidues p a) (toResidues p b) := by
  have h := ofResidues_mul p (toResidues p a) (toResidues p b)
  rw [ofResidues_toResidues p ha, ofResidues_toResidues p hb] at h
  rw [← h, toResidues_ofResidues]

/-- Reading modular negation agrees with executable negation. -/
theorem toResidues_negMod {a : PolyList Nat} (ha : ∀ t ∈ a, t.2 < p) :
    toResidues p (negMod p a) = neg (toResidues p a) := by
  have h := ofResidues_neg p (toResidues p a)
  rw [ofResidues_toResidues p ha] at h
  rw [← h, toResidues_ofResidues]

/-- Reading modular scalar multiplication agrees with executable scaling. -/
theorem toResidues_smulMod (c : Nat) {a : PolyList Nat}
    (ha : ∀ t ∈ a, t.2 < p) :
    toResidues p (smulMod p c a) = smul (Hex.ZMod64.ofNat p c) (toResidues p a) := by
  have h := ofResidues_smul_nat p c (toResidues p a)
  rw [ofResidues_toResidues p ha] at h
  rw [← h, toResidues_ofResidues]

/-- Modular addition preserves canonical residue form. -/
theorem addMod_canonical {n : Nat} {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    CanonicalMod p n (addMod p a b) := by
  have h := ofResidues_add p (toResidues p a) (toResidues p b)
  rw [ofResidues_toResidues p ha.2, ofResidues_toResidues p hb.2] at h
  rw [← h, ofResidues_canonical]
  exact add_canonical (toResidues_canonical p ha) (toResidues_canonical p hb)

/-- Modular multiplication preserves canonical residue form. -/
theorem mulMod_canonical {n : Nat} {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    CanonicalMod p n (mulMod p a b) := by
  have h := ofResidues_mul p (toResidues p a) (toResidues p b)
  rw [ofResidues_toResidues p ha.2, ofResidues_toResidues p hb.2] at h
  rw [← h, ofResidues_canonical]
  exact mul_canonical (toResidues_canonical p ha) (toResidues_canonical p hb)

/-- Modular negation preserves canonical residue form. -/
theorem negMod_canonical {n : Nat} {a : PolyList Nat} (ha : CanonicalMod p n a) :
    CanonicalMod p n (negMod p a) := by
  have h := ofResidues_neg p (toResidues p a)
  rw [ofResidues_toResidues p ha.2] at h
  rw [← h, ofResidues_canonical]
  exact neg_canonical (toResidues_canonical p ha)

/-- Modular scalar multiplication preserves canonical residue form, including
when the scalar itself is unreduced. -/
theorem smulMod_canonical (c : Nat) {n : Nat} {a : PolyList Nat}
    (ha : CanonicalMod p n a) : CanonicalMod p n (smulMod p c a) := by
  have h := ofResidues_smul_nat p c (toResidues p a)
  rw [ofResidues_toResidues p ha.2] at h
  rw [← h, ofResidues_canonical]
  exact smul_canonical (Hex.ZMod64.ofNat p c) (toResidues_canonical p ha)

/-- Modular subtraction preserves canonical residue form. -/
theorem subMod_canonical {n : Nat} {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    CanonicalMod p n (subMod p a b) :=
  addMod_canonical p ha (negMod_canonical p hb)

variable {n : Nat} {cmp : Hex.Mono n → Hex.Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Semantic denotation in the executable residue polynomial ring. -/
def denoteMod (a : PolyList Nat) : Hex.MvPoly n (Hex.ZMod64 p) cmp :=
  denote (toResidues p a)

/-- The empty residue list denotes zero. -/
@[simp] theorem denoteMod_nil : denoteMod p (cmp := cmp) [] = 0 := rfl

/-- Modular addition denotes polynomial addition on canonical inputs. -/
theorem denoteMod_addMod {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    denoteMod p (cmp := cmp) (addMod p a b) = denoteMod p a + denoteMod p b := by
  unfold denoteMod
  rw [toResidues_addMod p ha.2 hb.2]
  exact denote_add _ _

/-- Modular multiplication denotes polynomial multiplication on canonical inputs. -/
theorem denoteMod_mulMod {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    denoteMod p (cmp := cmp) (mulMod p a b) = denoteMod p a * denoteMod p b := by
  unfold denoteMod
  rw [toResidues_mulMod p ha.2 hb.2]
  exact denote_mul _ _ (toResidues_canonical p ha).1 (toResidues_canonical p hb).1

/-- Modular negation denotes polynomial negation on canonical inputs. -/
theorem denoteMod_negMod {a : PolyList Nat} (ha : CanonicalMod p n a) :
    denoteMod p (cmp := cmp) (negMod p a) = -denoteMod p a := by
  unfold denoteMod
  rw [toResidues_negMod p ha.2]
  exact denote_neg _

/-- Modular scalar multiplication denotes multiplication by a residue constant. -/
theorem denoteMod_smulMod (c : Nat) {a : PolyList Nat} (ha : CanonicalMod p n a) :
    denoteMod p (cmp := cmp) (smulMod p c a) =
      Hex.MvPoly.C (Hex.ZMod64.ofNat p c) * denoteMod p a := by
  unfold denoteMod
  rw [toResidues_smulMod p c ha.2]
  exact denote_smul _ _

/-- Modular subtraction denotes polynomial subtraction on canonical inputs. -/
theorem denoteMod_subMod {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    denoteMod p (cmp := cmp) (subMod p a b) = denoteMod p a - denoteMod p b := by
  rw [subMod, denoteMod_addMod p ha (negMod_canonical p hb), denoteMod_negMod p hb]
  rfl

/-- Canonical residue lists are uniquely determined by their denotation. -/
theorem denoteMod_injective {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b)
    (h : denoteMod p (cmp := cmp) a = denoteMod p b) : a = b := by
  have he := denote_injective (toResidues_canonical p ha) (toResidues_canonical p hb) h
  have := congrArg (ofResidues p) he
  simpa only [ofResidues_toResidues p ha.2, ofResidues_toResidues p hb.2] using this

/-- The existing structural zero test is exact for canonical residue lists. -/
theorem isZero_mod_iff {a : PolyList Nat} (ha : CanonicalMod p n a) :
    isZero a = true ↔ denoteMod p (cmp := cmp) a = 0 := by
  constructor
  · cases a <;> simp [isZero, denoteMod_nil]
  · intro h
    have hz : CanonicalMod p n [] := by simp [CanonicalMod, Canonical]
    have he := denoteMod_injective p ha hz h
    rw [he]; rfl

/-- The existing structural equality test is exact for canonical residue lists. -/
theorem beq_mod_iff {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    beq a b = true ↔ denoteMod p (cmp := cmp) a = denoteMod p b := by
  rw [beq_eq_true_iff]
  exact ⟨fun h => congrArg (denoteMod p) h, denoteMod_injective p ha hb⟩

/-- A producer polynomial quotes to a canonical residue list. -/
theorem residues_toList_canonical (a : Hex.MvPoly n (Hex.ZMod64 p) cmp) :
    CanonicalMod p n (ofResidues p (toList a)) :=
  (ofResidues_canonical p).mpr (toList_canonical a)

/-- The complete producer-to-kernel encoding round trip. -/
@[simp] theorem denoteMod_ofResidues (a : Hex.MvPoly n (Hex.ZMod64 p) cmp) :
    denoteMod p (ofResidues p (toList a)) = a := by
  unfold denoteMod
  rw [toResidues_ofResidues]
  exact denote_toList a

end Conversion
end Hex.MvPoly.Kernel
