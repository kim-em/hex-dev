/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Irreducibility

public section

/-!
The single-word `GF(2^n)` wrapper, for `n < 64`.

An element is one `UInt64` whose bits are the coefficients of a residue modulo
a monic degree-`n` irreducible, with the leading term implicit. Addition is
XOR; multiplication is a carry-less product followed by reduction against
precomputed masks.

This module also carries the packed-polynomial helpers both wrappers share, and
the two structure declarations, so that `HexGF2.Field.Poly` can build the
arbitrary-degree case on top of it.
-/

namespace Hex
namespace GF2Poly

/-- Coefficients above a reduced degree bound are zero. -/
theorem coeff_eq_false_of_reduced_bound_le {p : GF2Poly} {bound n : Nat}
    (hred : p.IsZero ∨ p.degree < bound) (hbound : bound ≤ n) :
    p.coeff n = false := by
  cases hred with
  | inl hzero =>
      rw [eq_zero_of_isZero hzero, coeff_zero]
  | inr hdegree =>
      by_cases hpzero : p.isZero = true
      · rw [eq_zero_of_isZero hpzero, coeff_zero]
      · have hpzeroFalse : p.isZero = false := by
          cases h : p.isZero <;> simp [h] at hpzero ⊢
        obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hpzeroFalse
        have hdn : d < n := by
          have hdegree' : d < bound := by
            simpa [degree, hd] using hdegree
          omega
        exact coeff_eq_false_of_degree?_lt hd hdn

/-- Bounded coefficient vector used as a finite-index code for reduced packed
polynomials. -/
@[expose]
def reducedCoeffVector (bound : Nat) (p : GF2Poly) : Fin bound → Bool :=
  fun i => p.coeff i

/-- Two reduced packed polynomials below the same bound are equal when their
bounded coefficient vectors agree. -/
theorem eq_of_reducedCoeffVector_eq {bound : Nat} {p q : GF2Poly}
    (hp : p.IsZero ∨ p.degree < bound)
    (hq : q.IsZero ∨ q.degree < bound)
    (hcoeff : reducedCoeffVector bound p = reducedCoeffVector bound q) :
    p = q := by
  apply ext_coeff
  intro n
  by_cases hn : n < bound
  · exact congrFun hcoeff ⟨n, hn⟩
  · have hbound : bound ≤ n := Nat.le_of_not_gt hn
    rw [coeff_eq_false_of_reduced_bound_le hp hbound,
      coeff_eq_false_of_reduced_bound_le hq hbound]

namespace Internal

/-- Internal Boolean coefficient values used to build finite coefficient-list
enumerations for packed quotient proofs. -/
@[expose]
def boolCoeffValues : List Bool :=
  [false, true]

/-- The internal Boolean coefficient enumeration has exactly the two field
coefficients. -/
@[simp, grind =] theorem boolCoeffValues_length : boolCoeffValues.length = 2 := by
  rfl

/-- Every Boolean coefficient appears in the internal coefficient enumeration. -/
theorem mem_boolCoeffValues (b : Bool) : b ∈ boolCoeffValues := by
  cases b <;> simp [boolCoeffValues]

/-- The internal Boolean coefficient enumeration contains no duplicates, so
coefficient-list enumeration does not duplicate choices at one position. -/
theorem boolCoeffValues_nodup : boolCoeffValues.Nodup := by
  simp [boolCoeffValues]

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hyx : y = x := hinj y (by simp [hy]) x (by simp) hxy
        exact hxs.1 (by simpa [hyx] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

private theorem nodup_flatMap_of_disjoint
    {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hrow : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisj :
      ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
        ∀ z, z ∈ f x → z ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hrow x (by simp), ?_, ?_⟩
      · exact ih hxs.2
          (by intro y hy; exact hrow y (by simp [hy]))
          (by
            intro y hy z hz hyz t hty htz
            exact hdisj y (by simp [hy]) z (by simp [hz]) hyz t hty htz)
      · intro a ha b hb hab
        rcases List.mem_flatMap.mp hb with ⟨y, hy, hby⟩
        exact hdisj x (by simp) y (by simp [hy]) (by
          intro hxy
          exact hxs.1 (hxy ▸ hy)) a ha (hab ▸ hby)

/-- Internal enumeration of all Boolean coefficient lists of length `d`,
ordered lexicographically by the head coefficient. -/
@[expose]
def coeffBoolLists : Nat → List (List Bool)
  | 0 => [[]]
  | d + 1 =>
      boolCoeffValues.flatMap fun b =>
        (coeffBoolLists d).map fun coeffs => b :: coeffs

/-- Base case of the coefficient-list enumeration: the only length-`0` Boolean
list is the empty list. -/
@[simp, grind =] theorem coeffBoolLists_zero :
    coeffBoolLists 0 = ([[]] : List (List Bool)) :=
  rfl

/-- Recursion equation for the coefficient-list enumeration: every length-`d+1`
list is obtained by prepending each Boolean head value to a length-`d` list. -/
@[simp, grind =] theorem coeffBoolLists_succ (d : Nat) :
    coeffBoolLists (d + 1) =
      boolCoeffValues.flatMap fun b =>
        (coeffBoolLists d).map fun coeffs => b :: coeffs :=
  rfl

/-- Every list produced by `coeffBoolLists d` has length exactly `d`. -/
theorem length_of_mem_coeffBoolLists {d : Nat} {coeffs : List Bool}
    (hmem : coeffs ∈ coeffBoolLists d) :
    coeffs.length = d := by
  induction d generalizing coeffs with
  | zero =>
      simpa [coeffBoolLists] using hmem
  | succ d ih =>
      rw [coeffBoolLists_succ] at hmem
      rcases List.mem_flatMap.mp hmem with ⟨b, _hb, htail⟩
      rcases List.mem_map.mp htail with ⟨tail, htail_mem, hcoeffs⟩
      subst coeffs
      simp [ih htail_mem]

/-- Membership in `coeffBoolLists d` is exactly having length `d`. -/
theorem mem_coeffBoolLists_iff {d : Nat} {coeffs : List Bool} :
    coeffs ∈ coeffBoolLists d ↔ coeffs.length = d := by
  induction d generalizing coeffs with
  | zero =>
      constructor
      · intro h
        simpa [coeffBoolLists] using h
      · intro h
        have hnil : coeffs = [] := List.eq_nil_of_length_eq_zero h
        subst coeffs
        simp [coeffBoolLists]
  | succ d ih =>
      constructor
      · intro h
        exact length_of_mem_coeffBoolLists h
      · intro h
        cases coeffs with
        | nil =>
            simp at h
        | cons b tail =>
            rw [coeffBoolLists_succ]
            apply List.mem_flatMap.mpr
            refine ⟨b, mem_boolCoeffValues b, ?_⟩
            apply List.mem_map.mpr
            refine ⟨tail, ?_, rfl⟩
            apply (ih (coeffs := tail)).mpr
            simpa using Nat.succ.inj h

/-- Every fixed-length Boolean coefficient list appears in the enumeration. -/
theorem mem_coeffBoolLists_of_length_eq {d : Nat} {coeffs : List Bool}
    (hlen : coeffs.length = d) :
    coeffs ∈ coeffBoolLists d :=
  (mem_coeffBoolLists_iff (d := d) (coeffs := coeffs)).mpr hlen

/-- The Boolean coefficient-list enumeration has exactly `2 ^ d` entries. -/
@[simp, grind =] theorem coeffBoolLists_length (d : Nat) :
    (coeffBoolLists d).length = 2 ^ d := by
  induction d with
  | zero =>
      simp [coeffBoolLists]
  | succ d ih =>
      rw [coeffBoolLists_succ]
      calc
        (boolCoeffValues.flatMap fun _b =>
            (coeffBoolLists d).map fun coeffs => _b :: coeffs).length =
            boolCoeffValues.length * (coeffBoolLists d).length := by
              induction boolCoeffValues with
              | nil => simp
              | cons b bs ihbs =>
                  simp [ihbs, Nat.add_mul, Nat.add_comm]
        _ = 2 * 2 ^ d := by simp [ih]
        _ = 2 ^ (d + 1) := by
          rw [Nat.pow_succ]
          exact Nat.mul_comm 2 (2 ^ d)

/-- The fixed-length Boolean coefficient-list enumeration has no duplicates. -/
theorem coeffBoolLists_nodup (d : Nat) :
    (coeffBoolLists d).Nodup := by
  induction d with
  | zero =>
      simp [coeffBoolLists]
  | succ d ih =>
      rw [coeffBoolLists_succ]
      apply nodup_flatMap_of_disjoint
      · exact boolCoeffValues_nodup
      · intro b _hb
        apply nodup_map_of_injective
        · exact ih
        · intro a _ha c _hc h
          exact List.cons.inj h |>.2
      · intro b hb c hc hne x hx hx'
        rcases List.mem_map.mp hx with ⟨tail, _htail, hxtail⟩
        rcases List.mem_map.mp hx' with ⟨tail', _htail', hxtail'⟩
        subst x
        have hhead : b = c := (List.cons.inj hxtail' |>.1).symm
        exact hne hhead

/-- Internal builder for the finite-enumeration proof: interpret `bs[i]` as
the coefficient of `x^(start + i)` in a packed `GF2Poly`. -/
@[expose]
def ofBoolListFrom (start : Nat) : List Bool → GF2Poly
  | [] => 0
  | b :: bs =>
      (if b then monomial start else 0) + ofBoolListFrom (start + 1) bs

/-- Internal builder for the finite-enumeration proof: interpret `bs[i]` as
the coefficient of `x^i` in a packed `GF2Poly`. -/
@[expose]
def ofBoolList (bs : List Bool) : GF2Poly :=
  ofBoolListFrom 0 bs

/-- The packed polynomial built from a coefficient list shifted by `start` has
no coefficient set strictly below `start`. -/
theorem coeff_ofBoolListFrom_lt (start : Nat) :
    ∀ (bs : List Bool) (n : Nat), n < start →
      (ofBoolListFrom start bs).coeff n = false := by
  intro bs
  induction bs generalizing start with
  | nil =>
      intro n _
      simp [ofBoolListFrom]
  | cons b bs ih =>
      intro n hn
      have hne : n ≠ start := Nat.ne_of_lt hn
      have h_left : (if b then monomial start else (0 : GF2Poly)).coeff n = false := by
        cases b with
        | true => simpa using coeff_monomial_ne hne
        | false => simp
      have h_right : (ofBoolListFrom (start + 1) bs).coeff n = false :=
        ih (start + 1) n (by omega)
      change ((if b then monomial start else (0 : GF2Poly))
          + ofBoolListFrom (start + 1) bs).coeff n = false
      rw [coeff_add_eq_bne, h_left, h_right]
      rfl

/-- The packed polynomial built from a coefficient list shifted by `start` reads
back the matching list entry, defaulting to `false` past the end. -/
theorem coeff_ofBoolListFrom_ge (start : Nat) :
    ∀ (bs : List Bool) (n : Nat), start ≤ n →
      (ofBoolListFrom start bs).coeff n = (bs[n - start]?).getD false := by
  intro bs
  induction bs generalizing start with
  | nil =>
      intro n _
      simp [ofBoolListFrom]
  | cons b bs ih =>
      intro n hge
      change ((if b then monomial start else (0 : GF2Poly))
          + ofBoolListFrom (start + 1) bs).coeff n = _
      rw [coeff_add_eq_bne]
      by_cases h_eq : n = start
      · subst h_eq
        have h_right : (ofBoolListFrom (n + 1) bs).coeff n = false :=
          coeff_ofBoolListFrom_lt (n + 1) bs n (Nat.lt_succ_self n)
        rw [h_right]
        have h_idx : n - n = 0 := Nat.sub_self n
        rw [h_idx]
        simp only [List.getElem?_cons_zero, Option.getD_some]
        cases b with
        | true =>
            have h_left : ((if (true : Bool) then monomial n
                else (0 : GF2Poly))).coeff n = true := by simp
            rw [h_left]
            rfl
        | false =>
            have h_left : ((if (false : Bool) then monomial n
                else (0 : GF2Poly))).coeff n = false := by simp
            rw [h_left]
            rfl
      · have h_lt : start < n := Nat.lt_of_le_of_ne hge (Ne.symm h_eq)
        have h_left : (if b then monomial start else (0 : GF2Poly)).coeff n = false := by
          cases b with
          | true => simpa using coeff_monomial_ne h_eq
          | false => simp
        have h_right :
            (ofBoolListFrom (start + 1) bs).coeff n =
              (bs[n - (start + 1)]?).getD false :=
          ih (start + 1) n (by omega)
        rw [h_left, h_right]
        have h_idx : n - start = (n - (start + 1)) + 1 := by omega
        rw [h_idx]
        simp [List.getElem?_cons_succ]

/-- Coefficient correctness for `ofBoolList`: indices below the length read the
matching list entry, indices at or above the length read `false`. -/
theorem coeff_ofBoolList (bs : List Bool) (n : Nat) :
    (ofBoolList bs).coeff n = (bs[n]?).getD false := by
  unfold ofBoolList
  have h := coeff_ofBoolListFrom_ge 0 bs n (Nat.zero_le n)
  simpa using h

/-- Indices at or above the list length read `false`. -/
theorem coeff_ofBoolList_length_le {bs : List Bool} {n : Nat}
    (h : bs.length ≤ n) : (ofBoolList bs).coeff n = false := by
  rw [coeff_ofBoolList]
  have hnone : bs[n]? = none := List.getElem?_eq_none h
  rw [hnone]
  rfl

/-- The packed polynomial built from a length-`d` Boolean coefficient list is
either zero or has degree strictly below `d`. -/
theorem ofBoolList_isZero_or_degree_lt (bs : List Bool) :
    (ofBoolList bs).IsZero ∨ (ofBoolList bs).degree < bs.length := by
  cases h : (ofBoolList bs).isZero with
  | true =>
      exact Or.inl h
  | false =>
      refine Or.inr ?_
      obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false h
      have hdeg : (ofBoolList bs).degree = d := degree_eq_of_degree?_eq_some hd
      rw [hdeg]
      rcases Nat.lt_or_ge d bs.length with hlt | hge'
      · exact hlt
      · have hcoeff_false : (ofBoolList bs).coeff d = false :=
          coeff_ofBoolList_length_le hge'
        have hcoeff_true : (ofBoolList bs).coeff d = true :=
          coeff_eq_true_of_degree?_eq_some hd
        rw [hcoeff_true] at hcoeff_false
        exact Bool.noConfusion hcoeff_false

end Internal

end GF2Poly

/-- `GF(2^n)` for arbitrary `n`, represented by reduced `GF2Poly` residues
modulo an irreducible polynomial. -/
structure GF2nPoly (f : GF2Poly) (hirr : GF2Poly.Irreducible f) where
  /-- The canonical residue representing this field element, reduced modulo `f`. -/
  val : GF2Poly
  /-- The representative is reduced modulo `f`: it is either zero or of degree
  below the modulus, so each field element has exactly one packed spelling.
  Zero is called out separately because the packed degree of the zero
  polynomial is `0`, not `-∞`. -/
  val_reduced : val.IsZero ∨ val.degree < f.degree

/-- `GF(2^n)` packed into one machine word. The modulus stores only the lower
`n` coefficients; the leading `x^n` term is implicit in
`GF2Poly.ofUInt64Monic irr n`. -/
structure GF2n (n : Nat) (irr : UInt64)
    (hn : 0 < n) (hn64 : n < 64)
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) where
  /-- The packed canonical representative: the lower `n` coefficients of the
  residue modulo the implicit modulus `x^n + irr`. -/
  val : UInt64
  /-- The representative is reduced: only the lower `n` bits are set, so each
  field element has exactly one packed spelling and equality of elements is
  equality of words. -/
  val_lt : val.toNat < 2 ^ n


namespace GF2n

variable {n : Nat} {irr : UInt64}
variable {hn : 0 < n} {hn64 : n < 64}
variable {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}

/-- Equality of packed single-word representatives follows from equality of
their stored canonical words. -/
private theorem eq_of_val_eq {a b : GF2n n irr hn hn64 hirr}
    (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

/-- The packed irreducible modulus polynomial defining this extension field. -/
@[expose]
def modulus : GF2Poly :=
  GF2Poly.ofUInt64Monic irr n

/-- The low-word mask selecting canonical representatives of degree `< n`. -/
@[expose]
def mask : UInt64 :=
  GF2Poly.lowerMask n

/-- Convert a machine word into its packed polynomial representative. -/
@[expose]
def toPolyWord (w : UInt64) : GF2Poly :=
  GF2Poly.ofUInt64 w

/-- Convert a `UInt64 × UInt64` carry-less product into a packed polynomial. -/
@[expose]
def toPolyWide (hi lo : UInt64) : GF2Poly :=
  GF2Poly.ofWords #[lo, hi]

/-- Reduce a packed polynomial modulo the fixed irreducible and read back the
single-word representative. -/
@[expose]
def reducePoly (p : GF2Poly) : UInt64 :=
  GF2Poly.packedReduceWord n irr p

/-- Repackage a word as a canonical representative below `2^n`. -/
@[expose]
def canonicalWord (w : UInt64) : UInt64 :=
  GF2Poly.canonicalWordLT n hn64 w

/-- Canonical words are bounded by the extension degree. -/
theorem canonicalWord_lt (w : UInt64) :
    (canonicalWord (n := n) (hn64 := hn64) w).toNat < 2 ^ n := by
  unfold canonicalWord
  simp [GF2Poly.canonicalWordLT]
  exact
    (Nat.mod_lt w.toNat (by
      show 0 < 2 ^ n
      exact Nat.pow_pos (by decide : 0 < 2)))

/-- Canonical constructor from a raw word by reduction modulo the field
modulus. -/
@[expose]
def reduce (w : UInt64) : GF2n n irr hn hn64 hirr :=
  ⟨canonicalWord (n := n) (reducePoly (n := n) (irr := irr) (toPolyWord w)),
    canonicalWord_lt (hn64 := hn64) _⟩

/-- Canonical constructor from a packed 128-bit carry-less product. -/
@[expose]
def reduceWide (hi lo : UInt64) : GF2n n irr hn hn64 hirr :=
  ⟨canonicalWord (n := n) (reducePoly (n := n) (irr := irr) (toPolyWide hi lo)),
    canonicalWord_lt (hn64 := hn64) _⟩

/-- Natural-number literals in characteristic two reduce to their parity. -/
@[expose]
def natCast (k : Nat) : GF2n n irr hn hn64 hirr :=
  if k % 2 = 0 then
    ⟨0, by
      show 0 < 2 ^ n
      exact Nat.pow_pos (by decide : 0 < 2)⟩
  else
    reduce 1

/-- Canonical additive identity. -/
@[expose]
def zero : GF2n n irr hn hn64 hirr :=
  ⟨0, by
    show 0 < 2 ^ n
    exact Nat.pow_pos (by decide : 0 < 2)⟩

instance : Zero (GF2n n irr hn hn64 hirr) where
  zero := zero

/-- Canonical multiplicative identity. -/
@[expose]
def one : GF2n n irr hn hn64 hirr :=
  reduce 1

instance : One (GF2n n irr hn hn64 hirr) where
  one := one

instance : NatCast (GF2n n irr hn hn64 hirr) where
  natCast := natCast

instance (k : Nat) : OfNat (GF2n n irr hn hn64 hirr) k where
  ofNat := natCast k

/-- Addition in characteristic two is word-wise XOR followed by canonical
reduction. -/
@[expose]
def add (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  reduce (a.val ^^^ b.val)

instance : Add (GF2n n irr hn hn64 hirr) where
  add := add

/-- Negation is the identity in characteristic two. -/
@[expose]
def neg (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  a

instance : Neg (GF2n n irr hn hn64 hirr) where
  neg := neg

/-- Subtraction coincides with addition in characteristic two. -/
@[expose]
def sub (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  add a b

instance : Sub (GF2n n irr hn hn64 hirr) where
  sub := sub

/-- Natural scalar multiplication in characteristic two depends only on the
parity of the scalar. -/
@[expose]
def nsmul (k : Nat) (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if k % 2 = 0 then 0 else a

instance : SMul Nat (GF2n n irr hn hn64 hirr) where
  smul := nsmul

/-- Multiplication uses the carry-less word primitive followed by reduction
modulo the packed irreducible. -/
@[expose]
def mul (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  let (hi, lo) := clmul a.val b.val
  reduceWide hi lo

instance : Mul (GF2n n irr hn hn64 hirr) where
  mul := mul

/-- Natural power in `GF(2^n)` by repeated squaring. -/
@[expose]
def pow (a : GF2n n irr hn hn64 hirr) (k : Nat) : GF2n n irr hn hn64 hirr :=
  let rec go (acc base : GF2n n irr hn hn64 hirr) (k : Nat) : GF2n n irr hn hn64 hirr :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      let base' := base * base
      go acc' base' (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 a k

/-- Square-and-multiply accumulator loop for `GF2n.pow`: `go acc base k`
computes `acc * base ^ k`. -/
add_decl_doc GF2n.pow.go

instance : Pow (GF2n n irr hn hn64 hirr) Nat where
  pow := pow

/-- Integer literals also reduce to parity because `-1 = 1` in characteristic
two. -/
@[expose]
def intCast (k : Int) : GF2n n irr hn hn64 hirr :=
  natCast k.natAbs

instance : IntCast (GF2n n irr hn hn64 hirr) where
  intCast := intCast

/-- Integer scalar multiplication depends only on parity as well. -/
@[expose]
def zsmul (k : Int) (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if k.natAbs % 2 = 0 then 0 else a

instance : SMul Int (GF2n n irr hn hn64 hirr) where
  smul := zsmul

/-- The extended Euclidean witness supplies an inverse candidate modulo the
packed irreducible. -/
@[expose]
def invWord (w : UInt64) : UInt64 :=
  GF2Poly.packedInvWord n irr w

/-- Inversion follows the packed extended-GCD path and uses the usual junk
value `0⁻¹ = 0`. -/
@[expose]
def inv (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if a.val == 0 then
    0
  else
    ⟨canonicalWord (n := n) (invWord (n := n) (irr := irr) a.val),
      canonicalWord_lt (hn64 := hn64) _⟩

instance : Inv (GF2n n irr hn hn64 hirr) where
  inv := inv

/-- Division is multiplication by the inverse candidate. -/
@[expose]
def div (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  a * b⁻¹

instance : Div (GF2n n irr hn hn64 hirr) where
  div := div

/-- Integer exponentiation uses inversion for negative exponents. -/
@[expose]
def zpow (a : GF2n n irr hn hn64 hirr) : Int → GF2n n irr hn hn64 hirr
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹

instance : HPow (GF2n n irr hn hn64 hirr) Int (GF2n n irr hn hn64 hirr) where
  hPow := zpow

/-- Division in `GF2n` unfolds to multiplication by the multiplicative inverse. -/
@[grind =] theorem div_eq_mul_inv (a b : GF2n n irr hn hn64 hirr) :
    a / b = a * b⁻¹ :=
  rfl

/-- The inverse of `0` in `GF2n` is `0` (the field convention that makes
inversion total). -/
@[simp, grind =] theorem inv_zero : (0 : GF2n n irr hn hn64 hirr)⁻¹ = 0 := by
  have hzeroVal : (0 : GF2n n irr hn hn64 hirr).val = 0 := by
    simp [OfNat.ofNat, natCast]
  apply eq_of_val_eq
  simp [Inv.inv, inv, hzeroVal]

/-- Every nonzero element of `GF2n` cancels against its inverse, witnessing that
`GF2n` is a field. -/
@[grind =] theorem mul_inv_cancel (a : GF2n n irr hn hn64 hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hval_ne : a.val ≠ 0 := by
    intro hval
    apply ha
    apply eq_of_val_eq
    change a.val = (zero (n := n) (irr := irr) (hn := hn) (hn64 := hn64)
      (hirr := hirr)).val
    simpa [zero] using hval
  apply eq_of_val_eq
  simp [HMul.hMul, Mul.mul, mul, Inv.inv, inv, hval_ne, reduceWide,
    reducePoly, invWord, canonicalWord]
  change GF2Poly.canonicalWordLT n hn64
      (GF2Poly.packedReduceWord n irr
        (toPolyWide (clmul a.val
          (GF2Poly.canonicalWordLT n hn64 (GF2Poly.packedInvWord n irr a.val))).fst
          (clmul a.val
            (GF2Poly.canonicalWordLT n hn64 (GF2Poly.packedInvWord n irr a.val))).snd)) =
    GF2Poly.canonicalWordLT n hn64 (GF2Poly.packedReduceWord n irr 1)
  rw [toPolyWide,
    GF2Poly.packedReduceWord_clmul_packedInvWord_eq_one
      (n := n) (irr := irr) (w := a.val) hn64 hirr hval_ne a.val_lt]

end GF2n

end Hex
