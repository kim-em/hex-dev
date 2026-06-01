import HexGF2.Irreducibility

/-!
Single-word extension-field wrappers for `hex-gf2`.

This module packages both the `n < 64` single-word case and the arbitrary-degree
packed-quotient case of `GF(2^n)` as reduced representatives with XOR addition
and modular multiplication modulo a fixed irreducible polynomial.
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

/-- The two coefficients of `GF(2)`, in a stable enumeration order. -/
def boolCoeffValues : List Bool :=
  [false, true]

@[simp] theorem boolCoeffValues_length : boolCoeffValues.length = 2 := by
  rfl

theorem mem_boolCoeffValues (b : Bool) : b ∈ boolCoeffValues := by
  cases b <;> simp [boolCoeffValues]

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

/-- All Boolean coefficient lists of length `d`, ordered lexicographically by
the head coefficient. -/
def coeffBoolLists : Nat → List (List Bool)
  | 0 => [[]]
  | d + 1 =>
      boolCoeffValues.flatMap fun b =>
        (coeffBoolLists d).map fun coeffs => b :: coeffs

@[simp] theorem coeffBoolLists_zero :
    coeffBoolLists 0 = ([[]] : List (List Bool)) :=
  rfl

@[simp] theorem coeffBoolLists_succ (d : Nat) :
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
@[simp] theorem coeffBoolLists_length (d : Nat) :
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

/-- Build a packed `GF2Poly` from a Boolean coefficient list, treating
`bs[i]` as the coefficient of `x^(start + i)`. -/
def ofBoolListFrom (start : Nat) : List Bool → GF2Poly
  | [] => 0
  | b :: bs =>
      (if b then monomial start else 0) + ofBoolListFrom (start + 1) bs

/-- Build a packed `GF2Poly` from a Boolean coefficient list, treating `bs[i]`
as the coefficient of `x^i`. -/
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

end GF2Poly

/-- `GF(2^n)` for arbitrary `n`, represented by reduced `GF2Poly` residues
modulo an irreducible polynomial. -/
structure GF2nPoly (f : GF2Poly) (hirr : GF2Poly.Irreducible f) where
  val : GF2Poly
  val_reduced : val.IsZero ∨ val.degree < f.degree

/-- `GF(2^n)` packed into one machine word. The modulus stores only the lower
`n` coefficients; the leading `x^n` term is implicit in
`GF2Poly.ofUInt64Monic irr n`. -/
structure GF2n (n : Nat) (irr : UInt64)
    (hn : 0 < n) (hn64 : n < 64)
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) where
  val : UInt64
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
def modulus : GF2Poly :=
  GF2Poly.ofUInt64Monic irr n

/-- The low-word mask selecting canonical representatives of degree `< n`. -/
def mask : UInt64 :=
  GF2Poly.lowerMask n

/-- Convert a machine word into its packed polynomial representative. -/
def toPolyWord (w : UInt64) : GF2Poly :=
  GF2Poly.ofUInt64 w

/-- Convert a `UInt64 × UInt64` carry-less product into a packed polynomial. -/
def toPolyWide (hi lo : UInt64) : GF2Poly :=
  GF2Poly.ofWords #[lo, hi]

/-- Reduce a packed polynomial modulo the fixed irreducible and read back the
single-word representative. -/
def reducePoly (p : GF2Poly) : UInt64 :=
  GF2Poly.packedReduceWord n irr p

/-- Repackage a word as a canonical representative below `2^n`. -/
private def canonicalWord (w : UInt64) : UInt64 :=
  GF2Poly.canonicalWordLT n hn64 w

/-- Canonical words are bounded by the extension degree. -/
private theorem canonicalWord_lt (w : UInt64) :
    (canonicalWord (n := n) (hn64 := hn64) w).toNat < 2 ^ n := by
  unfold canonicalWord
  simp [GF2Poly.canonicalWordLT]
  exact
    (Nat.mod_lt w.toNat (by
      show 0 < 2 ^ n
      exact Nat.pow_pos (by decide : 0 < 2)))

/-- Canonical constructor from a raw word by reduction modulo the field
modulus. -/
def reduce (w : UInt64) : GF2n n irr hn hn64 hirr :=
  ⟨canonicalWord (n := n) (reducePoly (n := n) (irr := irr) (toPolyWord w)),
    canonicalWord_lt (hn64 := hn64) _⟩

/-- Canonical constructor from a packed 128-bit carry-less product. -/
def reduceWide (hi lo : UInt64) : GF2n n irr hn hn64 hirr :=
  ⟨canonicalWord (n := n) (reducePoly (n := n) (irr := irr) (toPolyWide hi lo)),
    canonicalWord_lt (hn64 := hn64) _⟩

/-- Natural-number literals in characteristic two reduce to their parity. -/
def natCast (k : Nat) : GF2n n irr hn hn64 hirr :=
  if k % 2 = 0 then
    ⟨0, by
      show 0 < 2 ^ n
      exact Nat.pow_pos (by decide : 0 < 2)⟩
  else
    reduce 1

/-- Canonical additive identity. -/
def zero : GF2n n irr hn hn64 hirr :=
  ⟨0, by
    show 0 < 2 ^ n
    exact Nat.pow_pos (by decide : 0 < 2)⟩

instance : Zero (GF2n n irr hn hn64 hirr) where
  zero := zero

/-- Canonical multiplicative identity. -/
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
def add (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  reduce (a.val ^^^ b.val)

instance : Add (GF2n n irr hn hn64 hirr) where
  add := add

/-- Negation is the identity in characteristic two. -/
def neg (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  a

instance : Neg (GF2n n irr hn hn64 hirr) where
  neg := neg

/-- Subtraction coincides with addition in characteristic two. -/
def sub (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  add a b

instance : Sub (GF2n n irr hn hn64 hirr) where
  sub := sub

/-- Natural scalar multiplication in characteristic two depends only on the
parity of the scalar. -/
def nsmul (k : Nat) (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if k % 2 = 0 then 0 else a

instance : SMul Nat (GF2n n irr hn hn64 hirr) where
  smul := nsmul

/-- Multiplication uses the carry-less word primitive followed by reduction
modulo the packed irreducible. -/
def mul (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  let (hi, lo) := clmul a.val b.val
  reduceWide hi lo

instance : Mul (GF2n n irr hn hn64 hirr) where
  mul := mul

/-- Natural power in `GF(2^n)` by repeated squaring. -/
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

instance : Pow (GF2n n irr hn hn64 hirr) Nat where
  pow := pow

/-- Integer literals also reduce to parity because `-1 = 1` in characteristic
two. -/
def intCast (k : Int) : GF2n n irr hn hn64 hirr :=
  natCast k.natAbs

instance : IntCast (GF2n n irr hn hn64 hirr) where
  intCast := intCast

/-- Integer scalar multiplication depends only on parity as well. -/
def zsmul (k : Int) (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if k.natAbs % 2 = 0 then 0 else a

instance : SMul Int (GF2n n irr hn hn64 hirr) where
  smul := zsmul

/-- The extended Euclidean witness supplies an inverse candidate modulo the
packed irreducible. -/
private def invWord (w : UInt64) : UInt64 :=
  GF2Poly.packedInvWord n irr w

/-- Inversion follows the packed extended-GCD path and uses the usual junk
value `0⁻¹ = 0`. -/
def inv (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if a.val == 0 then
    0
  else
    ⟨canonicalWord (n := n) (invWord (n := n) (irr := irr) a.val),
      canonicalWord_lt (hn64 := hn64) _⟩

instance : Inv (GF2n n irr hn hn64 hirr) where
  inv := inv

/-- Division is multiplication by the inverse candidate. -/
def div (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  a * b⁻¹

instance : Div (GF2n n irr hn hn64 hirr) where
  div := div

/-- Integer exponentiation uses inversion for negative exponents. -/
def zpow (a : GF2n n irr hn hn64 hirr) : Int → GF2n n irr hn hn64 hirr
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹

instance : HPow (GF2n n irr hn hn64 hirr) Int (GF2n n irr hn hn64 hirr) where
  hPow := zpow

theorem div_eq_mul_inv (a b : GF2n n irr hn hn64 hirr) :
    a / b = a * b⁻¹ :=
  rfl

@[simp] theorem inv_zero : (0 : GF2n n irr hn hn64 hirr)⁻¹ = 0 := by
  have hzeroVal : (0 : GF2n n irr hn hn64 hirr).val = 0 := by
    simp [OfNat.ofNat, natCast]
  apply eq_of_val_eq
  simp [Inv.inv, inv, hzeroVal]

theorem mul_inv_cancel (a : GF2n n irr hn hn64 hirr) (ha : a ≠ 0) :
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

namespace GF2nPoly

variable {f : GF2Poly} {hirr : GF2Poly.Irreducible f}

private theorem add_pair_swap (a b c d : GF2Poly) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  apply GF2Poly.ext_coeff
  intro n
  rw [GF2Poly.coeff_add_eq_bne, GF2Poly.coeff_add_eq_bne,
    GF2Poly.coeff_add_eq_bne, GF2Poly.coeff_add_eq_bne,
    GF2Poly.coeff_add_eq_bne, GF2Poly.coeff_add_eq_bne]
  cases a.coeff n <;> cases b.coeff n <;> cases c.coeff n <;>
    cases d.coeff n <;> rfl

/-- Equality of packed polynomial representatives follows from equality of
their stored reduced polynomials. -/
theorem eq_of_val_eq {a b : GF2nPoly f hirr}
    (h : a.val = b.val) : a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

instance instDecidableEq : DecidableEq (GF2nPoly f hirr) := fun a b =>
  match decEq a.val b.val with
  | isTrue h => isTrue (eq_of_val_eq h)
  | isFalse h => isFalse (fun hab => h (congrArg GF2nPoly.val hab))

/-- Finite-index coefficient code for the reduced representative of a packed
quotient-field element. -/
def coeffVector (a : GF2nPoly f hirr) : Fin f.degree → Bool :=
  GF2Poly.reducedCoeffVector f.degree a.val

/-- The coefficient code is injective on packed quotient-field elements. -/
theorem eq_of_coeffVector_eq {a b : GF2nPoly f hirr}
    (hcoeff : coeffVector a = coeffVector b) :
    a = b := by
  apply eq_of_val_eq
  exact GF2Poly.eq_of_reducedCoeffVector_eq a.val_reduced b.val_reduced hcoeff

/-- The defining irreducible modulus polynomial of the packed quotient field. -/
def modulus : GF2Poly :=
  f

/-- Zero is a reduced representative modulo any packed irreducible. -/
private theorem zero_reduced : (0 : GF2Poly).IsZero ∨ (0 : GF2Poly).degree < f.degree := by
  exact Or.inl rfl

/-- Reduce a packed polynomial to its canonical residue class modulo `f`. -/
def reducePoly (p : GF2Poly) : GF2nPoly f hirr :=
  let r := p % modulus (f := f)
  if hzero : r.isZero = true then
    ⟨r, Or.inl hzero⟩
  else if hdegree : r.degree < f.degree then
    ⟨r, Or.inr hdegree⟩
  else
    ⟨0, zero_reduced (f := f)⟩

theorem reducePoly_val_eq_mod (p : GF2Poly) :
    (reducePoly (f := f) (hirr := hirr) p).val = p % f := by
  unfold reducePoly modulus
  by_cases hzero : (p % f).isZero = true
  · simp [hzero]
  · by_cases hdegree : (p % f).degree < f.degree
    · simp [hzero, hdegree]
    · have hrem := GF2Poly.mod_degree_lt p f hirr.1
      cases hrem with
      | inl hrem_zero => exact False.elim (hzero hrem_zero)
      | inr hrem_degree => exact False.elim (hdegree hrem_degree)

theorem reducePoly_eq_iff_mod_eq {p q : GF2Poly} :
    reducePoly (f := f) (hirr := hirr) p =
      reducePoly (f := f) (hirr := hirr) q ↔
    p % f = q % f := by
  constructor
  · intro h
    have hval := congrArg GF2nPoly.val h
    simpa [reducePoly_val_eq_mod (f := f) (hirr := hirr) p,
      reducePoly_val_eq_mod (f := f) (hirr := hirr) q] using hval
  · intro h
    apply eq_of_val_eq
    simp [reducePoly_val_eq_mod, h]

/-- Reducing an already-computed remainder gives the same quotient class as
reducing the original polynomial. -/
theorem reducePoly_mod_eq (p : GF2Poly) :
    reducePoly (f := f) (hirr := hirr) (p % f) =
      reducePoly (f := f) (hirr := hirr) p := by
  rw [reducePoly_eq_iff_mod_eq]
  exact GF2Poly.mod_eq_self_of_reduced (p % f) f
    (GF2Poly.mod_degree_lt p f hirr.1)

private theorem mod_add_mod_eq_mod_add (p q f : GF2Poly) :
    ((p % f) + (q % f)) % f = (p + q) % f := by
  let qp := (GF2Poly.divMod p f).1
  let rp := (GF2Poly.divMod p f).2
  let qq := (GF2Poly.divMod q f).1
  let rq := (GF2Poly.divMod q f).2
  have hp : p = rp + qp * f := by
    have hspec : qp * f + rp = p := by
      simpa [qp, rp] using GF2Poly.divMod_spec p f
    rw [← hspec, GF2Poly.add_comm]
  have hq : q = rq + qq * f := by
    have hspec : qq * f + rq = q := by
      simpa [qq, rq] using GF2Poly.divMod_spec q f
    rw [← hspec, GF2Poly.add_comm]
  have hsum :
      p + q = (rp + rq) + (qp + qq) * f := by
    rw [hp, hq, GF2Poly.left_distrib]
    exact add_pair_swap rp (qp * f) rq (qq * f)
  calc
    ((p % f) + (q % f)) % f = (rp + rq) % f := by rfl
    _ = ((rp + rq) + (qp + qq) * f) % f := by
          exact (GF2Poly.mod_add_mul_right_eq_mod (rp + rq) (qp + qq) f).symm
    _ = (p + q) % f := by rw [hsum]

private theorem mod_mul_mod_eq_mod_mul (p q f : GF2Poly) :
    ((p % f) * (q % f)) % f = (p * q) % f := by
  let qp := (GF2Poly.divMod p f).1
  let rp := (GF2Poly.divMod p f).2
  let qq := (GF2Poly.divMod q f).1
  let rq := (GF2Poly.divMod q f).2
  have hp : p = rp + qp * f := by
    have hspec : qp * f + rp = p := by
      simpa [qp, rp] using GF2Poly.divMod_spec p f
    rw [← hspec, GF2Poly.add_comm]
  have hq : q = rq + qq * f := by
    have hspec : qq * f + rq = q := by
      simpa [qq, rq] using GF2Poly.divMod_spec q f
    rw [← hspec, GF2Poly.add_comm]
  let c := qp * rq + (rp * qq + (qp * qq) * f)
  have hmul :
      p * q = rp * rq + c * f := by
    rw [hp, hq]
    calc
      (rp + qp * f) * (rq + qq * f)
          = (rp * rq + rp * (qq * f)) + ((qp * f) * rq + (qp * f) * (qq * f)) := by
              rw [GF2Poly.right_distrib, GF2Poly.left_distrib, GF2Poly.left_distrib]
              exact add_pair_swap (rp * rq) ((qp * f) * rq) (rp * (qq * f))
                ((qp * f) * (qq * f))
      _ = (rp * rq + (qp * f) * rq) + (rp * (qq * f) + (qp * f) * (qq * f)) := by
          exact add_pair_swap (rp * rq) (rp * (qq * f)) ((qp * f) * rq)
            ((qp * f) * (qq * f))
      _ = (rp * rq + (qp * rq) * f) +
            ((rp * qq) * f + ((qp * qq) * f) * f) := by
          have hqprq : (qp * f) * rq = (qp * rq) * f := by
            rw [GF2Poly.mul_assoc qp f rq, GF2Poly.mul_comm f rq,
              ← GF2Poly.mul_assoc qp rq f]
          have hrpqq : rp * (qq * f) = (rp * qq) * f := by
            rw [GF2Poly.mul_assoc rp qq f]
          have hqpqq : (qp * f) * (qq * f) = ((qp * qq) * f) * f := by
            calc
              (qp * f) * (qq * f) = qp * (f * (qq * f)) := by
                rw [GF2Poly.mul_assoc]
              _ = qp * ((f * qq) * f) := by
                rw [GF2Poly.mul_assoc f qq f]
              _ = qp * ((qq * f) * f) := by
                rw [GF2Poly.mul_comm f qq]
              _ = (qp * (qq * f)) * f := by
                rw [GF2Poly.mul_assoc qp (qq * f) f]
              _ = ((qp * qq) * f) * f := by
                rw [GF2Poly.mul_assoc qp qq f]
          rw [hqprq, hrpqq, hqpqq]
      _ = rp * rq + ((qp * rq + (rp * qq + (qp * qq) * f)) * f) := by
          have htail :
              (qp * rq) * f + ((rp * qq) * f + ((qp * qq) * f) * f) =
                (qp * rq + (rp * qq + (qp * qq) * f)) * f := by
            rw [← GF2Poly.left_distrib (rp * qq) ((qp * qq) * f) f,
              ← GF2Poly.left_distrib (qp * rq) (rp * qq + (qp * qq) * f) f]
          rw [GF2Poly.add_assoc, htail]
  calc
    ((p % f) * (q % f)) % f = (rp * rq) % f := by rfl
    _ = (rp * rq + c * f) % f := by
          exact (GF2Poly.mod_add_mul_right_eq_mod (rp * rq) c f).symm
    _ = (p * q) % f := by rw [hmul]

private theorem mod_eq_zero_of_dvd {p f : GF2Poly} (hf : f ≠ 0) (h : f ∣ p) :
    p % f = 0 := by
  rcases h with ⟨c, hc⟩
  have hrem_reduced : (p % f).isZero = true ∨ (p % f).degree < f.degree :=
    GF2Poly.mod_degree_lt p f hf
  have hfdvd_rem : f ∣ p % f := by
    let q := (GF2Poly.divMod p f).1
    let r := (GF2Poly.divMod p f).2
    have hspec : q * f + r = p := by
      simpa [q, r] using GF2Poly.divMod_spec p f
    refine ⟨q + c, ?_⟩
    calc
      p % f = r := rfl
      _ = q * f + (q * f + r) := by
        symm
        rw [← GF2Poly.add_assoc, GF2Poly.add_self, GF2Poly.zero_add]
      _ = q * f + p := by rw [hspec]
      _ = q * f + f * c := by rw [hc]
      _ = f * q + f * c := by rw [GF2Poly.mul_comm q f]
      _ = f * (q + c) := by rw [GF2Poly.right_distrib]
  by_cases hzero : p % f = 0
  · exact hzero
  · cases hrem_reduced with
    | inl hzero_isZero =>
        exact GF2Poly.eq_zero_of_isZero hzero_isZero
    | inr hlt =>
        have hle : f.degree ≤ (p % f).degree :=
          GF2Poly.degree_le_of_dvd_nonzero hf hzero hfdvd_rem
        omega

private theorem dvd_of_mod_eq_zero {p f : GF2Poly} (h : p % f = 0) :
    f ∣ p := by
  let q := (GF2Poly.divMod p f).1
  have hspec : q * f + p % f = p := by
    simpa [q, GF2Poly.mod] using GF2Poly.divMod_spec p f
  refine ⟨q, ?_⟩
  rw [h] at hspec
  rw [GF2Poly.add_zero] at hspec
  exact hspec.symm.trans (GF2Poly.mul_comm q f)

/-- Canonical additive identity. -/
def zero : GF2nPoly f hirr :=
  ⟨0, zero_reduced (f := f)⟩

instance : Zero (GF2nPoly f hirr) where
  zero := zero

theorem reducePoly_eq_zero_iff_dvd {p : GF2Poly} (hf : f ≠ 0) :
    reducePoly (f := f) (hirr := hirr) p = 0 ↔ f ∣ p := by
  constructor
  · intro h
    apply dvd_of_mod_eq_zero
    have hval := congrArg GF2nPoly.val h
    simpa [reducePoly_val_eq_mod (f := f) (hirr := hirr) p, zero] using hval
  · intro h
    apply eq_of_val_eq
    change (reducePoly (f := f) (hirr := hirr) p).val = (zero (f := f)).val
    simp [reducePoly_val_eq_mod, zero, mod_eq_zero_of_dvd hf h]

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {g : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → g a = g b → a = b) :
    (xs.map g).Nodup := by
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

private theorem length_filter_ne_eq_pred_of_mem_nodup
    {α : Type} [DecidableEq α] {z : α} :
    ∀ {xs : List α}, z ∈ xs → xs.Nodup →
      (xs.filter (fun a => decide (a ≠ z))).length = xs.length - 1
  | [], hmem, _ => by
      cases hmem
  | x :: xs, hmem, hnodup => by
      rw [List.nodup_cons] at hnodup
      by_cases hx : x = z
      · have hnot_mem : x ∉ xs := hnodup.1
        have hfilter : xs.filter (fun a => decide (a ≠ z)) = xs := by
          rw [List.filter_eq_self]
          intro a ha
          exact decide_eq_true (fun haz => hnot_mem (by simpa [hx, haz] using ha))
        rw [List.filter_cons_of_neg]
        · rw [hfilter]
          simp
        · simp [hx]
      · have hz_mem_xs : z ∈ xs := by
          cases hmem with
          | head =>
              exact False.elim (hx rfl)
          | tail _ hz =>
              exact hz
        have ih := length_filter_ne_eq_pred_of_mem_nodup hz_mem_xs hnodup.2
        have hlen_pos : 0 < xs.length := List.length_pos_of_mem hz_mem_xs
        rw [List.filter_cons_of_pos]
        · simp only [List.length_cons]
          rw [ih]
          omega
        · exact decide_eq_true hx

/--
Evaluate a Boolean coefficient list as a quotient expression in the class of
`X`. The list is low-coefficient first: `bs[i]` is the coefficient of `X^i`.
-/
def boolListExpression (bs : List Bool) : GF2nPoly f hirr :=
  reducePoly (f := f) (hirr := hirr) (GF2Poly.ofBoolList bs)

/-- The value of a Boolean quotient expression is the reduced packed
polynomial built from the same coefficient list. -/
theorem boolListExpression_val_eq_mod (bs : List Bool) :
    (boolListExpression (f := f) (hirr := hirr) bs).val =
      GF2Poly.ofBoolList bs % f := by
  unfold boolListExpression
  rw [reducePoly_val_eq_mod]

/-- All packed quotient-field elements, enumerated by reducing every length-`f.degree`
Boolean coefficient list. -/
def elements : List (GF2nPoly f hirr) :=
  (GF2Poly.coeffBoolLists f.degree).map
    (boolListExpression (f := f) (hirr := hirr))

@[simp] theorem elements_length :
    (elements (f := f) (hirr := hirr)).length = 2 ^ f.degree := by
  simp [elements]

/-- Every packed quotient-field element appears in `elements`. -/
theorem mem_elements (a : GF2nPoly f hirr) :
    a ∈ elements (f := f) (hirr := hirr) := by
  unfold elements
  apply List.mem_map.mpr
  refine ⟨List.ofFn (coeffVector a), ?_, ?_⟩
  · apply GF2Poly.mem_coeffBoolLists_of_length_eq
    simp
  · apply eq_of_val_eq
    rw [boolListExpression_val_eq_mod]
    have hofBL_red :
        (GF2Poly.ofBoolList (List.ofFn (coeffVector a))).IsZero ∨
          (GF2Poly.ofBoolList (List.ofFn (coeffVector a))).degree < f.degree := by
      have h := GF2Poly.ofBoolList_isZero_or_degree_lt (List.ofFn (coeffVector a))
      simp at h
      exact h
    have hofBL_eq :
        GF2Poly.ofBoolList (List.ofFn (coeffVector a)) = a.val := by
      apply GF2Poly.eq_of_reducedCoeffVector_eq hofBL_red a.val_reduced
      funext i
      unfold GF2Poly.reducedCoeffVector
      rw [GF2Poly.coeff_ofBoolList]
      have hi_lt : i.val < (List.ofFn (coeffVector a)).length := by
        rw [List.length_ofFn]; exact i.is_lt
      rw [List.getElem?_eq_getElem hi_lt]
      simp [List.getElem_ofFn, coeffVector, GF2Poly.reducedCoeffVector]
    rw [hofBL_eq]
    exact GF2Poly.mod_eq_self_of_reduced a.val f a.val_reduced

/-- The quotient expression built from an element's coefficient vector is that
element. -/
theorem boolListExpression_coeffVector (a : GF2nPoly f hirr) :
    boolListExpression (f := f) (hirr := hirr) (List.ofFn (coeffVector a)) = a := by
  apply eq_of_val_eq
  rw [boolListExpression_val_eq_mod]
  have hofBL_red :
      (GF2Poly.ofBoolList (List.ofFn (coeffVector a))).IsZero ∨
        (GF2Poly.ofBoolList (List.ofFn (coeffVector a))).degree < f.degree := by
    have h := GF2Poly.ofBoolList_isZero_or_degree_lt (List.ofFn (coeffVector a))
    simp at h
    exact h
  have hofBL_eq :
      GF2Poly.ofBoolList (List.ofFn (coeffVector a)) = a.val := by
    apply GF2Poly.eq_of_reducedCoeffVector_eq hofBL_red a.val_reduced
    funext i
    unfold GF2Poly.reducedCoeffVector
    rw [GF2Poly.coeff_ofBoolList]
    have hi_lt : i.val < (List.ofFn (coeffVector a)).length := by
      rw [List.length_ofFn]; exact i.is_lt
    rw [List.getElem?_eq_getElem hi_lt]
    simp [List.getElem_ofFn, coeffVector, GF2Poly.reducedCoeffVector]
  rw [hofBL_eq]
  exact GF2Poly.mod_eq_self_of_reduced a.val f a.val_reduced

/-- Every packed quotient element is generated by a Boolean coefficient list in
the class of `X`, with exactly `f.degree` coefficients. -/
theorem exists_boolListExpression (a : GF2nPoly f hirr) :
    ∃ bs : List Bool,
      bs.length = f.degree ∧
        boolListExpression (f := f) (hirr := hirr) bs = a := by
  refine ⟨List.ofFn (coeffVector a), ?_, boolListExpression_coeffVector
    (f := f) (hirr := hirr) a⟩
  simp

/-- The quotient enumeration has no duplicate elements. -/
theorem elements_nodup :
    (elements (f := f) (hirr := hirr)).Nodup := by
  unfold elements
  apply nodup_map_of_injective
  · exact GF2Poly.coeffBoolLists_nodup f.degree
  · intro bs hbs bs' hbs' hred
    have hbs_len := GF2Poly.length_of_mem_coeffBoolLists hbs
    have hbs'_len := GF2Poly.length_of_mem_coeffBoolLists hbs'
    have hbs_red :
        (GF2Poly.ofBoolList bs).IsZero ∨
          (GF2Poly.ofBoolList bs).degree < f.degree := by
      have h := GF2Poly.ofBoolList_isZero_or_degree_lt bs
      rw [hbs_len] at h
      exact h
    have hbs'_red :
        (GF2Poly.ofBoolList bs').IsZero ∨
          (GF2Poly.ofBoolList bs').degree < f.degree := by
      have h := GF2Poly.ofBoolList_isZero_or_degree_lt bs'
      rw [hbs'_len] at h
      exact h
    have hofBL_eq : GF2Poly.ofBoolList bs = GF2Poly.ofBoolList bs' := by
      have hred_val := congrArg GF2nPoly.val hred
      rw [boolListExpression_val_eq_mod, boolListExpression_val_eq_mod] at hred_val
      rw [GF2Poly.mod_eq_self_of_reduced (GF2Poly.ofBoolList bs) f hbs_red,
        GF2Poly.mod_eq_self_of_reduced (GF2Poly.ofBoolList bs') f hbs'_red] at hred_val
      exact hred_val
    apply List.ext_getElem (by rw [hbs_len, hbs'_len])
    intro i hi hi'
    have hcoeff : (GF2Poly.ofBoolList bs).coeff i = (GF2Poly.ofBoolList bs').coeff i :=
      congrArg (fun p : GF2Poly => p.coeff i) hofBL_eq
    rw [GF2Poly.coeff_ofBoolList, GF2Poly.coeff_ofBoolList,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hcoeff
    simpa using hcoeff

/-- The quotient has `2 ^ f.degree` canonical representatives. -/
theorem elements_card :
    (elements (f := f) (hirr := hirr)).length = 2 ^ f.degree :=
  elements_length (f := f) (hirr := hirr)

/-- The nonzero packed quotient-field elements, as a duplicate-free sublist of
`elements`. -/
def nonzeroElements : List (GF2nPoly f hirr) :=
  (elements (f := f) (hirr := hirr)).filter (fun a => decide (a ≠ 0))

/-- Membership in `nonzeroElements` is exactly nonzero quotient membership. -/
theorem mem_nonzeroElements (a : GF2nPoly f hirr) :
    a ∈ nonzeroElements (f := f) (hirr := hirr) ↔ a ≠ 0 := by
  simp [nonzeroElements, mem_elements a]

/-- The nonzero quotient enumeration has no duplicates. -/
theorem nonzeroElements_nodup :
    (nonzeroElements (f := f) (hirr := hirr)).Nodup := by
  unfold nonzeroElements
  exact (elements_nodup (f := f) (hirr := hirr)).filter _

/-- There are `2 ^ f.degree - 1` nonzero quotient representatives. -/
theorem nonzeroElements_card :
    (nonzeroElements (f := f) (hirr := hirr)).length = 2 ^ f.degree - 1 := by
  unfold nonzeroElements
  rw [length_filter_ne_eq_pred_of_mem_nodup
    (mem_elements (f := f) (hirr := hirr) 0)
    (elements_nodup (f := f) (hirr := hirr))]
  rw [elements_card]

/-- The quotient class of `X` modulo the packed irreducible `f`. -/
def X : GF2nPoly f hirr :=
  reducePoly (GF2Poly.monomial 1)

/-- Canonical multiplicative identity. -/
def one : GF2nPoly f hirr :=
  reducePoly 1

instance : One (GF2nPoly f hirr) where
  one := one

/-- Natural-number literals reduce to parity in characteristic two. -/
def natCast (k : Nat) : GF2nPoly f hirr :=
  if k % 2 = 0 then zero else one

instance : NatCast (GF2nPoly f hirr) where
  natCast := natCast

instance (k : Nat) : OfNat (GF2nPoly f hirr) k where
  ofNat := natCast k

/-- Addition in characteristic two is XOR on representatives, followed by
canonical reduction modulo `f`. -/
def add (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val + b.val)

instance : Add (GF2nPoly f hirr) where
  add := add

/-- Reducing a polynomial sum agrees with adding the reduced quotient
representatives. -/
theorem reducePoly_add_eq (p q : GF2Poly) :
    reducePoly (f := f) (hirr := hirr) (p + q) =
      reducePoly (f := f) (hirr := hirr)
        ((reducePoly (f := f) (hirr := hirr) p).val +
          (reducePoly (f := f) (hirr := hirr) q).val) := by
  rw [reducePoly_eq_iff_mod_eq]
  rw [reducePoly_val_eq_mod, reducePoly_val_eq_mod]
  exact (mod_add_mod_eq_mod_add p q f).symm

/-- Negation is the identity in characteristic two. -/
def neg (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  a

instance : Neg (GF2nPoly f hirr) where
  neg := neg

/-- Subtraction coincides with addition in characteristic two. -/
def sub (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  add a b

instance : Sub (GF2nPoly f hirr) where
  sub := sub

/-- Natural scalar multiplication depends only on parity. -/
def nsmul (k : Nat) (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if k % 2 = 0 then 0 else a

instance : SMul Nat (GF2nPoly f hirr) where
  smul := nsmul

/-- Multiplication uses packed `GF2Poly` multiplication followed by reduction
modulo the irreducible defining polynomial. -/
def mul (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val * b.val)

instance : Mul (GF2nPoly f hirr) where
  mul := mul

/-- Reducing a polynomial product agrees with multiplying the reduced quotient
representatives. -/
theorem reducePoly_mul_eq (p q : GF2Poly) :
    reducePoly (f := f) (hirr := hirr) (p * q) =
      reducePoly (f := f) (hirr := hirr)
        ((reducePoly (f := f) (hirr := hirr) p).val *
          (reducePoly (f := f) (hirr := hirr) q).val) := by
  rw [reducePoly_eq_iff_mod_eq]
  rw [reducePoly_val_eq_mod, reducePoly_val_eq_mod]
  exact (mod_mul_mod_eq_mod_mul p q f).symm

/-- Natural power in the packed quotient field by repeated squaring. -/
def pow (a : GF2nPoly f hirr) (k : Nat) : GF2nPoly f hirr :=
  let rec go (acc base : GF2nPoly f hirr) (k : Nat) : GF2nPoly f hirr :=
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

instance : Pow (GF2nPoly f hirr) Nat where
  pow := pow

/-- Iterated Frobenius squaring in the packed quotient, starting from a
specified quotient element. -/
def frobeniusIter (a : GF2nPoly f hirr) : Nat → GF2nPoly f hirr
  | 0 => a
  | k + 1 => frobeniusIter a k * frobeniusIter a k

@[simp] theorem frobeniusIter_zero (a : GF2nPoly f hirr) :
    frobeniusIter a 0 = a := rfl

@[simp] theorem frobeniusIter_succ (a : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter a (k + 1) = frobeniusIter a k * frobeniusIter a k := rfl

/-- Frobenius iterates compose by adding their iteration counts. -/
theorem frobeniusIter_add (a : GF2nPoly f hirr) (m n : Nat) :
    frobeniusIter (frobeniusIter a m) n = frobeniusIter a (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      rw [frobeniusIter_succ, ih]
      have hidx : m + (n + 1) = (m + n) + 1 := by omega
      rw [hidx, frobeniusIter_succ]

/-- Iterated quotient squaring of the class of `X` follows the executable
`xpow2kMod` remainder chain used by Rabin soundness. -/
theorem quotient_X_frobeniusIter_eq_reduce_xpow2kMod (k : Nat) :
    frobeniusIter (X (f := f) (hirr := hirr)) k =
      reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k) := by
  induction k with
  | zero =>
      change X (f := f) (hirr := hirr) =
        reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial 1 % f)
      rw [X, reducePoly_mod_eq]
  | succ k ih =>
      calc
        frobeniusIter (X (f := f) (hirr := hirr)) (k + 1)
            = reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k) *
                reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k) := by
                  rw [frobeniusIter_succ, ih]
        _ = reducePoly (f := f) (hirr := hirr)
              ((reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k)).val *
                (reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f k)).val) := rfl
        _ = reducePoly (f := f) (hirr := hirr)
              (GF2Poly.xpow2kMod f k * GF2Poly.xpow2kMod f k) := by
                rw [← reducePoly_mul_eq]
        _ = reducePoly (f := f) (hirr := hirr)
              ((GF2Poly.xpow2kMod f k * GF2Poly.xpow2kMod f k) % f) := by
                rw [reducePoly_mod_eq]
        _ = reducePoly (f := f) (hirr := hirr) (GF2Poly.xpow2kMod f (k + 1)) := by
                rfl

/-- Integer literals reduce to parity. -/
def intCast (k : Int) : GF2nPoly f hirr :=
  natCast k.natAbs

instance : IntCast (GF2nPoly f hirr) where
  intCast := intCast

/-- Integer scalar multiplication depends only on parity. -/
def zsmul (k : Int) (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if k.natAbs % 2 = 0 then 0 else a

instance : SMul Int (GF2nPoly f hirr) where
  smul := zsmul

/-- The extended Euclidean witness supplies an inverse candidate modulo the
packed irreducible. -/
private def invPoly (p : GF2Poly) : GF2Poly :=
  (GF2Poly.xgcd p (modulus (f := f))).left

/-- Inversion follows the packed extended-GCD path and uses the usual junk
value `0⁻¹ = 0`. -/
def inv (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if a.val.isZero then
    0
  else
    reducePoly (invPoly (f := f) a.val)

instance : Inv (GF2nPoly f hirr) where
  inv := inv

/-- Division is multiplication by the inverse candidate. -/
def div (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  a * b⁻¹

instance : Div (GF2nPoly f hirr) where
  div := div

/-- Integer exponentiation uses inversion for negative exponents. -/
def zpow (a : GF2nPoly f hirr) : Int → GF2nPoly f hirr
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹

instance : HPow (GF2nPoly f hirr) Int (GF2nPoly f hirr) where
  hPow := zpow

theorem div_eq_mul_inv (a b : GF2nPoly f hirr) :
    a / b = a * b⁻¹ :=
  rfl

@[simp] theorem inv_zero : (0 : GF2nPoly f hirr)⁻¹ = 0 := by
  have hzeroVal : (0 : GF2nPoly f hirr).val = 0 := by
    simp [OfNat.ofNat, natCast, zero]
  apply eq_of_val_eq
  simp [Inv.inv, inv, hzeroVal]

theorem mul_inv_cancel (a : GF2nPoly f hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hval_ne : a.val ≠ 0 := by
    intro hval
    apply ha
    apply eq_of_val_eq
    change a.val = (zero (f := f) (hirr := hirr)).val
    simpa [zero] using hval
  have hval_nonzero : a.val.isZero = false := by
    cases hzero : a.val.isZero
    · rfl
    · exfalso
      exact hval_ne (GF2Poly.eq_zero_of_isZero hzero)
  apply eq_of_val_eq
  simp [HMul.hMul, Mul.mul, mul, Inv.inv, inv, hval_nonzero, invPoly]
  change (reducePoly (f := f) (hirr := hirr)
      (a.val * (reducePoly (f := f) (hirr := hirr) (GF2Poly.xgcd a.val f).left).val)).val =
    (reducePoly (f := f) (hirr := hirr) 1).val
  rw [reducePoly_val_eq_mod
      (f := f) (hirr := hirr)
      (p := a.val * (reducePoly (f := f) (hirr := hirr) (GF2Poly.xgcd a.val f).left).val),
    reducePoly_val_eq_mod (f := f) (hirr := hirr) (p := (GF2Poly.xgcd a.val f).left),
    reducePoly_val_eq_mod (f := f) (hirr := hirr) (p := 1)]
  exact GF2Poly.mul_mod_xgcd_left_mod_eq_one_of_irreducible_of_nonzero_reduced
    hirr hval_ne a.val_reduced

private theorem GF2Poly_mulXk_zero (p : GF2Poly) : p.mulXk 0 = p := by
  apply GF2Poly.ext_coeff
  intro n
  rw [GF2Poly.coeff_mulXk, GF2Poly.coeff_shiftLeft]
  simp [GF2Poly.coeff]

private theorem GF2Poly_one_mul (p : GF2Poly) : (1 : GF2Poly) * p = p := by
  show GF2Poly.monomial 0 * p = p
  rw [GF2Poly.monomial_mul, GF2Poly_mulXk_zero]

/-- The value of a quotient product is the polynomial product reduced modulo
the defining irreducible. -/
@[simp] theorem mul_val (a b : GF2nPoly f hirr) :
    (a * b).val = (a.val * b.val) % f := by
  show (mul a b).val = _
  unfold mul
  rw [reducePoly_val_eq_mod]

/-- The value of the multiplicative identity is `(1 : GF2Poly) % f`. -/
@[simp] theorem one_val :
    (1 : GF2nPoly f hirr).val = (1 : GF2Poly) % f := by
  show (one (f := f) (hirr := hirr)).val = _
  unfold one
  rw [reducePoly_val_eq_mod]

/-- The value of a quotient sum is the polynomial sum reduced modulo the
defining irreducible. -/
@[simp] theorem add_val (a b : GF2nPoly f hirr) :
    (a + b).val = (a.val + b.val) % f := by
  show (add a b).val = _
  unfold add
  rw [reducePoly_val_eq_mod]

/-- Negation is the identity on the packed quotient. -/
@[simp] theorem neg_val (a : GF2nPoly f hirr) : (-a).val = a.val := rfl

/-- Subtraction coincides with addition on the packed quotient. -/
theorem sub_val (a b : GF2nPoly f hirr) :
    (a - b).val = (a.val + b.val) % f := by
  show (sub a b).val = _
  unfold sub
  exact add_val a b

/-- The value of the additive identity is the zero polynomial. -/
@[simp] theorem zero_val :
    (0 : GF2nPoly f hirr).val = (0 : GF2Poly) := rfl

example (a b : GF2nPoly f hirr) :
    ((a * b) + 1).val = ((a.val * b.val) % f + (1 : GF2Poly) % f) % f := by
  simp

/-- A reduced quotient value is its own remainder modulo `f`. -/
private theorem val_mod_eq (a : GF2nPoly f hirr) : a.val % f = a.val :=
  GF2Poly.mod_eq_self_of_reduced a.val f a.val_reduced

/-- Addition is commutative on the packed quotient. -/
theorem add_comm (a b : GF2nPoly f hirr) : a + b = b + a := by
  apply eq_of_val_eq
  rw [add_val, add_val, GF2Poly.add_comm]

/-- Addition is associative on the packed quotient. -/
theorem add_assoc (a b c : GF2nPoly f hirr) :
    (a + b) + c = a + (b + c) := by
  apply eq_of_val_eq
  rw [add_val, add_val, add_val, add_val]
  have hleft : (((a.val + b.val) % f) + c.val) % f =
      (a.val + b.val + c.val) % f := by
    have h := mod_add_mod_eq_mod_add (a.val + b.val) c.val f
    rw [val_mod_eq c] at h
    exact h
  have hright : (a.val + ((b.val + c.val) % f)) % f =
      (a.val + (b.val + c.val)) % f := by
    have h := mod_add_mod_eq_mod_add a.val (b.val + c.val) f
    rw [val_mod_eq a] at h
    exact h
  rw [hleft, hright, GF2Poly.add_assoc]

private theorem add_pair_swap_quot
    (a b c d : GF2nPoly f hirr) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc a b (c + d)]
  rw [← add_assoc b c d]
  rw [add_comm b c]
  rw [add_assoc c b d]
  rw [← add_assoc a c (b + d)]

/-- The additive identity is a left identity. -/
@[simp] theorem zero_add (a : GF2nPoly f hirr) :
    (0 : GF2nPoly f hirr) + a = a := by
  apply eq_of_val_eq
  rw [add_val, zero_val, GF2Poly.zero_add, val_mod_eq]

/-- The additive identity is a right identity. -/
@[simp] theorem add_zero (a : GF2nPoly f hirr) :
    a + (0 : GF2nPoly f hirr) = a := by
  rw [add_comm, zero_add]

/-- Every packed quotient element is its own additive inverse in
characteristic two. -/
@[simp] theorem add_self (a : GF2nPoly f hirr) : a + a = 0 := by
  apply eq_of_val_eq
  rw [add_val, GF2Poly.add_self]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Multiplication by zero on the right is zero. -/
@[simp] theorem mul_zero (a : GF2nPoly f hirr) :
    a * (0 : GF2nPoly f hirr) = 0 := by
  apply eq_of_val_eq
  rw [mul_val, zero_val, GF2Poly.mul_zero]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Multiplication by zero on the left is zero. -/
@[simp] theorem zero_mul (a : GF2nPoly f hirr) :
    (0 : GF2nPoly f hirr) * a = 0 := by
  apply eq_of_val_eq
  rw [mul_val, zero_val, GF2Poly.zero_mul]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Multiplication is commutative on the packed quotient. -/
theorem mul_comm (a b : GF2nPoly f hirr) : a * b = b * a := by
  apply eq_of_val_eq
  rw [mul_val, mul_val, GF2Poly.mul_comm]

/-- Multiplication is associative on the packed quotient. -/
theorem mul_assoc (a b c : GF2nPoly f hirr) :
    (a * b) * c = a * (b * c) := by
  apply eq_of_val_eq
  rw [mul_val, mul_val, mul_val, mul_val]
  have hca : ((a.val * b.val) % f * c.val) % f = (a.val * b.val * c.val) % f := by
    have h := mod_mul_mod_eq_mod_mul (a.val * b.val) c.val f
    rw [val_mod_eq c] at h
    exact h
  have hcb : (a.val * ((b.val * c.val) % f)) % f = (a.val * (b.val * c.val)) % f := by
    have h := mod_mul_mod_eq_mod_mul a.val (b.val * c.val) f
    rw [val_mod_eq a] at h
    exact h
  rw [hca, hcb, GF2Poly.mul_assoc]

/-- Multiplication distributes over addition on the left in the packed
quotient. -/
theorem left_distrib (a b c : GF2nPoly f hirr) :
    a * (b + c) = a * b + a * c := by
  apply eq_of_val_eq
  rw [mul_val, add_val, add_val, mul_val, mul_val]
  have hmul : (a.val * ((b.val + c.val) % f)) % f =
      (a.val * (b.val + c.val)) % f := by
    have h := mod_mul_mod_eq_mod_mul a.val (b.val + c.val) f
    rw [val_mod_eq a] at h
    exact h
  have hadd : (((a.val * b.val) % f) + ((a.val * c.val) % f)) % f =
      (a.val * b.val + a.val * c.val) % f :=
    mod_add_mod_eq_mod_add (a.val * b.val) (a.val * c.val) f
  rw [hmul, hadd, GF2Poly.right_distrib]

/-- Multiplication distributes over addition on the right in the packed
quotient. -/
theorem right_distrib (a b c : GF2nPoly f hirr) :
    (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, left_distrib, mul_comm c a, mul_comm c b]

/-- Squaring a sum is additive in characteristic two. -/
theorem add_sq (a b : GF2nPoly f hirr) :
    (a + b) * (a + b) = a * a + b * b := by
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) := by
      rw [right_distrib]
    _ = (a * a + a * b) + (b * a + b * b) := by
      rw [left_distrib, left_distrib]
    _ = (a * a + b * b) + (a * b + b * a) := by
      rw [add_comm (b * a) (b * b)]
      rw [add_pair_swap_quot]
    _ = (a * a + b * b) + (a * b + a * b) := by
      rw [mul_comm b a]
    _ = a * a + b * b := by
      rw [add_self, add_zero]

/-! ## Quotient-coefficient polynomial evaluation -/

/--
Evaluate a low-to-high quotient-coefficient list at a quotient point.

The list `[c₀, c₁, ...]` denotes `c₀ + β * (c₁ + β * (...))`. This
proof-facing evaluator is separate from executable packed polynomial
evaluation; it is used by quotient-field root-count arguments.
-/
def evalCoeffList : List (GF2nPoly f hirr) → GF2nPoly f hirr → GF2nPoly f hirr
  | [], _ => 0
  | c :: cs, β => c + β * evalCoeffList cs β

@[simp] theorem evalCoeffList_nil (β : GF2nPoly f hirr) :
    evalCoeffList ([] : List (GF2nPoly f hirr)) β = 0 :=
  rfl

@[simp] theorem evalCoeffList_cons
    (c : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (β : GF2nPoly f hirr) :
    evalCoeffList (c :: cs) β = c + β * evalCoeffList cs β :=
  rfl

/--
Synthetic quotient coefficients for the divided difference of `cs` at the
base point `α`.

If `P` is represented by `cs`, this list represents the quotient
`(P(T) + P(α)) / (T + α)` in characteristic two. Its length is one less
than the input list, which is the measure used by root-count induction.
-/
def dividedDifferenceCoeffs :
    List (GF2nPoly f hirr) → GF2nPoly f hirr → List (GF2nPoly f hirr)
  | [], _ => []
  | [_], _ => []
  | _ :: c :: cs, α =>
      evalCoeffList (c :: cs) α :: dividedDifferenceCoeffs (c :: cs) α

@[simp] theorem dividedDifferenceCoeffs_nil (α : GF2nPoly f hirr) :
    dividedDifferenceCoeffs ([] : List (GF2nPoly f hirr)) α = [] :=
  rfl

@[simp] theorem dividedDifferenceCoeffs_singleton
    (c : GF2nPoly f hirr) (α : GF2nPoly f hirr) :
    dividedDifferenceCoeffs ([c] : List (GF2nPoly f hirr)) α = [] :=
  rfl

@[simp] theorem dividedDifferenceCoeffs_cons_cons
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α : GF2nPoly f hirr) :
    dividedDifferenceCoeffs (c :: d :: cs) α =
      evalCoeffList (d :: cs) α :: dividedDifferenceCoeffs (d :: cs) α :=
  rfl

/-- The synthetic divided-difference coefficient list has one fewer entry. -/
@[simp] theorem dividedDifferenceCoeffs_length
    (cs : List (GF2nPoly f hirr)) (α : GF2nPoly f hirr) :
    (dividedDifferenceCoeffs cs α).length = cs.length - 1 := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      cases cs with
      | nil =>
          rfl
      | cons d ds =>
          simp [dividedDifferenceCoeffs, ih]

/--
Evaluate the divided difference of a quotient-coefficient polynomial between
the base point `α` and target point `β`.
-/
def dividedDifference
    (cs : List (GF2nPoly f hirr)) (α β : GF2nPoly f hirr) : GF2nPoly f hirr :=
  evalCoeffList (dividedDifferenceCoeffs cs α) β

@[simp] theorem dividedDifference_nil (α β : GF2nPoly f hirr) :
    dividedDifference ([] : List (GF2nPoly f hirr)) α β = 0 :=
  rfl

@[simp] theorem dividedDifference_cons
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α β : GF2nPoly f hirr) :
    dividedDifference (c :: d :: cs) α β =
      evalCoeffList (d :: cs) α + β * dividedDifference (d :: cs) α β :=
  rfl

private theorem add_self_right (a b : GF2nPoly f hirr) :
    a + (b + a) = b := by
  calc
    a + (b + a) = a + (a + b) := by rw [add_comm b a]
    _ = (a + a) + b := by rw [add_assoc]
    _ = b := by rw [add_self, zero_add]

/--
The quotient-coefficient divided difference satisfies
`P(β) + P(α) = (β + α) * DD(P, α, β)`.

This is the characteristic-two orientation of the usual
`P(β) - P(α) = (β - α) * Q(β)` identity, and is the API consumed by
the root-count induction.
-/
theorem evalCoeffList_add_evalCoeffList_eq_add_mul_dividedDifference
    (cs : List (GF2nPoly f hirr)) (α β : GF2nPoly f hirr) :
    evalCoeffList cs β + evalCoeffList cs α =
      (β + α) * dividedDifference cs α β := by
  induction cs with
  | nil =>
      simp [dividedDifference]
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp [dividedDifference, dividedDifferenceCoeffs]
      | cons d ds =>
          let Eβ := evalCoeffList (d :: ds) β
          let Eα := evalCoeffList (d :: ds) α
          let D := dividedDifference (d :: ds) α β
          have htail : Eβ + Eα = (β + α) * D := ih
          have hEβ : Eβ = Eα + (β + α) * D := by
            calc
              Eβ = Eα + (Eβ + Eα) := by
                exact (add_self_right (f := f) (hirr := hirr) Eα Eβ).symm
              _ = Eα + (β + α) * D := by rw [htail]
          calc
            evalCoeffList (c :: d :: ds) β + evalCoeffList (c :: d :: ds) α
                = (c + β * Eβ) + (c + α * Eα) := rfl
            _ = (c + c) + (β * Eβ + α * Eα) := by
                  exact add_pair_swap_quot c (β * Eβ) c (α * Eα)
            _ = β * Eβ + α * Eα := by rw [add_self, zero_add]
            _ = β * (Eα + (β + α) * D) + α * Eα := by rw [hEβ]
            _ = (β * Eα + β * ((β + α) * D)) + α * Eα := by
                  rw [left_distrib]
            _ = (β * Eα + α * Eα) + β * ((β + α) * D) := by
                  rw [add_assoc, add_comm (β * ((β + α) * D)) (α * Eα),
                    ← add_assoc]
            _ = (β + α) * Eα + β * ((β + α) * D) := by
                  rw [← right_distrib β α Eα]
            _ = (β + α) * Eα + (β * (β + α)) * D := by
                  rw [mul_assoc]
            _ = (β + α) * Eα + ((β + α) * β) * D := by
                  rw [mul_comm β (β + α)]
            _ = (β + α) * Eα + (β + α) * (β * D) := by
                  rw [mul_assoc]
            _ = (β + α) * (Eα + β * D) := by
                  rw [left_distrib]
            _ = (β + α) * dividedDifference (c :: d :: ds) α β := rfl

/-- Iterated Frobenius preserves multiplication in the packed quotient. -/
theorem frobeniusIter_mul (a b : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter (a * b) k = frobeniusIter a k * frobeniusIter b k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, frobeniusIter_succ, frobeniusIter_succ]
      let x := frobeniusIter a k
      let y := frobeniusIter b k
      change (x * y) * (x * y) = (x * x) * (y * y)
      calc
        (x * y) * (x * y) = x * (y * (x * y)) := by rw [mul_assoc]
        _ = x * ((y * x) * y) := by rw [mul_assoc y x y]
        _ = x * ((x * y) * y) := by rw [mul_comm y x]
        _ = x * (x * (y * y)) := by rw [mul_assoc x y y]
        _ = (x * x) * (y * y) := by rw [← mul_assoc]

/-- Iterated Frobenius preserves addition in the packed quotient. -/
theorem frobeniusIter_add_eq (a b : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter (a + b) k = frobeniusIter a k + frobeniusIter b k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, frobeniusIter_succ, frobeniusIter_succ, add_sq]

/-- Zero is fixed by every iterated Frobenius. -/
@[simp] theorem frobeniusIter_zero_eq (k : Nat) :
    frobeniusIter (0 : GF2nPoly f hirr) k = 0 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, zero_mul]

/-- Fixed packed quotient elements are closed under addition for a shared
Frobenius iterate. -/
theorem frobeniusIter_fixed_add {a b : GF2nPoly f hirr} {k : Nat}
    (ha : frobeniusIter a k = a) (hb : frobeniusIter b k = b) :
    frobeniusIter (a + b) k = a + b := by
  rw [frobeniusIter_add_eq, ha, hb]

/-- Fixed packed quotient elements are closed under multiplication for a shared
Frobenius iterate. -/
theorem frobeniusIter_fixed_mul {a b : GF2nPoly f hirr} {k : Nat}
    (ha : frobeniusIter a k = a) (hb : frobeniusIter b k = b) :
    frobeniusIter (a * b) k = a * b := by
  rw [frobeniusIter_mul, ha, hb]

/-- The multiplicative identity is a left identity. -/
theorem one_mul (a : GF2nPoly f hirr) :
    (1 : GF2nPoly f hirr) * a = a := by
  apply eq_of_val_eq
  rw [mul_val, one_val]
  have h : ((1 : GF2Poly) % f * a.val) % f = ((1 : GF2Poly) * a.val) % f := by
    have hh := mod_mul_mod_eq_mod_mul 1 a.val f
    rw [val_mod_eq a] at hh
    exact hh
  rw [h, GF2Poly_one_mul, val_mod_eq]

/-- The multiplicative identity is a right identity. -/
theorem mul_one (a : GF2nPoly f hirr) :
    a * (1 : GF2nPoly f hirr) = a := by
  rw [mul_comm, one_mul]

/-- One is fixed by every iterated Frobenius. -/
@[simp] theorem frobeniusIter_one_eq (k : Nat) :
    frobeniusIter (1 : GF2nPoly f hirr) k = 1 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [frobeniusIter_succ, ih, one_mul]

/-- Reducing the zero polynomial gives the quotient zero. -/
@[simp] theorem reducePoly_zero :
    reducePoly (f := f) (hirr := hirr) 0 = 0 := by
  apply eq_of_val_eq
  rw [reducePoly_val_eq_mod, zero_val]
  exact GF2Poly.mod_eq_self_of_reduced 0 f (Or.inl rfl)

/-- Reducing the constant-one monomial gives the quotient one. -/
@[simp] theorem reducePoly_monomial_zero :
    reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial 0) = 1 := by
  rfl

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then every
monomial quotient class is fixed by the same iterate. -/
theorem frobeniusIter_reducePoly_monomial_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) :
    ∀ n : Nat,
      frobeniusIter
          (reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n)) k =
        reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n)
  | 0 => by
      rw [reducePoly_monomial_zero, frobeniusIter_one_eq]
  | n + 1 => by
      have ih := frobeniusIter_reducePoly_monomial_eq_self_of_X_fixed hX n
      have hprod :
          reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial (n + 1)) =
            X (f := f) (hirr := hirr) *
              reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n) := by
        calc
          reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial (n + 1))
              = reducePoly (f := f) (hirr := hirr)
                  (GF2Poly.monomial 1 * GF2Poly.monomial n) := by
                    rw [GF2Poly.monomial_mul_monomial]
                    rw [Nat.add_comm]
          _ = reducePoly (f := f) (hirr := hirr)
                ((reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial 1)).val *
                  (reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n)).val) := by
                    rw [reducePoly_mul_eq]
          _ = X (f := f) (hirr := hirr) *
                reducePoly (f := f) (hirr := hirr) (GF2Poly.monomial n) := rfl
      rw [hprod]
      exact frobeniusIter_fixed_mul hX ih

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then any
Boolean coefficient list starting at an arbitrary monomial degree is fixed. -/
theorem frobeniusIter_reducePoly_ofBoolListFrom_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) :
    ∀ (start : Nat) (bs : List Bool),
      frobeniusIter
          (reducePoly (f := f) (hirr := hirr)
            (GF2Poly.ofBoolListFrom start bs)) k =
        reducePoly (f := f) (hirr := hirr)
          (GF2Poly.ofBoolListFrom start bs)
  | start, [] => by
      simp [GF2Poly.ofBoolListFrom]
  | start, b :: bs => by
      have htail :=
        frobeniusIter_reducePoly_ofBoolListFrom_eq_self_of_X_fixed hX (start + 1) bs
      have hterm :
          frobeniusIter
              (reducePoly (f := f) (hirr := hirr)
                (if b then GF2Poly.monomial start else 0)) k =
            reducePoly (f := f) (hirr := hirr)
              (if b then GF2Poly.monomial start else 0) := by
        cases b
        · simp
        · exact frobeniusIter_reducePoly_monomial_eq_self_of_X_fixed
            (f := f) (hirr := hirr) hX start
      have hsum :
          reducePoly (f := f) (hirr := hirr)
              ((if b then GF2Poly.monomial start else 0) +
                GF2Poly.ofBoolListFrom (start + 1) bs) =
            reducePoly (f := f) (hirr := hirr)
                (if b then GF2Poly.monomial start else 0) +
              reducePoly (f := f) (hirr := hirr)
                (GF2Poly.ofBoolListFrom (start + 1) bs) := by
        rw [reducePoly_add_eq]
        rfl
      change
        frobeniusIter
            (reducePoly (f := f) (hirr := hirr)
              ((if b then GF2Poly.monomial start else 0) +
                GF2Poly.ofBoolListFrom (start + 1) bs)) k =
          reducePoly (f := f) (hirr := hirr)
            ((if b then GF2Poly.monomial start else 0) +
              GF2Poly.ofBoolListFrom (start + 1) bs)
      rw [hsum]
      exact frobeniusIter_fixed_add hterm htail

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then every
Boolean coefficient expression generated from `X` is fixed. -/
theorem frobeniusIter_boolListExpression_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) (bs : List Bool) :
    frobeniusIter (boolListExpression (f := f) (hirr := hirr) bs) k =
      boolListExpression (f := f) (hirr := hirr) bs := by
  unfold boolListExpression GF2Poly.ofBoolList
  exact frobeniusIter_reducePoly_ofBoolListFrom_eq_self_of_X_fixed
    (f := f) (hirr := hirr) hX 0 bs

/-- If the quotient class of `X` is fixed by a Frobenius iterate, then every
packed quotient-field element is fixed by the same iterate. -/
theorem frobeniusIter_eq_self_of_X_fixed {k : Nat}
    (hX : frobeniusIter (X (f := f) (hirr := hirr)) k =
      X (f := f) (hirr := hirr)) (a : GF2nPoly f hirr) :
    frobeniusIter a k = a := by
  rcases exists_boolListExpression (f := f) (hirr := hirr) a with
    ⟨bs, _hlen, hbs⟩
  rw [← hbs]
  exact frobeniusIter_boolListExpression_eq_self_of_X_fixed
    (f := f) (hirr := hirr) hX bs

/-- The inverse cancels on the left for nonzero quotient elements. -/
theorem inv_mul_cancel (a : GF2nPoly f hirr) (ha : a ≠ 0) :
    a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel a ha

/-- The product of two nonzero packed quotient elements is nonzero. -/
theorem mul_ne_zero_of_ne_zero {a b : GF2nPoly f hirr}
    (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hab
  apply hb
  calc b
      = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel a ha]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = a⁻¹ * 0 := by rw [hab]
    _ = 0 := mul_zero _

/-- Left multiplication by a nonzero packed quotient element is injective. -/
theorem mul_left_injective {a : GF2nPoly f hirr} (ha : a ≠ 0)
    {b₁ b₂ : GF2nPoly f hirr} (heq : a * b₁ = a * b₂) :
    b₁ = b₂ := by
  have h := congrArg (fun x => a⁻¹ * x) heq
  dsimp at h
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel a ha, one_mul, one_mul] at h
  exact h

/-- Two `Nodup` lists with the same membership predicate are permutations. -/
private theorem perm_of_nodup_mem_iff
    {α : Type} :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → List.Perm xs ys
  | [], ys, _, _, hmem => by
      cases ys with
      | nil => exact .nil
      | cons y _ =>
          have hy : y ∈ ([] : List α) := (hmem y).mpr List.mem_cons_self
          exact absurd hy List.not_mem_nil
  | x :: xs', ys, hxs, hys, hmem => by
      have hxs_inv := List.nodup_cons.mp hxs
      have hx_not_in_xs' : x ∉ xs' := hxs_inv.1
      have hxs' : xs'.Nodup := hxs_inv.2
      have hx_mem : x ∈ ys := (hmem x).mp List.mem_cons_self
      obtain ⟨ys₁, ys₂, hys_eq⟩ := List.append_of_mem hx_mem
      subst hys_eq
      have hys_perm : List.Perm (ys₁ ++ x :: ys₂) (x :: (ys₁ ++ ys₂)) :=
        List.perm_middle
      have h_inner_nodup : (x :: (ys₁ ++ ys₂)).Nodup := hys_perm.nodup hys
      have h_inner_inv := List.nodup_cons.mp h_inner_nodup
      have hx_not_inner : x ∉ ys₁ ++ ys₂ := h_inner_inv.1
      have h_concat_nodup : (ys₁ ++ ys₂).Nodup := h_inner_inv.2
      have hmem' : ∀ a, a ∈ xs' ↔ a ∈ ys₁ ++ ys₂ := by
        intro a
        constructor
        · intro ha
          have ha_in_xs : a ∈ x :: xs' := List.mem_cons.mpr (Or.inr ha)
          have ha_in_ys : a ∈ ys₁ ++ x :: ys₂ := (hmem a).mp ha_in_xs
          have ha_in_split : a ∈ x :: (ys₁ ++ ys₂) := hys_perm.mem_iff.mp ha_in_ys
          rcases List.mem_cons.mp ha_in_split with hax | h
          · exact absurd (hax ▸ ha) hx_not_in_xs'
          · exact h
        · intro ha
          have ha_in_split : a ∈ x :: (ys₁ ++ ys₂) := List.mem_cons.mpr (Or.inr ha)
          have ha_in_ys : a ∈ ys₁ ++ x :: ys₂ := hys_perm.mem_iff.mpr ha_in_split
          have ha_in_xs : a ∈ x :: xs' := (hmem a).mpr ha_in_ys
          rcases List.mem_cons.mp ha_in_xs with hax | h
          · exact absurd (hax ▸ ha) hx_not_inner
          · exact h
      have ih_perm := perm_of_nodup_mem_iff hxs' h_concat_nodup hmem'
      exact (ih_perm.cons x).trans hys_perm.symm

/--
The highest coefficient in a low-to-high quotient coefficient list is nonzero.

This predicate gives the syntactic degree bound consumed by the root-count
theorem: a list satisfying it represents a polynomial of degree strictly below
the list length, with actual degree exactly `length - 1`.
-/
def coeffListTopNonzero : List (GF2nPoly f hirr) → Prop
  | cs => ∃ c, cs.getLast? = some c ∧ c ≠ 0

private theorem coeffListTopNonzero_tail_of_cons_cons
    {c d : GF2nPoly f hirr} {cs : List (GF2nPoly f hirr)}
    (h : coeffListTopNonzero (c :: d :: cs)) :
    coeffListTopNonzero (d :: cs) := by
  simpa [coeffListTopNonzero] using h

private theorem dividedDifferenceCoeffs_getLast?
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α : GF2nPoly f hirr) :
    (dividedDifferenceCoeffs (c :: d :: cs) α).getLast? =
      (d :: cs).getLast? := by
  induction cs generalizing c d with
  | nil =>
      simp [dividedDifferenceCoeffs, evalCoeffList]
  | cons e es ih =>
      cases es with
      | nil =>
          simp [dividedDifferenceCoeffs, evalCoeffList]
      | cons g gs =>
          simpa [dividedDifferenceCoeffs] using ih e g

private theorem coeffListTopNonzero_dividedDifferenceCoeffs
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    (α : GF2nPoly f hirr)
    (h : coeffListTopNonzero (d :: cs)) :
    coeffListTopNonzero (dividedDifferenceCoeffs (c :: d :: cs) α) := by
  rcases h with ⟨top, hlast, htop⟩
  refine ⟨top, ?_, htop⟩
  rw [dividedDifferenceCoeffs_getLast?]
  exact hlast

/-- Roots of a quotient-coefficient polynomial inside the canonical quotient
enumeration. -/
def rootsOfCoeffList (cs : List (GF2nPoly f hirr)) : List (GF2nPoly f hirr) :=
  (elements (f := f) (hirr := hirr)).filter
    (fun β => decide (evalCoeffList cs β = 0))

@[simp] theorem mem_rootsOfCoeffList
    (cs : List (GF2nPoly f hirr)) (β : GF2nPoly f hirr) :
    β ∈ rootsOfCoeffList (f := f) (hirr := hirr) cs ↔
      evalCoeffList cs β = 0 := by
  simp [rootsOfCoeffList, mem_elements β]

/-- The quotient-coefficient root list has no duplicate roots. -/
theorem rootsOfCoeffList_nodup (cs : List (GF2nPoly f hirr)) :
    (rootsOfCoeffList (f := f) (hirr := hirr) cs).Nodup := by
  unfold rootsOfCoeffList
  exact (elements_nodup (f := f) (hirr := hirr)).filter _

private theorem length_filter_le (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx]
        simp only [List.length_cons]
        exact Nat.succ_le_succ (length_filter_le p xs)
      · rw [List.filter_cons_of_neg hx]
        exact Nat.le_trans (length_filter_le p xs) (Nat.le_succ xs.length)

private theorem length_le_of_nodup_subset
    {α : Type} [DecidableEq α] {xs ys : List α}
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hsub : ∀ a, a ∈ xs → a ∈ ys) :
    xs.length ≤ ys.length := by
  let zs := ys.filter (fun a => decide (a ∈ xs))
  have hzs_nodup : zs.Nodup := hys.filter _
  have hmem : ∀ a, a ∈ xs ↔ a ∈ zs := by
    intro a
    constructor
    · intro ha
      exact List.mem_filter.mpr ⟨hsub a ha, decide_eq_true ha⟩
    · intro ha
      exact of_decide_eq_true (List.mem_filter.mp ha).2
  have hperm : List.Perm xs zs :=
    perm_of_nodup_mem_iff hxs hzs_nodup hmem
  have hlen_eq : xs.length = zs.length := hperm.length_eq
  calc
    xs.length = zs.length := hlen_eq
    _ ≤ ys.length := length_filter_le (fun a => decide (a ∈ xs)) ys

private theorem add_ne_zero_of_ne {a b : GF2nPoly f hirr} (h : a ≠ b) :
    a + b ≠ 0 := by
  intro hab
  apply h
  calc
    a = a + 0 := (add_zero a).symm
    _ = a + (a + b) := by rw [hab]
    _ = (a + a) + b := by rw [add_assoc]
    _ = b := by rw [add_self, zero_add]

private theorem roots_without_base_subset_dividedDifference_roots
    (c d : GF2nPoly f hirr) (cs : List (GF2nPoly f hirr))
    {α β : GF2nPoly f hirr}
    (hα : α ∈ rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs))
    (hβ : β ∈ rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs))
    (hβα : β ≠ α) :
    β ∈ rootsOfCoeffList (f := f) (hirr := hirr)
      (dividedDifferenceCoeffs (c :: d :: cs) α) := by
  have hα_eval :
      evalCoeffList (c :: d :: cs) α = 0 :=
    (mem_rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs) α).mp hα
  have hβ_eval :
      evalCoeffList (c :: d :: cs) β = 0 :=
    (mem_rootsOfCoeffList (f := f) (hirr := hirr) (c :: d :: cs) β).mp hβ
  have hident :=
    evalCoeffList_add_evalCoeffList_eq_add_mul_dividedDifference
      (f := f) (hirr := hirr) (c :: d :: cs) α β
  rw [hβ_eval, hα_eval, zero_add] at hident
  have hadd_ne : β + α ≠ 0 :=
    add_ne_zero_of_ne (f := f) (hirr := hirr) hβα
  have hdd_zero : dividedDifference (c :: d :: cs) α β = 0 := by
    apply mul_left_injective hadd_ne
    rw [mul_zero]
    exact hident.symm
  exact (mem_rootsOfCoeffList
    (f := f) (hirr := hirr)
    (dividedDifferenceCoeffs (c :: d :: cs) α) β).mpr hdd_zero

/--
A nonzero quotient-coefficient polynomial has at most its degree many roots in
the duplicate-free packed quotient enumeration.

The coefficient list is low-to-high, and `coeffListTopNonzero cs` says the
highest listed coefficient is nonzero, so the degree bound is `cs.length - 1`.
-/
theorem rootsOfCoeffList_length_le_degree
    (cs : List (GF2nPoly f hirr))
    (htop : coeffListTopNonzero (f := f) (hirr := hirr) cs) :
    (rootsOfCoeffList (f := f) (hirr := hirr) cs).length ≤ cs.length - 1 := by
  have hmain :
      ∀ n, ∀ cs : List (GF2nPoly f hirr), cs.length = n →
        coeffListTopNonzero (f := f) (hirr := hirr) cs →
        (rootsOfCoeffList (f := f) (hirr := hirr) cs).length ≤ cs.length - 1 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro cs hlen htop
        cases cs with
        | nil =>
            rcases htop with ⟨top, hlast, _htop_ne⟩
            simp at hlast
        | cons c cs =>
            cases cs with
            | nil =>
                rcases htop with ⟨top, hlast, htop_ne⟩
                simp at hlast
                subst top
                unfold rootsOfCoeffList
                simp [evalCoeffList, htop_ne]
            | cons d ds =>
                let P := c :: d :: ds
                let rootsP := rootsOfCoeffList (f := f) (hirr := hirr) P
                by_cases hnil : rootsP = []
                · rw [show rootsOfCoeffList (f := f) (hirr := hirr) P = [] from hnil]
                  simp
                · cases hrootsP : rootsP with
                  | nil =>
                      exact False.elim (hnil hrootsP)
                  | cons α rest =>
                      have hα : α ∈ rootsOfCoeffList (f := f) (hirr := hirr) P := by
                        show α ∈ rootsP
                        rw [hrootsP]
                        exact List.mem_cons_self
                      let rootsWithoutα :=
                        rootsP.filter (fun β => decide (β ≠ α))
                      let ddCoeffs := dividedDifferenceCoeffs P α
                      let rootsDD :=
                        rootsOfCoeffList (f := f) (hirr := hirr) ddCoeffs
                      have hrootsP_nodup : rootsP.Nodup := by
                        dsimp [rootsP]
                        exact rootsOfCoeffList_nodup (f := f) (hirr := hirr) P
                      have hα_filter_len :
                          rootsWithoutα.length = rootsP.length - 1 := by
                        exact length_filter_ne_eq_pred_of_mem_nodup
                          (z := α) hα hrootsP_nodup
                      have hdd_top : coeffListTopNonzero
                          (f := f) (hirr := hirr) ddCoeffs := by
                        dsimp [ddCoeffs, P]
                        exact coeffListTopNonzero_dividedDifferenceCoeffs
                          (f := f) (hirr := hirr) c d ds α
                          (coeffListTopNonzero_tail_of_cons_cons
                            (f := f) (hirr := hirr) htop)
                      have hsub :
                          ∀ β, β ∈ rootsWithoutα → β ∈ rootsDD := by
                        intro β hβ
                        have hβ_rootsP : β ∈ rootsP :=
                          (List.mem_filter.mp hβ).1
                        have hβ_ne : β ≠ α :=
                          of_decide_eq_true (List.mem_filter.mp hβ).2
                        dsimp [rootsDD, ddCoeffs, P]
                        exact roots_without_base_subset_dividedDifference_roots
                          (f := f) (hirr := hirr) c d ds hα hβ_rootsP hβ_ne
                      have hwithout_le_dd :
                          rootsWithoutα.length ≤ rootsDD.length := by
                        apply length_le_of_nodup_subset
                        · exact hrootsP_nodup.filter _
                        · dsimp [rootsDD]
                          exact rootsOfCoeffList_nodup
                            (f := f) (hirr := hirr) ddCoeffs
                        · exact hsub
                      have hdd_len : ddCoeffs.length = P.length - 1 := by
                        dsimp [ddCoeffs, P]
                        exact dividedDifferenceCoeffs_length
                          (f := f) (hirr := hirr) (c :: d :: ds) α
                      have hP_len : P.length = n := by
                        dsimp [P]
                        exact hlen
                      have hP_len_two : 2 ≤ P.length := by
                        dsimp [P]
                        simp
                      have hdd_lt : ddCoeffs.length < n := by
                        omega
                      have hdd_bound :
                          rootsDD.length ≤ ddCoeffs.length - 1 := by
                        dsimp [rootsDD]
                        exact ih ddCoeffs.length hdd_lt ddCoeffs rfl hdd_top
                      have hrootsP_pos : 0 < rootsP.length := by
                        rw [hrootsP]
                        simp
                      have hwithout_bound :
                          rootsWithoutα.length ≤ P.length - 2 := by
                        calc
                          rootsWithoutα.length ≤ rootsDD.length := hwithout_le_dd
                          _ ≤ ddCoeffs.length - 1 := hdd_bound
                          _ = P.length - 2 := by omega
                      have hrootsP_eq :
                          rootsP.length = rootsWithoutα.length + 1 := by
                        omega
                      have hrootsP_bound : rootsP.length ≤ P.length - 1 := by
                        omega
                      exact hrootsP_bound
  exact hmain cs.length cs rfl htop

/--
Direct root-count bound for the canonical `elements` filter form used by
callers.
-/
theorem evalCoeffList_rootsIn_elements_length_le_degree
    (cs : List (GF2nPoly f hirr))
    (htop : coeffListTopNonzero (f := f) (hirr := hirr) cs) :
    ((elements (f := f) (hirr := hirr)).filter
      (fun β => decide (evalCoeffList cs β = 0))).length ≤ cs.length - 1 :=
  rootsOfCoeffList_length_le_degree (f := f) (hirr := hirr) cs htop

/-- Multiplication by a nonzero packed quotient element permutes the nonzero
enumeration. The list of nonzero elements multiplied on the left by `a` is a
permutation of the original nonzero list. -/
theorem nonzeroElements_map_mul_left_perm
    {a : GF2nPoly f hirr} (ha : a ≠ 0) :
    List.Perm
      ((nonzeroElements (f := f) (hirr := hirr)).map (fun b => a * b))
      (nonzeroElements (f := f) (hirr := hirr)) := by
  let L : List (GF2nPoly f hirr) := nonzeroElements (f := f) (hirr := hirr)
  have hL_nodup : L.Nodup :=
    nonzeroElements_nodup (f := f) (hirr := hirr)
  have hmap_inj :
      ∀ b₁, b₁ ∈ L → ∀ b₂, b₂ ∈ L →
        (fun b => a * b) b₁ = (fun b => a * b) b₂ → b₁ = b₂ := by
    intro b₁ _ b₂ _ heq
    exact mul_left_injective ha heq
  have hmap_nodup : (L.map (fun b => a * b)).Nodup :=
    nodup_map_of_injective hL_nodup hmap_inj
  have hmem_iff : ∀ c, c ∈ L.map (fun b => a * b) ↔ c ∈ L := by
    intro c
    constructor
    · intro hc
      rcases List.mem_map.mp hc with ⟨b, hb_mem, hbc⟩
      have hb_ne : b ≠ 0 := (mem_nonzeroElements b).mp hb_mem
      have hab_ne : a * b ≠ 0 := mul_ne_zero_of_ne_zero ha hb_ne
      have hc_ne : c ≠ 0 := hbc ▸ hab_ne
      exact (mem_nonzeroElements c).mpr hc_ne
    · intro hc
      have hc_ne : c ≠ 0 := (mem_nonzeroElements c).mp hc
      refine List.mem_map.mpr ⟨a⁻¹ * c, ?_, ?_⟩
      · apply (mem_nonzeroElements _).mpr
        intro hac
        apply hc_ne
        calc c
            = 1 * c := (one_mul c).symm
          _ = (a * a⁻¹) * c := by rw [mul_inv_cancel a ha]
          _ = a * (a⁻¹ * c) := mul_assoc _ _ _
          _ = a * 0 := congrArg (a * ·) hac
          _ = 0 := mul_zero _
      · rw [← mul_assoc, mul_inv_cancel a ha, one_mul]
  exact perm_of_nodup_mem_iff hmap_nodup hL_nodup hmem_iff

/-- Linear natural powers in the packed quotient field. This proof-facing
variant has simple recursion equations; executable exponentiation remains the
`Pow` instance above. -/
def linearPow (a : GF2nPoly f hirr) : Nat → GF2nPoly f hirr
  | 0 => 1
  | n + 1 => linearPow a n * a

@[simp] theorem linearPow_zero (a : GF2nPoly f hirr) :
    linearPow a 0 = 1 :=
  rfl

@[simp] theorem linearPow_succ (a : GF2nPoly f hirr) (n : Nat) :
    linearPow a (n + 1) = linearPow a n * a :=
  rfl

/-- Linear quotient powers turn addition of exponents into multiplication. -/
theorem linearPow_add (a : GF2nPoly f hirr) (m n : Nat) :
    linearPow a (m + n) = linearPow a m * linearPow a n := by
  induction n with
  | zero =>
      rw [Nat.add_zero, linearPow_zero, mul_one]
  | succ n ih =>
      calc linearPow a (m + (n + 1))
          = linearPow a ((m + n) + 1) := by rw [Nat.add_succ]
        _ = linearPow a (m + n) * a := rfl
        _ = (linearPow a m * linearPow a n) * a := by rw [ih]
        _ = linearPow a m * (linearPow a n * a) := by rw [mul_assoc]
        _ = linearPow a m * linearPow a (n + 1) := rfl

/-- Linear powers of a product factor in the commutative packed quotient. -/
theorem linearPow_mul (a b : GF2nPoly f hirr) (n : Nat) :
    linearPow (a * b) n = linearPow a n * linearPow b n := by
  induction n with
  | zero =>
      rw [linearPow_zero, linearPow_zero, linearPow_zero, one_mul]
  | succ n ih =>
      calc linearPow (a * b) (n + 1)
          = linearPow (a * b) n * (a * b) := rfl
        _ = (linearPow a n * linearPow b n) * (a * b) := by rw [ih]
        _ = linearPow a n * (linearPow b n * (a * b)) := by rw [mul_assoc]
        _ = linearPow a n * ((linearPow b n * a) * b) := by
              rw [mul_assoc (linearPow b n) a b]
        _ = linearPow a n * ((a * linearPow b n) * b) := by
              rw [mul_comm (linearPow b n) a]
        _ = linearPow a n * (a * (linearPow b n * b)) := by
              rw [mul_assoc a (linearPow b n) b]
        _ = (linearPow a n * a) * (linearPow b n * b) := by
              rw [← mul_assoc]
        _ = linearPow a (n + 1) * linearPow b (n + 1) := rfl

/-- Iterated Frobenius squaring agrees with linear powering by `2^k`. -/
theorem frobeniusIter_eq_linearPow_two_pow (a : GF2nPoly f hirr) (k : Nat) :
    frobeniusIter a k = linearPow a (2 ^ k) := by
  induction k with
  | zero =>
      change a = linearPow a 1
      rw [show (1 : Nat) = 0 + 1 from rfl, linearPow_succ, linearPow_zero, one_mul]
  | succ k ih =>
      calc frobeniusIter a (k + 1)
          = frobeniusIter a k * frobeniusIter a k := rfl
        _ = linearPow a (2 ^ k) * linearPow a (2 ^ k) := by rw [ih]
        _ = linearPow a (2 ^ k + 2 ^ k) := by
              rw [linearPow_add]
        _ = linearPow a (2 ^ (k + 1)) := by
              rw [Nat.pow_succ]
              rw [show 2 ^ k + 2 ^ k = 2 ^ k * 2 by omega]

/-- The quotient identity is not zero under a positive-degree modulus. -/
theorem one_ne_zero (hf_pos : 0 < f.degree) :
    (1 : GF2nPoly f hirr) ≠ 0 := by
  intro h
  have hval := congrArg GF2nPoly.val h
  have hone_val : (1 : GF2nPoly f hirr).val = (1 : GF2Poly) := by
    rw [one_val]
    exact GF2Poly.mod_eq_self_of_reduced (1 : GF2Poly) f
      (Or.inr (by
        change (GF2Poly.monomial 0).degree < f.degree
        rw [show (GF2Poly.monomial 0).degree = 0 from by
          exact GF2Poly.degree_eq_of_degree?_eq_some (GF2Poly.degree?_monomial 0)]
        exact hf_pos))
  rw [hone_val, zero_val] at hval
  have hcoeff := congrArg (fun p : GF2Poly => p.coeff 0) hval
  change (GF2Poly.monomial 0).coeff 0 = (0 : GF2Poly).coeff 0 at hcoeff
  rw [GF2Poly.coeff_monomial_self, GF2Poly.coeff_zero] at hcoeff
  contradiction

/-- Coefficients for the characteristic-two polynomial `T^(2^k) + T`.

For `0 < k`, the list is low-to-high with nonzero coefficients exactly at
degrees `1` and `2^k`. The `k = 0` list intentionally evaluates to zero,
matching `T + T`; root-count callers use the positive-`k` theorem below. -/
def frobeniusFixedCoeffList (k : Nat) : List (GF2nPoly f hirr) :=
  if k = 0 then
    [0]
  else
    0 :: 1 :: (List.replicate (2 ^ k - 2) (0 : GF2nPoly f hirr) ++ [1])

private theorem evalCoeffList_replicate_zero_append_one
    (β : GF2nPoly f hirr) (n : Nat) :
    evalCoeffList (List.replicate n (0 : GF2nPoly f hirr) ++ [1]) β =
      linearPow β n := by
  induction n with
  | zero =>
      simp [evalCoeffList, linearPow_zero]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, evalCoeffList_cons]
      rw [ih, zero_add, linearPow_succ, mul_comm]

private theorem evalCoeffList_frobeniusFixedCoeffList_of_pos
    (β : GF2nPoly f hirr) {k : Nat} (hk : 0 < k) :
    evalCoeffList (frobeniusFixedCoeffList (f := f) (hirr := hirr) k) β =
      frobeniusIter β k + β := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have htwo : 2 ≤ 2 ^ k := by
    cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 hk)
    | succ k =>
        rw [Nat.pow_succ]
        have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
        omega
  rw [frobeniusFixedCoeffList, if_neg hk_ne]
  simp only [evalCoeffList_cons]
  rw [zero_add, evalCoeffList_replicate_zero_append_one,
    frobeniusIter_eq_linearPow_two_pow]
  have hpow_two : linearPow β 2 = β * β := by
    rw [show (2 : Nat) = 1 + 1 from rfl, linearPow_succ,
      linearPow_succ, linearPow_zero, one_mul]
  calc
    β * (1 + β * linearPow β (2 ^ k - 2))
        = β * 1 + β * (β * linearPow β (2 ^ k - 2)) := by
            rw [left_distrib]
    _ = β + β * (β * linearPow β (2 ^ k - 2)) := by rw [mul_one]
    _ = β + (β * β) * linearPow β (2 ^ k - 2) := by rw [mul_assoc]
    _ = β + linearPow β 2 * linearPow β (2 ^ k - 2) := by rw [hpow_two]
    _ = β + linearPow β (2 + (2 ^ k - 2)) := by
            have hadd :=
              (linearPow_add (f := f) (hirr := hirr) β 2 (2 ^ k - 2)).symm
            rw [hadd]
    _ = β + linearPow β (2 ^ k) := by
            have hidx : 2 + (2 ^ k - 2) = 2 ^ k := by omega
            rw [hidx]
    _ = linearPow β (2 ^ k) + β := by rw [add_comm]

private theorem getLast?_append_singleton {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).getLast? = some x := by
  induction xs with
  | nil =>
      simp
  | cons y ys ih =>
      cases ys with
      | nil => simp
      | cons z zs =>
          simpa using ih

private theorem coeffListTopNonzero_frobeniusFixedCoeffList_of_pos
    (hf_pos : 0 < f.degree) {k : Nat} (hk : 0 < k) :
    coeffListTopNonzero
      (f := f) (hirr := hirr)
      (frobeniusFixedCoeffList (f := f) (hirr := hirr) k) := by
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  refine ⟨1, ?_, one_ne_zero (f := f) (hirr := hirr) hf_pos⟩
  rw [frobeniusFixedCoeffList, if_neg hk_ne]
  change
    (((0 : GF2nPoly f hirr) :: 1 ::
        List.replicate (2 ^ k - 2) (0 : GF2nPoly f hirr)) ++ [1]).getLast? =
      some 1
  exact getLast?_append_singleton
    ((0 : GF2nPoly f hirr) :: 1 ::
      List.replicate (2 ^ k - 2) (0 : GF2nPoly f hirr)) 1

private theorem add_eq_zero_iff_eq (a b : GF2nPoly f hirr) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = a + 0 := (add_zero a).symm
      _ = a + (a + b) := by rw [h]
      _ = (a + a) + b := by rw [add_assoc]
      _ = b := by rw [add_self, zero_add]
  · intro h
    rw [h, add_self]

/--
At most `2^k` packed quotient elements are fixed by the `k`-fold Frobenius
when `0 < k`.

This is the root-count specialization for `T^(2^k) + T`, stated directly
against the canonical duplicate-free `elements` enumeration so downstream
Rabin arguments can combine it with `elements_card`.
-/
theorem frobeniusIter_fixed_elements_length_le_two_pow
    (hf_pos : 0 < f.degree) {k : Nat} (hk : 0 < k) :
    ((elements (f := f) (hirr := hirr)).filter
      (fun β => decide (frobeniusIter β k = β))).length ≤ 2 ^ k := by
  let cs := frobeniusFixedCoeffList (f := f) (hirr := hirr) k
  have htop :
      coeffListTopNonzero (f := f) (hirr := hirr) cs :=
    coeffListTopNonzero_frobeniusFixedCoeffList_of_pos
      (f := f) (hirr := hirr) hf_pos hk
  have hroot :=
    evalCoeffList_rootsIn_elements_length_le_degree
      (f := f) (hirr := hirr) cs htop
  have hlen : cs.length - 1 = 2 ^ k := by
    have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
    have htwo : 2 ≤ 2 ^ k := by
      cases k with
      | zero => exact False.elim (Nat.lt_irrefl 0 hk)
      | succ k =>
          rw [Nat.pow_succ]
          have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
          omega
    dsimp [cs]
    rw [frobeniusFixedCoeffList, if_neg hk_ne]
    simp
    omega
  have hfilter :
      (elements (f := f) (hirr := hirr)).filter
          (fun β => decide (frobeniusIter β k = β)) =
        (elements (f := f) (hirr := hirr)).filter
          (fun β => decide (evalCoeffList cs β = 0)) := by
    apply List.filter_congr
    intro β _hβ
    have heval :
        evalCoeffList cs β = frobeniusIter β k + β := by
      dsimp [cs]
      exact evalCoeffList_frobeniusFixedCoeffList_of_pos
        (f := f) (hirr := hirr) β hk
    by_cases hfixed : frobeniusIter β k = β
    · have hzero : evalCoeffList cs β = 0 := by
        rw [heval, hfixed, add_self]
      rw [decide_eq_true hfixed, decide_eq_true hzero]
    · have hnot_zero : evalCoeffList cs β ≠ 0 := by
        intro hzero
        apply hfixed
        exact (add_eq_zero_iff_eq
          (f := f) (hirr := hirr) (frobeniusIter β k) β).mp
          (by rw [← heval]; exact hzero)
      rw [decide_eq_false hfixed, decide_eq_false hnot_zero]
  rw [hfilter]
  exact hlen ▸ hroot

/--
If every packed quotient element is fixed by a positive Frobenius iterate,
then the iterate is at least the modulus degree.

This is the downstream cardinality form of the fixed-root bound: otherwise
all `2^f.degree` quotient elements would be roots of `T^(2^k) + T`, whose
packed root-count bound is only `2^k`.
-/
theorem frobeniusIter_universal_fixed_degree_le
    (hf_pos : 0 < f.degree) {k : Nat} (hk : 0 < k)
    (hfixed : ∀ β : GF2nPoly f hirr, frobeniusIter β k = β) :
    f.degree ≤ k := by
  have hfilter_eq :
      (elements (f := f) (hirr := hirr)).filter
          (fun β => decide (frobeniusIter β k = β)) =
        elements (f := f) (hirr := hirr) := by
    apply (List.filter_eq_self).mpr
    intro β _hβ
    exact decide_eq_true (hfixed β)
  have hbound :=
    frobeniusIter_fixed_elements_length_le_two_pow
      (f := f) (hirr := hirr) hf_pos hk
  rw [hfilter_eq, elements_card] at hbound
  by_cases hle : f.degree ≤ k
  · exact hle
  · have hlt : k < f.degree := Nat.lt_of_not_ge hle
    have hpow_lt : 2 ^ k < 2 ^ f.degree :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    exact False.elim (Nat.not_lt_of_ge hbound hpow_lt)

/--
For a positive iterate below the packed quotient degree, not every quotient
element can be fixed by Frobenius.

This contrapositive is the form Rabin soundness uses after reducing an
exponent modulo the irreducible factor degree.
-/
theorem not_forall_frobeniusIter_eq_self_of_pos_lt_degree
    (hf_pos : 0 < f.degree) {r : Nat} (hr_pos : 0 < r)
    (hr_lt : r < f.degree) :
    ¬ ∀ β : GF2nPoly f hirr, frobeniusIter β r = β := by
  intro hfixed
  have hdeg_le :
      f.degree ≤ r :=
    frobeniusIter_universal_fixed_degree_le
      (f := f) (hirr := hirr) hf_pos hr_pos hfixed
  exact Nat.not_lt_of_ge hdeg_le hr_lt

/-- A positive iterate below the quotient degree has some non-fixed element. -/
theorem exists_frobeniusIter_ne_self_of_pos_lt_degree
    (hf_pos : 0 < f.degree) {r : Nat} (hr_pos : 0 < r)
    (hr_lt : r < f.degree) :
    ∃ β : GF2nPoly f hirr, frobeniusIter β r ≠ β := by
  classical
  by_cases h : ∃ β : GF2nPoly f hirr, frobeniusIter β r ≠ β
  · exact h
  · exact False.elim
      (not_forall_frobeniusIter_eq_self_of_pos_lt_degree
        (f := f) (hirr := hirr) hf_pos hr_pos hr_lt
        (fun β => by
          by_cases hβ : frobeniusIter β r = β
          · exact hβ
          · exact False.elim (h ⟨β, hβ⟩)))

/--
For a positive iterate below the quotient degree, the quotient class of `X`
cannot be fixed by Frobenius.

If `X` were fixed, the existing quotient-generation theorem would make every
element fixed, contradicting the fixed-point cardinality bound.
-/
theorem frobeniusIter_X_ne_self_of_pos_lt_degree
    (hf_pos : 0 < f.degree) {r : Nat} (hr_pos : 0 < r)
    (hr_lt : r < f.degree) :
    frobeniusIter (X (f := f) (hirr := hirr)) r ≠
      X (f := f) (hirr := hirr) := by
  intro hX
  exact not_forall_frobeniusIter_eq_self_of_pos_lt_degree
    (f := f) (hirr := hirr) hf_pos hr_pos hr_lt
    (frobeniusIter_eq_self_of_X_fixed (f := f) (hirr := hirr) hX)

/-- Product of a list of packed quotient elements (right fold). -/
def listProd (xs : List (GF2nPoly f hirr)) : GF2nPoly f hirr :=
  xs.foldr (· * ·) 1

@[simp] theorem listProd_nil :
    listProd ([] : List (GF2nPoly f hirr)) = 1 :=
  rfl

@[simp] theorem listProd_cons (x : GF2nPoly f hirr)
    (xs : List (GF2nPoly f hirr)) :
    listProd (x :: xs) = x * listProd xs :=
  rfl

/-- The list product is invariant under `List.Perm`. -/
theorem listProd_perm {xs ys : List (GF2nPoly f hirr)}
    (h : List.Perm xs ys) :
    listProd xs = listProd ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
      simp only [listProd_cons]
      rw [ih]
  | swap x y zs =>
      simp only [listProd_cons]
      rw [← mul_assoc, ← mul_assoc, mul_comm x y]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Mapping a list by left-multiplication factors out as a linear power of the
multiplier times the original list product. -/
theorem listProd_map_mul_left (a : GF2nPoly f hirr)
    (xs : List (GF2nPoly f hirr)) :
    listProd (xs.map (fun b => a * b)) = linearPow a xs.length * listProd xs := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.length_nil, listProd_nil, linearPow_zero, one_mul]
  | cons x xs ih =>
      calc listProd ((x :: xs).map (fun b => a * b))
          = (a * x) * listProd (xs.map (fun b => a * b)) := by
              simp only [List.map_cons, listProd_cons]
        _ = (a * x) * (linearPow a xs.length * listProd xs) := by rw [ih]
        _ = a * (x * (linearPow a xs.length * listProd xs)) := by rw [mul_assoc]
        _ = a * ((x * linearPow a xs.length) * listProd xs) := by
              rw [mul_assoc x (linearPow a xs.length) (listProd xs)]
        _ = a * ((linearPow a xs.length * x) * listProd xs) := by
              rw [mul_comm x (linearPow a xs.length)]
        _ = a * (linearPow a xs.length * (x * listProd xs)) := by
              rw [mul_assoc (linearPow a xs.length) x (listProd xs)]
        _ = (a * linearPow a xs.length) * (x * listProd xs) := by
              rw [← mul_assoc]
        _ = linearPow a (xs.length + 1) * (x * listProd xs) := by
              rw [linearPow_succ, mul_comm (linearPow a xs.length) a]
        _ = linearPow a (x :: xs).length * listProd (x :: xs) := by
              simp only [listProd_cons, List.length_cons]

/-- The product of a list of nonzero packed quotient elements is nonzero. -/
theorem listProd_ne_zero (hf_pos : 0 < f.degree)
    {xs : List (GF2nPoly f hirr)}
    (hxs : ∀ x ∈ xs, x ≠ 0) :
    listProd xs ≠ 0 := by
  induction xs with
  | nil =>
      simp only [listProd_nil]
      exact one_ne_zero (f := f) (hirr := hirr) hf_pos
  | cons x xs ih =>
      simp only [listProd_cons]
      apply mul_ne_zero_of_ne_zero
      · exact hxs x List.mem_cons_self
      · exact ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

/-- Finite-field exponent theorem for the packed quotient: every nonzero
quotient element raised to the number of nonzero representatives is `1`. -/
theorem linearPow_pred_card_eq_one_of_ne_zero
    (hf_pos : 0 < f.degree) {a : GF2nPoly f hirr} (ha : a ≠ 0) :
    linearPow a (2 ^ f.degree - 1) = 1 := by
  let L : List (GF2nPoly f hirr) := nonzeroElements (f := f) (hirr := hirr)
  let P : GF2nPoly f hirr := listProd L
  have hL_card : L.length = 2 ^ f.degree - 1 :=
    nonzeroElements_card (f := f) (hirr := hirr)
  have hP_ne : P ≠ 0 :=
    listProd_ne_zero (f := f) (hirr := hirr) hf_pos
      (fun x hx => (mem_nonzeroElements x).mp hx)
  have hperm := nonzeroElements_map_mul_left_perm
    (f := f) (hirr := hirr) ha
  have hprod_eq : listProd (L.map (fun b => a * b)) = P :=
    listProd_perm hperm
  have hfactor : listProd (L.map (fun b => a * b)) = linearPow a L.length * P :=
    listProd_map_mul_left a L
  have hkey : linearPow a L.length * P = P := hfactor.symm.trans hprod_eq
  have hcancel : linearPow a L.length * P * P⁻¹ = P * P⁻¹ :=
    congrArg (fun x => x * P⁻¹) hkey
  rw [mul_assoc, mul_inv_cancel P hP_ne, mul_one] at hcancel
  rw [hL_card] at hcancel
  exact hcancel

/-- Every packed quotient element is fixed by the degree-cardinality
Frobenius iterate. -/
theorem frobeniusIter_degree_eq_self
    (hf_pos : 0 < f.degree) (a : GF2nPoly f hirr) :
    frobeniusIter a f.degree = a := by
  rw [frobeniusIter_eq_linearPow_two_pow]
  have hpos : 0 < 2 ^ f.degree := Nat.pow_pos (by decide : 0 < 2)
  have hsplit : 2 ^ f.degree = (2 ^ f.degree - 1) + 1 := by omega
  by_cases ha : a = 0
  · rw [ha, hsplit, linearPow_succ, mul_zero]
  · rw [hsplit, linearPow_succ,
      linearPow_pred_card_eq_one_of_ne_zero (f := f) (hirr := hirr) hf_pos ha,
      one_mul]

/-- Adding any multiple of the modulus degree to a Frobenius iterate does not
change the result. -/
theorem frobeniusIter_add_mul_degree_eq
    (hf_pos : 0 < f.degree) (a : GF2nPoly f hirr) (m q : Nat) :
    frobeniusIter a (m + f.degree * q) = frobeniusIter a m := by
  induction q with
  | zero =>
      rw [Nat.mul_zero, Nat.add_zero]
  | succ q ih =>
      have hidx : m + f.degree * (q + 1) = (m + f.degree * q) + f.degree := by
        rw [Nat.mul_succ]
        omega
      calc
        frobeniusIter a (m + f.degree * (q + 1))
            = frobeniusIter a ((m + f.degree * q) + f.degree) := by rw [hidx]
        _ = frobeniusIter (frobeniusIter a (m + f.degree * q)) f.degree := by
              rw [frobeniusIter_add]
        _ = frobeniusIter (frobeniusIter a m) f.degree := by rw [ih]
        _ = frobeniusIter a m :=
              frobeniusIter_degree_eq_self (f := f) (hirr := hirr) hf_pos
                (frobeniusIter a m)

/-- If a quotient element is fixed by the `n`-fold Frobenius, it is also fixed
by the remainder of `n` modulo the modulus degree. -/
theorem frobeniusIter_mod_degree_eq_of_fixed
    (hf_pos : 0 < f.degree) {a : GF2nPoly f hirr} {n : Nat}
    (hfixed : frobeniusIter a n = a) :
    frobeniusIter a (n % f.degree) = a := by
  have hdecomp : n % f.degree + f.degree * (n / f.degree) = n :=
    Nat.mod_add_div n f.degree
  have hperiod :
      frobeniusIter a (n % f.degree + f.degree * (n / f.degree)) =
        frobeniusIter a (n % f.degree) :=
    frobeniusIter_add_mul_degree_eq (f := f) (hirr := hirr) hf_pos a
      (n % f.degree) (n / f.degree)
  rw [hdecomp] at hperiod
  rw [← hperiod]
  exact hfixed

end GF2nPoly
end Hex
