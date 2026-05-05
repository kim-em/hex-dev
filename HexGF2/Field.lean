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

end GF2nPoly
end Hex
