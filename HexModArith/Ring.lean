import Init.Grind.Ring.Basic
import HexModArith.Basic

/-!
Ring-facing `ZMod64` API for `hex-mod-arith`.

This module adds the negation/cast surface around the executable `ZMod64`
operations and exposes the `Lean.Grind` semiring/ring/commutative-ring
instances expected by downstream libraries.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

private theorem neg_nonzero_toNat (a : ZMod64 p) {hpLt : p < UInt64.word}
    (hzero : a.val ≠ 0) :
    (-a.val - complementWord p hpLt).toNat = p - a.toNat := by
  have hzeroNat : a.toNat ≠ 0 := by
    intro h
    apply hzero
    apply UInt64.toNat_inj.mp
    simpa [toNat_eq_val] using h
  have hneg_toNat : (-a.val).toNat = UInt64.word - a.toNat := by
    rw [UInt64.toNat_neg]
    have hlt : UInt64.word - a.toNat < UInt64.word := by
      have hpos : 0 < a.toNat := Nat.pos_of_ne_zero hzeroNat
      omega
    rw [Nat.mod_eq_of_lt (by simpa [toNat_eq_val, UInt64.word, UInt64.size] using hlt)]
    simp [toNat_eq_val, UInt64.word, UInt64.size]
  have hge :
      UInt64.word ≤ UInt64.word - (UInt64.word - p) + (UInt64.word - a.toNat) := by
    have ha : a.toNat < p := a.isLt
    omega
  have hlt :
      UInt64.word - (UInt64.word - p) + (UInt64.word - a.toNat) -
          UInt64.word < UInt64.word := by
    have ha : a.toNat < p := a.isLt
    omega
  rw [UInt64.toNat_sub, hneg_toNat]
  simp [complementWord, UInt64.toNat_ofNatLT]
  rw [Nat.mod_eq_sub_mod (by simpa [UInt64.word] using hge),
    Nat.mod_eq_of_lt (by simpa [UInt64.word] using hlt)]
  have hfinal :
      UInt64.word - (UInt64.word - p) + (UInt64.word - a.toNat) - UInt64.word =
        p - a.toNat := by
    omega
  simpa [UInt64.word] using hfinal

private theorem neg_nonzero_lt (a : ZMod64 p) {hpLt : p < UInt64.word}
    (hzero : a.val ≠ 0) :
    (-a.val - complementWord p hpLt).toNat < p := by
  rw [neg_nonzero_toNat a hzero]
  have hzeroNat : a.toNat ≠ 0 := by
    intro h
    apply hzero
    apply UInt64.toNat_inj.mp
    simpa [toNat_eq_val] using h
  have ha : a.toNat < p := a.isLt
  omega

/-- The additive inverse represented by the complementary residue mod `p`. -/
def neg (a : ZMod64 p) : ZMod64 p := by
  by_cases hp : p = UInt64.word
  · refine ⟨-a.val, ?_⟩
    simpa [hp] using (UInt64.toNat_lt_size (-a.val))
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    let c64 := complementWord p hpLt
    by_cases hzero : a.val = 0
    · refine ⟨0, ?_⟩
      simp [Bounds.pPos (p := p)]
    · exact ⟨-a.val - c64, by simpa [c64] using neg_nonzero_lt a hzero⟩

/-- Natural-number literals in `ZMod64`. -/
def natCast (p : Nat) [Bounds p] (n : Nat) : ZMod64 p :=
  ofNat p n

/-- Natural scalar multiplication on `ZMod64`. -/
def nsmul (n : Nat) (a : ZMod64 p) : ZMod64 p :=
  ofNat p (n * a.toNat)

/-- Integer literals in `ZMod64`, reduced mod `p`. -/
def intCast (p : Nat) [Bounds p] : Int → ZMod64 p
  | .ofNat n => natCast p n
  | .negSucc n => neg (natCast p (n + 1))

/-- Integer scalar multiplication on `ZMod64`. -/
def zsmul (i : Int) (a : ZMod64 p) : ZMod64 p :=
  match i with
  | .ofNat n => nsmul n a
  | .negSucc n => neg (nsmul (n + 1) a)

/-- Integer casts of nonnegative representatives agree with natural casts. -/
@[simp] theorem intCast_ofNat (n : Nat) : intCast p (.ofNat n) = natCast p n :=
  rfl

/-- Integer casts of negative representatives use the complementary natural cast. -/
@[simp] theorem intCast_negSucc (n : Nat) :
    intCast p (.negSucc n) = neg (natCast p (n + 1)) :=
  rfl

/-- Integer scalar multiplication by a nonnegative integer is natural scalar multiplication. -/
@[simp] theorem zsmul_ofNat (n : Nat) (a : ZMod64 p) : zsmul (.ofNat n) a = nsmul n a :=
  rfl

/-- Integer scalar multiplication by a negative integer negates the positive natural multiple. -/
@[simp] theorem zsmul_negSucc (n : Nat) (a : ZMod64 p) :
    zsmul (.negSucc n) a = neg (nsmul (n + 1) a) :=
  rfl

instance : Neg (ZMod64 p) where
  neg := neg

instance : NatCast (ZMod64 p) where
  natCast := natCast p

instance (n : Nat) : OfNat (ZMod64 p) n where
  ofNat := natCast p n

instance : SMul Nat (ZMod64 p) where
  smul := nsmul

instance : IntCast (ZMod64 p) where
  intCast := intCast p

instance : SMul Int (ZMod64 p) where
  smul := zsmul

/-- Natural casts reduce their representative modulo `p`. -/
@[simp, grind =] theorem toNat_natCast (n : Nat) : (natCast p n).toNat = n % p := by
  rw [natCast, toNat_ofNat]

/-- Natural casts are residues built from the cast representative. -/
theorem natCast_eq_ofNat (n : Nat) :
    natCast p n = ofNat p n := by
  rfl

/-- Operator-level form of `natCast_eq_ofNat`. -/
theorem natCast_op_eq_ofNat (n : Nat) :
    (n : ZMod64 p) = ofNat p n := by
  simpa using natCast_eq_ofNat (p := p) n

/-- Negation takes the complementary representative modulo `p`. -/
@[simp, grind =] theorem toNat_neg (a : ZMod64 p) : (neg a).toNat = (p - a.toNat) % p := by
  unfold neg
  by_cases hp : p = UInt64.word
  · rw [dif_pos hp]
    change (-a.val).toNat = (p - a.toNat) % p
    rw [UInt64.toNat_neg]
    simp [toNat_eq_val, hp, UInt64.word]
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    rw [dif_neg hp]
    by_cases hzero : a.val = 0
    · rw [dif_pos hzero]
      change (0 : UInt64).toNat = (p - a.toNat) % p
      have htoNat : a.toNat = 0 := by simp [toNat_eq_val, hzero]
      have hval : a.val.toNat = 0 := by simpa [toNat_eq_val] using htoNat
      simp [toNat_eq_val, hval]
    · rw [dif_neg hzero]
      change (-a.val - complementWord p hpLt).toNat = (p - a.toNat) % p
      rw [neg_nonzero_toNat a hzero]
      have hzeroNat : a.toNat ≠ 0 := by
        intro h
        apply hzero
        apply UInt64.toNat_inj.mp
        simpa [toNat_eq_val] using h
      have hlt : p - a.toNat < p := by
        have ha : a.toNat < p := a.isLt
        omega
      rw [Nat.mod_eq_of_lt hlt]

/-- Negation is the residue built from the complementary representative. -/
theorem neg_eq_ofNat (a : ZMod64 p) :
    neg a = ofNat p (p - a.toNat) := by
  rw [eq_iff_toNat_eq, toNat_neg, toNat_ofNat]

/-- Operator-level form of `neg_eq_ofNat`. -/
theorem neg_op_eq_ofNat (a : ZMod64 p) :
    -a = ofNat p (p - a.toNat) := by
  simpa using neg_eq_ofNat a

/-- Natural scalar multiplication reduces the scaled representative modulo `p`. -/
@[simp, grind =] theorem toNat_nsmul (n : Nat) (a : ZMod64 p) :
    (nsmul n a).toNat = (n * a.toNat) % p := by
  rw [nsmul, toNat_ofNat]

/-- Natural scalar multiplication is the residue built from the scaled representative. -/
theorem nsmul_eq_ofNat (n : Nat) (a : ZMod64 p) :
    nsmul n a = ofNat p (n * a.toNat) := by
  rw [eq_iff_toNat_eq, toNat_nsmul, toNat_ofNat]

/-- Operator-level form of `nsmul_eq_ofNat`. -/
theorem nsmul_op_eq_ofNat (n : Nat) (a : ZMod64 p) :
    n • a = ofNat p (n * a.toNat) := by
  simpa using nsmul_eq_ofNat n a

/-- Integer casts of nonnegative representatives reduce modulo `p`. -/
@[simp, grind =] theorem toNat_intCast_ofNat (n : Nat) :
    (intCast p (.ofNat n)).toNat = n % p := by
  rw [intCast_ofNat, toNat_natCast]

/-- Integer casts of negative representatives use the complementary reduced representative. -/
@[simp, grind =] theorem toNat_intCast_negSucc (n : Nat) :
    (intCast p (.negSucc n)).toNat = (p - (n + 1) % p) % p := by
  rw [intCast_negSucc, toNat_neg, toNat_natCast]

/-- Nonnegative integer scalar multiplication reduces the scaled representative modulo `p`. -/
@[simp, grind =] theorem toNat_zsmul_ofNat (n : Nat) (a : ZMod64 p) :
    (zsmul (.ofNat n) a).toNat = (n * a.toNat) % p := by
  rw [zsmul_ofNat, toNat_nsmul]

/-- Negative integer scalar multiplication uses the complementary scaled representative. -/
@[simp, grind =] theorem toNat_zsmul_negSucc (n : Nat) (a : ZMod64 p) :
    (zsmul (.negSucc n) a).toNat = (p - ((n + 1) * a.toNat) % p) % p := by
  rw [zsmul_negSucc, toNat_neg, toNat_nsmul]

/-- Nat casts agree exactly when their representatives are congruent mod `p`. -/
theorem natCast_eq_natCast_iff (x y : Nat) :
    ((x : ZMod64 p) = y) ↔ x % p = y % p := by
  constructor
  · intro h
    simpa using congrArg ZMod64.toNat h
  · intro h
    apply ext
    apply UInt64.toNat_inj.mp
    simpa [toNat_natCast] using h

/-- A Nat literal vanishes in `ZMod64 p` exactly when `p` divides it. -/
theorem natCast_eq_zero_iff_dvd (n : Nat) : ((n : ZMod64 p) = 0) ↔ p ∣ n := by
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero ((natCast_eq_natCast_iff (p := p) n 0).mp h)
  · intro h
    exact (natCast_eq_natCast_iff (p := p) n 0).2 (Nat.mod_eq_zero_of_dvd h)

/-- The modulus itself casts to zero in `ZMod64 p`. -/
@[simp] theorem natCast_self : ((p : Nat) : ZMod64 p) = 0 := by
  exact (natCast_eq_natCast_iff (p := p) p 0).2 (by simp)

/-- The spec-level inverse law on canonical representatives. -/
theorem toNat_inv (a : ZMod64 p) (hcop : Nat.Coprime a.val.toNat p) :
    (a.inv * a).toNat = 1 % p := by
  simpa [ZMod64.toNat_eq_val] using inv_mul_eq_one (p := p) a hcop

private theorem nat_add_assoc_mod (x y z m : Nat) :
    (((x % m + y % m) % m + z % m) % m) =
      (x % m + (y % m + z % m) % m) % m := by
  calc
    (((x % m + y % m) % m + z % m) % m) = ((x + y) + z) % m := by
      rw [← Nat.add_mod x y m, ← Nat.add_mod (x + y) z m]
    _ = (x + (y + z)) % m := by rw [Nat.add_assoc]
    _ = (x % m + (y % m + z % m) % m) % m := by
      rw [← Nat.add_mod y z m, ← Nat.add_mod x (y + z) m]

private theorem nat_mul_assoc_mod (x y z m : Nat) :
    (((x % m * (y % m)) % m * (z % m)) % m) =
      (x % m * ((y % m * (z % m)) % m)) % m := by
  calc
    (((x % m * (y % m)) % m * (z % m)) % m) = ((x * y) * z) % m := by
      rw [← Nat.mul_mod x y m, ← Nat.mul_mod (x * y) z m]
    _ = (x * (y * z)) % m := by rw [Nat.mul_assoc]
    _ = (x % m * ((y % m * (z % m)) % m)) % m := by
      rw [← Nat.mul_mod y z m, ← Nat.mul_mod x (y * z) m]

private theorem nat_left_distrib_mod (x y z m : Nat) :
    (x % m * ((y % m + z % m) % m) % m) =
      ((x % m * (y % m)) % m + (x % m * (z % m)) % m) % m := by
  calc
    (x % m * ((y % m + z % m) % m) % m) = (x * (y + z)) % m := by
      rw [← Nat.add_mod y z m, ← Nat.mul_mod x (y + z) m]
    _ = (x * y + x * z) % m := by rw [Nat.left_distrib]
    _ = ((x % m * (y % m)) % m + (x % m * (z % m)) % m) % m := by
      rw [Nat.add_mod]
      rw [Nat.mul_mod x y m, Nat.mul_mod x z m]

private theorem nat_right_distrib_mod (x y z m : Nat) :
    (((x % m + y % m) % m) * (z % m) % m) =
      ((x % m * (z % m)) % m + (y % m * (z % m)) % m) % m := by
  calc
    (((x % m + y % m) % m) * (z % m) % m) = ((x + y) * z) % m := by
      rw [← Nat.add_mod x y m, ← Nat.mul_mod (x + y) z m]
    _ = (x * z + y * z) % m := by rw [Nat.right_distrib]
    _ = ((x % m * (z % m)) % m + (y % m * (z % m)) % m) % m := by
      rw [Nat.add_mod]
      rw [Nat.mul_mod x z m, Nat.mul_mod y z m]

private theorem nat_neg_add_cancel_mod (x m : Nat) (hx : x < m) :
    ((m - x) % m + x) % m = 0 := by
  by_cases hzero : x = 0
  · simp [hzero]
  · have hpos : 0 < x := Nat.pos_of_ne_zero hzero
    have hlt : m - x < m := by omega
    have hsum : m - x + x = m := Nat.sub_add_cancel (Nat.le_of_lt hx)
    rw [Nat.mod_eq_of_lt hlt, hsum, Nat.mod_self]

private theorem nat_neg_neg_mod (x m : Nat) (hx : x < m) :
    (m - (m - x) % m) % m = x := by
  by_cases hzero : x = 0
  · simp [hzero]
  · have hpos : 0 < x := Nat.pos_of_ne_zero hzero
    have hlt : m - x < m := by omega
    have hsub : m - (m - x) = x := by omega
    rw [Nat.mod_eq_of_lt hlt, hsub, Nat.mod_eq_of_lt hx]

private theorem nat_mul_comm_mod (x y m : Nat) :
    (x * y) % m = (y * x) % m := by
  rw [Nat.mul_comm]

private theorem neg_neg (a : ZMod64 p) : ZMod64.neg (ZMod64.neg a) = a := by
  apply ext_toNat
  rw [toNat_neg, toNat_neg]
  exact nat_neg_neg_mod a.toNat p a.isLt

instance : Lean.Grind.Semiring (ZMod64 p) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply ext_toNat
    rw [show a + 0 = ZMod64.add a ZMod64.zero from rfl]
    change (ZMod64.add a ZMod64.zero).toNat = a.toNat
    rw [toNat_add, toNat_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt a.isLt
  · intro a b
    apply ext_toNat
    change (ZMod64.add a b).toNat = (ZMod64.add b a).toNat
    rw [toNat_add, toNat_add]
    simp [Nat.add_comm]
  · intro a b c
    apply ext_toNat
    change (ZMod64.add (ZMod64.add a b) c).toNat =
      (ZMod64.add a (ZMod64.add b c)).toNat
    rw [toNat_add, toNat_add, toNat_add, toNat_add]
    simpa [toNat_eq_val, Nat.mod_mod] using
      nat_add_assoc_mod a.toNat b.toNat c.toNat p
  · intro a b c
    apply ext_toNat
    change (ZMod64.mul (ZMod64.mul a b) c).toNat =
      (ZMod64.mul a (ZMod64.mul b c)).toNat
    rw [toNat_mul, toNat_mul, toNat_mul, toNat_mul]
    simpa [toNat_eq_val, Nat.mod_mod] using
      nat_mul_assoc_mod a.toNat b.toNat c.toNat p
  · intro a
    apply ext_toNat
    change (ZMod64.mul a ZMod64.one).toNat = a.toNat
    rw [toNat_mul, toNat_one]
    simp [Nat.mod_eq_of_lt a.isLt]
  · intro a
    apply ext_toNat
    change (ZMod64.mul ZMod64.one a).toNat = a.toNat
    rw [toNat_mul, toNat_one]
    simp [Nat.mod_eq_of_lt a.isLt]
  · intro a b c
    apply ext_toNat
    change (ZMod64.mul a (ZMod64.add b c)).toNat =
      (ZMod64.add (ZMod64.mul a b) (ZMod64.mul a c)).toNat
    rw [toNat_mul, toNat_add, toNat_add, toNat_mul, toNat_mul]
    simpa [toNat_eq_val, Nat.mod_mod] using
      nat_left_distrib_mod a.toNat b.toNat c.toNat p
  · intro a b c
    apply ext_toNat
    change (ZMod64.mul (ZMod64.add a b) c).toNat =
      (ZMod64.add (ZMod64.mul a c) (ZMod64.mul b c)).toNat
    rw [toNat_mul, toNat_add, toNat_add, toNat_mul, toNat_mul]
    simpa [toNat_eq_val, Nat.mod_mod] using
      nat_right_distrib_mod a.toNat b.toNat c.toNat p
  · intro a
    apply ext_toNat
    change (ZMod64.mul ZMod64.zero a).toNat = (ZMod64.zero : ZMod64 p).toNat
    rw [toNat_mul, toNat_zero]
    simp
  · intro a
    apply ext_toNat
    change (ZMod64.mul a ZMod64.zero).toNat = (ZMod64.zero : ZMod64 p).toNat
    rw [toNat_mul, toNat_zero]
    simp
  · intro a
    apply ext_toNat
    change (ZMod64.pow a 0).toNat = (ZMod64.one : ZMod64 p).toNat
    rw [toNat_pow, toNat_one]
    simp
  · intro a n
    apply ext_toNat
    change (ZMod64.pow a (n + 1)).toNat =
      (ZMod64.mul (ZMod64.pow a n) a).toNat
    rw [toNat_pow, toNat_mul, toNat_pow]
    simp [Nat.pow_succ, Nat.mul_mod]
  · intro n
    apply ext_toNat
    change (OfNat.ofNat (n + 1) : ZMod64 p).toNat =
      (ZMod64.add (OfNat.ofNat n) ZMod64.one).toNat
    rw [show (OfNat.ofNat (n + 1) : ZMod64 p) = ZMod64.natCast p (n + 1) from rfl]
    rw [show (OfNat.ofNat n : ZMod64 p) = ZMod64.natCast p n from rfl]
    rw [toNat_natCast, toNat_add, toNat_natCast, toNat_one]
    simp [Nat.add_mod]
  · intro n
    rfl
  · intro n a
    apply ext_toNat
    change (ZMod64.nsmul n a).toNat = (ZMod64.mul (↑n : ZMod64 p) a).toNat
    rw [toNat_nsmul, toNat_mul]
    rw [show (↑n : ZMod64 p).toNat = (ZMod64.natCast p n).toNat from rfl]
    rw [toNat_natCast]
    simp [Nat.mul_mod]

/-- Adding zero on the right leaves a residue unchanged. -/
theorem add_zero (a : ZMod64 p) : a + 0 = a := by
  apply ext_toNat
  rw [show a + 0 = ZMod64.add a ZMod64.zero from rfl]
  change (ZMod64.add a ZMod64.zero).toNat = a.toNat
  rw [toNat_add, toNat_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.isLt

/-- Adding zero on the left leaves a residue unchanged. -/
theorem zero_add (a : ZMod64 p) : 0 + a = a := by
  apply ext_toNat
  rw [show 0 + a = ZMod64.add ZMod64.zero a from rfl]
  change (ZMod64.add ZMod64.zero a).toNat = a.toNat
  rw [toNat_add, toNat_zero]
  simpa using Nat.mod_eq_of_lt a.isLt

/-- Multiplying by zero on the right gives zero. -/
theorem mul_zero (a : ZMod64 p) : a * 0 = 0 := by
  apply ext_toNat
  change (ZMod64.mul a ZMod64.zero).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [toNat_mul, toNat_zero]
  simp

/-- Multiplying by zero on the left gives zero. -/
theorem zero_mul (a : ZMod64 p) : 0 * a = 0 := by
  apply ext_toNat
  change (ZMod64.mul ZMod64.zero a).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [toNat_mul, toNat_zero]
  simp

/-- Multiplying by one on the right leaves a residue unchanged. -/
theorem mul_one (a : ZMod64 p) : a * 1 = a := by
  apply ext_toNat
  change (ZMod64.mul a ZMod64.one).toNat = a.toNat
  rw [toNat_mul, toNat_one]
  simp [Nat.mod_eq_of_lt a.isLt]

/-- Multiplying by one on the left leaves a residue unchanged. -/
theorem one_mul (a : ZMod64 p) : 1 * a = a := by
  apply ext_toNat
  change (ZMod64.mul ZMod64.one a).toNat = a.toNat
  rw [toNat_mul, toNat_one]
  simp [Nat.mod_eq_of_lt a.isLt]

/-- Every residue to the zeroth power is one. -/
theorem pow_zero (a : ZMod64 p) : a ^ 0 = 1 := by
  apply ext_toNat
  change (ZMod64.pow a 0).toNat = (ZMod64.one : ZMod64 p).toNat
  rw [toNat_pow, toNat_one]
  simp

/-- Every residue to the first power is itself. -/
@[simp] theorem pow_one (a : ZMod64 p) : a ^ 1 = a := by
  apply ext_toNat
  change (ZMod64.pow a 1).toNat = a.toNat
  rw [toNat_pow]
  simpa using Nat.mod_eq_of_lt a.isLt

/-- Successor powers multiply the previous power by the base. -/
theorem pow_succ (a : ZMod64 p) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := by
  apply ext_toNat
  change (ZMod64.pow a (n + 1)).toNat =
    (ZMod64.mul (ZMod64.pow a n) a).toNat
  rw [toNat_pow, toNat_mul, toNat_pow]
  simp [Nat.pow_succ, Nat.mul_mod]

/-- Any positive power of zero is zero. -/
@[simp] theorem zero_pow {n : Nat} (hn : n ≠ 0) : (0 : ZMod64 p) ^ n = 0 := by
  apply ext_toNat
  change (ZMod64.pow ZMod64.zero n).toNat = (ZMod64.zero : ZMod64 p).toNat
  rw [toNat_pow, toNat_zero]
  cases n with
  | zero => contradiction
  | succ n => simp

/-- Every power of one is one. -/
@[simp] theorem one_pow (n : Nat) : (1 : ZMod64 p) ^ n = 1 := by
  apply ext_toNat
  change (ZMod64.pow ZMod64.one n).toNat = (ZMod64.one : ZMod64 p).toNat
  rw [toNat_pow, toNat_one]
  rw [← Nat.pow_mod (1 : Nat) n p]
  simp

instance : Lean.Grind.Ring (ZMod64 p) where
  neg_add_cancel := by
    intro a
    apply ext_toNat
    change (ZMod64.add (ZMod64.neg a) a).toNat = (ZMod64.zero : ZMod64 p).toNat
    rw [toNat_add, toNat_neg, toNat_zero]
    simpa [Nat.mod_mod] using nat_neg_add_cancel_mod a.toNat p a.isLt
  sub_eq_add_neg := by
    intro a b
    apply ext_toNat
    change (ZMod64.sub a b).toNat = (ZMod64.add a (ZMod64.neg b)).toNat
    rw [toNat_sub, toNat_add, toNat_neg]
    simp
  neg_zsmul := by
    intro i a
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            apply ext_toNat
            change (ZMod64.nsmul 0 a).toNat = (ZMod64.neg (ZMod64.nsmul 0 a)).toNat
            rw [toNat_nsmul, toNat_neg, toNat_nsmul]
            simp
        | succ n =>
            rfl
    | negSucc n =>
        exact (neg_neg (ZMod64.nsmul (n + 1) a)).symm
  intCast_neg := by
    intro i
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            apply ext_toNat
            change (ZMod64.natCast p 0).toNat = (ZMod64.neg (ZMod64.natCast p 0)).toNat
            rw [toNat_natCast, toNat_neg, toNat_natCast]
            simp
        | succ n =>
            rfl
    | negSucc n =>
        exact (neg_neg (ZMod64.natCast p (n + 1))).symm

instance : Lean.Grind.CommRing (ZMod64 p) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply ext_toNat
  change (ZMod64.mul a b).toNat = (ZMod64.mul b a).toNat
  rw [toNat_mul, toNat_mul]
  exact nat_mul_comm_mod a.toNat b.toNat p

instance : Lean.Grind.IsCharP (ZMod64 p) p where
  ofNat_ext_iff {x y} := natCast_eq_natCast_iff (p := p) x y

end ZMod64

end Hex
