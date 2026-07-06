/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyFp.Degree
public meta import HexModArith.Ring
public import HexModArith.Prime
public import HexPolyFp.Degree

public section
set_option backward.proofsInPublic true

/-!
Scalar-multiple and characteristic-`p` algebra foundations for the Yun
square-free decomposition: power/binomial/`pthRoot` algebra, field
helpers, `normalizeMonic`, `monicGcd`, and the C-scaling gcd lemmas.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- One square-free factor together with its multiplicity. -/
structure SquareFreeFactor (p : Nat) [ZMod64.Bounds p] where
  /-- The square-free factor polynomial. -/
  factor : FpPoly p
  /-- The exponent with which `factor` divides the original polynomial. -/
  multiplicity : Nat

/-- A square-free decomposition records the scalar unit and the nonconstant factors. -/
structure SquareFreeDecomposition (p : Nat) [ZMod64.Bounds p] where
  /-- The leading-coefficient scalar unit pulled out of the polynomial. -/
  unit : ZMod64 p
  /-- The square-free factors together with their multiplicities. -/
  factors : List (SquareFreeFactor p)

/-- Detect the unit polynomial `1`. -/
@[expose]
def isOne (f : FpPoly p) : Bool :=
  match f.degree? with
  | some 0 =>
      if f.coeff 0 = (1 : ZMod64 p) then
        true
      else
        false
  | _ => false

/-- `isOne f` returns `true` only for the constant polynomial `1`. -/
private theorem eq_one_of_isOne_true
    (f : FpPoly p) (h : isOne f = true) :
    f = 1 := by
  unfold isOne at h
  cases hdeg : f.degree? with
  | none =>
      simp [hdeg] at h
  | some d =>
      cases d with
      | zero =>
        simp [hdeg] at h
        have hcoeff0 : f.coeff 0 = (1 : ZMod64 p) := h
        have hsize : f.size = 1 := by
          unfold DensePoly.degree? at hdeg
          by_cases hzero : f.size = 0
          · simp [hzero] at hdeg
          · simp [hzero] at hdeg
            omega
        apply DensePoly.ext_coeff
        intro n
        cases n with
        | zero =>
            change f.coeff 0 = (DensePoly.C (1 : ZMod64 p)).coeff 0
            simpa [DensePoly.coeff_C] using hcoeff0
        | succ n =>
            have hn : f.size ≤ n + 1 := by omega
            change f.coeff (n + 1) = (DensePoly.C (1 : ZMod64 p)).coeff (n + 1)
            rw [DensePoly.coeff_eq_zero_of_size_le f hn]
            exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm
      | succ d =>
        simp [hdeg] at h

/-- Polynomial exponentiation uses square-and-multiply on the exponent bits. -/
@[expose]
def pow (f : FpPoly p) (n : Nat) : FpPoly p :=
  let rec go (acc base : FpPoly p) (k : Nat) : FpPoly p :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      go acc' (base * base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 f n

/-- `pow f 1` is `f`. -/
private theorem pow_one (f : FpPoly p) :
    pow f 1 = f := by
  unfold pow
  simp [pow.go]

/-- Reference exponentiation by linear recursion (`powLinear f n = f ^ n`),
the specification the square-and-multiply `pow` is proved against. -/
private def powLinear (f : FpPoly p) : Nat → FpPoly p
  | 0 => 1
  | n + 1 => powLinear f n * f

/-- `powLinear` turns exponent addition into multiplication. -/
private theorem powLinear_add (f : FpPoly p) (m n : Nat) :
    powLinear f (m + n) = powLinear f m * powLinear f n := by
  induction n with
  | zero =>
      simp [powLinear]
  | succ n ih =>
      rw [Nat.add_succ, powLinear, ih, powLinear]
      exact DensePoly.mul_assoc_poly (powLinear f m) (powLinear f n) f

/-- Doubling the exponent of `powLinear` is the same as squaring the base. -/
private theorem powLinear_double (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n) = powLinear (f * f) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [htwo]
      change powLinear f ((2 * n + 1) + 1) =
        powLinear (f * f) n * (f * f)
      rw [powLinear, powLinear, ih]
      exact DensePoly.mul_assoc_poly (powLinear (f * f) n) f f

/-- An odd exponent of `powLinear` peels off one base factor and squares the rest. -/
private theorem powLinear_double_add_one (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n + 1) = f * powLinear (f * f) n := by
  rw [powLinear, powLinear_double]
  exact mul_comm (powLinear (f * f) n) f

/-- The square-and-multiply loop computes `acc * powLinear base k`, linking the
executable `pow.go` to the reference `powLinear`. -/
private theorem pow_go_eq_mul_powLinear (acc base : FpPoly p) (k : Nat) :
    pow.go acc base k = acc * powLinear base k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [pow.go.eq_def]
      by_cases hk : k = 0
      · simp [hk, powLinear]
      · rw [dif_neg hk]
        have hlt : k / 2 < k :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide : 1 < 2)
        cases Nat.mod_two_eq_zero_or_one k with
        | inl hmod0 =>
            have hk_eq : k = 2 * (k / 2) := by
              have h := Nat.mod_add_div k 2
              omega
            have hnot : ¬k % 2 = 1 := by omega
            have hdiv : 2 * (k / 2) / 2 = k / 2 :=
              Nat.mul_div_right (k / 2) (by decide : 0 < 2)
            rw [if_neg hnot]
            calc
              pow.go acc (base * base) (k / 2)
                  = acc * powLinear (base * base) (k / 2) := by
                    exact ih (k / 2) hlt acc (base * base)
              _ = acc * powLinear base k := by
                    rw [hk_eq, hdiv, powLinear_double]
        | inr hmod1 =>
            have hk_eq : k = 2 * (k / 2) + 1 := by
              have h := Nat.mod_add_div k 2
              omega
            rw [if_pos hmod1]
            calc
              pow.go (acc * base) (base * base) (k / 2)
                  = (acc * base) * powLinear (base * base) (k / 2) := by
                    exact ih (k / 2) hlt (acc * base) (base * base)
              _ = acc * (base * powLinear (base * base) (k / 2)) := by
                    exact DensePoly.mul_assoc_poly acc base
                      (powLinear (base * base) (k / 2))
              _ = acc * powLinear base (2 * (k / 2) + 1) := by
                    rw [powLinear_double_add_one]
              _ = acc * powLinear base k := by
                    rw [← hk_eq]

/-- The square-and-multiply `pow` agrees with the reference `powLinear`. -/
private theorem pow_eq_powLinear (f : FpPoly p) (n : Nat) :
    pow f n = powLinear f n := by
  unfold pow
  rw [pow_go_eq_mul_powLinear]
  exact one_mul (powLinear f n)

/-- Iterating `powLinear` multiplies the exponents. -/
private theorem powLinear_powLinear_mul (f : FpPoly p) (m n : Nat) :
    powLinear (powLinear f n) m = powLinear f (m * n) := by
  induction m with
  | zero =>
      simp [powLinear]
  | succ m ih =>
      rw [powLinear, ih]
      simpa [Nat.succ_mul] using (powLinear_add f (m * n) n).symm

/-- `powLinear` distributes over a product of bases. -/
private theorem powLinear_mul_base (f g : FpPoly p) (n : Nat) :
    powLinear (f * g) n = powLinear f n * powLinear g n := by
  induction n with
  | zero =>
      simp [powLinear]
  | succ n ih =>
      rw [powLinear, ih, powLinear, powLinear]
      calc
        (powLinear f n * powLinear g n) * (f * g) =
            powLinear f n * (powLinear g n * (f * g)) := by
              exact DensePoly.mul_assoc_poly
                (powLinear f n) (powLinear g n) (f * g)
        _ = powLinear f n * ((powLinear g n * f) * g) := by
              exact congrArg (fun x => powLinear f n * x)
                (DensePoly.mul_assoc_poly (powLinear g n) f g).symm
        _ = powLinear f n * ((f * powLinear g n) * g) := by
              rw [mul_comm (powLinear g n) f]
        _ = powLinear f n * (f * (powLinear g n * g)) := by
              exact congrArg (fun x => powLinear f n * x)
                (DensePoly.mul_assoc_poly f (powLinear g n) g)
        _ = (powLinear f n * f) * (powLinear g n * g) := by
              exact (DensePoly.mul_assoc_poly
                (powLinear f n) f (powLinear g n * g)).symm

/-- `pow` turns exponent addition into multiplication. -/
private theorem pow_add_exp (f : FpPoly p) (m n : Nat) :
    pow f (m + n) = pow f m * pow f n := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_add f m n

/-- `pow f (n + 1)` is `pow f n` times one more factor of `f`. -/
private theorem pow_succ (f : FpPoly p) (n : Nat) :
    pow f (n + 1) = pow f n * f := by
  rw [pow_eq_powLinear, pow_eq_powLinear]
  rfl

/-- `pow` distributes over a product of bases. -/
private theorem pow_mul_base (f g : FpPoly p) (n : Nat) :
    pow (f * g) n = pow f n * pow g n := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_mul_base f g n

/-- Iterating `pow` multiplies the exponents. -/
private theorem pow_pow_mul' (f : FpPoly p) (m n : Nat) :
    pow (pow f n) m = pow f (m * n) := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_powLinear_mul f m n

/-- Interior binomial coefficients `choose p k` (for `0 < k < p`) vanish mod `p`,
the arithmetic fact underlying Frobenius additivity. -/
private theorem zmod64_natCast_choose_prime_eq_zero
    (hp : Hex.Nat.Prime p) {k : Nat} (hk0 : 0 < k) (hkp : k < p) :
    ((Hex.Nat.choose p k : Nat) : ZMod64 p) = 0 := by
  exact (ZMod64.natCast_eq_zero_iff_dvd (p := p) (Hex.Nat.choose p k)).2
    (Hex.Nat.choose_prime_dvd hp hk0 hkp)

/-- Scalar scaling of a polynomial is additive in the scalar. -/
private theorem scale_add_scalar (c d : ZMod64 p) (f : FpPoly p) :
    DensePoly.scale (c + d) f = DensePoly.scale c f + DensePoly.scale d f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_cd : (c + d) * (0 : ZMod64 p) = 0 := by grind
  have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
  have hzero_d : d * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_cd, DensePoly.coeff_add_semiring,
    DensePoly.coeff_scale _ _ _ hzero_c, DensePoly.coeff_scale _ _ _ hzero_d]
  grind

/-- Scalar scaling commutes through the right factor of a product. -/
private theorem scale_mul_right (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f * g) = f * DensePoly.scale c g := by
  calc
    DensePoly.scale c (f * g) = DensePoly.scale c (g * f) := by
      exact congrArg (fun x => DensePoly.scale c x) (DensePoly.mul_comm_poly f g)
    _ = DensePoly.scale c g * f := scale_mul_left c g f
    _ = f * DensePoly.scale c g := by
      exact DensePoly.mul_comm_poly (DensePoly.scale c g) f

/-- `powLinear f (n + 1)` factors one `f` out on the left. -/
private theorem powLinear_succ_left (f : FpPoly p) (n : Nat) :
    powLinear f (n + 1) = f * powLinear f n := by
  rw [powLinear]
  exact DensePoly.mul_comm_poly (powLinear f n) f

/-- Scaling by a `Nat`-cast sum splits additively over the summands. -/
private theorem powLinearBinom_scalar_add
    (a b : Nat) (h : FpPoly p) :
    DensePoly.scale (((a + b : Nat) : ZMod64 p)) h =
      DensePoly.scale (a : ZMod64 p) h + DensePoly.scale (b : ZMod64 p) h := by
  have hcast : (((a + b : Nat) : ZMod64 p)) = (a : ZMod64 p) + (b : ZMod64 p) := by
    grind
  rw [hcast]
  exact scale_add_scalar (a : ZMod64 p) (b : ZMod64 p) h

/-- Scaling by `0` annihilates a polynomial. -/
private theorem powLinearBinom_scalar_zero (h : FpPoly p) :
    DensePoly.scale (0 : ZMod64 p) h = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : (0 : ZMod64 p) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_zero]
  grind

/-- Scaling by `1` is the identity. -/
private theorem powLinearBinom_scalar_one (h : FpPoly p) :
    DensePoly.scale (1 : ZMod64 p) h = h :=
  scale_one_left h

/-- Right-multiplication by the zero polynomial gives `0`. -/
private theorem powLinearBinom_mul_zero (h : FpPoly p) :
    h * (0 : FpPoly p) = 0 :=
  Eq.trans (DensePoly.mul_comm_poly h 0) (DensePoly.zero_mul h)

/-- Absorb a left factor into a scaled product, reassociating it onto the left. -/
private theorem mul_powLinearBinom_scaled_left
    (c : ZMod64 p) (f a b : FpPoly p) :
    f * DensePoly.scale c (a * b) = DensePoly.scale c ((f * a) * b) := by
  calc
    f * DensePoly.scale c (a * b) =
        DensePoly.scale c (f * (a * b)) := by
          exact (scale_mul_right c f (a * b)).symm
    _ = DensePoly.scale c ((f * a) * b) := by
          exact congrArg (fun x => DensePoly.scale c x)
            (DensePoly.mul_assoc_poly f a b).symm

/-- Absorb a left factor `g` into a scaled product, commuting it inside onto the right factor. -/
private theorem mul_powLinearBinom_scaled_right
    (c : ZMod64 p) (g a b : FpPoly p) :
    g * DensePoly.scale c (a * b) = DensePoly.scale c (a * (g * b)) := by
  calc
    g * DensePoly.scale c (a * b) =
        DensePoly.scale c (a * b) * g := by
          exact DensePoly.mul_comm_poly g (DensePoly.scale c (a * b))
    _ = DensePoly.scale c ((a * b) * g) := by
          exact (scale_mul_left c (a * b) g).symm
    _ = DensePoly.scale c (a * (g * b)) := by
          apply congrArg (fun x => DensePoly.scale c x)
          calc
            (a * b) * g = a * (b * g) := DensePoly.mul_assoc_poly a b g
            _ = a * (g * b) := by
                  exact congrArg (fun x => a * x) (DensePoly.mul_comm_poly b g)

/-- The `k`-th binomial term `choose n k • (f^(n-k) * g^k)` in the expansion of `(f + g)^n`. -/
private def powLinearBinomTerm (f g : FpPoly p) (n k : Nat) : FpPoly p :=
  DensePoly.scale (Hex.Nat.choose n k : ZMod64 p)
    (powLinear f (n - k) * powLinear g k)

/-- The partial sum of the first `k` binomial terms of `(f + g)^n`. -/
private def powLinearBinomSum (f g : FpPoly p) (n : Nat) : Nat → FpPoly p
  | 0 => 0
  | k + 1 => powLinearBinomSum f g n k + powLinearBinomTerm f g n k

/-- The zeroth binomial term at `n + 1` factors one `f` out of the zeroth term at `n`. -/
private theorem powLinearBinomTerm_succ_zero (f g : FpPoly p) (n : Nat) :
    powLinearBinomTerm f g (n + 1) 0 =
      f * powLinearBinomTerm f g n 0 := by
  unfold powLinearBinomTerm
  simp [Hex.Nat.choose]
  change DensePoly.scale (1 : ZMod64 p) (powLinear f (n + 1) * powLinear g 0) =
    f * DensePoly.scale (1 : ZMod64 p) (powLinear f n * powLinear g 0)
  rw [powLinearBinom_scalar_one, powLinearBinom_scalar_one]
  have hg0 : powLinear g 0 = 1 := rfl
  rw [hg0]
  calc
    powLinear f (n + 1) * 1 = powLinear f (n + 1) :=
      DensePoly.mul_one_right_poly (powLinear f (n + 1))
    _ = f * powLinear f n := powLinear_succ_left f n
    _ = f * (powLinear f n * 1) := by
          exact congrArg (fun x => f * x)
            (DensePoly.mul_one_right_poly (powLinear f n)).symm

/-- Pascal's rule for binomial terms when `k < n`: the `(k+1)`-th term at `n+1` splits as `f * (term n (k+1)) + g * (term n k)`. -/
private theorem powLinearBinomTerm_succ_succ_of_lt
    (f g : FpPoly p) {n k : Nat} (hk : k < n) :
    powLinearBinomTerm f g (n + 1) (k + 1) =
      f * powLinearBinomTerm f g n (k + 1) +
        g * powLinearBinomTerm f g n k := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_succ_succ, powLinearBinom_scalar_add]
  have hsub : n + 1 - (k + 1) = n - k := by omega
  rw [hsub]
  have hf :
      (f * powLinear f (n - (k + 1))) * powLinear g (k + 1) =
        powLinear f (n - k) * powLinear g (k + 1) := by
    have hsub' : n - k = n - (k + 1) + 1 := by omega
    have hbase :
        f * powLinear f (n - (k + 1)) = powLinear f (n - k) := by
      rw [hsub', powLinear_succ_left]
    exact congrArg (fun x => x * powLinear g (k + 1)) hbase
  have hg :
      powLinear f (n - k) * (g * powLinear g k) =
        powLinear f (n - k) * powLinear g (k + 1) := by
    exact congrArg (fun x => powLinear f (n - k) * x)
      (powLinear_succ_left g k).symm
  rw [mul_powLinearBinom_scaled_left, mul_powLinearBinom_scaled_right, hf, hg]
  exact DensePoly.add_comm_poly _ _

/-- The diagonal (`k = n`) case of Pascal's rule for binomial terms. -/
private theorem powLinearBinomTerm_succ_succ_top
    (f g : FpPoly p) (n : Nat) :
    powLinearBinomTerm f g (n + 1) (n + 1) =
      f * powLinearBinomTerm f g n (n + 1) +
        g * powLinearBinomTerm f g n n := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_succ_succ]
  have hzero_choose : Hex.Nat.choose n (n + 1) = 0 :=
    Hex.Nat.choose_eq_zero_of_lt (by omega)
  rw [hzero_choose, Hex.Nat.choose_self]
  have hcast : (((1 + 0 : Nat) : ZMod64 p)) = (1 : ZMod64 p) := by grind
  rw [hcast]
  have hsub_left : n + 1 - (n + 1) = 0 := by omega
  have hsub_mid : n - (n + 1) = 0 := by omega
  have hsub_right : n - n = 0 := by omega
  rw [hsub_left, hsub_mid, hsub_right]
  change DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g (n + 1)) =
    f * DensePoly.scale (0 : ZMod64 p) (powLinear f 0 * powLinear g (n + 1)) +
      g * DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g n)
  rw [powLinearBinom_scalar_one, powLinearBinom_scalar_zero, powLinearBinom_mul_zero]
  have hzadd : (0 : FpPoly p) +
      g * DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g n) =
        g * DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g n) :=
    DensePoly.zero_add _
  rw [hzadd, powLinearBinom_scalar_one]
  have hf0 : powLinear f 0 = 1 := rfl
  rw [hf0]
  calc
    1 * powLinear g (n + 1) = powLinear g (n + 1) := by
      exact one_mul (powLinear g (n + 1))
    _ = g * powLinear g n := powLinear_succ_left g n
    _ = g * (1 * powLinear g n) := by
          rw [one_mul]

/-- Pascal's rule for binomial terms for every `k ≤ n`, combining the strict and diagonal cases. -/
private theorem powLinearBinomTerm_succ_succ
    (f g : FpPoly p) {n k : Nat} (hk : k ≤ n) :
    powLinearBinomTerm f g (n + 1) (k + 1) =
      f * powLinearBinomTerm f g n (k + 1) +
        g * powLinearBinomTerm f g n k := by
  by_cases hlt : k < n
  · exact powLinearBinomTerm_succ_succ_of_lt f g hlt
  · have hk_eq : k = n := by omega
    subst k
    exact powLinearBinomTerm_succ_succ_top f g n

/-- The row recurrence from Pascal's rule: the partial sum at row `n+1` splits as `f * (sum n (m+1)) + g * (sum n m)`. -/
private theorem powLinearBinomSum_succ_row
    (f g : FpPoly p) (n m : Nat) (hm : m ≤ n + 1) :
    powLinearBinomSum f g (n + 1) (m + 1) =
      f * powLinearBinomSum f g n (m + 1) +
        g * powLinearBinomSum f g n m := by
  induction m with
  | zero =>
      simp [powLinearBinomSum, powLinearBinomTerm_succ_zero]
  | succ m ih =>
      rw [powLinearBinomSum, ih (by omega), powLinearBinomSum, powLinearBinomSum,
        powLinearBinomTerm_succ_succ f g (by omega : m ≤ n)]
      have hdistL :
          f * (powLinearBinomSum f g n m + powLinearBinomTerm f g n m) =
            f * powLinearBinomSum f g n m + f * powLinearBinomTerm f g n m :=
        DensePoly.mul_add_right_poly f
          (powLinearBinomSum f g n m) (powLinearBinomTerm f g n m)
      have hdistR₁ :
          f * (powLinearBinomSum f g n (m + 1) +
              powLinearBinomTerm f g n (m + 1)) =
            f * powLinearBinomSum f g n (m + 1) +
              f * powLinearBinomTerm f g n (m + 1) :=
        DensePoly.mul_add_right_poly f
          (powLinearBinomSum f g n (m + 1)) (powLinearBinomTerm f g n (m + 1))
      have hdistR₂ :
          g * (powLinearBinomSum f g n m + powLinearBinomTerm f g n m) =
            g * powLinearBinomSum f g n m + g * powLinearBinomTerm f g n m :=
        DensePoly.mul_add_right_poly g
          (powLinearBinomSum f g n m) (powLinearBinomTerm f g n m)
      rw [hdistL, hdistR₁, hdistR₂]
      have hsum :
          powLinearBinomSum f g n (m + 1) =
            powLinearBinomSum f g n m + powLinearBinomTerm f g n m := rfl
      rw [hsum, ← hdistL]
      apply DensePoly.ext_coeff
      intro i
      repeat rw [DensePoly.coeff_add_semiring]
      grind

/-- A binomial term with index `k` above the degree `n` vanishes. -/
private theorem powLinearBinomTerm_above
    (f g : FpPoly p) {n k : Nat} (hk : n < k) :
    powLinearBinomTerm f g n k = 0 := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_eq_zero_of_lt hk]
  exact powLinearBinom_scalar_zero _

/-- Extending the partial sum one step past the diagonal adds nothing, since that term vanishes. -/
private theorem powLinearBinomSum_top_succ
    (f g : FpPoly p) (n : Nat) :
    powLinearBinomSum f g n (n + 1 + 1) =
      powLinearBinomSum f g n (n + 1) := by
  rw [powLinearBinomSum, powLinearBinomTerm_above f g (by omega : n < n + 1)]
  exact DensePoly.add_zero_poly _

/-- The binomial theorem: `(f + g)^n` equals its full binomial sum over the first `n + 1` terms. -/
private theorem powLinear_add_binom_sum
    (f g : FpPoly p) (n : Nat) :
    powLinear (f + g) n = powLinearBinomSum f g n (n + 1) := by
  induction n with
  | zero =>
      simp [powLinear, powLinearBinomSum, powLinearBinomTerm, Hex.Nat.choose]
      exact (powLinearBinom_scalar_one (1 : FpPoly p)).symm
  | succ n ih =>
      rw [powLinear_succ_left, ih, powLinearBinomSum_succ_row f g n (n + 1) (by omega),
        powLinearBinomSum_top_succ f g n]
      exact DensePoly.mul_add_left_poly f g (powLinearBinomSum f g n (n + 1))

/-- The zeroth term of the degree-`p` binomial expansion is `f^p`. -/
private theorem powLinearBinomTerm_prime_zero (f g : FpPoly p) :
    powLinearBinomTerm f g p 0 = powLinear f p := by
  unfold powLinearBinomTerm
  simp
  change DensePoly.scale (1 : ZMod64 p) (powLinear f p * powLinear g 0) =
    powLinear f p
  rw [powLinearBinom_scalar_one]
  exact DensePoly.mul_one_right_poly (powLinear f p)

/-- The top term of the degree-`p` binomial expansion is `g^p`. -/
private theorem powLinearBinomTerm_prime_top (f g : FpPoly p) :
    powLinearBinomTerm f g p p = powLinear g p := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_self]
  have hsub : p - p = 0 := by omega
  rw [hsub]
  change DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g p) =
    powLinear g p
  rw [powLinearBinom_scalar_one]
  exact one_mul (powLinear g p)

/-- For prime `p` and `0 < k < p`, the middle binomial terms vanish, since `p` divides the binomial coefficient. -/
private theorem powLinearBinomTerm_prime_middle
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) {k : Nat} (hk0 : 0 < k) (hkp : k < p) :
    powLinearBinomTerm f g p k = 0 := by
  unfold powLinearBinomTerm
  rw [zmod64_natCast_choose_prime_eq_zero hp hk0 hkp]
  exact powLinearBinom_scalar_zero _

/-- For prime `p` and `m < p`, the partial sum through the vanishing middle terms collapses to `f^p`. -/
private theorem powLinearBinomSum_prime_middle
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) {m : Nat} (hm : m < p) :
    powLinearBinomSum f g p (m + 1) = powLinear f p := by
  induction m with
  | zero =>
      rw [powLinearBinomSum, powLinearBinomTerm_prime_zero]
      exact DensePoly.zero_add _
  | succ m ih =>
      rw [powLinearBinomSum, ih (by omega),
        powLinearBinomTerm_prime_middle hp f g (by omega : 0 < m + 1) (by omega)]
      exact DensePoly.add_zero_poly _

/-- The freshman's-dream identity `(f + g)^p = f^p + g^p` for prime `p`. -/
private theorem powLinear_add_prime
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) :
    powLinear (f + g) p = powLinear f p + powLinear g p := by
  have hp_two : 2 ≤ p := Hex.Nat.Prime.two_le hp
  have hp_pos : 0 < p := by omega
  rw [powLinear_add_binom_sum, powLinearBinomSum]
  have hmid : powLinearBinomSum f g p p = powLinear f p := by
    have hmid0 :
        powLinearBinomSum f g p ((p - 1) + 1) = powLinear f p :=
      powLinearBinomSum_prime_middle hp f g (by omega : p - 1 < p)
    simpa [Nat.sub_add_cancel hp_pos] using hmid0
  rw [hmid, powLinearBinomTerm_prime_top]

/-- Multiply the factors in a square-free decomposition with their multiplicities. -/
@[expose]
def weightedProduct (factors : List (SquareFreeFactor p)) : FpPoly p :=
  factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1

/-- `weightedProduct` of the empty factor list is the constant polynomial `1`. -/
private theorem weightedProduct_nil :
    weightedProduct ([] : List (SquareFreeFactor p)) = 1 := by
  rfl

/-- Folding the weighted product from accumulator `acc` factors as `acc * weightedProduct factors`. -/
private theorem weightedProduct_foldl_eq_mul
    (acc : FpPoly p) (factors : List (SquareFreeFactor p)) :
    factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) acc =
      acc * weightedProduct factors := by
  induction factors generalizing acc with
  | nil =>
      rw [weightedProduct_nil]
      exact (DensePoly.mul_one_right_poly acc).symm
  | cons sf factors ih =>
      unfold weightedProduct
      simp only [List.foldl_cons]
      rw [ih (acc * pow sf.factor sf.multiplicity),
        ih ((1 : FpPoly p) * pow sf.factor sf.multiplicity)]
      have hone :
          (1 : FpPoly p) * pow sf.factor sf.multiplicity =
            pow sf.factor sf.multiplicity := by
        exact one_mul (pow sf.factor sf.multiplicity)
      rw [hone]
      exact DensePoly.mul_assoc_poly acc (pow sf.factor sf.multiplicity) (weightedProduct factors)

/-- `weightedProduct` of a cons splits off the head factor raised to its multiplicity. -/
private theorem weightedProduct_cons
    (sf : SquareFreeFactor p) (factors : List (SquareFreeFactor p)) :
    weightedProduct (sf :: factors) =
      pow sf.factor sf.multiplicity * weightedProduct factors := by
  unfold weightedProduct
  simp only [List.foldl_cons]
  rw [weightedProduct_foldl_eq_mul]
  exact congrArg (fun x => x * weightedProduct factors) (one_mul (pow sf.factor sf.multiplicity))

/-- `weightedProduct` of an append is the product of the two sublist weighted products. -/
private theorem weightedProduct_append
    (left right : List (SquareFreeFactor p)) :
    weightedProduct (left ++ right) = weightedProduct left * weightedProduct right := by
  unfold weightedProduct
  rw [List.foldl_append]
  simpa [weightedProduct] using
    weightedProduct_foldl_eq_mul
      (p := p)
      (left.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1)
      right

/-- `weightedProduct` of a singleton is that factor raised to its multiplicity. -/
private theorem weightedProduct_singleton (sf : SquareFreeFactor p) :
    weightedProduct [sf] = pow sf.factor sf.multiplicity := by
  rw [weightedProduct_cons, weightedProduct_nil]
  exact DensePoly.mul_one_right_poly (pow sf.factor sf.multiplicity)

/-- `weightedProduct` of a reversed cons appends the new factor's power on the right. -/
private theorem weightedProduct_reverse_cons
    (sf : SquareFreeFactor p) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (sf :: accRev).reverse =
      weightedProduct accRev.reverse * pow sf.factor sf.multiplicity := by
  rw [List.reverse_cons, weightedProduct_append, weightedProduct_singleton]

/--
Extract the formal `p`-th root by keeping exactly the coefficients whose
degrees are multiples of `p`.
-/
@[expose]
def pthRoot (f : FpPoly p) : FpPoly p :=
  let rootSize := (f.size + p - 1) / p
  ofCoeffs <|
    (List.range rootSize).map (fun i => f.coeff (i * p)) |>.toArray

/-- Below the root size, `pthRoot f` reads coefficient `i` from `f` at degree `i * p`. -/
private theorem pthRoot_coeff_of_lt
    (f : FpPoly p) {i : Nat} (hi : i < (f.size + p - 1) / p) :
    (pthRoot f).coeff i = f.coeff (i * p) := by
  unfold pthRoot ofCoeffs
  rw [DensePoly.coeff_ofCoeffs]
  simp [Array.getD, hi]

/-- Every coefficient of `pthRoot f` is the coefficient of `f` at the `p`-fold degree `i * p`. -/
private theorem pthRoot_coeff (f : FpPoly p) (i : Nat) :
    (pthRoot f).coeff i = f.coeff (i * p) := by
  by_cases hi : i < (f.size + p - 1) / p
  · exact pthRoot_coeff_of_lt f hi
  · unfold pthRoot ofCoeffs
    rw [DensePoly.coeff_ofCoeffs]
    simp [Array.getD, hi]
    exact (DensePoly.coeff_eq_zero_of_size_le f (by
      have hp : 0 < p := ZMod64.Bounds.pPos (p := p)
      have hle : (f.size + p - 1) / p ≤ i := Nat.le_of_not_gt hi
      have hraw : f.size + p - 1 ≤ i * p + p - 1 :=
        (Nat.div_le_iff_le_mul hp).mp hle
      omega)).symm

/-- Right additive identity for a `ZMod64 p` coefficient. -/
private theorem zmod64_add_zero_coeff (a : ZMod64 p) :
    a + 0 = a := by
  grind

/-- Left additive identity for a `ZMod64 p` coefficient. -/
private theorem zmod64_zero_add_coeff (a : ZMod64 p) :
    0 + a = a := by
  grind

/-- The sum of two zero `ZMod64 p` coefficients is zero. -/
private theorem zmod64_add_zero_zero_coeff :
    (0 : ZMod64 p) + 0 = 0 := by
  grind

/-- The single coefficient contribution `g_i x^i`, represented with dense shifts. -/
private def coeffTerm (g : FpPoly p) (i : Nat) : FpPoly p :=
  DensePoly.shift i (DensePoly.scale (g.coeff i) (1 : FpPoly p))

/-- Finite sum of the coefficient contributions of `g` below the bound `m`. -/
private def coeffFold (g : FpPoly p) (m : Nat) : FpPoly p :=
  (List.range m).foldl (fun acc i => acc + coeffTerm g i) 0

/-- Project a monomial coefficient contribution back to a dense coefficient. -/
private theorem coeffTerm_coeff (g : FpPoly p) (i n : Nat) :
    (coeffTerm g i).coeff n = if n = i then g.coeff i else 0 := by
  unfold coeffTerm
  have hzero : g.coeff i * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_shift_scale i (g.coeff i) (1 : FpPoly p) n hzero]
  by_cases hlt : n < i
  · simp only [hlt, if_true]
    have hne : n ≠ i := by omega
    simp [hne]
    rfl
  · simp only [hlt, if_false]
    change g.coeff i * (DensePoly.C (1 : ZMod64 p)).coeff (n - i) =
      if n = i then g.coeff i else 0
    rw [DensePoly.coeff_C]
    by_cases hni : n = i
    · simp [hni]
    · have hsub : n - i ≠ 0 := by omega
      simp [hni, hsub]
      exact hzero

/-- The `k`th power of the single term `g_i x^i` contributes `(g_i)^k` only at degree `k * i`. -/
private theorem powLinear_coeffTerm_coeff (g : FpPoly p) (i k n : Nat) :
    (powLinear (coeffTerm g i) k).coeff n =
      if n = k * i then (g.coeff i) ^ k else 0 := by
  induction k generalizing n with
  | zero =>
      simp [powLinear]
      change (DensePoly.C (1 : ZMod64 p)).coeff n =
        if n = 0 then 1 else 0
      rw [DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
        change (0 : ZMod64 p) = (0 : ZMod64 p)
        rfl
  | succ k ih =>
      rw [powLinear]
      change (powLinear (coeffTerm g i) k *
          DensePoly.shift i (DensePoly.scale (g.coeff i) (1 : FpPoly p))).coeff n =
        if n = (k + 1) * i then (g.coeff i) ^ (k + 1) else 0
      rw [coeff_mul_shift_scale_one]
      by_cases hin : i ≤ n
      · rw [if_pos hin, ih]
        by_cases hprev : n - i = k * i
        · have hn : n = (k + 1) * i := by
            calc
              n = n - i + i := (Nat.sub_add_cancel hin).symm
              _ = k * i + i := by rw [hprev]
              _ = (k + 1) * i := by rw [Nat.succ_mul]
          rw [if_pos hprev, if_pos hn]
          exact (Lean.Grind.Semiring.pow_succ (g.coeff i) k).symm
        · have hn : n ≠ (k + 1) * i := by
            intro hn
            apply hprev
            calc
              n - i = (k + 1) * i - i := by rw [hn]
              _ = k * i := by rw [Nat.succ_mul]; omega
          rw [if_neg hprev, if_neg hn]
          grind
      · have hn : n ≠ (k + 1) * i := by
          intro hn
          have hki : i ≤ (k + 1) * i := by
            rw [Nat.succ_mul]
            omega
          omega
        rw [if_neg hin, if_neg hn]

/-- Coefficient projection for the bounded finite coefficient fold. -/
private theorem coeffFold_coeff (g : FpPoly p) (m n : Nat) :
    (coeffFold g m).coeff n = if n < m then g.coeff n else 0 := by
  induction m with
  | zero =>
      unfold coeffFold
      simp only [List.range_zero, List.foldl_nil]
      rw [DensePoly.coeff_zero]
      simp
      rfl
  | succ m ih =>
      unfold coeffFold
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change ((List.range m).foldl (fun acc i => acc + coeffTerm g i) 0 +
          coeffTerm g m).coeff n = if n < m + 1 then g.coeff n else 0
      rw [DensePoly.coeff_add_semiring]
      change (coeffFold g m).coeff n + (coeffTerm g m).coeff n =
        if n < m + 1 then g.coeff n else 0
      rw [ih, coeffTerm_coeff]
      by_cases hlt : n < m
      · rw [if_pos hlt]
        have hne : n ≠ m := by omega
        rw [if_neg hne, if_pos (by omega : n < m + 1)]
        exact zmod64_add_zero_coeff (g.coeff n)
      · by_cases heq : n = m
        · rw [if_neg hlt]
          rw [if_pos heq, if_pos (by omega : n < m + 1), heq]
          exact zmod64_zero_add_coeff (g.coeff m)
        · have hsucc : ¬n < m + 1 := by omega
          rw [if_neg hlt, if_neg heq, if_neg hsucc]
          exact zmod64_add_zero_zero_coeff

/-- Any coefficient fold whose bound reaches `g.size` reconstructs `g`. -/
private theorem coeffFold_eq_of_size_le (g : FpPoly p) (m : Nat) (hm : g.size ≤ m) :
    coeffFold g m = g := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeffFold_coeff]
  by_cases hn : n < m
  · simp [hn]
  · simp [hn]
    exact (DensePoly.coeff_eq_zero_of_size_le g (by omega)).symm

/-- Reconstruct a polynomial from exactly its stored coefficient range. -/
private theorem coeffFold_size_eq (g : FpPoly p) :
    coeffFold g g.size = g := by
  exact coeffFold_eq_of_size_le g g.size (Nat.le_refl g.size)

/--
Coefficient expansion for a power of a bounded coefficient fold.

The successor case is the finite schoolbook convolution of the already
expanded `k` choices with one more bounded coefficient choice from `g`.
-/
private def coeffFoldPowerCoeff (g : FpPoly p) (m : Nat) : Nat → Nat → ZMod64 p
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n =>
      (List.range (powLinear (coeffFold g m) k).size).foldl
        (fun acc i =>
          acc + coeffFoldPowerCoeff g m k i *
            (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0))
        0

/-- Coefficient `n` of `(coeffFold g m)^k` equals the recursive expansion `coeffFoldPowerCoeff g m k n`. -/
private theorem powLinear_coeffFold_coeff_expansion (g : FpPoly p) (m k n : Nat) :
    (powLinear (coeffFold g m) k).coeff n = coeffFoldPowerCoeff g m k n := by
  induction k generalizing n with
  | zero =>
      simp [powLinear, coeffFoldPowerCoeff]
      change (DensePoly.C (1 : ZMod64 p)).coeff n = if n = 0 then 1 else 0
      exact DensePoly.coeff_C (1 : ZMod64 p) n
  | succ k ih =>
      rw [powLinear, coeff_mul]
      unfold mulCoeffSum
      simp only [coeffFoldPowerCoeff]
      let xs := List.range (powLinear (coeffFold g m) k).size
      change xs.foldl
          (fun acc i => acc + mulCoeffTerm (powLinear (coeffFold g m) k) (coeffFold g m) n i)
          0 =
        xs.foldl
          (fun acc i =>
            acc + coeffFoldPowerCoeff g m k i *
              (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0))
          0
      suffices hfold :
          ∀ acc,
            xs.foldl
                (fun acc i =>
                  acc + mulCoeffTerm (powLinear (coeffFold g m) k) (coeffFold g m) n i)
                acc =
              xs.foldl
                (fun acc i =>
                  acc + coeffFoldPowerCoeff g m k i *
                    (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0))
                acc by
        exact hfold 0
      intro acc
      induction xs generalizing acc with
      | nil =>
          rfl
      | cons i xs ihxs =>
          simp only [List.foldl_cons]
          have hterm :
              mulCoeffTerm (powLinear (coeffFold g m) k) (coeffFold g m) n i =
                coeffFoldPowerCoeff g m k i *
                  (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0) := by
            unfold mulCoeffTerm
            rw [ih, coeffFold_coeff]
            by_cases hni : n < i
            · simp [hni]
            · simp [hni]
          rw [hterm]
          exact ihxs _

/-- Specialises the coefficient expansion of `(coeffFold g m)^k` to the prime exponent `k = p`. -/
private theorem powLinear_coeffFold_prime_coeff_expansion (g : FpPoly p) (m n : Nat) :
    (powLinear (coeffFold g m) p).coeff n = coeffFoldPowerCoeff g m p n :=
  powLinear_coeffFold_coeff_expansion g m p n

/--
Prime-characteristic cancellation for the recursive coefficient expansion of
`(coeffFold g m)^p`: all mixed `p`-tuples vanish, leaving only diagonal
choices from the bounded coefficient fold.
-/
private theorem coeffFoldPowerCoeff_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    coeffFoldPowerCoeff g m p n =
      if n % p = 0 then
        if n / p < m then (g.coeff (n / p)) ^ p else 0
      else
        0 := by
  have hp_pos : 0 < p := by
    have hp2 := Hex.Nat.Prime.two_le hp
    omega
  rw [← powLinear_coeffFold_prime_coeff_expansion]
  induction m with
  | zero =>
      have hcoeffFold_zero : coeffFold g 0 = 0 := by
        unfold coeffFold
        simp [List.range_zero]
      rw [hcoeffFold_zero]
      have hpow_zero_p_coeff : (powLinear (0 : FpPoly p) p).coeff n = 0 := by
        have hgeneral : ∀ k, 0 < k →
            (powLinear (0 : FpPoly p) k).coeff n = 0 := by
          intro k hk
          cases k with
          | zero => omega
          | succ k' =>
              rw [powLinear, powLinearBinom_mul_zero]
              exact DensePoly.coeff_zero n
        exact hgeneral p hp_pos
      rw [hpow_zero_p_coeff]
      have hne : ¬ n / p < 0 := Nat.not_lt_zero _
      by_cases hmod : n % p = 0
      · rw [if_pos hmod, if_neg hne]
      · rw [if_neg hmod]
  | succ m ih =>
      have hsucc : coeffFold g (m + 1) = coeffFold g m + coeffTerm g m := by
        unfold coeffFold
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
      rw [hsucc, powLinear_add_prime hp,
        DensePoly.coeff_add_semiring,
        ih, powLinear_coeffTerm_coeff]
      by_cases hmod : n % p = 0
      · rw [if_pos hmod, if_pos hmod]
        have hn_eq : n = p * (n / p) := by
          have hdiv := Nat.div_add_mod n p
          omega
        by_cases hlt : n / p < m
        · rw [if_pos hlt]
          have hne : n ≠ p * m := by
            intro heq
            have hmul : p * (n / p) = p * m := by rw [← hn_eq]; exact heq
            have hdivm : n / p = m := Nat.eq_of_mul_eq_mul_left hp_pos hmul
            omega
          rw [if_neg hne]
          have hltsucc : n / p < m + 1 := by omega
          rw [if_pos hltsucc]
          exact zmod64_add_zero_coeff (g.coeff (n / p) ^ p)
        · rw [if_neg hlt]
          by_cases heq : n / p = m
          · have hnm : n = p * m := by rw [hn_eq, heq]
            rw [if_pos hnm]
            have hltsucc : n / p < m + 1 := by omega
            rw [if_pos hltsucc, heq]
            exact zmod64_zero_add_coeff (g.coeff m ^ p)
          · have hne : n ≠ p * m := by
              intro habs
              have hmul : p * (n / p) = p * m := by rw [← hn_eq]; exact habs
              have hdivm : n / p = m := Nat.eq_of_mul_eq_mul_left hp_pos hmul
              exact heq hdivm
            rw [if_neg hne]
            have hltsucc : ¬ n / p < m + 1 := by omega
            rw [if_neg hltsucc]
            exact zmod64_add_zero_zero_coeff
      · rw [if_neg hmod, if_neg hmod]
        have hne : n ≠ p * m := by
          intro heq
          have hmodzero : n % p = 0 := by
            rw [heq]
            exact Nat.mul_mod_right p m
          exact hmod hmodzero
        rw [if_neg hne]
        exact zmod64_add_zero_zero_coeff

/-- Freshman's-dream coefficient of `(coeffFold g m)^p`: nonzero only at `p`-divisible degrees, where it is `(g.coeff (n/p))^p`. -/
private theorem powLinear_coeffFold_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    (powLinear (coeffFold g m) p).coeff n =
      if n % p = 0 then
        if n / p < m then (g.coeff (n / p)) ^ p else 0
      else
        0 := by
  rw [powLinear_coeffFold_prime_coeff_expansion]
  exact coeffFoldPowerCoeff_prime_coeff hp g m n

/--
Freshman's-dream coefficient support for a `p`th power over `F_p[x]`.
This is the dense-polynomial convolution fact needed by the formal
`p`-th-root reconstruction: only exponent tuples with all mass on one
input coefficient survive modulo `p`.
-/
private theorem powLinear_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (n : Nat) :
    (powLinear g p).coeff n =
      if n % p = 0 then g.coeff (n / p) ^ p else 0 := by
  calc
    (powLinear g p).coeff n =
        (powLinear (coeffFold g g.size) p).coeff n := by
          rw [coeffFold_size_eq g]
    _ =
        if n % p = 0 then
          if n / p < g.size then (g.coeff (n / p)) ^ p else 0
        else
          0 := by
            exact powLinear_coeffFold_prime_coeff hp g g.size n
    _ = if n % p = 0 then g.coeff (n / p) ^ p else 0 := by
          by_cases hn : n % p = 0
          · rw [if_pos hn]
            by_cases hsize : n / p < g.size
            · rw [if_pos hsize]
              rw [if_pos hn]
            · rw [if_neg hsize]
              have hcoeff : g.coeff (n / p) = 0 :=
                DensePoly.coeff_eq_zero_of_size_le g (by omega)
              rw [hcoeff, if_pos hn]
              exact (ZMod64.pow_prime hp (0 : ZMod64 p)).symm
          · rw [if_neg hn]
            rw [if_neg hn]

/--
Coefficient form of the prime-field Frobenius law for the formal `p`-th root:
the `p`th power restores coefficients in degrees divisible by `p` and has zero
coefficients elsewhere.
-/
private theorem pthRoot_pow_prime_coeff
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (n : Nat) :
    (pow (pthRoot f) p).coeff n =
      if n % p = 0 then f.coeff n else 0 := by
  rw [pow_eq_powLinear, powLinear_prime_coeff hp]
  by_cases hn : n % p = 0
  · simp [hn]
    have hmul : n / p * p = n := by
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hn))
    rw [pthRoot_coeff, hmul]
    exact ZMod64.pow_prime hp (f.coeff n)
  · simp [hn]

/-- A nonzero residue `a : ZMod64 p` over a prime modulus has `a.toNat` coprime to `p`. -/
private theorem zmod64_coprime_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    Nat.Coprime a.toNat p := by
  rw [Nat.Coprime]
  have hnot_dvd : ¬ p ∣ a.toNat := by
    intro hdiv
    rcases hdiv with ⟨k, hk⟩
    have ha_pos : 0 < a.toNat := by
      by_cases hnat : a.toNat = 0
      · exfalso
        apply ha
        apply ZMod64.ext
        apply UInt64.toNat_inj.mp
        exact hnat
      · exact Nat.pos_of_ne_zero hnat
    have hk_pos : 0 < k := by
      cases k with
      | zero =>
          exfalso
          have : a.toNat = 0 := by simpa using hk
          omega
      | succ k => exact Nat.succ_pos k
    have hle : p ≤ a.toNat := by
      rw [hk]
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p hk_pos
    exact (Nat.not_le_of_gt a.toNat_lt) hle
  have hgcd_dvd_p : Nat.gcd a.toNat p ∣ p := Nat.gcd_dvd_right a.toNat p
  rcases hp.2 (Nat.gcd a.toNat p) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply hnot_dvd
    rcases Nat.gcd_dvd_left a.toNat p with ⟨k, hk⟩
    rw [hgcd] at hk
    exact ⟨k, hk⟩

/-- `a * a⁻¹ = 1` for any nonzero `a : ZMod64 p` over a prime modulus. -/
private theorem zmod64_mul_inv_eq_one_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hcop := zmod64_coprime_of_prime_ne_zero hp ha
  have hinv : (a⁻¹ * a).toNat = (1 : ZMod64 p).toNat := by
    exact ZMod64.inv_mul_eq_one (p := p) a hcop
  have hcomm : a * a⁻¹ = a⁻¹ * a := by grind
  rw [hcomm]
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using hinv

/-- `(1 : ZMod64 p)` is nonzero over a prime modulus. -/
private theorem zmod64_one_ne_zero_of_prime
    (hp : Hex.Nat.Prime p) :
    (1 : ZMod64 p) ≠ 0 := by
  intro hone
  have hnat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat hone
  change (ZMod64.one : ZMod64 p).toNat = (ZMod64.zero : ZMod64 p).toNat at hnat
  have hp_gt : 1 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  rw [ZMod64.toNat_one, ZMod64.toNat_zero, Nat.mod_eq_of_lt hp_gt] at hnat
  omega

/-- `isOne` returns `true` on the constant polynomial `1 : FpPoly p` over a prime modulus. -/
private theorem isOne_one [ZMod64.PrimeModulus p] :
    isOne (1 : FpPoly p) = true := by
  unfold isOne
  have hone_ne : (1 : ZMod64 p) ≠ 0 :=
    zmod64_one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p))
  have hcoeffs : (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
    DensePoly.coeffs_C_of_ne_zero hone_ne
  have hsize : (1 : FpPoly p).size = 1 := by
    simpa [DensePoly.size] using congrArg Array.size hcoeffs
  have hdegree : (1 : FpPoly p).degree? = some 0 := by
    unfold DensePoly.degree?
    simp [hsize]
  rw [hdegree]
  have hcoeff0 : (1 : FpPoly p).coeff 0 = (1 : ZMod64 p) := by
    change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (1 : ZMod64 p)
    rw [DensePoly.coeff_C]
    simp
  simp [hcoeff0]

/-- The inverse `a⁻¹` of a nonzero `a : ZMod64 p` is itself nonzero over a prime modulus. -/
private theorem zmod64_inv_ne_zero_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 := by
  intro hinv
  have hone := zmod64_mul_inv_eq_one_of_prime_ne_zero hp ha
  rw [hinv] at hone
  have hzero : a * (0 : ZMod64 p) = 0 := by grind
  rw [hzero] at hone
  exact zmod64_one_ne_zero_of_prime hp hone.symm

/-- `a * 0 = 0` in `ZMod64 p`. -/
private theorem zmod64_mul_zero (a : ZMod64 p) :
    a * 0 = 0 := by
  grind

/-- Nonzero executable `FpPoly` values have nonzero leading coefficient.

The proof converts `isZero = false` to positive dense-polynomial size, then
uses the invariant that the last stored coefficient of a positive-size dense
polynomial is nonzero. -/
theorem fpPoly_leadingCoeff_ne_zero_of_isZero_false
    (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.leadingCoeff f ≠ 0 := by
  have hpos : 0 < f.size := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
      Nat.pos_iff_ne_zero] using hzero
  have hlast := DensePoly.coeff_last_ne_zero_of_pos_size f hpos
  have hlead : DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
    simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
  rw [hlead]
  exact hlast

/-- Split off the leading coefficient so the recursive Yun loop can work on a monic input. -/
@[expose]
def normalizeMonic (f : FpPoly p) : ZMod64 p × FpPoly p :=
  if f.isZero then
    (0, 0)
  else
    let unit := DensePoly.leadingCoeff f
    (unit, DensePoly.scale unit⁻¹ f)

/-- `normalizeMonic` returns `(0, 0)` on a zero input polynomial. -/
private theorem normalizeMonic_zero
    (f : FpPoly p) (hzero : f.isZero = true) :
    normalizeMonic f = (0, 0) := by
  simp [normalizeMonic, hzero]

/-- An `FpPoly p` whose `isZero` flag is `true` equals the zero polynomial. -/
private theorem eq_zero_of_isZero_true
    (f : FpPoly p) (hzero : f.isZero = true) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : f.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero
  rw [DensePoly.coeff_eq_zero_of_size_le f (by omega)]
  exact DensePoly.coeff_zero n

/-- `DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2` reconstructs a zero `f`. -/
private theorem normalizeMonic_zero_reconstruct
    (f : FpPoly p) (hzero : f.isZero = true) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_zero f hzero, eq_zero_of_isZero_true f hzero]
  exact mul_zero (DensePoly.C (0 : ZMod64 p))

/-- On a nonzero `f`, `normalizeMonic f` is the pair of its leading coefficient and
`f` scaled by that coefficient's inverse. -/
private theorem normalizeMonic_nonzero
    (f : FpPoly p) (hzero : f.isZero = false) :
    normalizeMonic f =
      (DensePoly.leadingCoeff f, DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) := by
  simp [normalizeMonic, hzero]

/-- `DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2` reconstructs a nonzero `f`
over a prime modulus. -/
private theorem normalizeMonic_nonzero_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_nonzero f hzero, C_mul_eq_scale, scale_scale]
  have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  rw [zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne]
  exact scale_one_left f

/-- `DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2` reconstructs `f` for every
input over a prime modulus. -/
private theorem normalizeMonic_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  cases hzero : f.isZero
  · exact normalizeMonic_nonzero_reconstruct hp f hzero
  · exact normalizeMonic_zero_reconstruct f hzero

/-- The polynomial part `(normalizeMonic f).2` is monic whenever `f` is nonzero. -/
private theorem normalizeMonic_nonzero_monic
    [ZMod64.PrimeModulus p] (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.Monic (normalizeMonic f).2 := by
  rw [normalizeMonic_nonzero f hzero]
  have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hinv_ne : (DensePoly.leadingCoeff f)⁻¹ ≠ (0 : ZMod64 p) := by
    intro hinv
    change ZMod64.inv (DensePoly.leadingCoeff f) = (0 : ZMod64 p) at hinv
    have hone := ZMod64.inv_mul_eq_one_of_prime
      (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
    rw [hinv] at hone
    have hzero_mul : (0 : ZMod64 p) * DensePoly.leadingCoeff f = 0 := by grind
    rw [hzero_mul] at hone
    exact zmod64_one_ne_zero_of_prime
      (ZMod64.PrimeModulus.prime (p := p)) hone.symm
  unfold DensePoly.Monic
  have hfsize : f.size ≠ 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
      Bool.not_eq_true] using hzero
  rw [leadingCoeff_scale_of_ne_zero_of_nonzero (p := p) hinv_ne f hfsize]
  exact ZMod64.inv_mul_eq_one_of_prime
    (ZMod64.PrimeModulus.prime (p := p)) hlead_ne

/-- The polynomial part `(normalizeMonic f).2` is nonzero whenever `f` is nonzero. -/
private theorem normalizeMonic_nonzero_isZero_false
    [ZMod64.PrimeModulus p] (f : FpPoly p) (hzero : f.isZero = false) :
    (normalizeMonic f).2.isZero = false := by
  rw [normalizeMonic_nonzero f hzero]
  have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hinv_ne : (DensePoly.leadingCoeff f)⁻¹ ≠ (0 : ZMod64 p) := by
    intro hinv
    change ZMod64.inv (DensePoly.leadingCoeff f) = (0 : ZMod64 p) at hinv
    have hone := ZMod64.inv_mul_eq_one_of_prime
      (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
    rw [hinv] at hone
    have hzero_mul : (0 : ZMod64 p) * DensePoly.leadingCoeff f = 0 := by grind
    rw [hzero_mul] at hone
    exact zmod64_one_ne_zero_of_prime
      (ZMod64.PrimeModulus.prime (p := p)) hone.symm
  have hsize :
      (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = f.size :=
    scale_size_eq_of_ne_zero (p := p) hinv_ne f
  have hpos : 0 < (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size := by
    rw [hsize]
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
      Nat.pos_iff_ne_zero] using hzero
  simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
    Nat.pos_iff_ne_zero] using hpos

/-- Monic-normalized gcd: the canonical monic associate of `DensePoly.gcd c w`.

Routing the Yun square-free loop's gcd through this keeps every intermediate
polynomial monic. A raw `DensePoly.gcd` of a coprime pair can be a non-trivial
constant unit over `F_p` for `p > 2` (e.g. `gcd (x^2+1) (x+1) = 2` over `F_5`);
emitting `c / gcd c w` then leaks that scalar into the square-free factor,
breaking the exact reconstruction `weightedProduct = f`. The monic associate
divides `c` and `w` exactly as the raw gcd does, so every reconstruction
identity carries over, but the emitted quotient stays monic. -/
@[expose]
def monicGcd (c w : FpPoly p) : FpPoly p :=
  (normalizeMonic (DensePoly.gcd c w)).2

/-- Definitional unfolding lemma for `monicGcd`. The def itself is sealed
`@[irreducible]` (below) to keep `normalizeMonic` from being unfolded by
`simp`/`decide` during defeq, which otherwise causes kernel-reduction timeouts;
this lemma is the controlled re-entry point. -/
private theorem monicGcd_def (c w : FpPoly p) :
    monicGcd c w = (normalizeMonic (DensePoly.gcd c w)).2 := rfl

attribute [irreducible] monicGcd

/-- The raw gcd is a constant multiple of `monicGcd`, recovered from
`normalizeMonic_reconstruct`. -/
private theorem gcd_eq_C_mul_monicGcd
    (hp : Hex.Nat.Prime p) (c w : FpPoly p) :
    DensePoly.C (normalizeMonic (DensePoly.gcd c w)).1 * monicGcd c w =
      DensePoly.gcd c w := by
  rw [monicGcd_def]; exact normalizeMonic_reconstruct hp (DensePoly.gcd c w)

/-- `monicGcd c w` divides the raw gcd (they are associates). -/
private theorem monicGcd_dvd_gcd
    (hp : Hex.Nat.Prime p) (c w : FpPoly p) :
    monicGcd c w ∣ DensePoly.gcd c w :=
  ⟨DensePoly.C (normalizeMonic (DensePoly.gcd c w)).1, by
    rw [mul_comm]; exact (gcd_eq_C_mul_monicGcd hp c w).symm⟩

/-- `monicGcd c w` divides `c`. -/
private theorem monicGcd_dvd_left
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (c w : FpPoly p) :
    monicGcd c w ∣ c := by
  obtain ⟨q1, h1⟩ := monicGcd_dvd_gcd hp c w
  obtain ⟨q2, h2⟩ := DensePoly.gcd_dvd_left c w
  refine ⟨q1 * q2, ?_⟩
  calc c = DensePoly.gcd c w * q2 := h2
    _ = monicGcd c w * q1 * q2 := by rw [h1]
    _ = monicGcd c w * (q1 * q2) := DensePoly.mul_assoc_poly (monicGcd c w) q1 q2

/-- `monicGcd c w` divides `w`. -/
private theorem monicGcd_dvd_right
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (c w : FpPoly p) :
    monicGcd c w ∣ w := by
  obtain ⟨q1, h1⟩ := monicGcd_dvd_gcd hp c w
  obtain ⟨q2, h2⟩ := DensePoly.gcd_dvd_right c w
  refine ⟨q1 * q2, ?_⟩
  calc w = DensePoly.gcd c w * q2 := h2
    _ = monicGcd c w * q1 * q2 := by rw [h1]
    _ = monicGcd c w * (q1 * q2) := DensePoly.mul_assoc_poly (monicGcd c w) q1 q2

/-- Left exact-division reconstruction across `monicGcd`. -/
private theorem div_monicGcd_mul_reconstruct
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (c w : FpPoly p) :
    (c / monicGcd c w) * monicGcd c w = c := by
  have hspec := DensePoly.div_mul_add_mod c (monicGcd c w)
  have hmod : c % monicGcd c w = 0 :=
    DensePoly.mod_eq_zero_of_dvd c (monicGcd c w) (monicGcd_dvd_left hp c w)
  rw [hmod, add_zero] at hspec
  exact hspec

/-- Right exact-division reconstruction across `monicGcd`. -/
private theorem div_monicGcd_right_mul_reconstruct
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (c w : FpPoly p) :
    (w / monicGcd c w) * monicGcd c w = w := by
  have hspec := DensePoly.div_mul_add_mod w (monicGcd c w)
  have hmod : w % monicGcd c w = 0 :=
    DensePoly.mod_eq_zero_of_dvd w (monicGcd c w) (monicGcd_dvd_right hp c w)
  rw [hmod, add_zero] at hspec
  exact hspec

/-- `monicGcd c w` is monic whenever the raw gcd is nonzero. -/
private theorem monicGcd_monic_of_gcd_nonzero
    [ZMod64.PrimeModulus p] (c w : FpPoly p)
    (hgcd : (DensePoly.gcd c w).isZero = false) :
    DensePoly.Monic (monicGcd c w) := by
  rw [monicGcd_def]; exact normalizeMonic_nonzero_monic (DensePoly.gcd c w) hgcd

/-- `monicGcd c w` is nonzero whenever the raw gcd is nonzero. -/
private theorem monicGcd_isZero_false_of_gcd_nonzero
    [ZMod64.PrimeModulus p] (c w : FpPoly p)
    (hgcd : (DensePoly.gcd c w).isZero = false) :
    (monicGcd c w).isZero = false := by
  rw [monicGcd_def]; exact normalizeMonic_nonzero_isZero_false (DensePoly.gcd c w) hgcd

/-! ### Scalar-multiple algebra foundations

Foundational `FpPoly p` algebra for transporting `DensePoly.derivative`,
`DensePoly.gcd`, and exact division across a common nonzero scalar multiple
`DensePoly.C u * f`. These lemmas underpin the Yun split-synchronization
theorem used by the square-free decomposition correctness chain.
-/

/-- The constant polynomial `DensePoly.C u` is nonzero whenever the scalar `u` is nonzero. -/
private theorem C_ne_zero_of_ne_zero {u : ZMod64 p} (hu : u ≠ 0) :
    (DensePoly.C u : FpPoly p) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hzero
  change (DensePoly.C u : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
  simp at hcoeff
  exact hu hcoeff

/--
Left cancellation by a nonzero constant polynomial: `C u · a = C u · b ⇒ a = b`.
Reduces to right cancellation via commutativity.
-/
private theorem C_mul_left_cancel
    [ZMod64.PrimeModulus p] {u : ZMod64 p} (hu : u ≠ 0) {a b : FpPoly p}
    (h : DensePoly.C u * a = DensePoly.C u * b) : a = b := by
  have hcomm_a : a * DensePoly.C u = DensePoly.C u * a :=
    DensePoly.mul_comm_poly a (DensePoly.C u : FpPoly p)
  have hcomm_b : b * DensePoly.C u = DensePoly.C u * b :=
    DensePoly.mul_comm_poly b (DensePoly.C u : FpPoly p)
  apply mul_right_cancel_of_ne_zero (C_ne_zero_of_ne_zero hu)
  rw [hcomm_a, hcomm_b]
  exact h

/--
Divisibility is preserved when multiplying both sides by a common constant scalar.
-/
private theorem C_mul_dvd_C_mul_of_dvd (u : ZMod64 p) {a b : FpPoly p}
    (h : a ∣ b) : DensePoly.C u * a ∣ DensePoly.C u * b := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc DensePoly.C u * b
      = DensePoly.C u * (a * k) := by rw [hk]
    _ = (DensePoly.C u * a) * k :=
        (DensePoly.mul_assoc_poly (DensePoly.C u : FpPoly p) a k).symm

/--
Divisibility cancellation by a nonzero constant scalar: if `C u · a ∣ C u · b`
then `a ∣ b`.
-/
private theorem dvd_of_C_mul_dvd_C_mul
    [ZMod64.PrimeModulus p] {u : ZMod64 p} (hu : u ≠ 0) {a b : FpPoly p}
    (h : DensePoly.C u * a ∣ DensePoly.C u * b) : a ∣ b := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply C_mul_left_cancel hu
  calc DensePoly.C u * b
      = DensePoly.C u * a * k := hk
    _ = DensePoly.C u * (a * k) := DensePoly.mul_assoc_poly _ _ _

/--
A size-one `FpPoly p` is a constant polynomial whose value is its `coeff 0`.
-/
private theorem eq_C_of_size_one
    {f : FpPoly p} (hsize : f.size = 1) :
    f = DensePoly.C (f.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  cases n with
  | zero =>
      rw [DensePoly.coeff_C]
      simp
  | succ n =>
      have hsize_le : f.size ≤ n + 1 := by omega
      rw [DensePoly.coeff_eq_zero_of_size_le f hsize_le, DensePoly.coeff_C]
      simp

/--
A size-one `FpPoly p` has nonzero `coeff 0` (its leading coefficient).
-/
private theorem coeff_zero_ne_zero_of_size_one
    {f : FpPoly p} (hsize : f.size = 1) :
    f.coeff 0 ≠ 0 := by
  have hpos : 0 < f.size := by omega
  have hlast := DensePoly.coeff_last_ne_zero_of_pos_size f hpos
  rw [hsize] at hlast
  exact hlast

/--
The size of `(1 : FpPoly p)` is one (its coefficient array stores `[1]`).
-/
private theorem one_size_eq
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) :
    (1 : FpPoly p).size = 1 := by
  show (DensePoly.C (1 : ZMod64 p) : FpPoly p).size = 1
  exact DensePoly.size_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)

/--
Polynomial units in `FpPoly p` (over a prime modulus) are size-one polynomials:
if `a * b = 1` then both factors have size one. The product-size identity
`size_mul_eq_add_sub_one` forces each size to one.
-/
private theorem size_eq_one_of_mul_eq_one
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) {a b : FpPoly p}
    (h : a * b = 1) :
    a.size = 1 ∧ b.size = 1 := by
  have hone_ne : (1 : FpPoly p) ≠ 0 := by
    intro hzero
    have hsize_one : (1 : FpPoly p).size = 1 := one_size_eq hp
    have hsize_zero : (1 : FpPoly p).size = 0 := by
      rw [hzero]; rfl
    omega
  have ha_ne : a ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at h
    exact hone_ne h.symm
  have hb_ne : b ≠ 0 := by
    intro hb
    rw [hb, mul_zero] at h
    exact hone_ne h.symm
  have ha_pos : 0 < a.size := size_pos_of_ne_zero ha_ne
  have hb_pos : 0 < b.size := size_pos_of_ne_zero hb_ne
  have hsize_mul := size_mul_eq_add_sub_one a b ha_ne hb_ne
  have hab_size : (a * b).size = 1 := by
    rw [h]; exact one_size_eq hp
  rw [hab_size] at hsize_mul
  omega

/--
Polynomial units in `FpPoly p` are scalar constants: if `a * b = 1` then there
exists `w ≠ 0` with `a = C w`. Combines `size_eq_one_of_mul_eq_one` with
`eq_C_of_size_one` and `coeff_zero_ne_zero_of_size_one`.
-/
private theorem eq_C_of_mul_eq_one
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) {a b : FpPoly p}
    (h : a * b = 1) :
    ∃ w : ZMod64 p, w ≠ 0 ∧ a = DensePoly.C w := by
  have hsize := (size_eq_one_of_mul_eq_one hp h).1
  refine ⟨a.coeff 0, coeff_zero_ne_zero_of_size_one hsize, ?_⟩
  exact eq_C_of_size_one hsize

/--
Gcd scalar-multiple bridge over a prime modulus: scaling both arguments of
`DensePoly.gcd` by the same nonzero constant scales the gcd by some nonzero
constant `v`. The proof uses Bezout (`xgcd_bezout`) to extract a candidate
generator and the `GcdLaws.dvd_gcd` package to show the two generators are
associates; the unit characterisation (`eq_C_of_mul_eq_one`) pins it as a
constant.
-/
private theorem gcd_C_mul_C_mul_eq_C_mul_gcd
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (u : ZMod64 p) (hu : u ≠ 0) (f g : FpPoly p) :
    ∃ v : ZMod64 p, v ≠ 0 ∧
      DensePoly.gcd (DensePoly.C u * f) (DensePoly.C u * g) =
        DensePoly.C v * DensePoly.gcd f g := by
  by_cases hgcd_zero : DensePoly.gcd f g = 0
  · -- gcd f g = 0 forces f = 0 and g = 0.
    have hf_zero : f = 0 := by
      have hdvd : DensePoly.gcd f g ∣ f := DensePoly.gcd_dvd_left f g
      rw [hgcd_zero] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [zero_mul] at hk
      exact hk
    have hg_zero : g = 0 := by
      have hdvd : DensePoly.gcd f g ∣ g := DensePoly.gcd_dvd_right f g
      rw [hgcd_zero] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [zero_mul] at hk
      exact hk
    refine ⟨1, zmod64_one_ne_zero_of_prime hp, ?_⟩
    have hCuf_zero : DensePoly.C u * f = (0 : FpPoly p) := by
      rw [hf_zero]
      exact mul_zero (DensePoly.C u : FpPoly p)
    have hCug_zero : DensePoly.C u * g = (0 : FpPoly p) := by
      rw [hg_zero]
      exact mul_zero (DensePoly.C u : FpPoly p)
    have hCmul_zero : DensePoly.C (1 : ZMod64 p) * DensePoly.gcd f g = (0 : FpPoly p) := by
      rw [hgcd_zero]
      exact mul_zero (DensePoly.C (1 : ZMod64 p) : FpPoly p)
    rw [hCuf_zero, hCug_zero, hCmul_zero, DensePoly.gcd_zero_zero]
  · -- gcd f g ≠ 0: build the scalar via Bezout + size analysis.
    have hCu_ne : (DensePoly.C u : FpPoly p) ≠ 0 := C_ne_zero_of_ne_zero hu
    let d : FpPoly p := DensePoly.gcd (DensePoly.C u * f) (DensePoly.C u * g)
    -- Bezout for the scaled inputs.
    obtain ⟨α, β, hbez⟩ :
        ∃ α β : FpPoly p,
          α * (DensePoly.C u * f) + β * (DensePoly.C u * g) = d :=
      ⟨(DensePoly.xgcd (DensePoly.C u * f) (DensePoly.C u * g)).left,
        (DensePoly.xgcd (DensePoly.C u * f) (DensePoly.C u * g)).right,
        (DensePoly.xgcd_bezout (DensePoly.C u * f) (DensePoly.C u * g)).trans
          (DensePoly.xgcd_gcd_eq_gcd (DensePoly.C u * f) (DensePoly.C u * g))⟩
    -- Rewrite the Bezout sum as `C u * (α * f + β * g)`.
    let P : FpPoly p := α * f + β * g
    have hd_eq : d = DensePoly.C u * P := by
      have hassoc_mul : ∀ x y : FpPoly p,
          x * (DensePoly.C u * y) = DensePoly.C u * (x * y) := by
        intro x y
        calc x * (DensePoly.C u * y)
            = (x * DensePoly.C u) * y :=
              (DensePoly.mul_assoc_poly x (DensePoly.C u : FpPoly p) y).symm
          _ = (DensePoly.C u * x) * y := by
              have hcomm : x * (DensePoly.C u : FpPoly p) = DensePoly.C u * x :=
                DensePoly.mul_comm_poly x (DensePoly.C u : FpPoly p)
              exact congrArg (fun z => z * y) hcomm
          _ = DensePoly.C u * (x * y) :=
              DensePoly.mul_assoc_poly (DensePoly.C u : FpPoly p) x y
      have hexpand : α * (DensePoly.C u * f) + β * (DensePoly.C u * g) =
          DensePoly.C u * (α * f + β * g) := by
        rw [hassoc_mul α f, hassoc_mul β g]
        exact (DensePoly.mul_add_right_poly (DensePoly.C u : FpPoly p) (α * f) (β * g)).symm
      rw [← hbez, hexpand]
    -- `d ∣ C u * f` and `d ∣ C u * g`, so `C u * P ∣ C u * f` and `C u * P ∣ C u * g`.
    have hd_dvd_l : d ∣ DensePoly.C u * f :=
      DensePoly.gcd_dvd_left (DensePoly.C u * f) (DensePoly.C u * g)
    have hd_dvd_r : d ∣ DensePoly.C u * g :=
      DensePoly.gcd_dvd_right (DensePoly.C u * f) (DensePoly.C u * g)
    have hP_dvd_f : P ∣ f := by
      apply dvd_of_C_mul_dvd_C_mul (u := u) hu
      rw [← hd_eq]
      exact hd_dvd_l
    have hP_dvd_g : P ∣ g := by
      apply dvd_of_C_mul_dvd_C_mul (u := u) hu
      rw [← hd_eq]
      exact hd_dvd_r
    have hP_dvd_gcd : P ∣ DensePoly.gcd f g :=
      DensePoly.dvd_gcd P f g hP_dvd_f hP_dvd_g
    -- Conversely, `C u * gcd f g ∣ C u * f` and `C u * gcd f g ∣ C u * g`, so
    -- `C u * gcd f g ∣ d = C u * P`, hence `gcd f g ∣ P`.
    have hCgcd_dvd_l : DensePoly.C u * DensePoly.gcd f g ∣ DensePoly.C u * f :=
      C_mul_dvd_C_mul_of_dvd u (DensePoly.gcd_dvd_left f g)
    have hCgcd_dvd_r : DensePoly.C u * DensePoly.gcd f g ∣ DensePoly.C u * g :=
      C_mul_dvd_C_mul_of_dvd u (DensePoly.gcd_dvd_right f g)
    have hCgcd_dvd_d : DensePoly.C u * DensePoly.gcd f g ∣ d :=
      DensePoly.dvd_gcd _ _ _ hCgcd_dvd_l hCgcd_dvd_r
    have hgcd_dvd_P : DensePoly.gcd f g ∣ P := by
      apply dvd_of_C_mul_dvd_C_mul (u := u) hu
      rw [← hd_eq]
      exact hCgcd_dvd_d
    -- Combine `P ∣ gcd f g` and `gcd f g ∣ P`: `P = gcd f g * k` and
    -- `gcd f g = P * k'`, hence `k * k' = 1` by cancellation.
    rcases hP_dvd_gcd with ⟨k', hk'⟩
    rcases hgcd_dvd_P with ⟨k, hk⟩
    have hk_unit : k * k' = 1 := by
      have hcalc : DensePoly.gcd f g * (k * k') = DensePoly.gcd f g := by
        calc DensePoly.gcd f g * (k * k')
            = (DensePoly.gcd f g * k) * k' :=
              (DensePoly.mul_assoc_poly (DensePoly.gcd f g) k k').symm
          _ = P * k' := by rw [← hk]
          _ = DensePoly.gcd f g := hk'.symm
      have hcalc2 : (k * k') * DensePoly.gcd f g = 1 * DensePoly.gcd f g := by
        rw [one_mul]
        calc (k * k') * DensePoly.gcd f g
            = DensePoly.gcd f g * (k * k') :=
              DensePoly.mul_comm_poly (k * k') (DensePoly.gcd f g)
          _ = DensePoly.gcd f g := hcalc
      exact mul_right_cancel_of_ne_zero hgcd_zero hcalc2
    -- k is a unit, hence k = C w for some w ≠ 0.
    obtain ⟨w, hw_ne, hk_eq⟩ := eq_C_of_mul_eq_one hp hk_unit
    -- Therefore P = gcd f g * C w = C w * gcd f g.
    have hP_eq : P = DensePoly.C w * DensePoly.gcd f g := by
      rw [hk, hk_eq]
      exact DensePoly.mul_comm_poly (DensePoly.gcd f g) (DensePoly.C w)
    -- Finally d = C u * P = C u * C w * gcd f g = C (u * w) * gcd f g.
    have huw_ne : u * w ≠ 0 := by
      intro hzero
      rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hh | hh
      · exact hu hh
      · exact hw_ne hh
    refine ⟨u * w, huw_ne, ?_⟩
    show d = DensePoly.C (u * w) * DensePoly.gcd f g
    rw [hd_eq, hP_eq]
    -- C u * (C w * gcd f g) = C (u * w) * gcd f g
    have hC_mul_C : (DensePoly.C u * DensePoly.C w : FpPoly p) = DensePoly.C (u * w) := by
      rw [C_mul_eq_scale]
      apply DensePoly.ext_coeff
      intro n
      have hzero : u * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero u
      rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C, DensePoly.coeff_C]
      cases n with
      | zero => rfl
      | succ n => exact hzero
    calc DensePoly.C u * (DensePoly.C w * DensePoly.gcd f g)
        = (DensePoly.C u * DensePoly.C w) * DensePoly.gcd f g :=
          (DensePoly.mul_assoc_poly (DensePoly.C u : FpPoly p) (DensePoly.C w)
            (DensePoly.gcd f g)).symm
      _ = DensePoly.C (u * w) * DensePoly.gcd f g := by rw [hC_mul_C]

/--
Two-`DensePoly.C` constants combine into a single `DensePoly.C` of the
product, in `FpPoly p`. Used by the asymmetric scalar bridges below to
fold scalar factors during cancellation.
-/
private theorem fpPoly_C_mul_C_eq (a b : ZMod64 p) :
    (DensePoly.C a * DensePoly.C b : FpPoly p) = DensePoly.C (a * b) := by
  rw [C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  have hzero : a * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero a
  rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => rfl
  | succ n => exact hzero

/--
Unit-scalar swap on a divisibility hypothesis: if `C u · d ∣ a` for a
nonzero scalar `u`, then for any other nonzero scalar `v`, `C v · d ∣ a`.
The witness is rescaled by `C (u · v⁻¹)` so that
`(C v · d) · (C (u · v⁻¹) · k) = (C u · d) · k`.
-/
private theorem C_mul_dvd_of_C_mul_dvd_unit_swap
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {u v : ZMod64 p} (_hu : u ≠ 0) (hv : v ≠ 0) {d a : FpPoly p}
    (h : DensePoly.C u * d ∣ a) : DensePoly.C v * d ∣ a := by
  rcases h with ⟨k, hk⟩
  refine ⟨DensePoly.C (u * v⁻¹) * k, ?_⟩
  have hv_uv_inv : v * (u * v⁻¹) = u := by
    have hcomm : u * v⁻¹ = v⁻¹ * u := by grind
    have hv_inv : v * v⁻¹ = (1 : ZMod64 p) :=
      zmod64_mul_inv_eq_one_of_prime_ne_zero hp hv
    calc v * (u * v⁻¹)
        = v * (v⁻¹ * u) := by rw [hcomm]
      _ = (v * v⁻¹) * u := by grind
      _ = 1 * u := by rw [hv_inv]
      _ = u := by grind
  have hCu_rewrite :
      (DensePoly.C u : FpPoly p) = DensePoly.C v * DensePoly.C (u * v⁻¹) := by
    rw [fpPoly_C_mul_C_eq, hv_uv_inv]
  -- Polynomial algebra: (C v * d) * (C (u*v⁻¹) * k) = (C u * d) * k.
  have hgoal :
      (DensePoly.C v * d) * (DensePoly.C (u * v⁻¹) * k) =
        (DensePoly.C u * d) * k := by
    rw [hCu_rewrite]
    calc (DensePoly.C v * d) * (DensePoly.C (u * v⁻¹) * k)
        = ((DensePoly.C v * d) * DensePoly.C (u * v⁻¹)) * k :=
          (DensePoly.mul_assoc_poly _ _ _).symm
      _ = (DensePoly.C v * (d * DensePoly.C (u * v⁻¹))) * k :=
          congrArg (fun x => x * k) (DensePoly.mul_assoc_poly _ _ _)
      _ = (DensePoly.C v * (DensePoly.C (u * v⁻¹) * d)) * k :=
          congrArg
            (fun x => (DensePoly.C v * x) * k)
            (DensePoly.mul_comm_poly d (DensePoly.C (u * v⁻¹) : FpPoly p))
      _ = ((DensePoly.C v * DensePoly.C (u * v⁻¹)) * d) * k :=
          congrArg (fun x => x * k)
            (DensePoly.mul_assoc_poly _ _ _).symm
  rw [hk, ← hgoal]

/--
Asymmetric gcd scalar-multiple bridge: scaling the two arguments of
`DensePoly.gcd` by *different* nonzero constants `u_c`, `u_w` scales the
gcd by some nonzero constant `v`. The proof routes through divisibility
manipulation (rather than the Bezout factoring used by
`gcd_C_mul_C_mul_eq_C_mul_gcd`) because the two scalars cannot be
factored out as a single common constant. Used by the inner Yun split
synchronization to thread scalar factors through one step of
`yunFactorsContributionWithLevel`.
-/
private theorem gcd_C_mul_left_C_mul_right_eq_C_mul_gcd
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (u_c u_w : ZMod64 p) (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0) (c w : FpPoly p) :
    ∃ v : ZMod64 p, v ≠ 0 ∧
      DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) =
        DensePoly.C v * DensePoly.gcd c w := by
  by_cases hgcd_zero : DensePoly.gcd c w = 0
  · have hc_zero : c = 0 := by
      have hdvd : DensePoly.gcd c w ∣ c := DensePoly.gcd_dvd_left c w
      rw [hgcd_zero] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [zero_mul] at hk
      exact hk
    have hw_zero : w = 0 := by
      have hdvd : DensePoly.gcd c w ∣ w := DensePoly.gcd_dvd_right c w
      rw [hgcd_zero] at hdvd
      rcases hdvd with ⟨k, hk⟩
      rw [zero_mul] at hk
      exact hk
    refine ⟨1, zmod64_one_ne_zero_of_prime hp, ?_⟩
    have hCu_c_mul_c_zero : (DensePoly.C u_c : FpPoly p) * c = 0 := by
      rw [hc_zero, mul_zero]
    have hCu_w_mul_w_zero : (DensePoly.C u_w : FpPoly p) * w = 0 := by
      rw [hw_zero, mul_zero]
    rw [hCu_c_mul_c_zero, hCu_w_mul_w_zero, DensePoly.gcd_zero_zero,
        hgcd_zero, mul_zero]
  · have hCu_c_ne : (DensePoly.C u_c : FpPoly p) ≠ 0 := C_ne_zero_of_ne_zero hu_c
    have hCu_w_ne : (DensePoly.C u_w : FpPoly p) ≠ 0 := C_ne_zero_of_ne_zero hu_w
    let d : FpPoly p :=
      DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w)
    have hd_dvd_l : d ∣ DensePoly.C u_c * c :=
      DensePoly.gcd_dvd_left (DensePoly.C u_c * c) (DensePoly.C u_w * w)
    have hd_dvd_r : d ∣ DensePoly.C u_w * w :=
      DensePoly.gcd_dvd_right (DensePoly.C u_c * c) (DensePoly.C u_w * w)
    have hgcd_dvd_Cuc_c : DensePoly.gcd c w ∣ DensePoly.C u_c * c := by
      rcases DensePoly.gcd_dvd_left c w with ⟨q, hq⟩
      refine ⟨q * DensePoly.C u_c, ?_⟩
      have step_c : (c * DensePoly.C u_c : FpPoly p) =
          DensePoly.gcd c w * q * DensePoly.C u_c :=
        congrArg (fun x => x * DensePoly.C u_c) hq
      calc DensePoly.C u_c * c
          = c * DensePoly.C u_c := DensePoly.mul_comm_poly _ _
        _ = DensePoly.gcd c w * q * DensePoly.C u_c := step_c
        _ = DensePoly.gcd c w * (q * DensePoly.C u_c) :=
            DensePoly.mul_assoc_poly _ _ _
    have hgcd_dvd_Cuw_w : DensePoly.gcd c w ∣ DensePoly.C u_w * w := by
      rcases DensePoly.gcd_dvd_right c w with ⟨q, hq⟩
      refine ⟨q * DensePoly.C u_w, ?_⟩
      have step_w : (w * DensePoly.C u_w : FpPoly p) =
          DensePoly.gcd c w * q * DensePoly.C u_w :=
        congrArg (fun x => x * DensePoly.C u_w) hq
      calc DensePoly.C u_w * w
          = w * DensePoly.C u_w := DensePoly.mul_comm_poly _ _
        _ = DensePoly.gcd c w * q * DensePoly.C u_w := step_w
        _ = DensePoly.gcd c w * (q * DensePoly.C u_w) :=
            DensePoly.mul_assoc_poly _ _ _
    have hgcd_dvd_d : DensePoly.gcd c w ∣ d :=
      DensePoly.dvd_gcd (DensePoly.gcd c w)
        (DensePoly.C u_c * c) (DensePoly.C u_w * w)
        hgcd_dvd_Cuc_c hgcd_dvd_Cuw_w
    have huc_inv_uc : (u_c⁻¹ * u_c : ZMod64 p) = 1 := by
      have hcomm : u_c * u_c⁻¹ = u_c⁻¹ * u_c := by grind
      rw [← hcomm]
      exact zmod64_mul_inv_eq_one_of_prime_ne_zero hp hu_c
    have huw_inv_uw : (u_w⁻¹ * u_w : ZMod64 p) = 1 := by
      have hcomm : u_w * u_w⁻¹ = u_w⁻¹ * u_w := by grind
      rw [← hcomm]
      exact zmod64_mul_inv_eq_one_of_prime_ne_zero hp hu_w
    have hCC_uc_inv_uc :
        (DensePoly.C u_c⁻¹ * DensePoly.C u_c : FpPoly p) = 1 := by
      rw [fpPoly_C_mul_C_eq, huc_inv_uc]; rfl
    have hCC_uw_inv_uw :
        (DensePoly.C u_w⁻¹ * DensePoly.C u_w : FpPoly p) = 1 := by
      rw [fpPoly_C_mul_C_eq, huw_inv_uw]; rfl
    have hCucinv_d_dvd_c : DensePoly.C u_c⁻¹ * d ∣ c := by
      rcases hd_dvd_l with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      calc c
          = 1 * c := (one_mul c).symm
        _ = (DensePoly.C u_c⁻¹ * DensePoly.C u_c) * c := by rw [hCC_uc_inv_uc]
        _ = DensePoly.C u_c⁻¹ * (DensePoly.C u_c * c) :=
            DensePoly.mul_assoc_poly _ _ _
        _ = DensePoly.C u_c⁻¹ * (d * k) := by rw [hk]
        _ = (DensePoly.C u_c⁻¹ * d) * k :=
            (DensePoly.mul_assoc_poly _ _ _).symm
    have hCuwinv_d_dvd_w : DensePoly.C u_w⁻¹ * d ∣ w := by
      rcases hd_dvd_r with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      calc w
          = 1 * w := (one_mul w).symm
        _ = (DensePoly.C u_w⁻¹ * DensePoly.C u_w) * w := by rw [hCC_uw_inv_uw]
        _ = DensePoly.C u_w⁻¹ * (DensePoly.C u_w * w) :=
            DensePoly.mul_assoc_poly _ _ _
        _ = DensePoly.C u_w⁻¹ * (d * k) := by rw [hk]
        _ = (DensePoly.C u_w⁻¹ * d) * k :=
            (DensePoly.mul_assoc_poly _ _ _).symm
    have hCucinv_d_dvd_w : DensePoly.C u_c⁻¹ * d ∣ w :=
      C_mul_dvd_of_C_mul_dvd_unit_swap hp
        (zmod64_inv_ne_zero_of_prime_ne_zero hp hu_w)
        (zmod64_inv_ne_zero_of_prime_ne_zero hp hu_c)
        hCuwinv_d_dvd_w
    have hCucinv_d_dvd_gcd : DensePoly.C u_c⁻¹ * d ∣ DensePoly.gcd c w :=
      DensePoly.dvd_gcd (DensePoly.C u_c⁻¹ * d) c w
        hCucinv_d_dvd_c hCucinv_d_dvd_w
    have hd_dvd_Cuc_gcd : d ∣ DensePoly.C u_c * DensePoly.gcd c w := by
      have hCmul :
          DensePoly.C u_c * (DensePoly.C u_c⁻¹ * d) ∣
            DensePoly.C u_c * DensePoly.gcd c w :=
        C_mul_dvd_C_mul_of_dvd u_c hCucinv_d_dvd_gcd
      have hd_eq :
          DensePoly.C u_c * (DensePoly.C u_c⁻¹ * d) = d := by
        calc DensePoly.C u_c * (DensePoly.C u_c⁻¹ * d)
            = (DensePoly.C u_c * DensePoly.C u_c⁻¹) * d :=
              (DensePoly.mul_assoc_poly _ _ _).symm
          _ = (1 : FpPoly p) * d := by
                have h_uc_swap :
                    (DensePoly.C u_c * DensePoly.C u_c⁻¹ : FpPoly p) =
                      DensePoly.C u_c⁻¹ * DensePoly.C u_c :=
                  DensePoly.mul_comm_poly _ _
                rw [h_uc_swap, hCC_uc_inv_uc]
          _ = d := one_mul d
      rw [← hd_eq]
      exact hCmul
    rcases hgcd_dvd_d with ⟨t, ht⟩
    rcases hd_dvd_Cuc_gcd with ⟨t', ht'⟩
    have hcancel :
        DensePoly.C u_c * DensePoly.gcd c w =
          DensePoly.gcd c w * (t * t') := by
      calc DensePoly.C u_c * DensePoly.gcd c w
          = d * t' := ht'
        _ = (DensePoly.gcd c w * t) * t' := by rw [ht]
        _ = DensePoly.gcd c w * (t * t') :=
            DensePoly.mul_assoc_poly _ _ _
    have hC_uc_eq_tt' : (DensePoly.C u_c : FpPoly p) = t * t' := by
      have hcomm_l :
          (DensePoly.C u_c : FpPoly p) * DensePoly.gcd c w =
            DensePoly.gcd c w * DensePoly.C u_c :=
        DensePoly.mul_comm_poly _ _
      have hcomm_r :
          DensePoly.gcd c w * (t * t') =
            (t * t') * DensePoly.gcd c w :=
        DensePoly.mul_comm_poly _ _
      have hready :
          (DensePoly.C u_c : FpPoly p) * DensePoly.gcd c w =
            (t * t') * DensePoly.gcd c w := by
        rw [hcancel, hcomm_r]
      exact mul_right_cancel_of_ne_zero hgcd_zero hready
    have htt'_eq_C_uc : (t * t' : FpPoly p) = DensePoly.C u_c :=
      hC_uc_eq_tt'.symm
    have hC_uc_inv_tt' : (DensePoly.C u_c⁻¹ * (t * t') : FpPoly p) = 1 := by
      rw [htt'_eq_C_uc]
      calc (DensePoly.C u_c⁻¹ * DensePoly.C u_c : FpPoly p)
          = DensePoly.C (u_c⁻¹ * u_c) := fpPoly_C_mul_C_eq _ _
        _ = DensePoly.C 1 := by rw [huc_inv_uc]
        _ = 1 := rfl
    have hCucinv_t_mul_t' : ((DensePoly.C u_c⁻¹ * t) * t' : FpPoly p) = 1 := by
      calc (DensePoly.C u_c⁻¹ * t) * t'
          = DensePoly.C u_c⁻¹ * (t * t') :=
            DensePoly.mul_assoc_poly _ _ _
        _ = 1 := hC_uc_inv_tt'
    obtain ⟨w_unit, hw_unit_ne, hCucinv_t_eq⟩ :=
      eq_C_of_mul_eq_one hp hCucinv_t_mul_t'
    have ht_eq : t = DensePoly.C (u_c * w_unit) := by
      have huc_uc_inv : u_c * u_c⁻¹ = (1 : ZMod64 p) :=
        zmod64_mul_inv_eq_one_of_prime_ne_zero hp hu_c
      have hCuc_Cucinv :
          (DensePoly.C u_c * DensePoly.C u_c⁻¹ : FpPoly p) = 1 := by
        rw [fpPoly_C_mul_C_eq, huc_uc_inv]; rfl
      calc t
          = 1 * t := (one_mul t).symm
        _ = (DensePoly.C u_c * DensePoly.C u_c⁻¹) * t := by rw [hCuc_Cucinv]
        _ = DensePoly.C u_c * (DensePoly.C u_c⁻¹ * t) :=
            DensePoly.mul_assoc_poly _ _ _
        _ = DensePoly.C u_c * DensePoly.C w_unit := by rw [hCucinv_t_eq]
        _ = DensePoly.C (u_c * w_unit) := fpPoly_C_mul_C_eq _ _
    have hu_c_w_unit_ne : u_c * w_unit ≠ 0 := by
      intro hzero
      rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hh | hh
      · exact hu_c hh
      · exact hw_unit_ne hh
    refine ⟨u_c * w_unit, hu_c_w_unit_ne, ?_⟩
    show d = DensePoly.C (u_c * w_unit) * DensePoly.gcd c w
    calc d
        = DensePoly.gcd c w * t := ht
      _ = DensePoly.gcd c w * DensePoly.C (u_c * w_unit) := by rw [ht_eq]
      _ = DensePoly.C (u_c * w_unit) * DensePoly.gcd c w :=
          DensePoly.mul_comm_poly _ _

/-- `gcd_eq_zero_forces_zero` shows a vanishing `gcd c w` forces both `c` and
`w` to vanish, since the gcd divides each input. -/
private theorem gcd_eq_zero_forces_zero [ZMod64.PrimeModulus p] (c w : FpPoly p)
    (h : DensePoly.gcd c w = 0) :
    c = 0 ∧ w = 0 := by
  constructor
  · have hdvd : DensePoly.gcd c w ∣ c := DensePoly.gcd_dvd_left c w
    rw [h] at hdvd
    rcases hdvd with ⟨q, hq⟩
    simpa using hq
  · have hdvd : DensePoly.gcd c w ∣ w := DensePoly.gcd_dvd_right c w
    rw [h] at hdvd
    rcases hdvd with ⟨q, hq⟩
    simpa using hq

/-- `scaled_gcd_eq_zero` shows scaling both inputs by constants keeps a
vanishing `gcd c w` vanishing. -/
private theorem scaled_gcd_eq_zero
    [ZMod64.PrimeModulus p]
    (u_c u_w : ZMod64 p) (c w : FpPoly p)
    (h : DensePoly.gcd c w = 0) :
    DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) = 0 := by
  rcases gcd_eq_zero_forces_zero c w h with ⟨hc, hw⟩
  rw [hc, hw, mul_zero, mul_zero, DensePoly.gcd_zero_zero]

/-- `div_zero_eq_zero` states that dividing any polynomial by the zero
polynomial yields `0`. -/
private theorem div_zero_eq_zero (f : FpPoly p) :
    f / (0 : FpPoly p) = 0 := by
  have hpair :=
    DensePoly.divMod_eq_zero_self_of_size_zero_core f (0 : FpPoly p) (by simp)
  exact congrArg Prod.fst hpair

/-- `div_zero_C_mul_left` shows constant scaling commutes with division by the
zero polynomial on the left input `c` when `gcd c w` vanishes. -/
private theorem div_zero_C_mul_left
    [ZMod64.PrimeModulus p]
    (u : ZMod64 p) {c w : FpPoly p} (h : DensePoly.gcd c w = 0) :
    (DensePoly.C u * c) / (0 : FpPoly p) =
      DensePoly.C u * (c / (0 : FpPoly p)) := by
  have hc : c = 0 := (gcd_eq_zero_forces_zero c w h).1
  simp [hc, div_zero_eq_zero]

/-- `div_zero_C_mul_right` shows constant scaling commutes with division by the
zero polynomial on the right input `w` when `gcd c w` vanishes. -/
private theorem div_zero_C_mul_right
    [ZMod64.PrimeModulus p]
    (u : ZMod64 p) {c w : FpPoly p} (h : DensePoly.gcd c w = 0) :
    (DensePoly.C u * w) / (0 : FpPoly p) =
      DensePoly.C u * (w / (0 : FpPoly p)) := by
  have hw : w = 0 := (gcd_eq_zero_forces_zero c w h).2
  simp [hw, div_zero_eq_zero]


end FpPoly
end Hex
