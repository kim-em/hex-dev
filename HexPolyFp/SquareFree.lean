import HexModArith.Prime
import HexPolyFp.Basic

/-!
Executable square-free decomposition for `F_p[x]`.

This module implements a Yun-style square-free decomposition for
`Hex.FpPoly p`, recording the unit factor and the positive-multiplicity
square-free factors obtained from repeated gcd/derivative steps and
`p`-th-root descent in characteristic `p`. The public API carries an
explicit `Hex.Nat.Prime p` contract because the exported factorization and
square-free theorems are intended for prime-field coefficients.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- One square-free factor together with its multiplicity. -/
structure SquareFreeFactor (p : Nat) [ZMod64.Bounds p] where
  factor : FpPoly p
  multiplicity : Nat

/-- A square-free decomposition records the scalar unit and the nonconstant factors. -/
structure SquareFreeDecomposition (p : Nat) [ZMod64.Bounds p] where
  unit : ZMod64 p
  factors : List (SquareFreeFactor p)

/-- Detect the unit polynomial `1`. -/
private def isOne (f : FpPoly p) : Bool :=
  match f.degree? with
  | some 0 =>
      if f.coeff 0 = (1 : ZMod64 p) then
        true
      else
        false
  | _ => false

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
private def pow (f : FpPoly p) (n : Nat) : FpPoly p :=
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

private theorem pow_one (f : FpPoly p) :
    pow f 1 = f := by
  unfold pow
  simp [pow.go]

private def powLinear (f : FpPoly p) : Nat → FpPoly p
  | 0 => 1
  | n + 1 => powLinear f n * f

private theorem powLinear_add (f : FpPoly p) (m n : Nat) :
    powLinear f (m + n) = powLinear f m * powLinear f n := by
  induction n with
  | zero =>
      simp [powLinear]
  | succ n ih =>
      rw [Nat.add_succ, powLinear, ih, powLinear]
      exact DensePoly.mul_assoc_poly (powLinear f m) (powLinear f n) f

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

private theorem powLinear_double_add_one (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n + 1) = f * powLinear (f * f) n := by
  rw [powLinear, powLinear_double]
  exact mul_comm (powLinear (f * f) n) f

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

private theorem pow_eq_powLinear (f : FpPoly p) (n : Nat) :
    pow f n = powLinear f n := by
  unfold pow
  rw [pow_go_eq_mul_powLinear]
  exact one_mul (powLinear f n)

private theorem powLinear_powLinear_mul (f : FpPoly p) (m n : Nat) :
    powLinear (powLinear f n) m = powLinear f (m * n) := by
  induction m with
  | zero =>
      simp [powLinear]
  | succ m ih =>
      rw [powLinear, ih]
      simpa [Nat.succ_mul] using (powLinear_add f (m * n) n).symm

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

private theorem pow_add_exp (f : FpPoly p) (m n : Nat) :
    pow f (m + n) = pow f m * pow f n := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_add f m n

private theorem pow_succ (f : FpPoly p) (n : Nat) :
    pow f (n + 1) = pow f n * f := by
  rw [pow_eq_powLinear, pow_eq_powLinear]
  rfl

private theorem derivative_pow_succ (f : FpPoly p) (n : Nat) :
    DensePoly.derivative (pow f (n + 1)) =
      DensePoly.derivative (pow f n) * f + pow f n * DensePoly.derivative f := by
  rw [pow_succ]
  exact DensePoly.derivative_mul (pow f n) f

private theorem pow_mul_base (f g : FpPoly p) (n : Nat) :
    pow (f * g) n = pow f n * pow g n := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_mul_base f g n

private theorem pow_pow_mul' (f : FpPoly p) (m n : Nat) :
    pow (pow f n) m = pow f (m * n) := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_powLinear_mul f m n

private theorem zmod64_add_pow_prime
    (hp : Hex.Nat.Prime p) (a b : ZMod64 p) :
    (a + b) ^ p = a ^ p + b ^ p := by
  rw [ZMod64.pow_prime hp (a + b), ZMod64.pow_prime hp a, ZMod64.pow_prime hp b]

private theorem zmod64_natCast_choose_prime_eq_zero
    (hp : Hex.Nat.Prime p) {k : Nat} (hk0 : 0 < k) (hkp : k < p) :
    ((Hex.Nat.choose p k : Nat) : ZMod64 p) = 0 := by
  exact (ZMod64.natCast_eq_zero_iff_dvd (p := p) (Hex.Nat.choose p k)).2
    (Hex.Nat.choose_prime_dvd hp hk0 hkp)

private theorem scale_add_scalar (c d : ZMod64 p) (f : FpPoly p) :
    DensePoly.scale (c + d) f = DensePoly.scale c f + DensePoly.scale d f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_cd : (c + d) * (0 : ZMod64 p) = 0 := by grind
  have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
  have hzero_d : d * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_cd]
  rw [DensePoly.coeff_add_semiring]
  rw [DensePoly.coeff_scale _ _ _ hzero_c]
  rw [DensePoly.coeff_scale _ _ _ hzero_d]
  grind

private theorem scale_mul_right (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f * g) = f * DensePoly.scale c g := by
  calc
    DensePoly.scale c (f * g) = DensePoly.scale c (g * f) := by
      exact congrArg (fun x => DensePoly.scale c x) (DensePoly.mul_comm_poly f g)
    _ = DensePoly.scale c g * f := scale_mul_left c g f
    _ = f * DensePoly.scale c g := by
      exact DensePoly.mul_comm_poly (DensePoly.scale c g) f

private theorem powLinear_succ_left (f : FpPoly p) (n : Nat) :
    powLinear f (n + 1) = f * powLinear f n := by
  rw [powLinear]
  exact DensePoly.mul_comm_poly (powLinear f n) f

private theorem powLinearBinom_scalar_add
    (a b : Nat) (h : FpPoly p) :
    DensePoly.scale (((a + b : Nat) : ZMod64 p)) h =
      DensePoly.scale (a : ZMod64 p) h + DensePoly.scale (b : ZMod64 p) h := by
  have hcast : (((a + b : Nat) : ZMod64 p)) = (a : ZMod64 p) + (b : ZMod64 p) := by
    grind
  rw [hcast]
  exact scale_add_scalar (a : ZMod64 p) (b : ZMod64 p) h

private theorem powLinearBinom_scalar_zero (h : FpPoly p) :
    DensePoly.scale (0 : ZMod64 p) h = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : (0 : ZMod64 p) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_zero]
  grind

private theorem powLinearBinom_scalar_one (h : FpPoly p) :
    DensePoly.scale (1 : ZMod64 p) h = h :=
  scale_one_left h

private theorem powLinearBinom_mul_zero (h : FpPoly p) :
    h * (0 : FpPoly p) = 0 :=
  Eq.trans (DensePoly.mul_comm_poly h 0) (DensePoly.zero_mul h)

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

private def powLinearBinomTerm (f g : FpPoly p) (n k : Nat) : FpPoly p :=
  DensePoly.scale (Hex.Nat.choose n k : ZMod64 p)
    (powLinear f (n - k) * powLinear g k)

private def powLinearBinomSum (f g : FpPoly p) (n : Nat) : Nat → FpPoly p
  | 0 => 0
  | k + 1 => powLinearBinomSum f g n k + powLinearBinomTerm f g n k

private theorem powLinearBinomTerm_succ_zero (f g : FpPoly p) (n : Nat) :
    powLinearBinomTerm f g (n + 1) 0 =
      f * powLinearBinomTerm f g n 0 := by
  unfold powLinearBinomTerm
  simp [Hex.Nat.choose]
  change DensePoly.scale (1 : ZMod64 p) (powLinear f (n + 1) * powLinear g 0) =
    f * DensePoly.scale (1 : ZMod64 p) (powLinear f n * powLinear g 0)
  rw [powLinearBinom_scalar_one]
  rw [powLinearBinom_scalar_one]
  have hg0 : powLinear g 0 = 1 := rfl
  rw [hg0]
  calc
    powLinear f (n + 1) * 1 = powLinear f (n + 1) :=
      DensePoly.mul_one_right_poly (powLinear f (n + 1))
    _ = f * powLinear f n := powLinear_succ_left f n
    _ = f * (powLinear f n * 1) := by
          exact congrArg (fun x => f * x)
            (DensePoly.mul_one_right_poly (powLinear f n)).symm

private theorem powLinearBinomTerm_succ_succ_of_lt
    (f g : FpPoly p) {n k : Nat} (hk : k < n) :
    powLinearBinomTerm f g (n + 1) (k + 1) =
      f * powLinearBinomTerm f g n (k + 1) +
        g * powLinearBinomTerm f g n k := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_succ_succ]
  rw [powLinearBinom_scalar_add]
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
  rw [mul_powLinearBinom_scaled_left]
  rw [mul_powLinearBinom_scaled_right]
  rw [hf, hg]
  exact DensePoly.add_comm_poly _ _

private theorem powLinearBinomTerm_succ_succ_top
    (f g : FpPoly p) (n : Nat) :
    powLinearBinomTerm f g (n + 1) (n + 1) =
      f * powLinearBinomTerm f g n (n + 1) +
        g * powLinearBinomTerm f g n n := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_succ_succ]
  have hzero_choose : Hex.Nat.choose n (n + 1) = 0 :=
    Hex.Nat.choose_eq_zero_of_lt (by omega)
  rw [hzero_choose]
  rw [Hex.Nat.choose_self]
  have hcast : (((1 + 0 : Nat) : ZMod64 p)) = (1 : ZMod64 p) := by grind
  rw [hcast]
  have hsub_left : n + 1 - (n + 1) = 0 := by omega
  have hsub_mid : n - (n + 1) = 0 := by omega
  have hsub_right : n - n = 0 := by omega
  rw [hsub_left, hsub_mid, hsub_right]
  change DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g (n + 1)) =
    f * DensePoly.scale (0 : ZMod64 p) (powLinear f 0 * powLinear g (n + 1)) +
      g * DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g n)
  rw [powLinearBinom_scalar_one]
  rw [powLinearBinom_scalar_zero]
  rw [powLinearBinom_mul_zero]
  have hzadd : (0 : FpPoly p) +
      g * DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g n) =
        g * DensePoly.scale (1 : ZMod64 p) (powLinear f 0 * powLinear g n) :=
    DensePoly.zero_add _
  rw [hzadd]
  rw [powLinearBinom_scalar_one]
  have hf0 : powLinear f 0 = 1 := rfl
  rw [hf0]
  calc
    1 * powLinear g (n + 1) = powLinear g (n + 1) := by
      exact one_mul (powLinear g (n + 1))
    _ = g * powLinear g n := powLinear_succ_left g n
    _ = g * (1 * powLinear g n) := by
          rw [one_mul]

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

private theorem powLinearBinomSum_succ_row
    (f g : FpPoly p) (n m : Nat) (hm : m ≤ n + 1) :
    powLinearBinomSum f g (n + 1) (m + 1) =
      f * powLinearBinomSum f g n (m + 1) +
        g * powLinearBinomSum f g n m := by
  induction m with
  | zero =>
      simp [powLinearBinomSum, powLinearBinomTerm_succ_zero]
  | succ m ih =>
      rw [powLinearBinomSum, ih (by omega)]
      rw [powLinearBinomSum]
      rw [powLinearBinomSum]
      rw [powLinearBinomTerm_succ_succ f g (by omega : m ≤ n)]
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
      rw [hsum]
      rw [← hdistL]
      apply DensePoly.ext_coeff
      intro i
      repeat rw [DensePoly.coeff_add_semiring]
      grind

private theorem powLinearBinomTerm_above
    (f g : FpPoly p) {n k : Nat} (hk : n < k) :
    powLinearBinomTerm f g n k = 0 := by
  unfold powLinearBinomTerm
  rw [Hex.Nat.choose_eq_zero_of_lt hk]
  exact powLinearBinom_scalar_zero _

private theorem powLinearBinomSum_top_succ
    (f g : FpPoly p) (n : Nat) :
    powLinearBinomSum f g n (n + 1 + 1) =
      powLinearBinomSum f g n (n + 1) := by
  rw [powLinearBinomSum]
  rw [powLinearBinomTerm_above f g (by omega : n < n + 1)]
  exact DensePoly.add_zero_poly _

private theorem powLinear_add_binom_sum
    (f g : FpPoly p) (n : Nat) :
    powLinear (f + g) n = powLinearBinomSum f g n (n + 1) := by
  induction n with
  | zero =>
      simp [powLinear, powLinearBinomSum, powLinearBinomTerm, Hex.Nat.choose]
      exact (powLinearBinom_scalar_one (1 : FpPoly p)).symm
  | succ n ih =>
      rw [powLinear_succ_left, ih]
      rw [powLinearBinomSum_succ_row f g n (n + 1) (by omega)]
      rw [powLinearBinomSum_top_succ f g n]
      exact DensePoly.mul_add_left_poly f g (powLinearBinomSum f g n (n + 1))

private theorem powLinearBinomTerm_prime_zero (f g : FpPoly p) :
    powLinearBinomTerm f g p 0 = powLinear f p := by
  unfold powLinearBinomTerm
  simp
  change DensePoly.scale (1 : ZMod64 p) (powLinear f p * powLinear g 0) =
    powLinear f p
  rw [powLinearBinom_scalar_one]
  exact DensePoly.mul_one_right_poly (powLinear f p)

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

private theorem powLinearBinomTerm_prime_middle
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) {k : Nat} (hk0 : 0 < k) (hkp : k < p) :
    powLinearBinomTerm f g p k = 0 := by
  unfold powLinearBinomTerm
  rw [zmod64_natCast_choose_prime_eq_zero hp hk0 hkp]
  exact powLinearBinom_scalar_zero _

private theorem powLinearBinomSum_prime_middle
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) {m : Nat} (hm : m < p) :
    powLinearBinomSum f g p (m + 1) = powLinear f p := by
  induction m with
  | zero =>
      rw [powLinearBinomSum, powLinearBinomTerm_prime_zero]
      exact DensePoly.zero_add _
  | succ m ih =>
      rw [powLinearBinomSum, ih (by omega)]
      rw [powLinearBinomTerm_prime_middle hp f g (by omega : 0 < m + 1) (by omega)]
      exact DensePoly.add_zero_poly _

private theorem powLinear_add_prime
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) :
    powLinear (f + g) p = powLinear f p + powLinear g p := by
  have hp_two : 2 ≤ p := Hex.Nat.Prime.two_le hp
  have hp_pos : 0 < p := by omega
  rw [powLinear_add_binom_sum]
  rw [powLinearBinomSum]
  have hmid : powLinearBinomSum f g p p = powLinear f p := by
    have hmid0 :
        powLinearBinomSum f g p ((p - 1) + 1) = powLinear f p :=
      powLinearBinomSum_prime_middle hp f g (by omega : p - 1 < p)
    simpa [Nat.sub_add_cancel hp_pos] using hmid0
  rw [hmid, powLinearBinomTerm_prime_top]

private theorem foldl_poly_sum_mul_right
    {α : Type _} (xs : List α) (term : α → FpPoly p) (acc h : FpPoly p) :
    (xs.foldl (fun acc x => acc + term x) acc) * h =
      xs.foldl (fun acc x => acc + term x * h) (acc * h) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + term x)]
      have hstart : (acc + term x) * h = acc * h + term x * h :=
        DensePoly.mul_add_left_poly acc (term x) h
      rw [hstart]

private theorem foldl_poly_sum_mul_left
    {α : Type _} (xs : List α) (term : α → FpPoly p) (acc h : FpPoly p) :
    h * xs.foldl (fun acc x => acc + term x) acc =
      xs.foldl (fun acc x => acc + h * term x) (h * acc) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + term x)]
      have hstart : h * (acc + term x) = h * acc + h * term x :=
        DensePoly.mul_add_right_poly h acc (term x)
      rw [hstart]

private theorem scale_foldl_poly_sum
    {α : Type _} (c : ZMod64 p) (xs : List α) (term : α → FpPoly p) (acc : FpPoly p) :
    DensePoly.scale c (xs.foldl (fun acc x => acc + term x) acc) =
      xs.foldl (fun acc x => acc + DensePoly.scale c (term x))
        (DensePoly.scale c acc) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + term x)]
      rw [scale_add]

private theorem zmod64_fold_add_pow_prime_acc
    (hp : Hex.Nat.Prime p) (xs : List (ZMod64 p)) (acc : ZMod64 p) :
    (xs.foldl (fun acc x => acc + x) acc) ^ p =
      (xs.map fun x => x ^ p).foldl (fun acc x => acc + x) (acc ^ p) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (acc + x), zmod64_add_pow_prime hp acc x]

private theorem zmod64_fold_add_pow_prime
    (hp : Hex.Nat.Prime p) (xs : List (ZMod64 p)) :
    (xs.foldl (fun acc x => acc + x) 0) ^ p =
      (xs.map fun x => x ^ p).foldl (fun acc x => acc + x) 0 := by
  simpa [ZMod64.pow_prime hp (0 : ZMod64 p)] using
    zmod64_fold_add_pow_prime_acc (p := p) hp xs (0 : ZMod64 p)

private theorem zmod64_index_fold_add_pow_prime
    (hp : Hex.Nat.Prime p) (xs : List Nat) (term : Nat → ZMod64 p) :
    (xs.foldl (fun acc i => acc + term i) 0) ^ p =
      xs.foldl (fun acc i => acc + term i ^ p) 0 := by
  simpa [List.foldl_map] using
    zmod64_fold_add_pow_prime (p := p) hp (xs.map term)

/-- Multiply the factors in a square-free decomposition with their multiplicities. -/
def weightedProduct (factors : List (SquareFreeFactor p)) : FpPoly p :=
  factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1

private theorem weightedProduct_nil :
    weightedProduct ([] : List (SquareFreeFactor p)) = 1 := by
  rfl

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
      rw [ih (acc * pow sf.factor sf.multiplicity)]
      rw [ih ((1 : FpPoly p) * pow sf.factor sf.multiplicity)]
      have hone :
          (1 : FpPoly p) * pow sf.factor sf.multiplicity =
            pow sf.factor sf.multiplicity := by
        exact one_mul (pow sf.factor sf.multiplicity)
      rw [hone]
      exact DensePoly.mul_assoc_poly acc (pow sf.factor sf.multiplicity) (weightedProduct factors)

private theorem weightedProduct_cons
    (sf : SquareFreeFactor p) (factors : List (SquareFreeFactor p)) :
    weightedProduct (sf :: factors) =
      pow sf.factor sf.multiplicity * weightedProduct factors := by
  unfold weightedProduct
  simp only [List.foldl_cons]
  rw [weightedProduct_foldl_eq_mul]
  exact congrArg (fun x => x * weightedProduct factors) (one_mul (pow sf.factor sf.multiplicity))

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

private theorem weightedProduct_singleton (sf : SquareFreeFactor p) :
    weightedProduct [sf] = pow sf.factor sf.multiplicity := by
  rw [weightedProduct_cons, weightedProduct_nil]
  exact DensePoly.mul_one_right_poly (pow sf.factor sf.multiplicity)

private theorem weightedProduct_reverse_cons
    (sf : SquareFreeFactor p) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (sf :: accRev).reverse =
      weightedProduct accRev.reverse * pow sf.factor sf.multiplicity := by
  rw [List.reverse_cons, weightedProduct_append, weightedProduct_singleton]

/--
Extract the formal `p`-th root by keeping exactly the coefficients whose
degrees are multiples of `p`.
-/
private def pthRoot (f : FpPoly p) : FpPoly p :=
  let rootSize := (f.size + p - 1) / p
  ofCoeffs <|
    (List.range rootSize).map (fun i => f.coeff (i * p)) |>.toArray

private theorem pthRoot_coeff_of_lt
    (f : FpPoly p) {i : Nat} (hi : i < (f.size + p - 1) / p) :
    (pthRoot f).coeff i = f.coeff (i * p) := by
  unfold pthRoot ofCoeffs
  rw [DensePoly.coeff_ofCoeffs]
  simp [Array.getD, hi]

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

private theorem zmod64_add_zero_coeff (a : ZMod64 p) :
    a + 0 = a := by
  grind

private theorem zmod64_zero_add_coeff (a : ZMod64 p) :
    0 + a = a := by
  grind

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

private theorem coeff_foldl_coeffTerm_coeff
    (g : FpPoly p) (xs : List Nat) (acc : FpPoly p) (n : Nat) :
    (xs.foldl (fun acc i => acc + coeffTerm g i) acc).coeff n =
      xs.foldl (fun acc i => acc + (coeffTerm g i).coeff n) (acc.coeff n) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + coeffTerm g i)]
      rw [DensePoly.coeff_add_semiring]

private theorem coeffFold_coeff_index_fold (g : FpPoly p) (m n : Nat) :
    (coeffFold g m).coeff n =
      (List.range m).foldl (fun acc i => acc + (coeffTerm g i).coeff n) 0 := by
  unfold coeffFold
  simpa [DensePoly.coeff_zero] using
    coeff_foldl_coeffTerm_coeff (p := p) g (List.range m) (0 : FpPoly p) n

private theorem coeffFold_coeff_index_fold_pow_prime
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    ((coeffFold g m).coeff n) ^ p =
      (List.range m).foldl
        (fun acc i => acc + (coeffTerm g i).coeff n ^ p) 0 := by
  rw [coeffFold_coeff_index_fold]
  exact zmod64_index_fold_add_pow_prime
    (p := p) hp (List.range m) (fun i => (coeffTerm g i).coeff n)

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
        rw [if_neg hne]
        rw [if_pos (by omega : n < m + 1)]
        exact zmod64_add_zero_coeff (g.coeff n)
      · by_cases heq : n = m
        · rw [if_neg hlt]
          rw [if_pos heq]
          rw [if_pos (by omega : n < m + 1)]
          rw [heq]
          exact zmod64_zero_add_coeff (g.coeff m)
        · have hsucc : ¬n < m + 1 := by omega
          rw [if_neg hlt]
          rw [if_neg heq]
          rw [if_neg hsucc]
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
            rw [if_pos hltsucc]
            rw [heq]
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

private theorem coeffFoldPowerCoeff_prime_coeff_of_mod_ne_zero
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) (hn : n % p ≠ 0) :
    coeffFoldPowerCoeff g m p n = 0 := by
  rw [coeffFoldPowerCoeff_prime_coeff hp g m n]
  simp [hn]

private theorem coeffFoldPowerCoeff_prime_coeff_of_mod_eq_zero
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) (hn : n % p = 0) :
    coeffFoldPowerCoeff g m p n =
      if n / p < m then (g.coeff (n / p)) ^ p else 0 := by
  rw [coeffFoldPowerCoeff_prime_coeff hp g m n]
  simp [hn]

private theorem powLinear_coeffFold_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    (powLinear (coeffFold g m) p).coeff n =
      if n % p = 0 then
        if n / p < m then (g.coeff (n / p)) ^ p else 0
      else
        0 := by
  rw [powLinear_coeffFold_prime_coeff_expansion]
  exact coeffFoldPowerCoeff_prime_coeff hp g m n

private theorem powLinear_add_prime_coeff
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) (n : Nat) :
    (powLinear (f + g) p).coeff n =
      (powLinear f p).coeff n + (powLinear g p).coeff n := by
  rw [powLinear_add_prime hp f g]
  exact DensePoly.coeff_add_semiring _ _ _

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
              rw [hcoeff]
              rw [if_pos hn]
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
        simpa [ZMod64.toNat_eq_val] using hnat
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

private theorem zmod64_mul_inv_eq_one_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hcop := zmod64_coprime_of_prime_ne_zero hp ha
  have hinv : (a⁻¹ * a).toNat = (1 : ZMod64 p).toNat := by
    simpa [ZMod64.toNat_one] using ZMod64.inv_mul_eq_one (p := p) a hcop
  have hcomm : a * a⁻¹ = a⁻¹ * a := by grind
  rw [hcomm]
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using hinv

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

private theorem zmod64_inv_ne_zero_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 := by
  intro hinv
  have hone := zmod64_mul_inv_eq_one_of_prime_ne_zero hp ha
  rw [hinv] at hone
  have hzero : a * (0 : ZMod64 p) = 0 := by grind
  rw [hzero] at hone
  exact zmod64_one_ne_zero_of_prime hp hone.symm

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
    unfold DensePoly.leadingCoeff DensePoly.coeff
    rw [Array.back?_eq_getElem?]
    have hidx : f.coeffs.size - 1 < f.coeffs.size := by
      simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
    simp [Array.getD, DensePoly.size, hidx]
  rw [hlead]
  exact hlast

/-- Split off the leading coefficient so the recursive Yun loop can work on a monic input. -/
private def normalizeMonic (f : FpPoly p) : ZMod64 p × FpPoly p :=
  if f.isZero then
    (0, 0)
  else
    let unit := DensePoly.leadingCoeff f
    (unit, DensePoly.scale unit⁻¹ f)

private theorem normalizeMonic_zero
    (f : FpPoly p) (hzero : f.isZero = true) :
    normalizeMonic f = (0, 0) := by
  simp [normalizeMonic, hzero]

private theorem eq_zero_of_isZero_true
    (f : FpPoly p) (hzero : f.isZero = true) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : f.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero
  rw [DensePoly.coeff_eq_zero_of_size_le f (by omega)]
  exact DensePoly.coeff_zero n

private theorem normalizeMonic_zero_reconstruct
    (f : FpPoly p) (hzero : f.isZero = true) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_zero f hzero]
  rw [eq_zero_of_isZero_true f hzero]
  exact mul_zero (DensePoly.C (0 : ZMod64 p))

private theorem normalizeMonic_nonzero
    (f : FpPoly p) (hzero : f.isZero = false) :
    normalizeMonic f =
      (DensePoly.leadingCoeff f, DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) := by
  simp [normalizeMonic, hzero]

private theorem normalizeMonic_nonzero_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_nonzero f hzero]
  rw [C_mul_eq_scale, scale_scale]
  have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  rw [zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne]
  exact scale_one_left f

private theorem normalizeMonic_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  cases hzero : f.isZero
  · exact normalizeMonic_nonzero_reconstruct hp f hzero
  · exact normalizeMonic_zero_reconstruct f hzero

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

/-! ### Scalar-multiple algebra foundations

Foundational `FpPoly p` algebra for transporting `DensePoly.derivative`,
`DensePoly.gcd`, and exact division across a common nonzero scalar multiple
`DensePoly.C u * f`. These lemmas underpin the Yun split-synchronization
theorem used by the square-free decomposition correctness chain.
-/

private theorem C_ne_zero_of_ne_zero {u : ZMod64 p} (hu : u ≠ 0) :
    (DensePoly.C u : FpPoly p) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hzero
  change (DensePoly.C u : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
  simp at hcoeff
  exact hu hcoeff

/--
Derivative is linear over constant-polynomial scaling: `D(C c · f) = C c · D(f)`.
Uses the Leibniz rule and `derivative_C_semiring`.
-/
private theorem derivative_C_mul (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.derivative (DensePoly.C c * f) =
      DensePoly.C c * DensePoly.derivative f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero c
  have hzeroN : ((n + 1 : Nat) : ZMod64 p) * (0 : ZMod64 p) = 0 :=
    Lean.Grind.Semiring.mul_zero _
  rw [C_mul_eq_scale c f, C_mul_eq_scale c (DensePoly.derivative f)]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_derivative _ _ hzeroN]
  rw [DensePoly.coeff_derivative _ _ hzeroN]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

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
  simpa [hsize] using hlast

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
        DensePoly.xgcd_bezout (DensePoly.C u * f) (DensePoly.C u * g)⟩
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

/--
One-sided (left) gcd scalar-multiple bridge: a corollary of
`gcd_C_mul_left_C_mul_right_eq_C_mul_gcd` with `u_w = 1`.
-/
private theorem gcd_C_mul_left_eq_C_mul_gcd
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (u : ZMod64 p) (hu : u ≠ 0) (f g : FpPoly p) :
    ∃ v : ZMod64 p, v ≠ 0 ∧
      DensePoly.gcd (DensePoly.C u * f) g =
        DensePoly.C v * DensePoly.gcd f g := by
  have h1 : (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 := rfl
  have h2 : (DensePoly.C (1 : ZMod64 p) : FpPoly p) * g = g := by
    rw [h1, one_mul]
  obtain ⟨v, hv, heq⟩ :=
    gcd_C_mul_left_C_mul_right_eq_C_mul_gcd hp u 1 hu
      (zmod64_one_ne_zero_of_prime hp) f g
  rw [h2] at heq
  exact ⟨v, hv, heq⟩

/--
One-sided (right) gcd scalar-multiple bridge: a corollary of
`gcd_C_mul_left_C_mul_right_eq_C_mul_gcd` with `u_c = 1`.
-/
private theorem gcd_C_mul_right_eq_C_mul_gcd
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (u : ZMod64 p) (hu : u ≠ 0) (f g : FpPoly p) :
    ∃ v : ZMod64 p, v ≠ 0 ∧
      DensePoly.gcd f (DensePoly.C u * g) =
        DensePoly.C v * DensePoly.gcd f g := by
  have h1 : (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 := rfl
  have h2 : (DensePoly.C (1 : ZMod64 p) : FpPoly p) * f = f := by
    rw [h1, one_mul]
  obtain ⟨v, hv, heq⟩ :=
    gcd_C_mul_left_C_mul_right_eq_C_mul_gcd hp 1 u
      (zmod64_one_ne_zero_of_prime hp) hu f g
  rw [h2] at heq
  exact ⟨v, hv, heq⟩

/--
Quotient compatibility under scalar relation for the Yun `c = f / g` and
tail `w / g` steps: when `g ∣ f` with `g ≠ 0` and both scalars `u, v` are
nonzero, the scaled quotient `(C u · f) / (C v · g)` equals
`C (u · v⁻¹) · (f / g)`. The proof uses uniqueness of the executable quotient
through `mul_right_cancel_of_ne_zero`.
-/
private theorem div_C_mul_C_mul_of_dvd
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {u v : ZMod64 p} (_hu : u ≠ 0) (hv : v ≠ 0)
    (f g : FpPoly p) (hdvd : g ∣ f) (hg_ne : g ≠ 0) :
    (DensePoly.C u * f) / (DensePoly.C v * g) =
      DensePoly.C (u * v⁻¹) * (f / g) := by
  -- Exact-division identity for the unscaled quotient.
  have hquot_mul : (f / g) * g = f := by
    have hmod : f % g = 0 := DensePoly.mod_eq_zero_of_dvd f g hdvd
    have hrec : (f / g) * g + (f % g) = f := DensePoly.div_mul_add_mod f g
    rw [hmod] at hrec
    rwa [add_zero] at hrec
  -- The scaled divisor is nonzero.
  have hCv_ne : (DensePoly.C v : FpPoly p) ≠ 0 := C_ne_zero_of_ne_zero hv
  have hCvg_ne : DensePoly.C v * g ≠ 0 := mul_ne_zero_of_ne_zero hCv_ne hg_ne
  -- The scaled dividend is divisible by the scaled divisor.
  have hC_mul_C_eq : ∀ a b : ZMod64 p, ∀ q : FpPoly p,
      (DensePoly.C a * DensePoly.C b) * q = DensePoly.C (a * b) * q := by
    intro a b q
    have hzero_a : a * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero a
    have hCC : (DensePoly.C a * DensePoly.C b : FpPoly p) = DensePoly.C (a * b) := by
      rw [C_mul_eq_scale]
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale _ _ _ hzero_a, DensePoly.coeff_C, DensePoly.coeff_C]
      cases n with
      | zero => rfl
      | succ n => exact hzero_a
    rw [hCC]
  -- v * (u * v⁻¹) = u (commute v through and use v · v⁻¹ = 1).
  have hv_inv : v * v⁻¹ = (1 : ZMod64 p) :=
    zmod64_mul_inv_eq_one_of_prime_ne_zero hp hv
  have hv_uv_inv : v * (u * v⁻¹) = u := by
    have hcomm : u * v⁻¹ = v⁻¹ * u := by grind
    calc v * (u * v⁻¹)
        = v * (v⁻¹ * u) := by rw [hcomm]
      _ = (v * v⁻¹) * u := by grind
      _ = 1 * u := by rw [hv_inv]
      _ = u := by grind
  -- Show C u * f = (C v * g) * (C (u * v⁻¹) * (f / g)).
  have hC_mul_C_eq_C : ∀ a b : ZMod64 p,
      (DensePoly.C a * DensePoly.C b : FpPoly p) = DensePoly.C (a * b) := by
    intro a b
    have hzero : a * (0 : ZMod64 p) = 0 := Lean.Grind.Semiring.mul_zero a
    rw [C_mul_eq_scale]
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C, DensePoly.coeff_C]
    cases n with
    | zero => rfl
    | succ n => exact hzero
  have hreconstruct :
      DensePoly.C u * f = (DensePoly.C v * g) * (DensePoly.C (u * v⁻¹) * (f / g)) := by
    have step1 : DensePoly.C u * f = DensePoly.C u * ((f / g) * g) := by
      rw [hquot_mul]
    have hcomm_q_g : (f / g) * g = g * (f / g) :=
      DensePoly.mul_comm_poly (f / g) g
    have step2 : DensePoly.C u * ((f / g) * g) = DensePoly.C u * (g * (f / g)) :=
      congrArg (fun x => DensePoly.C u * x) hcomm_q_g
    have step3 : DensePoly.C u * (g * (f / g)) = (DensePoly.C u * g) * (f / g) :=
      (DensePoly.mul_assoc_poly (DensePoly.C u : FpPoly p) g (f / g)).symm
    have step4 : (DensePoly.C u * g) * (f / g) =
        (DensePoly.C (v * (u * v⁻¹)) * g) * (f / g) := by
      have h : DensePoly.C u = DensePoly.C (v * (u * v⁻¹) : ZMod64 p) := by
        rw [hv_uv_inv]
      rw [h]
    have step5 : (DensePoly.C (v * (u * v⁻¹)) * g) * (f / g) =
        (DensePoly.C v * DensePoly.C (u * v⁻¹) * g) * (f / g) := by
      have h := hC_mul_C_eq_C v (u * v⁻¹)
      rw [← h]
    have step6 : (DensePoly.C v * DensePoly.C (u * v⁻¹) * g) * (f / g) =
        (DensePoly.C v * (DensePoly.C (u * v⁻¹) * g)) * (f / g) :=
      congrArg (fun x => x * (f / g))
        (DensePoly.mul_assoc_poly (DensePoly.C v : FpPoly p)
          (DensePoly.C (u * v⁻¹)) g)
    have step7 : (DensePoly.C v * (DensePoly.C (u * v⁻¹) * g)) * (f / g) =
        (DensePoly.C v * (g * DensePoly.C (u * v⁻¹))) * (f / g) := by
      have hcomm : (DensePoly.C (u * v⁻¹) : FpPoly p) * g = g * DensePoly.C (u * v⁻¹) :=
        DensePoly.mul_comm_poly (DensePoly.C (u * v⁻¹) : FpPoly p) g
      have hC_g : DensePoly.C v * (DensePoly.C (u * v⁻¹) * g) =
          DensePoly.C v * (g * DensePoly.C (u * v⁻¹)) :=
        congrArg (fun x => DensePoly.C v * x) hcomm
      exact congrArg (fun x => x * (f / g)) hC_g
    have step8 : (DensePoly.C v * (g * DensePoly.C (u * v⁻¹))) * (f / g) =
        ((DensePoly.C v * g) * DensePoly.C (u * v⁻¹)) * (f / g) :=
      congrArg (fun x => x * (f / g))
        (DensePoly.mul_assoc_poly (DensePoly.C v : FpPoly p) g
          (DensePoly.C (u * v⁻¹))).symm
    have step9 : ((DensePoly.C v * g) * DensePoly.C (u * v⁻¹)) * (f / g) =
        (DensePoly.C v * g) * (DensePoly.C (u * v⁻¹) * (f / g)) :=
      DensePoly.mul_assoc_poly (DensePoly.C v * g) (DensePoly.C (u * v⁻¹)) (f / g)
    exact step1.trans (step2.trans (step3.trans (step4.trans (step5.trans
      (step6.trans (step7.trans (step8.trans step9)))))))
  -- C v * g divides C u * f, so the executable quotient * divisor reconstructs the dividend.
  have hdvd_scaled : DensePoly.C v * g ∣ DensePoly.C u * f := by
    refine ⟨DensePoly.C (u * v⁻¹) * (f / g), ?_⟩
    exact hreconstruct
  have hmod_zero : (DensePoly.C u * f) % (DensePoly.C v * g) = 0 :=
    DensePoly.mod_eq_zero_of_dvd (DensePoly.C u * f) (DensePoly.C v * g) hdvd_scaled
  have hrec_scaled :
      ((DensePoly.C u * f) / (DensePoly.C v * g)) * (DensePoly.C v * g) +
        ((DensePoly.C u * f) % (DensePoly.C v * g)) =
        DensePoly.C u * f :=
    DensePoly.div_mul_add_mod (DensePoly.C u * f) (DensePoly.C v * g)
  have hquot_mul_scaled :
      ((DensePoly.C u * f) / (DensePoly.C v * g)) * (DensePoly.C v * g) =
        DensePoly.C u * f := by
    rw [hmod_zero] at hrec_scaled
    rwa [add_zero] at hrec_scaled
  -- (C u * f) / (C v * g) * (C v * g) = (C (u * v⁻¹) * (f / g)) * (C v * g).
  have hcancel_eq :
      ((DensePoly.C u * f) / (DensePoly.C v * g)) * (DensePoly.C v * g) =
        (DensePoly.C (u * v⁻¹) * (f / g)) * (DensePoly.C v * g) := by
    rw [hquot_mul_scaled, hreconstruct]
    exact DensePoly.mul_comm_poly (DensePoly.C v * g)
      (DensePoly.C (u * v⁻¹) * (f / g))
  exact mul_right_cancel_of_ne_zero hCvg_ne hcancel_eq

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

private theorem scaled_gcd_eq_zero
    [ZMod64.PrimeModulus p]
    (u_c u_w : ZMod64 p) (c w : FpPoly p)
    (h : DensePoly.gcd c w = 0) :
    DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) = 0 := by
  rcases gcd_eq_zero_forces_zero c w h with ⟨hc, hw⟩
  rw [hc, hw, mul_zero, mul_zero, DensePoly.gcd_zero_zero]

private theorem div_zero_eq_zero (f : FpPoly p) :
    f / (0 : FpPoly p) = 0 := by
  have hpair :=
    DensePoly.divMod_eq_zero_self_of_size_zero_core f (0 : FpPoly p) (by simp)
  simpa [DensePoly.div] using congrArg Prod.fst hpair

private theorem div_zero_C_mul_left
    [ZMod64.PrimeModulus p]
    (u : ZMod64 p) {c w : FpPoly p} (h : DensePoly.gcd c w = 0) :
    (DensePoly.C u * c) / (0 : FpPoly p) =
      DensePoly.C u * (c / (0 : FpPoly p)) := by
  have hc : c = 0 := (gcd_eq_zero_forces_zero c w h).1
  simp [hc, div_zero_eq_zero]

private theorem div_zero_C_mul_right
    [ZMod64.PrimeModulus p]
    (u : ZMod64 p) {c w : FpPoly p} (h : DensePoly.gcd c w = 0) :
    (DensePoly.C u * w) / (0 : FpPoly p) =
      DensePoly.C u * (w / (0 : FpPoly p)) := by
  have hw : w = 0 := (gcd_eq_zero_forces_zero c w h).2
  simp [hw, div_zero_eq_zero]

/--
Yun's inner loop: peel off the factors with multiplicities `i`, `i + 1`, ...
from the coprime/repeated split `(c, w)`, consing each discovered factor onto
the reverse-order accumulator.
-/
private def yunFactorsWithLevel
    (c w : FpPoly p) (base level : Nat) (fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (accRev, w)
  | fuel + 1 =>
      if isOne c then
        (accRev, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let accRev' :=
          if isOne z then
            accRev
          else
            { factor := z, multiplicity := base * level } :: accRev
        yunFactorsWithLevel y (w / y) base (level + 1) fuel accRev'

private def yunFactors
    (c w : FpPoly p) (i : Nat) (fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (accRev, w)
  | fuel + 1 =>
      if isOne c then
        (accRev, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let accRev' :=
          if isOne z then
            accRev
          else
            { factor := z, multiplicity := i } :: accRev
        yunFactors y (w / y) (i + 1) fuel accRev'

/--
Specification payload for `yunFactors`: the first component is the product
contributed by factors discovered from `(c, w, i, fuel)`, and the second is
the repeated part that remains for the `p`-th-root descent.
-/
private def yunFactorsContributionWithLevel
    (c w : FpPoly p) (base level : Nat) : Nat → FpPoly p × FpPoly p
  | 0 => (1, w)
  | fuel + 1 =>
      if isOne c then
        (1, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let tail := yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel
        let contribution :=
          if isOne z then
            tail.1
          else
            pow z (base * level) * tail.1
        (contribution, tail.2)

private def yunFactorsContribution
    (c w : FpPoly p) (i : Nat) : Nat → FpPoly p × FpPoly p
  | 0 => (1, w)
  | fuel + 1 =>
      if isOne c then
        (1, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let tail := yunFactorsContribution y (w / y) (i + 1) fuel
        let contribution :=
          if isOne z then
            tail.1
          else
            pow z i * tail.1
        (contribution, tail.2)

private theorem yunFactorsWithLevel_reconstruction_invariant
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    let loop := yunFactorsWithLevel c w base level fuel accRev
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    loop.2 = contribution.2 ∧
      weightedProduct loop.1.reverse =
        weightedProduct accRev.reverse * contribution.1 := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel, yunFactorsContributionWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel, yunFactorsContributionWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (level + 1) accRev
        · have htail := ih y (w / y) (level + 1)
            ({ factor := z, multiplicity := base * level } :: accRev)
          constructor
          · simpa [y, z, hz] using htail.1
          · have hmul :
                weightedProduct (yunFactorsWithLevel y (w / y) base (level + 1) fuel
                    ({ factor := z, multiplicity := base * level } :: accRev)).1.reverse =
                  weightedProduct accRev.reverse *
                    (pow z (base * level) *
                      (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1) := by
              calc
                weightedProduct (yunFactorsWithLevel y (w / y) base (level + 1) fuel
                    ({ factor := z, multiplicity := base * level } :: accRev)).1.reverse
                    = weightedProduct ({ factor := z, multiplicity := base * level } :: accRev).reverse *
                        (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                          simpa [y, z] using htail.2
                _ = (weightedProduct accRev.reverse * pow z (base * level)) *
                        (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                          rw [weightedProduct_reverse_cons]
                _ = weightedProduct accRev.reverse *
                        (pow z (base * level) *
                          (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1) := by
                          exact DensePoly.mul_assoc_poly
                            (weightedProduct accRev.reverse) (pow z (base * level))
                            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1
            simpa [y, z, hz] using hmul

private theorem yunFactors_reconstruction_invariant
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    let loop := yunFactors c w i fuel accRev
    let contribution := yunFactorsContribution c w i fuel
    loop.2 = contribution.2 ∧
      weightedProduct loop.1.reverse =
        weightedProduct accRev.reverse * contribution.1 := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors, yunFactorsContribution]
  | succ fuel ih =>
      simp only [yunFactors, yunFactorsContribution]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · have htail := ih y (w / y) (i + 1) ({ factor := z, multiplicity := i } :: accRev)
          constructor
          · simpa [y, z, hz] using htail.1
          · have hmul :
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse =
                  weightedProduct accRev.reverse *
                    (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
              calc
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse
                    = weightedProduct ({ factor := z, multiplicity := i } :: accRev).reverse *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          simpa [y, z] using htail.2
                _ = (weightedProduct accRev.reverse * pow z i) *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          rw [weightedProduct_reverse_cons]
                _ = weightedProduct accRev.reverse *
                        (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
                          exact DensePoly.mul_assoc_poly
                            (weightedProduct accRev.reverse) (pow z i)
                            (yunFactorsContribution y (w / y) (i + 1) fuel).1
            simpa [y, z, hz] using hmul

/--
Product contribution of `squareFreeAuxRev` before it is multiplied into the
caller-provided reverse accumulator.
-/
private def squareFreeAuxRevContribution (f : FpPoly p) (multiplicity : Nat) :
    Nat → FpPoly p
  | 0 => 1
  | fuel + 1 =>
      if f.isZero then
        1
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel
        else
          let g := DensePoly.gcd f df
          let c := f / g
          let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
          if isOne contribution.2 then
            contribution.1
          else
            contribution.1 *
              squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel

private theorem squareFreeAuxRevContribution_pthRoot_correct_pow
    (_hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (_hfuel : f.size < fuel + 1)
    (_hzero : f.isZero = false)
    (_hdf : (DensePoly.derivative f).isZero = true)
    (hroot :
      squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
      pow (pthRoot f) (multiplicity * p) := by
  exact hroot

private theorem derivative_coeff_pred_of_pos_lt
    (f : FpPoly p) {n : Nat} (hn0 : 0 < n) (hn : n < f.size) :
    (DensePoly.derivative f).coeff (n - 1) =
      ((n : Nat) : ZMod64 p) * f.coeff n := by
  unfold DensePoly.derivative
  rw [DensePoly.coeff_ofCoeffs_list]
  have hpred : n - 1 < f.size - 1 := by omega
  have hget :
      (((List.range (f.size - 1)).map
          (fun i => (((i + 1 : Nat) : ZMod64 p) * f.coeff (i + 1)))).getD
        (n - 1) (0 : ZMod64 p)) =
          (((n - 1 + 1 : Nat) : ZMod64 p) * f.coeff (n - 1 + 1)) := by
    simp [List.getD, hpred]
  have hsucc : n - 1 + 1 = n := by omega
  simpa [hsucc] using hget

private theorem zmod64_natCast_ne_zero_of_mod_ne_zero
    (n : Nat) (hn : n % p ≠ 0) :
    ((n : Nat) : ZMod64 p) ≠ 0 := by
  intro hzero
  apply hn
  have hnat := congrArg ZMod64.toNat hzero
  simpa using hnat

private theorem derivative_zero_coeff_non_pmultiple
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (n : Nat)
    (hdf : (DensePoly.derivative f).isZero = true) (hn : n % p ≠ 0) :
    f.coeff n = 0 := by
  by_cases hsize : f.size ≤ n
  · exact DensePoly.coeff_eq_zero_of_size_le f hsize
  · have hnlt : n < f.size := Nat.lt_of_not_ge hsize
    have hn0 : 0 < n := by
      cases n with
      | zero =>
          simp at hn
      | succ n =>
          exact Nat.succ_pos n
    have hderiv_zero_poly : DensePoly.derivative f = 0 :=
      eq_zero_of_isZero_true (DensePoly.derivative f) hdf
    have hderiv_coeff : (DensePoly.derivative f).coeff (n - 1) = 0 := by
      rw [hderiv_zero_poly]
      exact DensePoly.coeff_zero (R := ZMod64 p) (n - 1)
    have hmul :
        ((n : Nat) : ZMod64 p) * f.coeff n = 0 := by
      rw [← derivative_coeff_pred_of_pos_lt f hn0 hnlt]
      exact hderiv_coeff
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hmul with hnzero | hcoeff
    · exact False.elim (zmod64_natCast_ne_zero_of_mod_ne_zero n hn hnzero)
    · exact hcoeff

private theorem size_pos_of_isZero_false
    (f : FpPoly p) (hzero : f.isZero = false) :
    0 < f.size := by
  simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
    Nat.pos_iff_ne_zero] using hzero

private theorem size_eq_zero_of_isZero_true
    (f : FpPoly p) (hzero : f.isZero = true) :
    f.size = 0 := by
  simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero

private theorem pthRoot_one
    (hp : Hex.Nat.Prime p) :
    pthRoot (1 : FpPoly p) = 1 := by
  apply DensePoly.ext_coeff
  intro i
  rw [pthRoot_coeff]
  cases i with
  | zero =>
      simp
  | succ i =>
      have hp_pos : 0 < p := by
        have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
        omega
      have hne : (i + 1) * p ≠ 0 := by
        exact Nat.mul_ne_zero (Nat.succ_ne_zero i) (Nat.ne_of_gt hp_pos)
      change (DensePoly.C (1 : ZMod64 p)).coeff ((i + 1) * p) =
        (DensePoly.C (1 : ZMod64 p)).coeff (i + 1)
      rw [DensePoly.coeff_C, DensePoly.coeff_C]
      simp [hne]

private theorem pow_one_base (n : Nat) :
    pow (1 : FpPoly p) n = 1 := by
  rw [pow_eq_powLinear]
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [powLinear, ih]
      exact mul_one (1 : FpPoly p)

private theorem squareFreeAuxRevContribution_one
    (hp : Hex.Nat.Prime p) (multiplicity fuel : Nat) :
    squareFreeAuxRevContribution (1 : FpPoly p) multiplicity fuel = 1 := by
  induction fuel generalizing multiplicity with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [squareFreeAuxRevContribution]
      have hone_ne : (1 : FpPoly p).isZero = false := by
        have hcoeffs :
            (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        simp [DensePoly.isZero, hcoeffs]
      have hdf_one : (DensePoly.derivative (1 : FpPoly p)).isZero = true := by
        have hcoeffs :
            (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        have hsize : (1 : FpPoly p).size = 1 := by
          simpa [DensePoly.size] using congrArg Array.size hcoeffs
        unfold DensePoly.derivative
        simp [hsize, DensePoly.isZero, DensePoly.ofCoeffs, DensePoly.trimTrailingZeros]
        rfl
      simp [hone_ne]
      rw [hdf_one]
      rw [pthRoot_one hp]
      exact ih (multiplicity * p)

private theorem derivative_isZero_true_of_size_one
    (f : FpPoly p) (hsize : f.size = 1) :
    (DensePoly.derivative f).isZero = true := by
  unfold DensePoly.derivative
  simp [hsize, DensePoly.isZero, DensePoly.ofCoeffs, DensePoly.trimTrailingZeros]
  rfl

private theorem pthRoot_eq_self_of_size_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hsize : f.size = 1) :
    pthRoot f = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [pthRoot_coeff]
  cases n with
  | zero =>
      simp
  | succ n =>
      have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
      have hidx : 1 ≤ (n + 1) * p := by
        have hp_one : 1 ≤ p := by omega
        have hmul : 1 * p ≤ (n + 1) * p :=
          Nat.mul_le_mul_right p (by omega)
        omega
      have hroot_zero :
          f.coeff ((n + 1) * p) = 0 := by
        apply DensePoly.coeff_eq_zero_of_size_le
        omega
      have hf_zero : f.coeff (n + 1) = 0 := by
        apply DensePoly.coeff_eq_zero_of_size_le
        omega
      rw [hroot_zero, hf_zero]

private theorem squareFreeAuxRevContribution_size_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hsize : f.size = 1) :
    squareFreeAuxRevContribution f multiplicity fuel = 1 := by
  induction fuel generalizing f multiplicity with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [squareFreeAuxRevContribution]
      have hzero : f.isZero = false := by
        cases hz : f.isZero
        · rfl
        · have hzero_size : f.size = 0 := size_eq_zero_of_isZero_true f hz
          omega
      have hdf : (DensePoly.derivative f).isZero = true :=
        derivative_isZero_true_of_size_one f hsize
      rw [if_neg (by simp [hzero]), if_pos hdf]
      have hroot_size : (pthRoot f).size = 1 := by
        rw [pthRoot_eq_self_of_size_one hp f hsize, hsize]
      exact ih (pthRoot f) (multiplicity * p) hroot_size

private theorem squareFreeAuxRevContribution_pthRoot_constant_correct
    (hp : Hex.Nat.Prime p) (multiplicity fuel : Nat) :
    squareFreeAuxRevContribution (pthRoot (1 : FpPoly p)) multiplicity fuel =
      pow (pthRoot (1 : FpPoly p)) multiplicity := by
  rw [pthRoot_one hp, squareFreeAuxRevContribution_one hp, pow_one_base]

private theorem derivative_zero_top_degree_mod_eq_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (f.size - 1) % p = 0 := by
  by_cases hmod : (f.size - 1) % p = 0
  · exact hmod
  ·
    have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
    have hcoeff_zero :=
      derivative_zero_coeff_non_pmultiple hp f (f.size - 1) hdf hmod
    have hcoeff_ne := DensePoly.coeff_last_ne_zero_of_pos_size f hpos
    exact False.elim (hcoeff_ne hcoeff_zero)

private theorem pthRoot_nonzero_of_derivative_zero_nonconstant
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hsize : 1 < f.size) :
    (pthRoot f).isZero = false := by
  by_cases hroot_false : (pthRoot f).isZero = false
  · exact hroot_false
  ·
    have hroot_true : (pthRoot f).isZero = true := by
      cases h : (pthRoot f).isZero <;> simp [h] at hroot_false ⊢
    have hroot_size : (pthRoot f).size = 0 :=
      size_eq_zero_of_isZero_true (pthRoot f) hroot_true
    let i := (f.size - 1) / p
    have hcoeff_root_zero :
        (pthRoot f).coeff i = 0 := by
      exact DensePoly.coeff_eq_zero_of_size_le (pthRoot f) (by
        rw [hroot_size]
        exact Nat.zero_le i)
    have hcoeff_f_zero : f.coeff (f.size - 1) = 0 := by
      have hmod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
      have hmul : i * p = f.size - 1 := by
        have h := Nat.mod_add_div (f.size - 1) p
        rw [hmod, Nat.zero_add] at h
        simpa [i, Nat.mul_comm] using h
      rw [pthRoot_coeff] at hcoeff_root_zero
      simpa [hmul] using hcoeff_root_zero
    have hpos : 0 < f.size := by omega
    exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f hpos hcoeff_f_zero)

private theorem pthRoot_fuel_decrease_of_derivative_zero_nonconstant
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hsize : 1 < f.size) :
    (pthRoot f).size < fuel := by
  by_cases hlt : (pthRoot f).size < fuel
  · exact hlt
  ·
    have hf_le : f.size ≤ fuel := by omega
    have hfuel_pos : 0 < fuel := by omega
    let i := (pthRoot f).size - 1
    have hi_lt : i < (pthRoot f).size := by omega
    have hroot_coeff_ne :
        (pthRoot f).coeff i ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size (pthRoot f) (by omega)
    have hroot_coeff_zero :
        (pthRoot f).coeff i = 0 := by
      rw [pthRoot_coeff]
      exact DensePoly.coeff_eq_zero_of_size_le f (by
        have hp_two : 2 ≤ p := Hex.Nat.Prime.two_le hp
        have hige : fuel - 1 ≤ i := by omega
        have hi : i * p ≥ fuel := by
          dsimp [i]
          have hfuel_ge_two : 2 ≤ fuel := by omega
          calc
            fuel = (fuel - 1) + 1 := by omega
            _ ≤ (fuel - 1) + (fuel - 1) := by omega
            _ = 2 * (fuel - 1) := by omega
            _ ≤ p * i := by
              exact Nat.mul_le_mul hp_two hige
            _ = i * p := Nat.mul_comm p i
        omega)
    exact False.elim (hroot_coeff_ne hroot_coeff_zero)

private theorem pthRoot_frobenius_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (_hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) p = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [pthRoot_pow_prime_coeff hp f n]
  by_cases hn : n % p = 0
  · simp [hn]
  · simp [hn, derivative_zero_coeff_non_pmultiple hp f n hdf hn]

private theorem pthRoot_frobenius_of_derivative_zero'
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) p = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [pthRoot_pow_prime_coeff hp f n]
  by_cases hn : n % p = 0
  · simp [hn]
  · simp [hn, derivative_zero_coeff_non_pmultiple hp f n hdf hn]

private theorem pthRoot_dvd_self_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pthRoot f ∣ f := by
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  refine ⟨pow (pthRoot f) (p - 1), ?_⟩
  calc
    f = pow (pthRoot f) p := by
      exact (pthRoot_frobenius_of_derivative_zero hp f hzero hdf).symm
    _ = pow (pthRoot f) (1 + (p - 1)) := by
      have hp_eq : 1 + (p - 1) = p := by omega
      rw [hp_eq]
    _ = pow (pthRoot f) 1 * pow (pthRoot f) (p - 1) := by
      exact pow_add_exp (pthRoot f) 1 (p - 1)
    _ = pthRoot f * pow (pthRoot f) (p - 1) := by
      rw [pow_one]

private theorem pow_pow_mul
    (f : FpPoly p) (m n : Nat) (_hm : 0 < m) :
    pow (pow f n) m = pow f (m * n) := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_powLinear_mul f m n

private theorem pthRoot_pow_mul_prime_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) (multiplicity * p) = pow f multiplicity := by
  calc
    pow (pthRoot f) (multiplicity * p) =
        pow (pow (pthRoot f) p) multiplicity := by
          exact (pow_pow_mul (pthRoot f) multiplicity p hmultiplicity).symm
    _ = pow f multiplicity := by
          rw [pthRoot_frobenius_of_derivative_zero hp f hzero hdf]

private theorem squareFreeAuxRevContribution_derivative_zero_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hroot :
      squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
      pow f multiplicity := by
  calc
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p) := by
          exact squareFreeAuxRevContribution_pthRoot_correct_pow
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf hroot
    _ = pow f multiplicity := by
          exact pthRoot_pow_mul_prime_of_derivative_zero
            hp f multiplicity hmultiplicity hzero hdf

private def squareFreeContributionReachable (f : FpPoly p) : Prop :=
  f.size = 1 → f = 1

private theorem squareFreeContributionReachable_of_monic
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    squareFreeContributionReachable f := by
  intro hsize
  apply DensePoly.ext_coeff
  intro n
  cases n with
  | zero =>
      have hpos : 0 < f.size := by omega
      have hlead : DensePoly.leadingCoeff f = f.coeff 0 := by
        have hlead_last :
            DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
          unfold DensePoly.leadingCoeff DensePoly.coeff
          rw [Array.back?_eq_getElem?]
          have hidx : f.coeffs.size - 1 < f.coeffs.size := by
            simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
          simp [Array.getD, DensePoly.size, hidx]
        simpa [hsize] using hlead_last
      change f.coeff 0 = (DensePoly.C (1 : ZMod64 p)).coeff 0
      rw [← hlead, hmonic]
      exact (DensePoly.coeff_C (1 : ZMod64 p) 0).symm
  | succ n =>
      have hn : f.size ≤ n + 1 := by omega
      change f.coeff (n + 1) = (DensePoly.C (1 : ZMod64 p)).coeff (n + 1)
      rw [DensePoly.coeff_eq_zero_of_size_le f hn]
      exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm

private theorem normalizedDerivativeActiveState_of_monic_nonzero
    (c w : FpPoly p)
    (hc_monic : DensePoly.Monic c)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false) :
    squareFreeContributionReachable c ∧
      c.isZero = false ∧
        w.isZero = false := by
  exact ⟨squareFreeContributionReachable_of_monic c hc_monic, hc_zero, hw_zero⟩

private theorem pthRoot_reachable_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeContributionReachable (pthRoot f) := by
  intro hroot_size
  have hf_size_one : f.size = 1 := by
    by_cases hf : f.size = 1
    · exact hf
    ·
      have hf_gt : 1 < f.size := by
        have hpos := size_pos_of_isZero_false f hzero
        omega
      have htop_mod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
      let i := (f.size - 1) / p
      have hi_pos : 0 < i := by
        have hdiv : i * p = f.size - 1 := by
          have h := Nat.mod_add_div (f.size - 1) p
          rw [htop_mod, Nat.zero_add] at h
          simpa [i, Nat.mul_comm] using h
        by_cases hi : i = 0
        · rw [hi] at hdiv
          simp at hdiv
          omega
        · exact Nat.pos_of_ne_zero hi
      have hi_ge : 1 ≤ i := Nat.succ_le_of_lt hi_pos
      have hroot_zero :
          (pthRoot f).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (pthRoot f) (by
          rw [hroot_size]
          exact hi_ge)
      have hf_zero : f.coeff (f.size - 1) = 0 := by
        have hmul : i * p = f.size - 1 := by
          have h := Nat.mod_add_div (f.size - 1) p
          rw [htop_mod, Nat.zero_add] at h
          simpa [i, Nat.mul_comm] using h
        rw [pthRoot_coeff] at hroot_zero
        simpa [hmul] using hroot_zero
      exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f (by omega) hf_zero)
  have hf_one : f = 1 := hreachable hf_size_one
  rw [hf_one]
  exact pthRoot_one hp

private theorem div_gcd_mul_reconstruct [ZMod64.PrimeModulus p] (f df : FpPoly p) :
    (f / DensePoly.gcd f df) * DensePoly.gcd f df = f := by
  have hspec := DensePoly.div_mul_add_mod f (DensePoly.gcd f df)
  have hmod :
      f % DensePoly.gcd f df = 0 :=
    DensePoly.mod_eq_zero_of_dvd f (DensePoly.gcd f df)
      (DensePoly.gcd_dvd_left f df)
  rw [hmod] at hspec
  rw [add_zero] at hspec
  exact hspec

private theorem gcd_mul_div_reconstruct [ZMod64.PrimeModulus p] (f df : FpPoly p) :
    DensePoly.gcd f df * (f / DensePoly.gcd f df) = f := by
  rw [mul_comm]
  exact div_gcd_mul_reconstruct f df

private theorem div_gcd_right_mul_reconstruct [ZMod64.PrimeModulus p] (c w : FpPoly p) :
    (w / DensePoly.gcd c w) * DensePoly.gcd c w = w := by
  have hspec := DensePoly.div_mul_add_mod w (DensePoly.gcd c w)
  have hmod :
      w % DensePoly.gcd c w = 0 :=
    DensePoly.mod_eq_zero_of_dvd w (DensePoly.gcd c w)
      (DensePoly.gcd_dvd_right c w)
  rw [hmod] at hspec
  rw [add_zero] at hspec
  exact hspec

private theorem gcd_mul_div_right_reconstruct [ZMod64.PrimeModulus p] (c w : FpPoly p) :
    DensePoly.gcd c w * (w / DensePoly.gcd c w) = w := by
  rw [mul_comm]
  exact div_gcd_right_mul_reconstruct c w

/-- A monic prime-field polynomial is nonzero: its leading coefficient `1` is
nonzero by `zmod64_one_ne_zero_of_prime`, while a zero polynomial has leading
coefficient `0`. -/
private theorem ne_zero_of_monic_fpoly
    (hp : Hex.Nat.Prime p) {f : FpPoly p} (hmonic : DensePoly.Monic f) :
    f ≠ 0 := by
  intro hzero
  have hlead_one : DensePoly.leadingCoeff f = 1 := hmonic
  rw [hzero] at hlead_one
  have hlead_zero : DensePoly.leadingCoeff (0 : FpPoly p) = (0 : ZMod64 p) := by
    unfold DensePoly.leadingCoeff
    rfl
  rw [hlead_zero] at hlead_one
  exact zmod64_one_ne_zero_of_prime hp hlead_one.symm

/-- A monic prime-field polynomial has unit scalar `1` under `normalizeMonic`:
the recorded leading coefficient is `1`, matching the leading coefficient of
the input. Companion to `normalizeMonic_eq_self_of_monic`. -/
private theorem normalizeMonic_fst_eq_one_of_monic
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    (normalizeMonic f).1 = 1 := by
  have hzero : f.isZero = false := by
    cases hz : f.isZero with
    | false => rfl
    | true =>
        exfalso
        have hf_zero : f = 0 := eq_zero_of_isZero_true f hz
        have hlead : DensePoly.leadingCoeff f = (1 : ZMod64 p) := hmonic
        rw [hf_zero, DensePoly.leadingCoeff_zero] at hlead
        exact zmod64_one_ne_zero_of_prime hp hlead.symm
  rw [normalizeMonic_nonzero f hzero]
  exact hmonic

/-- `normalizeMonic` is transparent on an already-monic polynomial: the
polynomial component of the split is the input unchanged. This lets downstream
code collapse a normalized provider back to the raw polynomial whenever it has
an explicit `DensePoly.Monic` hypothesis for that exact polynomial. -/
private theorem normalizeMonic_eq_self_of_monic
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    (normalizeMonic f).2 = f := by
  have hfst : (normalizeMonic f).1 = 1 :=
    normalizeMonic_fst_eq_one_of_monic hp f hmonic
  have hrec : DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f :=
    normalizeMonic_reconstruct hp f
  rw [hfst] at hrec
  have hC_one : DensePoly.C (1 : ZMod64 p) = (1 : FpPoly p) := rfl
  rw [hC_one, one_mul] at hrec
  exact hrec

/-- Exact-quotient monicity: given a multiplicative factorization `q * b = a`
with `a` and `b` both monic in `FpPoly p`, the quotient `q` is also monic.

Used as substrate for the Yun derivative-active monic-residual invariant
(#6155): each Yun-loop transition produces an exact-quotient residual
`w / gcd c w` whose monicity is dispatched by combining this lemma with the
reconstruction identity `(w / gcd c w) * gcd c w = w`. The lemma also handles
the initial split residual `f / gcd f f'` symmetrically. -/
private theorem monic_of_mul_eq_monic_of_monic
    [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    {a b q : FpPoly p}
    (ha_monic : DensePoly.Monic a)
    (hb_monic : DensePoly.Monic b)
    (hrec : q * b = a) :
    DensePoly.Monic q := by
  have ha_ne : a ≠ 0 := ne_zero_of_monic_fpoly hp ha_monic
  have hb_ne : b ≠ 0 := ne_zero_of_monic_fpoly hp hb_monic
  have hq_ne : q ≠ 0 := by
    intro hq
    apply ha_ne
    rw [← hrec, hq, zero_mul]
  have hlead_a : DensePoly.leadingCoeff a = 1 := ha_monic
  have hlead_b : DensePoly.leadingCoeff b = 1 := hb_monic
  have hlead_mul :
      DensePoly.leadingCoeff (q * b) =
        DensePoly.leadingCoeff q * DensePoly.leadingCoeff b :=
    FpPoly.leadingCoeff_mul q b hq_ne hb_ne
  have hlead_q_b :
      DensePoly.leadingCoeff q * DensePoly.leadingCoeff b = 1 := by
    rw [← hlead_mul, hrec, hlead_a]
  have hlead_q : DensePoly.leadingCoeff q = 1 := by
    rw [hlead_b] at hlead_q_b
    simpa using hlead_q_b
  exact hlead_q

/-- Exact-quotient monicity for the left Yun residual: from monic `c` and a
monic gcd-output divisor, the left exact quotient `c / DensePoly.gcd c w` is
monic. This is a direct corollary of `monic_of_mul_eq_monic_of_monic` paired
with the reconstruction identity `(c / gcd c w) * gcd c w = c`. -/
private theorem monic_div_gcd_left_of_monic
    [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p)
    (hc_monic : DensePoly.Monic c)
    (hgcd_monic : DensePoly.Monic (DensePoly.gcd c w)) :
    DensePoly.Monic (c / DensePoly.gcd c w) :=
  monic_of_mul_eq_monic_of_monic hp hc_monic hgcd_monic
    (div_gcd_mul_reconstruct c w)

/-- Exact-quotient monicity for the right Yun residual: from monic `w` and a
monic gcd-output divisor, the right exact quotient `w / DensePoly.gcd c w` is
monic. This is the quotient threaded into the next Yun derivative-active state
`(gcd c w, w / gcd c w)`, so this lemma supplies the residual-monicity step
needed by the #6155 invariant induction. -/
private theorem monic_div_gcd_right_of_monic
    [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p)
    (hw_monic : DensePoly.Monic w)
    (hgcd_monic : DensePoly.Monic (DensePoly.gcd c w)) :
    DensePoly.Monic (w / DensePoly.gcd c w) :=
  monic_of_mul_eq_monic_of_monic hp hw_monic hgcd_monic
    (div_gcd_right_mul_reconstruct c w)

/--
Algebraic step identity used to thread the scaled Yun product invariant through
a single non-terminating iteration. With `y = gcd c w`, `z = c / y`, and
`v = w / y`, the input `pow c (base * level) * pow w base` rebalances to
`pow z (base * level) * pow y (base * (level + 1)) * pow v base`, capturing the
emission of `z` at multiplicity `base * level` while moving `g`'s remaining
factor into the next level.
-/
private theorem yunFactorsContributionWithLevel_pow_step_algebra
    [ZMod64.PrimeModulus p] (c w : FpPoly p) (base level : Nat) :
    pow c (base * level) * pow w base =
      pow (c / DensePoly.gcd c w) (base * level) *
        pow (DensePoly.gcd c w) (base * (level + 1)) *
        pow (w / DensePoly.gcd c w) base := by
  have hqg : (c / DensePoly.gcd c w) * DensePoly.gcd c w = c :=
    div_gcd_mul_reconstruct c w
  have hvg : (w / DensePoly.gcd c w) * DensePoly.gcd c w = w :=
    div_gcd_right_mul_reconstruct c w
  have hexp : base * level + base = base * (level + 1) := by
    rw [Nat.mul_succ]
  calc pow c (base * level) * pow w base
      = pow ((c / DensePoly.gcd c w) * DensePoly.gcd c w) (base * level) *
          pow ((w / DensePoly.gcd c w) * DensePoly.gcd c w) base := by rw [hqg, hvg]
    _ = (pow (c / DensePoly.gcd c w) (base * level) *
            pow (DensePoly.gcd c w) (base * level)) *
          (pow (w / DensePoly.gcd c w) base * pow (DensePoly.gcd c w) base) := by
        rw [pow_mul_base (c / DensePoly.gcd c w) (DensePoly.gcd c w) (base * level),
            pow_mul_base (w / DensePoly.gcd c w) (DensePoly.gcd c w) base]
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          (pow (DensePoly.gcd c w) (base * level) *
            (pow (w / DensePoly.gcd c w) base * pow (DensePoly.gcd c w) base)) := by
        exact DensePoly.mul_assoc_poly _ _ _
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          ((pow (DensePoly.gcd c w) (base * level) * pow (w / DensePoly.gcd c w) base) *
            pow (DensePoly.gcd c w) base) := by
        exact congrArg
          (fun x => pow (c / DensePoly.gcd c w) (base * level) * x)
          (DensePoly.mul_assoc_poly
            (pow (DensePoly.gcd c w) (base * level))
            (pow (w / DensePoly.gcd c w) base)
            (pow (DensePoly.gcd c w) base)).symm
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          ((pow (w / DensePoly.gcd c w) base * pow (DensePoly.gcd c w) (base * level)) *
            pow (DensePoly.gcd c w) base) := by
        exact congrArg
          (fun x => pow (c / DensePoly.gcd c w) (base * level) *
            (x * pow (DensePoly.gcd c w) base))
          (DensePoly.mul_comm_poly
            (pow (DensePoly.gcd c w) (base * level))
            (pow (w / DensePoly.gcd c w) base))
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          (pow (w / DensePoly.gcd c w) base *
            (pow (DensePoly.gcd c w) (base * level) * pow (DensePoly.gcd c w) base)) := by
        exact congrArg
          (fun x => pow (c / DensePoly.gcd c w) (base * level) * x)
          (DensePoly.mul_assoc_poly
            (pow (w / DensePoly.gcd c w) base)
            (pow (DensePoly.gcd c w) (base * level))
            (pow (DensePoly.gcd c w) base))
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          (pow (w / DensePoly.gcd c w) base *
            pow (DensePoly.gcd c w) (base * level + base)) := by
        rw [← pow_add_exp]
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          (pow (w / DensePoly.gcd c w) base *
            pow (DensePoly.gcd c w) (base * (level + 1))) := by
        rw [hexp]
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          (pow (DensePoly.gcd c w) (base * (level + 1)) *
            pow (w / DensePoly.gcd c w) base) := by
        exact congrArg
          (fun x => pow (c / DensePoly.gcd c w) (base * level) * x)
          (DensePoly.mul_comm_poly
            (pow (w / DensePoly.gcd c w) base)
            (pow (DensePoly.gcd c w) (base * (level + 1))))
    _ = pow (c / DensePoly.gcd c w) (base * level) *
          pow (DensePoly.gcd c w) (base * (level + 1)) *
          pow (w / DensePoly.gcd c w) base := by
        exact (DensePoly.mul_assoc_poly _ _ _).symm

/--
Recursive termination predicate for the scaled Yun loop: the loop on
`(c, w, base, level)` reaches `isOne c = true` within `fuel` iterations.
The predicate is structural in `fuel`, with the witness chain mirroring
the loop's recursion through `(gcd c w, w / gcd c w, base, level + 1)`.
-/
private def yunFactorsLevelCompletes (c w : FpPoly p) (base : Nat) :
    Nat → Nat → Prop
  | _, 0 => isOne c = true
  | level, fuel + 1 =>
      isOne c = true ∨
        yunFactorsLevelCompletes
          (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel

/--
Normalized termination predicate for the scaled Yun loop. This mirrors
`yunFactorsLevelCompletes`, but tests the normalized current contribution.
It is the right progress predicate for raw scalar-unit states, where `c` may
be a non-one constant while `(normalizeMonic c).2 = 1`.
-/
private def yunFactorsNormalizedLevelCompletes (c w : FpPoly p) (base : Nat) :
    Nat → Nat → Prop
  | _, 0 => isOne (normalizeMonic c).2 = true
  | level, fuel + 1 =>
      isOne (normalizeMonic c).2 = true ∨
        yunFactorsNormalizedLevelCompletes
          (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel

/--
Conditional product invariant for the scaled Yun loop: when the loop
terminates by `isOne c = true` within the supplied `fuel`, the loop's
contribution times the power of its residual recovers
`pow c (base * level) * pow w base`. This is the deep algebraic content
of Yun's identity, packaged with the termination predicate so the
inductive base case discharges cleanly.
-/
private theorem yunFactorsContributionWithLevel_pow_invariant_of_completes
    [ZMod64.PrimeModulus p] (c w : FpPoly p) (base level fuel : Nat)
    (hcompletes : yunFactorsLevelCompletes c w base level fuel) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    contribution.1 * pow contribution.2 base =
      pow c (base * level) * pow w base := by
  induction fuel generalizing c w level with
  | zero =>
      -- contribution = (1, w); hcompletes gives c = 1.
      have hc_eq : c = 1 := eq_one_of_isOne_true c hcompletes
      subst hc_eq
      simp [yunFactorsContributionWithLevel, pow_one_base]
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · -- Loop terminates immediately: contribution = (1, w), c = 1.
        have hc_eq : c = 1 := eq_one_of_isOne_true c hc
        subst hc_eq
        simp [yunFactorsContributionWithLevel, hc, pow_one_base]
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_completes :
            yunFactorsLevelCompletes
              (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel := by
          cases hcompletes with
          | inl hcone => exact False.elim (hc hcone)
          | inr htail => exact htail
        have htail := ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
          htail_completes
        -- htail :
        --   (yunFactorsContributionWithLevel y v base (level+1) fuel).1 *
        --     pow (yunFactorsContributionWithLevel y v base (level+1) fuel).2 base =
        --   pow y (base * (level + 1)) * pow v base
        simp only [yunFactorsContributionWithLevel, hc_false]
        -- Goal involves let-bound y := gcd c w, z := c/y, tail := ...
        by_cases hz : isOne (c / DensePoly.gcd c w) = true
        · -- z = 1 case: contribution.1 = tail.1
          have hz_eq : c / DensePoly.gcd c w = 1 := eq_one_of_isOne_true _ hz
          simp [hz_eq, pow_one_base]
          -- pow c (b*l) = pow (z * y) (b*l) = pow z (b*l) * pow y (b*l)
          -- With z = 1: pow c (b*l) = pow y (b*l)
          -- htail gives: tail.1 * pow tail.2 base = pow y (base*(level+1)) * pow v base
          -- We want: tail.1 * pow tail.2 base = pow c (b*l) * pow w base
          -- This follows from the step algebra with z=1.
          have hstep :=
            yunFactorsContributionWithLevel_pow_step_algebra c w base level
          rw [hz_eq, pow_one_base, one_mul] at hstep
          rw [hstep]
          exact htail
        · -- z ≠ 1 case: contribution.1 = pow z (b*l) * tail.1
          have hz_false : isOne (c / DensePoly.gcd c w) = false := by
            cases h : isOne (c / DensePoly.gcd c w)
            · rfl
            · exact False.elim (hz h)
          simp [hz_false]
          -- Goal: pow z (b*l) * tail.1 * pow tail.2 base = pow c (b*l) * pow w base
          have hstep :=
            yunFactorsContributionWithLevel_pow_step_algebra c w base level
          calc pow (c / DensePoly.gcd c w) (base * level) *
                  (yunFactorsContributionWithLevel
                    (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel).1 *
                  pow (yunFactorsContributionWithLevel
                    (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel).2 base
              = pow (c / DensePoly.gcd c w) (base * level) *
                  ((yunFactorsContributionWithLevel
                    (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel).1 *
                    pow (yunFactorsContributionWithLevel
                      (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel).2 base) :=
                DensePoly.mul_assoc_poly _ _ _
            _ = pow (c / DensePoly.gcd c w) (base * level) *
                  (pow (DensePoly.gcd c w) (base * (level + 1)) *
                    pow (w / DensePoly.gcd c w) base) :=
                congrArg
                  (fun x => pow (c / DensePoly.gcd c w) (base * level) * x) htail
            _ = pow (c / DensePoly.gcd c w) (base * level) *
                  pow (DensePoly.gcd c w) (base * (level + 1)) *
                  pow (w / DensePoly.gcd c w) base :=
                (DensePoly.mul_assoc_poly _ _ _).symm
            _ = pow c (base * level) * pow w base := hstep.symm

private theorem gcd_isZero_false_of_right_isZero_false
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hb : b.isZero = false) :
    (DensePoly.gcd a b).isZero = false := by
  cases hg : (DensePoly.gcd a b).isZero
  · rfl
  · have hg_zero : DensePoly.gcd a b = 0 :=
      eq_zero_of_isZero_true (DensePoly.gcd a b) hg
    rcases DensePoly.gcd_dvd_right a b with ⟨q, hq⟩
    have hb_zero : b = 0 := by
      rw [hq, hg_zero, zero_mul]
    have hb_true : b.isZero = true := by
      rw [hb_zero]
      rfl
    rw [hb_true] at hb
    cases hb

private theorem yunFactorsContribution_step_split
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) :
    let y := DensePoly.gcd c w
    let z := c / y
    z * y = c ∧ (w / y) * y = w := by
  constructor
  · exact div_gcd_mul_reconstruct c w
  · exact div_gcd_right_mul_reconstruct c w

private theorem dvd_add_poly
    {d a b : FpPoly p} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a + b := by
  rcases hda with ⟨qa, hqa⟩
  rcases hdb with ⟨qb, hqb⟩
  refine ⟨qa + qb, ?_⟩
  calc a + b
      = d * qa + d * qb := by rw [hqa, hqb]
    _ = d * (qa + qb) := (DensePoly.mul_add_right_poly d qa qb).symm

private theorem dvd_mul_left_of_dvd
    {d a b : FpPoly p} (hda : d ∣ a) :
    d ∣ b * a := by
  rcases hda with ⟨q, hq⟩
  refine ⟨b * q, ?_⟩
  calc b * a
      = b * (d * q) := by rw [hq]
    _ = (b * d) * q := (DensePoly.mul_assoc_poly b d q).symm
    _ = (d * b) * q := by
          exact congrArg (fun x => x * q) (DensePoly.mul_comm_poly b d)
    _ = d * (b * q) := DensePoly.mul_assoc_poly d b q

private theorem dvd_mul_right_of_dvd
    {d a b : FpPoly p} (hda : d ∣ a) :
    d ∣ a * b := by
  rcases hda with ⟨q, hq⟩
  refine ⟨q * b, ?_⟩
  calc a * b
      = (d * q) * b := by rw [hq]
    _ = d * (q * b) := DensePoly.mul_assoc_poly d q b

private theorem dvd_sub_poly
    {d a b : FpPoly p} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a - b := by
  exact DensePoly.dvd_sub_poly hda hdb

private theorem pow_succ_dvd_mul_right_of_dvd
    {d a b : FpPoly p} {n : Nat}
    (h : pow d (n + 1) ∣ a) :
    pow d (n + 2) ∣ a * d * b := by
  rcases h with ⟨q, hq⟩
  refine ⟨q * b, ?_⟩
  calc a * d * b
      = (pow d (n + 1) * q) * d * b := by rw [hq]
    _ = (pow d (n + 1) * (q * d)) * b := by
          exact congrArg (fun x => x * b)
            (DensePoly.mul_assoc_poly (pow d (n + 1)) q d)
    _ = (pow d (n + 1) * (d * q)) * b := by
          exact congrArg (fun x => (pow d (n + 1) * x) * b)
            (DensePoly.mul_comm_poly q d)
    _ = (pow d (n + 1) * d) * q * b := by
          exact congrArg (fun x => x * b)
            (DensePoly.mul_assoc_poly (pow d (n + 1)) d q).symm
    _ = pow d (n + 2) * (q * b) := by
          rw [← pow_succ d (n + 1)]
          exact DensePoly.mul_assoc_poly (pow d (n + 2)) q b

private theorem pow_succ_dvd_mul_of_dvd_left_of_pow_dvd_right
    {d a b : FpPoly p} {n : Nat}
    (hda : d ∣ a) (hdb : pow d n ∣ b) :
    pow d (n + 1) ∣ a * b := by
  rcases hda with ⟨qa, hqa⟩
  rcases hdb with ⟨qb, hqb⟩
  refine ⟨qa * qb, ?_⟩
  calc a * b
      = (d * qa) * (pow d n * qb) := by rw [hqa, hqb]
    _ = (pow d n * d) * (qa * qb) := by
          calc
            (d * qa) * (pow d n * qb)
                = ((d * qa) * pow d n) * qb := by
                  exact (DensePoly.mul_assoc_poly (d * qa) (pow d n) qb).symm
            _ = (pow d n * (d * qa)) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_comm_poly (d * qa) (pow d n))
            _ = ((pow d n * d) * qa) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_assoc_poly (pow d n) d qa).symm
            _ = (pow d n * d) * (qa * qb) := by
                  exact DensePoly.mul_assoc_poly (pow d n * d) qa qb
    _ = pow d (n + 1) * (qa * qb) := by rw [← pow_succ d n]

private theorem pow_succ_dvd_mul_of_pow_dvd_left_of_dvd_right
    {d a b : FpPoly p} {n : Nat}
    (hda : pow d n ∣ a) (hdb : d ∣ b) :
    pow d (n + 1) ∣ a * b := by
  rcases hda with ⟨qa, hqa⟩
  rcases hdb with ⟨qb, hqb⟩
  refine ⟨qa * qb, ?_⟩
  calc a * b
      = (pow d n * qa) * (d * qb) := by rw [hqa, hqb]
    _ = (pow d n * d) * (qa * qb) := by
          calc
            (pow d n * qa) * (d * qb)
                = ((pow d n * qa) * d) * qb := by
                  exact (DensePoly.mul_assoc_poly (pow d n * qa) d qb).symm
            _ = (pow d n * (qa * d)) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_assoc_poly (pow d n) qa d)
            _ = (pow d n * (d * qa)) * qb := by
                  exact congrArg (fun x => (pow d n * x) * qb)
                    (DensePoly.mul_comm_poly qa d)
            _ = ((pow d n * d) * qa) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_assoc_poly (pow d n) d qa).symm
            _ = (pow d n * d) * (qa * qb) := by
                  exact DensePoly.mul_assoc_poly (pow d n * d) qa qb
    _ = pow d (n + 1) * (qa * qb) := by rw [← pow_succ d n]

private theorem quotient_common_dvd_mul_derivative_base
    [ZMod64.PrimeModulus p] (d c : FpPoly p)
    (hdc : d ∣ c)
    (hddc : d ∣ DensePoly.derivative c) :
    ∃ q, c = d * q ∧ d ∣ q * DensePoly.derivative d := by
  rcases hdc with ⟨q, hq⟩
  refine ⟨q, hq, ?_⟩
  have hderiv :
      DensePoly.derivative c =
        DensePoly.derivative d * q + d * DensePoly.derivative q := by
    rw [hq]
    exact DensePoly.derivative_mul d q
  have hd_second : d ∣ d * DensePoly.derivative q := ⟨DensePoly.derivative q, rfl⟩
  have hd_first : d ∣ DensePoly.derivative d * q := by
    have hsub : d ∣ DensePoly.derivative c - d * DensePoly.derivative q :=
      dvd_sub_poly hddc hd_second
    have hfirst_eq :
        DensePoly.derivative c - d * DensePoly.derivative q =
          DensePoly.derivative d * q := by
      rw [hderiv]
      rw [sub_eq_add_neg]
      calc
        (DensePoly.derivative d * q + d * DensePoly.derivative q) +
            -(d * DensePoly.derivative q)
            = DensePoly.derivative d * q +
                (d * DensePoly.derivative q + -(d * DensePoly.derivative q)) := by
              exact DensePoly.add_assoc_poly
                (DensePoly.derivative d * q) (d * DensePoly.derivative q)
                (-(d * DensePoly.derivative q))
        _ = DensePoly.derivative d * q + 0 := by rw [add_right_neg]
        _ = DensePoly.derivative d * q := add_zero _
    simpa [hfirst_eq] using hsub
  exact (DensePoly.mul_comm_poly q (DensePoly.derivative d)).symm ▸ hd_first

private theorem pow_succ_dvd_cofactor_mul_derivative
    [ZMod64.PrimeModulus p] {d a : FpPoly p}
    (h : d ∣ a * DensePoly.derivative d) :
    ∀ m : Nat, pow d (m + 1) ∣ a * DensePoly.derivative (pow d (m + 1)) := by
  intro m
  induction m with
  | zero =>
      rw [pow_one]
      exact h
  | succ k ih =>
      rw [pow_succ]
      have hderiv :
          a * DensePoly.derivative (pow d (k + 1) * d) =
            a * (DensePoly.derivative (pow d (k + 1)) * d +
              pow d (k + 1) * DensePoly.derivative d) := by
        exact congrArg (fun x => a * x)
          (DensePoly.derivative_mul (pow d (k + 1)) d)
      rw [hderiv]
      have hsplit :
          a * (DensePoly.derivative (pow d (k + 1)) * d +
              pow d (k + 1) * DensePoly.derivative d) =
            a * (DensePoly.derivative (pow d (k + 1)) * d) +
              a * (pow d (k + 1) * DensePoly.derivative d) :=
        DensePoly.mul_add_right_poly a
          (DensePoly.derivative (pow d (k + 1)) * d)
          (pow d (k + 1) * DensePoly.derivative d)
      rw [hsplit]
      exact dvd_add_poly
        (by
          rcases ih with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          calc
            a * (DensePoly.derivative (pow d (k + 1)) * d)
                = (a * DensePoly.derivative (pow d (k + 1))) * d := by
                  exact (DensePoly.mul_assoc_poly a
                    (DensePoly.derivative (pow d (k + 1))) d).symm
            _ = (pow d (k + 1) * q) * d := by rw [hq]
            _ = (pow d (k + 1) * d) * q := by
                  calc
                    (pow d (k + 1) * q) * d
                        = pow d (k + 1) * (q * d) := by
                          exact DensePoly.mul_assoc_poly (pow d (k + 1)) q d
                    _ = pow d (k + 1) * (d * q) := by
                          exact congrArg (fun x => pow d (k + 1) * x)
                            (DensePoly.mul_comm_poly q d)
                    _ = (pow d (k + 1) * d) * q := by
                          exact (DensePoly.mul_assoc_poly (pow d (k + 1)) d q).symm
            _ = (pow d (k + 1) * d) * q := by rfl)
        (by
          rcases h with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          calc
            a * (pow d (k + 1) * DensePoly.derivative d)
                = (a * DensePoly.derivative d) * pow d (k + 1) := by
                  calc
                    a * (pow d (k + 1) * DensePoly.derivative d)
                        = a * (DensePoly.derivative d * pow d (k + 1)) := by
                          exact congrArg (fun x => a * x)
                            (DensePoly.mul_comm_poly (pow d (k + 1))
                              (DensePoly.derivative d))
                    _ = (a * DensePoly.derivative d) * pow d (k + 1) := by
                          exact (DensePoly.mul_assoc_poly a
                            (DensePoly.derivative d) (pow d (k + 1))).symm
            _ = (d * q) * pow d (k + 1) := by rw [hq]
            _ = (pow d (k + 1) * d) * q := by
                  calc
                    (d * q) * pow d (k + 1)
                        = pow d (k + 1) * (d * q) := by
                          exact DensePoly.mul_comm_poly (d * q) (pow d (k + 1))
                    _ = (pow d (k + 1) * d) * q := by
                          exact (DensePoly.mul_assoc_poly (pow d (k + 1)) d q).symm
            _ = (pow d (k + 1) * d) * q := by rfl)

private theorem quotient_common_dvd_pow_derivative_factor
    [ZMod64.PrimeModulus p] (d c h : FpPoly p)
    (hdc : d ∣ c)
    (hddc : d ∣ DensePoly.derivative c) :
    ∀ n : Nat,
      pow d (n + 2) ∣ c * (pow d n * DensePoly.derivative d * h) := by
  rcases quotient_common_dvd_mul_derivative_base d c hdc hddc with ⟨q, hq, hdqd⟩
  rcases hdqd with ⟨r, hr⟩
  intro n
  refine ⟨r * h, ?_⟩
  calc c * (pow d n * DensePoly.derivative d * h)
      = (d * q) * (pow d n * DensePoly.derivative d * h) := by rw [hq]
    _ = (pow d n * d * (q * DensePoly.derivative d)) * h := by
          calc
            (d * q) * (pow d n * DensePoly.derivative d * h)
                = ((d * q) * (pow d n * DensePoly.derivative d)) * h := by
                  exact (DensePoly.mul_assoc_poly (d * q)
                    (pow d n * DensePoly.derivative d) h).symm
            _ = ((pow d n * DensePoly.derivative d) * (d * q)) * h := by
                  exact congrArg (fun x => x * h)
                    (DensePoly.mul_comm_poly (d * q) (pow d n * DensePoly.derivative d))
            _ = (pow d n * (DensePoly.derivative d * (d * q))) * h := by
                  exact congrArg (fun x => x * h)
                    (DensePoly.mul_assoc_poly (pow d n) (DensePoly.derivative d) (d * q))
            _ = (pow d n * ((DensePoly.derivative d * d) * q)) * h := by
                  exact congrArg (fun x => (pow d n * x) * h)
                    (DensePoly.mul_assoc_poly (DensePoly.derivative d) d q).symm
            _ = (pow d n * ((d * DensePoly.derivative d) * q)) * h := by
                  exact congrArg (fun x => (pow d n * (x * q)) * h)
                    (DensePoly.mul_comm_poly (DensePoly.derivative d) d)
            _ = (pow d n * (d * (DensePoly.derivative d * q))) * h := by
                  exact congrArg (fun x => (pow d n * x) * h)
                    (DensePoly.mul_assoc_poly d (DensePoly.derivative d) q)
            _ = ((pow d n * d) * (DensePoly.derivative d * q)) * h := by
                  exact congrArg (fun x => x * h)
                    (DensePoly.mul_assoc_poly (pow d n) d (DensePoly.derivative d * q)).symm
            _ = ((pow d n * d) * (q * DensePoly.derivative d)) * h := by
                  exact congrArg (fun x => ((pow d n * d) * x) * h)
                    (DensePoly.mul_comm_poly (DensePoly.derivative d) q)
    _ = (pow d n * d * (d * r)) * h := by rw [hr]
    _ = (pow d (n + 1) * d) * (r * h) := by
          rw [← pow_succ d n]
          calc
            pow d (n + 1) * (d * r) * h
                = (pow d (n + 1) * d) * r * h := by
                  exact congrArg (fun x => x * h)
                    (DensePoly.mul_assoc_poly (pow d (n + 1)) d r).symm
            _ = (pow d (n + 1) * d) * (r * h) := by
                  exact DensePoly.mul_assoc_poly (pow d (n + 1) * d) r h
    _ = pow d (n + 2) * (r * h) := by rw [← pow_succ d (n + 1)]

private theorem quotient_common_dvd_pow_tail_factor
    [ZMod64.PrimeModulus p] (d c h : FpPoly p)
    (hdc : d ∣ c) :
    ∀ n : Nat,
      pow d (n + 2) ∣ c * (pow d (n + 1) * h) := by
  rcases hdc with ⟨q, hq⟩
  intro n
  refine ⟨q * h, ?_⟩
  calc c * (pow d (n + 1) * h)
      = (d * q) * (pow d (n + 1) * h) := by rw [hq]
    _ = (pow d (n + 1) * d) * (q * h) := by
          calc
            (d * q) * (pow d (n + 1) * h)
                = ((d * q) * pow d (n + 1)) * h := by
                  exact (DensePoly.mul_assoc_poly (d * q) (pow d (n + 1)) h).symm
            _ = (pow d (n + 1) * (d * q)) * h := by
                  exact congrArg (fun x => x * h)
                    (DensePoly.mul_comm_poly (d * q) (pow d (n + 1)))
            _ = ((pow d (n + 1) * d) * q) * h := by
                  exact congrArg (fun x => x * h)
                    (DensePoly.mul_assoc_poly (pow d (n + 1)) d q).symm
            _ = (pow d (n + 1) * d) * (q * h) := by
                  exact DensePoly.mul_assoc_poly (pow d (n + 1) * d) q h
    _ = pow d (n + 2) * (q * h) := by rw [← pow_succ d (n + 1)]

private theorem yunStep_common_dvd_derivative_product
    (z y d : FpPoly p)
    (hdz : d ∣ z) (hdy : d ∣ y) :
    d ∣ DensePoly.derivative (z * y) := by
  have hterms :
      d ∣ DensePoly.derivative z * y + z * DensePoly.derivative y :=
    dvd_add_poly
      (dvd_mul_left_of_dvd hdy)
      (dvd_mul_right_of_dvd hdz)
  exact (DensePoly.derivative_mul z y).symm ▸ hterms

private theorem yunStep_common_dvd_derivative_current
    [ZMod64.PrimeModulus p]
    (c w d : FpPoly p)
    (hdz : d ∣ c / DensePoly.gcd c w)
    (hdy : d ∣ DensePoly.gcd c w) :
    d ∣ DensePoly.derivative c := by
  let y := DensePoly.gcd c w
  let z := c / y
  have hprod : z * y = c := by
    simpa [z, y] using div_gcd_mul_reconstruct c w
  rw [← hprod]
  exact yunStep_common_dvd_derivative_product z y d hdz hdy

private theorem derivativeSplit_common_dvd_quotient_derivative_dvd_gcd
    [ZMod64.PrimeModulus p]
    (f d : FpPoly p)
    (hdc : d ∣ f / DensePoly.gcd f (DensePoly.derivative f))
    (hddc : d ∣ DensePoly.derivative
      (f / DensePoly.gcd f (DensePoly.derivative f))) :
    d ∣ DensePoly.gcd f (DensePoly.derivative f) := by
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  have hprod : c * g = f := by
    simpa [c, g] using div_gcd_mul_reconstruct f (DensePoly.derivative f)
  have hdf :
      DensePoly.derivative f =
        DensePoly.derivative c * g + c * DensePoly.derivative g := by
    rw [← hprod]
    exact DensePoly.derivative_mul c g
  have hdf_dvd_f : d ∣ f := by
    rw [← hprod]
    exact dvd_mul_right_of_dvd (a := c) (b := g) (d := d) (by simpa [c, g] using hdc)
  have hdf_dvd_derivative : d ∣ DensePoly.derivative f := by
    rw [hdf]
    exact dvd_add_poly
      (dvd_mul_right_of_dvd (a := DensePoly.derivative c) (b := g) (d := d)
        (by simpa [c, g] using hddc))
      (dvd_mul_right_of_dvd (a := c) (b := DensePoly.derivative g) (d := d)
        (by simpa [c, g] using hdc))
  exact DensePoly.dvd_gcd d f (DensePoly.derivative f) hdf_dvd_f hdf_dvd_derivative

private theorem derivativeSplit_quotient_pow_succ_dvd_gcd
    [ZMod64.PrimeModulus p] (f d : FpPoly p)
    (hdc : d ∣ f / DensePoly.gcd f (DensePoly.derivative f))
    (hddc : d ∣ DensePoly.derivative
      (f / DensePoly.gcd f (DensePoly.derivative f))) :
    ∀ n, pow d n ∣ DensePoly.gcd f (DensePoly.derivative f) →
      pow d (n + 1) ∣ DensePoly.gcd f (DensePoly.derivative f) := by
  intro n hpow
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  rcases quotient_common_dvd_mul_derivative_base d c
      (by simpa [c, g] using hdc) (by simpa [c, g] using hddc) with
    ⟨a, ha, hcofactor⟩
  have hprod : c * g = f := by
    simpa [c, g] using div_gcd_mul_reconstruct f (DensePoly.derivative f)
  have hdf :
      DensePoly.derivative f =
        DensePoly.derivative c * g + c * DensePoly.derivative g := by
    rw [← hprod]
    exact DensePoly.derivative_mul c g
  cases n with
  | zero =>
      rw [pow_one]
      exact derivativeSplit_common_dvd_quotient_derivative_dvd_gcd f d
        (by exact ⟨a, by simpa [c, g] using ha⟩) hddc
  | succ k =>
      rcases hpow with ⟨q, hq⟩
      have hg_eq : g = pow d (k + 1) * q := by simpa [g] using hq
      have hsucc_dvd_f : pow d (k + 2) ∣ f := by
        rw [← hprod]
        rw [ha, hg_eq]
        refine ⟨a * q, ?_⟩
        calc
          (d * a) * (pow d (k + 1) * q)
              = (pow d (k + 1) * d) * (a * q) := by
                calc
                  (d * a) * (pow d (k + 1) * q)
                      = ((d * a) * pow d (k + 1)) * q := by
                        exact (DensePoly.mul_assoc_poly (d * a) (pow d (k + 1)) q).symm
                  _ = (pow d (k + 1) * (d * a)) * q := by
                        exact congrArg (fun x => x * q)
                          (DensePoly.mul_comm_poly (d * a) (pow d (k + 1)))
                  _ = ((pow d (k + 1) * d) * a) * q := by
                        exact congrArg (fun x => x * q)
                          (DensePoly.mul_assoc_poly (pow d (k + 1)) d a).symm
                  _ = (pow d (k + 1) * d) * (a * q) := by
                        exact DensePoly.mul_assoc_poly (pow d (k + 1) * d) a q
          _ = pow d (k + 2) * (a * q) := by rw [← pow_succ d (k + 1)]
      have hsucc_dvd_derivative : pow d (k + 2) ∣ DensePoly.derivative f := by
        rw [hdf]
        have hleft : pow d (k + 2) ∣ DensePoly.derivative c * g := by
          rw [hg_eq]
          exact pow_succ_dvd_mul_of_dvd_left_of_pow_dvd_right
            (by simpa [c, g] using hddc)
            (by exact ⟨q, rfl⟩)
        have hright : pow d (k + 2) ∣ c * DensePoly.derivative g := by
          rw [ha, hg_eq]
          have hderiv :
              (d * a) * DensePoly.derivative (pow d (k + 1) * q) =
                (d * a) * (DensePoly.derivative (pow d (k + 1)) * q +
                  pow d (k + 1) * DensePoly.derivative q) := by
            exact congrArg (fun x => (d * a) * x)
              (DensePoly.derivative_mul (pow d (k + 1)) q)
          rw [hderiv]
          have hsplit :
              (d * a) * (DensePoly.derivative (pow d (k + 1)) * q +
                  pow d (k + 1) * DensePoly.derivative q) =
                (d * a) * (DensePoly.derivative (pow d (k + 1)) * q) +
                  (d * a) * (pow d (k + 1) * DensePoly.derivative q) :=
            DensePoly.mul_add_right_poly (d * a)
              (DensePoly.derivative (pow d (k + 1)) * q)
              (pow d (k + 1) * DensePoly.derivative q)
          rw [hsplit]
          exact dvd_add_poly
            (by
              have haux := pow_succ_dvd_cofactor_mul_derivative hcofactor k
              rcases haux with ⟨r, hr⟩
              refine ⟨r * q, ?_⟩
              calc
                (d * a) * (DensePoly.derivative (pow d (k + 1)) * q)
                    = d * ((a * DensePoly.derivative (pow d (k + 1))) * q) := by
                      calc
                        (d * a) * (DensePoly.derivative (pow d (k + 1)) * q)
                            = ((d * a) * DensePoly.derivative (pow d (k + 1))) * q := by
                              exact (DensePoly.mul_assoc_poly (d * a)
                                (DensePoly.derivative (pow d (k + 1))) q).symm
                        _ = (d * (a * DensePoly.derivative (pow d (k + 1)))) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_assoc_poly d a
                                  (DensePoly.derivative (pow d (k + 1))))
                        _ = d * ((a * DensePoly.derivative (pow d (k + 1))) * q) := by
                              exact DensePoly.mul_assoc_poly d
                                (a * DensePoly.derivative (pow d (k + 1))) q
                _ = d * ((pow d (k + 1) * r) * q) := by rw [hr]
                _ = (pow d (k + 1) * d) * (r * q) := by
                      calc
                        d * ((pow d (k + 1) * r) * q)
                            = (d * (pow d (k + 1) * r)) * q := by
                              exact (DensePoly.mul_assoc_poly d (pow d (k + 1) * r) q).symm
                        _ = ((pow d (k + 1) * r) * d) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_comm_poly d (pow d (k + 1) * r))
                        _ = (pow d (k + 1) * (r * d)) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_assoc_poly (pow d (k + 1)) r d)
                        _ = (pow d (k + 1) * (d * r)) * q := by
                              exact congrArg (fun x => (pow d (k + 1) * x) * q)
                                (DensePoly.mul_comm_poly r d)
                        _ = ((pow d (k + 1) * d) * r) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_assoc_poly (pow d (k + 1)) d r).symm
                        _ = (pow d (k + 1) * d) * (r * q) := by
                              exact DensePoly.mul_assoc_poly (pow d (k + 1) * d) r q
                _ = pow d (k + 2) * (r * q) := by rw [← pow_succ d (k + 1)])
            (by
              refine ⟨a * DensePoly.derivative q, ?_⟩
              calc
                (d * a) * (pow d (k + 1) * DensePoly.derivative q)
                    = (pow d (k + 1) * d) * (a * DensePoly.derivative q) := by
                      calc
                        (d * a) * (pow d (k + 1) * DensePoly.derivative q)
                            = ((d * a) * pow d (k + 1)) * DensePoly.derivative q := by
                              exact (DensePoly.mul_assoc_poly (d * a)
                                (pow d (k + 1)) (DensePoly.derivative q)).symm
                        _ = (pow d (k + 1) * (d * a)) * DensePoly.derivative q := by
                              exact congrArg (fun x => x * DensePoly.derivative q)
                                (DensePoly.mul_comm_poly (d * a) (pow d (k + 1)))
                        _ = ((pow d (k + 1) * d) * a) * DensePoly.derivative q := by
                              exact congrArg (fun x => x * DensePoly.derivative q)
                                (DensePoly.mul_assoc_poly (pow d (k + 1)) d a).symm
                        _ = (pow d (k + 1) * d) * (a * DensePoly.derivative q) := by
                              exact DensePoly.mul_assoc_poly (pow d (k + 1) * d) a
                                (DensePoly.derivative q)
                _ = pow d (k + 2) * (a * DensePoly.derivative q) := by
                      rw [← pow_succ d (k + 1)])
        exact dvd_add_poly hleft hright
      exact DensePoly.dvd_gcd (pow d (k + 2)) f (DensePoly.derivative f)
        hsucc_dvd_f hsucc_dvd_derivative

private theorem yunFactorsContribution_stop_of_isOne
    (c w : FpPoly p) (i fuel : Nat)
    (hc : isOne c = true) :
    yunFactorsContribution c w i (fuel + 1) = (1, w) := by
  simp [yunFactorsContribution, hc]

private theorem yunFactorsContribution_terminal_of_isOne
    (c w : FpPoly p) (i fuel : Nat)
    (hc : isOne c = true) :
    let contribution := yunFactorsContribution c w i (fuel + 1)
    contribution.1 = 1 ∧ contribution.2 = w ∧ c = 1 := by
  have hstop := yunFactorsContribution_stop_of_isOne c w i fuel hc
  have hc_one := eq_one_of_isOne_true c hc
  dsimp
  rw [hstop]
  exact ⟨rfl, rfl, hc_one⟩

private theorem yunFactorsContribution_step_of_not_isOne_of_isOne_z
    (c w : FpPoly p) (i fuel : Nat)
    (hc : isOne c = false)
    (hz : isOne (c / DensePoly.gcd c w) = true) :
    yunFactorsContribution c w i (fuel + 1) =
      yunFactorsContribution
        (DensePoly.gcd c w) (w / DensePoly.gcd c w) (i + 1) fuel := by
  simp [yunFactorsContribution, hc, hz]

private theorem yunFactorsContribution_step_of_not_isOne_of_not_isOne_z
    (c w : FpPoly p) (i fuel : Nat)
    (hc : isOne c = false)
    (hz : isOne (c / DensePoly.gcd c w) = false) :
    yunFactorsContribution c w i (fuel + 1) =
      (pow (c / DensePoly.gcd c w) i *
          (yunFactorsContribution
            (DensePoly.gcd c w) (w / DensePoly.gcd c w) (i + 1) fuel).1,
        (yunFactorsContribution
          (DensePoly.gcd c w) (w / DensePoly.gcd c w) (i + 1) fuel).2) := by
  simp [yunFactorsContribution, hc, hz]

private theorem yunFactorsContribution_tail_repeated_descent
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hc : isOne c = false) :
    let y := DensePoly.gcd c w
    let tail := yunFactorsContribution y (w / y) (multiplicity + 1) fuel
    let contribution := yunFactorsContribution c w multiplicity (fuel + 1)
    contribution.2 = tail.2 ∧
      squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel =
        squareFreeAuxRevContribution (pthRoot tail.2) (multiplicity * p) fuel := by
  by_cases hz : isOne (c / DensePoly.gcd c w)
  · simp [yunFactorsContribution, hc, hz]
  · simp [yunFactorsContribution, hc, hz]

private theorem yunFactorsContribution_step_preserves_target
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity fuel : Nat) (target : FpPoly p)
    (hc : isOne c = false)
    (htarget_one :
      isOne (c / DensePoly.gcd c w) = true →
        (yunFactorsContribution
          (DensePoly.gcd c w) (w / DensePoly.gcd c w)
          (multiplicity + 1) fuel).1 = target)
    (htarget_factor :
      isOne (c / DensePoly.gcd c w) = false →
        pow (c / DensePoly.gcd c w) multiplicity *
          (yunFactorsContribution
            (DensePoly.gcd c w) (w / DensePoly.gcd c w)
            (multiplicity + 1) fuel).1 = target) :
    let tail :=
      yunFactorsContribution
        (DensePoly.gcd c w) (w / DensePoly.gcd c w)
        (multiplicity + 1) fuel
    let contribution := yunFactorsContribution c w multiplicity (fuel + 1)
    contribution.1 = target ∧
      contribution.2 = tail.2 ∧
        (c / DensePoly.gcd c w) * DensePoly.gcd c w = c ∧
          (w / DensePoly.gcd c w) * DensePoly.gcd c w = w := by
  dsimp
  have hsplit := yunFactorsContribution_step_split c w
  by_cases hz : isOne (c / DensePoly.gcd c w) = true
  · have hstep :=
      yunFactorsContribution_step_of_not_isOne_of_isOne_z
        c w multiplicity fuel hc hz
    rw [hstep]
    exact ⟨htarget_one hz, rfl, hsplit.1, hsplit.2⟩
  · have hz_false : isOne (c / DensePoly.gcd c w) = false := by
      cases h : isOne (c / DensePoly.gcd c w)
      · rfl
      · exact False.elim (hz h)
    have hstep :=
      yunFactorsContribution_step_of_not_isOne_of_not_isOne_z
        c w multiplicity fuel hc hz_false
    rw [hstep]
    exact ⟨htarget_factor hz_false, rfl, hsplit.1, hsplit.2⟩

/--
One nonterminal Yun step preserves the caller's target contribution and
keeps the repeated tail aligned with the recursive state.  This packages the
algebra needed by the successor fuel proof: callers supply the target facts
for the recursive tail, and the lemma returns the corresponding current-state
facts plus the two gcd/division reconstruction equalities.
-/
private theorem yunFactorsContribution_step_target_combiner
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity fuel : Nat) (target : FpPoly p)
    (hc : isOne c = false)
    (htarget_one :
      isOne (c / DensePoly.gcd c w) = true →
        (yunFactorsContribution
          (DensePoly.gcd c w) (w / DensePoly.gcd c w)
          (multiplicity + 1) fuel).1 = target)
    (htarget_factor :
      isOne (c / DensePoly.gcd c w) = false →
        pow (c / DensePoly.gcd c w) multiplicity *
          (yunFactorsContribution
            (DensePoly.gcd c w) (w / DensePoly.gcd c w)
            (multiplicity + 1) fuel).1 = target) :
    let y := DensePoly.gcd c w
    let tail :=
      yunFactorsContribution y (w / y) (multiplicity + 1) fuel
    let contribution := yunFactorsContribution c w multiplicity (fuel + 1)
    contribution.1 = target ∧
      contribution.2 = tail.2 ∧
        squareFreeAuxRevContribution (pthRoot contribution.2)
            (multiplicity * p) fuel =
          squareFreeAuxRevContribution (pthRoot tail.2)
            (multiplicity * p) fuel ∧
          (c / y) * y = c ∧ (w / y) * y = w := by
  dsimp
  have htarget :=
    yunFactorsContribution_step_preserves_target
      c w multiplicity fuel target hc htarget_one htarget_factor
  have hdescent :=
    yunFactorsContribution_tail_repeated_descent
      c w multiplicity fuel hc
  exact
    ⟨htarget.1, htarget.2.1, hdescent.2,
      htarget.2.2.1, htarget.2.2.2⟩

private theorem yunFactorsContribution_initial_state_split
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    c * g = f := by
  dsimp
  exact div_gcd_mul_reconstruct f (DensePoly.derivative f)

private theorem yunFactorsContribution_initial_state_done
    (f : FpPoly p) (multiplicity fuel : Nat) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity (fuel + 1)
    isOne contribution.2 = true →
      contribution.1 =
        weightedProduct (yunFactors c g multiplicity (fuel + 1) []).1.reverse := by
  dsimp
  intro _hrepeated
  have hloop :=
    yunFactors_reconstruction_invariant
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f)) multiplicity (fuel + 1) []
  have hproduct := hloop.2
  simpa [weightedProduct_nil] using hproduct.symm

private theorem yunFactorsContribution_initial_state_tail
    (f : FpPoly p) (multiplicity fuel : Nat) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity (fuel + 1)
    isOne contribution.2 = false →
      contribution.1 =
        weightedProduct (yunFactors c g multiplicity (fuel + 1) []).1.reverse := by
  dsimp
  intro _hrepeated
  have hloop :=
    yunFactors_reconstruction_invariant
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f)) multiplicity (fuel + 1) []
  have hproduct := hloop.2
  simpa [weightedProduct_nil] using hproduct.symm

/--
Fuel-indexed product invariant for the derivative-active Yun branch, specialized to the
initial split `g = gcd f f'`, `c = f / g`.  This records the offset-form
product emitted by Yun's loop; assembling that contribution into the outer
`pow f multiplicity` contract is a separate factorisation step.
-/
private theorem yunFactorsContribution_derivative_active_initial_state_invariant
    (f : FpPoly p) (multiplicity fuel : Nat) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity (fuel + 1)
    (isOne contribution.2 = true →
        contribution.1 =
          weightedProduct (yunFactors c g multiplicity (fuel + 1) []).1.reverse) ∧
      (isOne contribution.2 = false →
        contribution.1 =
          weightedProduct (yunFactors c g multiplicity (fuel + 1) []).1.reverse) := by
  dsimp
  constructor
  · exact
      yunFactorsContribution_initial_state_done
        f multiplicity fuel
  · exact
      yunFactorsContribution_initial_state_tail
        f multiplicity fuel

private theorem yunFactorsContribution_derivative_active_split_algebra_succ
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (_hfuel : f.size < fuel + 2)
    (_hzero : f.isZero = false)
    (_hdf : (DensePoly.derivative f).isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity (fuel + 1)
    c * g = f ∧
      (isOne contribution.2 = true →
        contribution.1 =
          weightedProduct (yunFactors c g multiplicity (fuel + 1) []).1.reverse) ∧
        (isOne contribution.2 = false →
          contribution.1 =
            weightedProduct (yunFactors c g multiplicity (fuel + 1) []).1.reverse) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  have hcg : c * g = f := by
    simpa [c, g] using yunFactorsContribution_initial_state_split f
  refine ⟨hcg, ?_⟩
  exact
    (yunFactorsContribution_derivative_active_initial_state_invariant
      f multiplicity fuel)

private theorem yunFactorsContribution_derivative_active_split_algebra
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity fuel
    c * g = f ∧
      (isOne contribution.2 = true →
        contribution.1 =
          weightedProduct (yunFactors c g multiplicity fuel []).1.reverse) ∧
        (isOne contribution.2 = false →
          contribution.1 =
            weightedProduct (yunFactors c g multiplicity fuel []).1.reverse) := by
  cases fuel with
  | zero =>
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      exact
        yunFactorsContribution_derivative_active_split_algebra_succ
          hp f multiplicity fuel hmultiplicity hfuel hzero hdf

private theorem yunFactorsContribution_initial_state_product_invariant
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity fuel
    (isOne contribution.2 = true →
      contribution.1 =
        weightedProduct (yunFactors c g multiplicity fuel []).1.reverse) ∧
      (isOne contribution.2 = false →
        contribution.1 =
          weightedProduct (yunFactors c g multiplicity fuel []).1.reverse) := by
  exact
    (yunFactorsContribution_derivative_active_split_algebra
      hp f multiplicity fuel hmultiplicity hfuel hzero hdf).2

private theorem yunFactorsContribution_reconstruct_core
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (_hfuel : f.size < fuel + 1)
    (_hzero : f.isZero = false)
    (_hdf : (DensePoly.derivative f).isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity fuel
    (isOne contribution.2 = true →
      contribution.1 =
        weightedProduct (yunFactors c g multiplicity fuel []).1.reverse) ∧
      (isOne contribution.2 = false →
        contribution.1 =
          weightedProduct (yunFactors c g multiplicity fuel []).1.reverse) := by
  dsimp
  exact
    yunFactorsContribution_initial_state_product_invariant
      hp f multiplicity fuel hmultiplicity _hfuel _hzero _hdf

private theorem yunFactorsContribution_reconstruct_done
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hrepeated :
      isOne (yunFactorsContribution
        (f / DensePoly.gcd f (DensePoly.derivative f))
        (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2 = true) :
    (yunFactorsContribution
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).1 =
        weightedProduct
          (yunFactors
            (f / DensePoly.gcd f (DensePoly.derivative f))
            (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel []).1.reverse := by
  exact (yunFactorsContribution_reconstruct_core
    hp f multiplicity fuel hmultiplicity hfuel hzero hdf).1 hrepeated

private theorem yunFactorsContribution_reconstruct_tail
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hrepeated :
      isOne (yunFactorsContribution
        (f / DensePoly.gcd f (DensePoly.derivative f))
        (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2 = false) :
    (yunFactorsContribution
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).1 *
        squareFreeAuxRevContribution
          (pthRoot (yunFactorsContribution
            (f / DensePoly.gcd f (DensePoly.derivative f))
            (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2)
          (multiplicity * p) fuel =
          weightedProduct
            (yunFactors
              (f / DensePoly.gcd f (DensePoly.derivative f))
              (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel []).1.reverse *
            squareFreeAuxRevContribution
              (pthRoot (yunFactorsContribution
                (f / DensePoly.gcd f (DensePoly.derivative f))
                (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2)
              (multiplicity * p) fuel := by
  rw [(yunFactorsContribution_reconstruct_core
    hp f multiplicity fuel hmultiplicity hfuel hzero hdf).2 hrepeated]

private theorem yunFactorsContribution_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity fuel
    if isOne contribution.2 then
      contribution.1 =
        weightedProduct (yunFactors c g multiplicity fuel []).1.reverse
    else
      contribution.1 *
        squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel =
          weightedProduct (yunFactors c g multiplicity fuel []).1.reverse *
            squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel := by
  simp only
  by_cases hrepeated :
      isOne (yunFactorsContribution
        (f / DensePoly.gcd f (DensePoly.derivative f))
        (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2
  · simpa [hrepeated] using
      yunFactorsContribution_reconstruct_done
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hrepeated
  · have hrepeated_false :
        isOne (yunFactorsContribution
          (f / DensePoly.gcd f (DensePoly.derivative f))
          (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2 = false := by
      cases h :
          isOne (yunFactorsContribution
            (f / DensePoly.gcd f (DensePoly.derivative f))
            (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel).2
      · rfl
      · exact False.elim (hrepeated h)
    simpa [hrepeated_false] using
      yunFactorsContribution_reconstruct_tail
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hrepeated_false

/--
Inductive predicate capturing states `(c, w, fuel)` reachable from the initial
derivative-active split of `f`. Used to scope the state payload hypothesis
expected by `yunFactorsLevelCompletes_of_derivative_active_initial_split`,
which the derivative-active branch threads into the recursive correctness
chain.
-/
private inductive yunFactorsDerivativeActiveReachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    FpPoly p → FpPoly p → Nat → Prop
  | derivativeSplit (fuel : Nat)
      (hdf : (DensePoly.derivative f).isZero ≠ true) :
      yunFactorsDerivativeActiveReachable hp f
        (f / DensePoly.gcd f (DensePoly.derivative f))
        (DensePoly.gcd f (DensePoly.derivative f))
        fuel
  | step (c w : FpPoly p) (fuel : Nat) :
      yunFactorsDerivativeActiveReachable hp f c w (fuel + 1) →
      yunFactorsDerivativeActiveReachable hp f
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        fuel

/--
Recursive residual derivative-zero invariant for the `squareFreeAuxRev`
loop. At each non-trivial step the residual `loop.2` is either trivial
(`isOne`) or has zero derivative, and the recursion into `pthRoot loop.2`
continues to satisfy the same invariant.
-/
private def squareFreeAuxRevResidualSatisfied
    (g : FpPoly p) (m : Nat) : Nat → Prop
  | 0 => True
  | fuel + 1 =>
      if g.isZero then True
      else if (DensePoly.derivative g).isZero then
        squareFreeAuxRevResidualSatisfied (pthRoot g) (m * p) fuel
      else
        let g_inner := DensePoly.gcd g (DensePoly.derivative g)
        let c_inner := g / g_inner
        let loop := yunFactorsWithLevel c_inner g_inner m 1 fuel []
        ((isOne loop.2 = true) ∨ (DensePoly.derivative loop.2).isZero = true) ∧
          ((isOne loop.2 = false) →
            squareFreeAuxRevResidualSatisfied
              (pthRoot loop.2) (m * p) fuel)

/--
Tail-recursive square-free decomposition over `F_p[x]`, accumulating factors
in reverse output order. A derivative-zero branch descends through the formal
`p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAuxRev (f : FpPoly p) (multiplicity : Nat) :
    Nat → List (SquareFreeFactor p) → List (SquareFreeFactor p)
  | 0, accRev => accRev
  | fuel + 1, accRev =>
      if f.isZero then
        accRev
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRev (pthRoot f) (multiplicity * p) fuel accRev
        else
          let g := DensePoly.gcd f df
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          let accRev' := loop.1
          let repeated := loop.2
          if isOne repeated then
            accRev'
          else
            squareFreeAuxRev (pthRoot repeated) (multiplicity * p) fuel accRev'

/--
Recursive square-free decomposition over `F_p[x]`. A derivative-zero branch
descends through the formal `p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAux (f : FpPoly p) (multiplicity : Nat)
    (fuel : Nat) : List (SquareFreeFactor p) :=
  (squareFreeAuxRev f multiplicity fuel []).reverse

private theorem squareFreeAuxRev_reconstruction_invariant
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (squareFreeAuxRev f multiplicity fuel accRev).reverse =
      weightedProduct accRev.reverse *
        squareFreeAuxRevContribution f multiplicity fuel := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simp [squareFreeAuxRev, squareFreeAuxRevContribution]
  | succ fuel ih =>
      simp only [squareFreeAuxRev, squareFreeAuxRevContribution]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
          have hloop :=
            yunFactorsWithLevel_reconstruction_invariant c g multiplicity 1 fuel accRev
          have hloop_repeated : loop.2 = contribution.2 := by
            simpa [loop, contribution] using hloop.1
          have hloop_product :
              weightedProduct loop.1.reverse =
                weightedProduct accRev.reverse * contribution.1 := by
            simpa [loop, contribution] using hloop.2
          by_cases hrepeated : isOne loop.2
          · have hcontribution_one : isOne contribution.2 := by
              simpa [hloop_repeated] using hrepeated
            simpa [g, c, loop, contribution, hrepeated, hcontribution_one] using hloop_product
          · have hcontribution_not_one : isOne contribution.2 = false := by
              cases hc : isOne contribution.2
              · exact rfl
              · exfalso
                apply hrepeated
                simpa [hloop_repeated] using hc
            have hrec :
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  weightedProduct loop.1.reverse *
                    squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := by
              exact ih (pthRoot loop.2) (multiplicity * p) loop.1
            have hrec_contribution :
                squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel =
                  squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel := by
              rw [hloop_repeated]
            have hcalc :
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  weightedProduct accRev.reverse *
                    (contribution.1 *
                      squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel) := by
              calc
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse
                    = weightedProduct loop.1.reverse *
                        squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := hrec
                _ = (weightedProduct accRev.reverse * contribution.1) *
                        squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := by
                      rw [hloop_product]
                _ = weightedProduct accRev.reverse *
                        (contribution.1 *
                          squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel) := by
                      exact DensePoly.mul_assoc_poly
                        (weightedProduct accRev.reverse) contribution.1
                        (squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel)
                _ = weightedProduct accRev.reverse *
                        (contribution.1 *
                          squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel) := by
                      rw [hrec_contribution]
            simpa [g, c, loop, contribution, hrepeated, hcontribution_not_one, hloop_repeated]
              using hcalc

private def squareFreeFactorCoprimeRel :
    SquareFreeFactor p → SquareFreeFactor p → Prop :=
  fun a b => (normalizeMonic (DensePoly.gcd a.factor b.factor)).2 = 1

private def squareFreeFactorSquareFreeRel (sf : SquareFreeFactor p) : Prop :=
  (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 = 1

private inductive yunFactorsPairwiseReachable :
    FpPoly p → FpPoly p → Nat → Prop
  | derivativeSplit (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
      (hdf : (DensePoly.derivative f).isZero ≠ true) :
      yunFactorsPairwiseReachable
        (f / DensePoly.gcd f (DensePoly.derivative f))
        (DensePoly.gcd f (DensePoly.derivative f))
        fuel
  | step (c w : FpPoly p) (fuel : Nat) :
      yunFactorsPairwiseReachable c w (fuel + 1) →
      yunFactorsPairwiseReachable
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        fuel

private theorem yunFactorsPairwiseReachable_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsPairwiseReachable
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      fuel :=
  yunFactorsPairwiseReachable.derivativeSplit hp f fuel hdf

private theorem yunFactorsPairwiseReachable_step
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    yunFactorsPairwiseReachable
      (DensePoly.gcd c w)
      (w / DensePoly.gcd c w)
      fuel :=
  yunFactorsPairwiseReachable.step c w fuel hreachable

private def yunFactorsCurrentTailCoprime
    (c w : FpPoly p) (base level fuel : Nat) : Prop :=
  let y := DensePoly.gcd c w
  let z := c / y
  ∀ sf ∈ (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse,
    squareFreeFactorCoprimeRel { factor := z, multiplicity := base * level } sf

private def yunFactorsPairwiseReady
    (c w : FpPoly p) (base : Nat) : Nat → Nat → Prop
  | _, 0 => True
  | level, fuel + 1 =>
      let y := DensePoly.gcd c w
      let z := c / y
      yunFactorsPairwiseReady y (w / y) base (level + 1) fuel ∧
        (isOne c = false →
          isOne z = false →
            yunFactorsCurrentTailCoprime c w base level fuel)

private theorem yunFactorsPairwiseReady_step
    (c w : FpPoly p) (base level fuel : Nat)
    (hready : yunFactorsPairwiseReady c w base level (fuel + 1)) :
    yunFactorsPairwiseReady
      (DensePoly.gcd c w)
      (w / DensePoly.gcd c w)
      base
      (level + 1)
      fuel := by
  simpa [yunFactorsPairwiseReady] using hready.1

private theorem yunFactorsPairwiseReady_succ_of_current_tail
    (c w : FpPoly p) (base level fuel : Nat)
    (htail :
      yunFactorsPairwiseReady
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        base
        (level + 1)
        fuel)
    (hcurrent :
      isOne c = false →
        isOne (c / DensePoly.gcd c w) = false →
          yunFactorsCurrentTailCoprime c w base level fuel) :
    yunFactorsPairwiseReady c w base level (fuel + 1) := by
  simpa [yunFactorsPairwiseReady] using And.intro htail hcurrent

private structure yunFactorsPairwiseInvariant
    (c w : FpPoly p) (base level fuel : Nat) : Prop where
  reachable : yunFactorsPairwiseReachable c w fuel
  ready : yunFactorsPairwiseReady c w base level fuel

private theorem yunFactorsPairwiseInvariant_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hready :
      yunFactorsPairwiseReady
        (f / DensePoly.gcd f (DensePoly.derivative f))
        (DensePoly.gcd f (DensePoly.derivative f))
        base
        level
        fuel) :
    yunFactorsPairwiseInvariant
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      base
      level
      fuel where
  reachable := yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf
  ready := hready

private theorem yunFactorsPairwiseInvariant_step
    (c w : FpPoly p) (base level fuel : Nat)
    (hinv : yunFactorsPairwiseInvariant c w base level (fuel + 1)) :
    yunFactorsPairwiseInvariant
      (DensePoly.gcd c w)
      (w / DensePoly.gcd c w)
      base
      (level + 1)
      fuel where
  reachable := yunFactorsPairwiseReachable_step c w fuel hinv.reachable
  ready := yunFactorsPairwiseReady_step c w base level fuel hinv.ready

private theorem pairwise_append_of_cross
    {α : Type} (r : α → α → Prop) {xs ys : List α} :
    xs.Pairwise r →
    ys.Pairwise r →
    (∀ x ∈ xs, ∀ y ∈ ys, r x y) →
    (xs ++ ys).Pairwise r := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      intro hxs hys hcross
      simp only [List.pairwise_cons] at hxs ⊢
      constructor
      · intro z hz
        rcases List.mem_append.mp hz with hmem | hmem
        · exact hxs.1 z hmem
        · exact hcross x (by simp) z hmem
      · apply ih hxs.2 hys
        intro a ha b hb
        exact hcross a (by simp [ha]) b hb

private theorem yunFactorsWithLevel_reverse_append
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactorsWithLevel c w base level fuel accRev).1.reverse =
      accRev.reverse ++ (yunFactorsWithLevel c w base level fuel []).1.reverse := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (level + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          have hacc := ih y (w / y) (level + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (level + 1) [sf]
          simpa [y, z, hz, sf] using
            (calc
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel (sf :: accRev)).1.reverse
                  = (sf :: accRev).reverse ++
                      (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse := hacc
              _ = accRev.reverse ++
                    (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse := by
                  rw [hsingle]
                  simp [List.reverse_cons, List.append_assoc])

private theorem yunFactorsWithLevel_repeated_eq_nil
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactorsWithLevel c w base level fuel accRev).2 =
      (yunFactorsWithLevel c w base level fuel []).2 := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (level + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          have hacc := ih y (w / y) (level + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (level + 1) [sf]
          simpa [y, z, hz, sf] using hacc.trans hsingle.symm

private theorem dvd_trans_poly
    {a b c : FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc c
      = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := DensePoly.mul_assoc_poly a x y

private theorem yunFactorsWithLevel_repeated_dvd_repeated_of_acc
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactorsWithLevel c w base level fuel accRev).2 ∣ w := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel]
      exact ⟨1, by rw [mul_one]⟩
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
        exact ⟨1, by rw [mul_one]⟩
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        have hdiv_tail : w / y ∣ w := by
          exact ⟨y, by simpa [y] using (div_gcd_right_mul_reconstruct c w).symm⟩
        by_cases hz : isOne z
        · exact dvd_trans_poly
            (by simpa [y, z, hz] using ih y (w / y) (level + 1) accRev)
            hdiv_tail
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          exact dvd_trans_poly
            (by simpa [y, z, hz, sf] using ih y (w / y) (level + 1) (sf :: accRev))
            hdiv_tail

private theorem yunFactorsWithLevel_repeated_dvd_repeated
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat) :
    (yunFactorsWithLevel c w base level fuel []).2 ∣ w := by
  exact yunFactorsWithLevel_repeated_dvd_repeated_of_acc c w base level fuel []

private def yunFactorsResidualDerivativeZero
    (c w : FpPoly p) (multiplicity fuel : Nat) : Prop :=
  let loop := yunFactors c w multiplicity fuel []
  isOne loop.2 = false → (DensePoly.derivative loop.2).isZero = true

private def yunFactorsContributionResidualDerivativeZero
    (c w : FpPoly p) (multiplicity fuel : Nat) : Prop :=
  let contribution := yunFactorsContribution c w multiplicity fuel
  isOne contribution.2 = false →
    (DensePoly.derivative contribution.2).isZero = true

private def yunFactorsContributionResidualComplete
    (c w : FpPoly p) (multiplicity : Nat) : Nat → Prop
  | 0 =>
      isOne w = false → (DensePoly.derivative w).isZero = true
  | fuel + 1 =>
      if isOne c then
        isOne w = false → (DensePoly.derivative w).isZero = true
      else
        let y := DensePoly.gcd c w
        yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel

private theorem yunFactorsContributionResidualDerivativeZero_of_complete
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hcomplete :
      yunFactorsContributionResidualComplete c w multiplicity fuel) :
    yunFactorsContributionResidualDerivativeZero c w multiplicity fuel := by
  induction fuel generalizing c w multiplicity with
  | zero =>
      intro hrepeated
      simpa [yunFactorsContributionResidualDerivativeZero,
        yunFactorsContributionResidualComplete, yunFactorsContribution]
        using hcomplete hrepeated
  | succ fuel ih =>
      intro hrepeated
      by_cases hc : isOne c = true
      · have hcomplete_here :
            isOne w = false → (DensePoly.derivative w).isZero = true := by
          simpa [yunFactorsContributionResidualComplete, hc] using hcomplete
        have hrepeated_here : isOne w = false := by
          simpa [yunFactorsContribution, hc] using hrepeated
        simpa [yunFactorsContributionResidualDerivativeZero,
          yunFactorsContribution, hc] using hcomplete_here hrepeated_here
      · let y := DensePoly.gcd c w
        have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have hcomplete_tail :
            yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel := by
          simpa [yunFactorsContributionResidualComplete, hc_false, y] using hcomplete
        have htail :
            yunFactorsContributionResidualDerivativeZero y (w / y) (multiplicity + 1) fuel :=
          ih y (w / y) (multiplicity + 1) hcomplete_tail
        have hrepeated_tail :
            isOne (yunFactorsContribution y (w / y) (multiplicity + 1) fuel).2 = false := by
          simpa [yunFactorsContribution, hc_false, y] using hrepeated
        simpa [yunFactorsContributionResidualDerivativeZero,
          yunFactorsContribution, hc_false, y] using htail hrepeated_tail

private theorem yunFactorsContributionResidualComplete_of_derivativeZero
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hresidual :
      yunFactorsContributionResidualDerivativeZero c w multiplicity fuel) :
    yunFactorsContributionResidualComplete c w multiplicity fuel := by
  induction fuel generalizing c w multiplicity with
  | zero =>
      intro hrepeated
      simpa [yunFactorsContributionResidualDerivativeZero,
        yunFactorsContribution] using hresidual hrepeated
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hres_here :
            isOne w = false → (DensePoly.derivative w).isZero = true := by
          intro hone_w
          have hres_lifted :
              isOne (yunFactorsContribution c w multiplicity (fuel + 1)).2 = false := by
            simpa [yunFactorsContribution, hc] using hone_w
          simpa [yunFactorsContribution, hc] using hresidual hres_lifted
        simpa [yunFactorsContributionResidualComplete, hc] using hres_here
      · let y := DensePoly.gcd c w
        have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have hres_tail :
            yunFactorsContributionResidualDerivativeZero y (w / y) (multiplicity + 1) fuel := by
          intro hone_tail
          have hres_lifted :
              isOne (yunFactorsContribution c w multiplicity (fuel + 1)).2 = false := by
            simpa [yunFactorsContribution, hc_false, y] using hone_tail
          simpa [yunFactorsContribution, hc_false, y] using hresidual hres_lifted
        have htail :
            yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel :=
          ih y (w / y) (multiplicity + 1) hres_tail
        simpa [yunFactorsContributionResidualComplete, hc_false, y] using htail

private theorem yunFactorsResidualDerivativeZero_of_contribution
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hresidual :
      yunFactorsContributionResidualDerivativeZero c w multiplicity fuel) :
    yunFactorsResidualDerivativeZero c w multiplicity fuel := by
  intro hloop
  let loop := yunFactors c w multiplicity fuel []
  let contribution := yunFactorsContribution c w multiplicity fuel
  have hloop_repeated : loop.2 = contribution.2 := by
    simpa [loop, contribution] using
      (yunFactors_reconstruction_invariant c w multiplicity fuel []).1
  have hcontribution_not_one : isOne contribution.2 = false := by
    simpa [loop, contribution, hloop_repeated] using hloop
  simpa [loop, contribution, hloop_repeated] using
    (hresidual hcontribution_not_one)

private theorem yunFactorsResidualDerivativeZero_of_derivative_split_contribution
    (_hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hdf : (DensePoly.derivative f).isZero = false)
    (hresidual :
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      yunFactorsContributionResidualDerivativeZero c g multiplicity fuel) :
    yunFactorsResidualDerivativeZero
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel := by
  exact
    yunFactorsResidualDerivativeZero_of_contribution
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel
      hresidual

private theorem yunFactorsResidualDerivativeZero_of_derivative_split_complete
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hcomplete :
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      yunFactorsContributionResidualComplete c g multiplicity fuel) :
    yunFactorsResidualDerivativeZero
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel := by
  apply yunFactorsResidualDerivativeZero_of_derivative_split_contribution
    hp f multiplicity fuel hdf
  exact
    yunFactorsContributionResidualDerivativeZero_of_complete
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel
      hcomplete

/--
Derivative-active provider for `yunFactorsContributionResidualComplete`.

The completion fact required by `yunFactorsResidualDerivativeZero_of_derivative_split_complete`
is supplied by a single recursion-tip derivative-zero witness on the eventual
`yunFactorsContribution` residual. That witness has the precise shape needed to
exclude the `fuel = 0` counterexample (where the residual is exactly the input
`w = gcd f (derivative f)`) by demanding the derivative-zero fact at exactly the
terminal recursion state.
-/
private theorem yunFactorsContributionResidualComplete_of_derivative_active
    (_hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hdf : (DensePoly.derivative f).isZero = false)
    (hresidual :
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      yunFactorsContributionResidualDerivativeZero c g multiplicity fuel) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsContributionResidualComplete c g multiplicity fuel := by
  exact
    yunFactorsContributionResidualComplete_of_derivativeZero
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel
      hresidual

/--
Derivative-active residual derivative-zero fact, threaded through the
completion provider. Composes `yunFactorsContributionResidualComplete_of_derivative_active`
with `yunFactorsResidualDerivativeZero_of_derivative_split_complete` to expose
the concrete loop residual derivative-zero fact under the same
`yunFactorsContributionResidualDerivativeZero` hypothesis.
-/
private theorem yunFactorsResidualDerivativeZero_of_derivative_active
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hresidual :
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      yunFactorsContributionResidualDerivativeZero c g multiplicity fuel) :
    yunFactorsResidualDerivativeZero
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel := by
  apply yunFactorsResidualDerivativeZero_of_derivative_split_complete
    hp f multiplicity fuel hdf
  exact
    yunFactorsContributionResidualComplete_of_derivative_active
      hp f multiplicity fuel hdf hresidual

/--
The residual component of the scaled Yun contribution
`yunFactorsContributionWithLevel` agrees with that of the unscaled
`yunFactorsContribution`. The two recursions share an identical
`.2`-projection: the base/level scaling only affects the emitted
`pow z (base * level)` exponents in the first component.
-/
private theorem yunFactorsContributionWithLevel_residual_eq_yunFactorsContribution
    (c w : FpPoly p) (base level fuel : Nat) :
    (yunFactorsContributionWithLevel c w base level fuel).2 =
      (yunFactorsContribution c w level fuel).2 := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsContributionWithLevel, yunFactorsContribution]
  | succ fuel ih =>
      simp only [yunFactorsContributionWithLevel, yunFactorsContribution]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        exact ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)

/--
Derivative-zero of the residual carries between the scaled
`yunFactorsContributionWithLevel` and the unscaled
`yunFactorsContribution`: both have the same residual, so the
derivative-zero fact transports directly.
-/
private theorem yunFactorsContributionWithLevel_residual_derivative_zero_of_unscaled
    (c w : FpPoly p) (base level fuel : Nat)
    (hresidual : yunFactorsContributionResidualDerivativeZero c w level fuel) :
    isOne (yunFactorsContributionWithLevel c w base level fuel).2 = false →
      (DensePoly.derivative
          (yunFactorsContributionWithLevel c w base level fuel).2).isZero = true := by
  intro hone
  rw [yunFactorsContributionWithLevel_residual_eq_yunFactorsContribution] at hone ⊢
  exact hresidual hone

private theorem dvd_one_of_mul_right_dvd_right
    [ZMod64.PrimeModulus p] {d g : FpPoly p}
    (hg : g.isZero = false) (hdiv : d * g ∣ g) :
    d ∣ (1 : FpPoly p) := by
  have hg_ne : g ≠ 0 := by
    intro hzero
    rw [hzero] at hg
    change (0 : FpPoly p).isZero = false at hg
    have hzero_isZero : (0 : FpPoly p).isZero = true := rfl
    rw [hzero_isZero] at hg
    cases hg
  rcases hdiv with ⟨q, hq⟩
  have hd_ne : d ≠ 0 := by
    intro hd
    apply hg_ne
    rw [hq, hd, zero_mul, zero_mul]
  have hdg_ne : d * g ≠ 0 := by
    intro hdg
    apply hg_ne
    rw [hq, hdg, zero_mul]
  have hq_ne : q ≠ 0 := by
    intro hq_zero
    apply hg_ne
    rw [hq, hq_zero, mul_zero]
  have hdeg_dg := degree?_mul_eq_add_degree? d g hd_ne hg_ne
  have hdeg_all := degree?_mul_eq_add_degree? (d * g) q hdg_ne hq_ne
  have hdeg_eq :
      g.degree?.getD 0 = (d * g * q).degree?.getD 0 := by
    rw [← hq]
  have hd_degree_zero : d.degree?.getD 0 = 0 := by
    rw [hdeg_all, hdeg_dg] at hdeg_eq
    omega
  have hd_size_pos : 0 < d.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hd_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le d (by omega)
  have hd_size_ne : d.size ≠ 0 := Nat.pos_iff_ne_zero.mp hd_size_pos
  have hd_degree : d.degree? = some (d.size - 1) := by
    unfold DensePoly.degree?
    simp [hd_size_ne]
  have hd_size_one : d.size = 1 := by
    rw [hd_degree] at hd_degree_zero
    simp at hd_degree_zero
    omega
  have hcoeff_ne : d.coeff 0 ≠ 0 := by
    have hlast := DensePoly.coeff_last_ne_zero_of_pos_size d hd_size_pos
    simpa [hd_size_one] using hlast
  have hd_const : d = DensePoly.C (d.coeff 0) := by
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        rw [DensePoly.coeff_C]
        simp
    | succ n =>
        have hsize_le : d.size ≤ n + 1 := by
          rw [hd_size_one]
          omega
        rw [DensePoly.coeff_eq_zero_of_size_le d hsize_le, DensePoly.coeff_C]
        simp
  rw [hd_const, ← scale_one_poly]
  exact dvd_scale_self_of_ne_zero hcoeff_ne (1 : FpPoly p)

private theorem ne_zero_of_isZero_false {f : FpPoly p}
    (hf : f.isZero = false) :
    f ≠ 0 := by
  intro hzero
  rw [hzero] at hf
  change (0 : FpPoly p).isZero = false at hf
  have hzero_isZero : (0 : FpPoly p).isZero = true := rfl
  rw [hzero_isZero] at hf
  cases hf

/--
One derivative-active Yun step is stable under a common nonzero scalar multiple.

The executable `DensePoly.gcd` is only canonical up to a nonzero scalar, so the
statement exposes the scalar `v` selected by the gcd bridge. With that scalar
made explicit, both the repeated part `g = gcd f f'` and the quotient
`c = f / g` synchronize across the raw scaled input `C u * f`.
-/
private theorem yunScalarStep
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {u : ZMod64 p} (hu : u ≠ 0) (f : FpPoly p)
    (hder : (DensePoly.derivative f).isZero = false) :
    ∃ v : ZMod64 p, v ≠ 0 ∧
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let raw := DensePoly.C u * f
      let rawG := DensePoly.gcd raw (DensePoly.derivative raw)
      rawG = DensePoly.C v * g ∧
        raw / rawG = DensePoly.C (u * v⁻¹) * (f / g) := by
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let raw := DensePoly.C u * f
  have hder_raw :
      DensePoly.derivative raw =
        DensePoly.C u * DensePoly.derivative f := by
    simpa [raw] using derivative_C_mul u f
  obtain ⟨v, hv, hgcd⟩ :=
    gcd_C_mul_C_mul_eq_C_mul_gcd hp u hu f (DensePoly.derivative f)
  refine ⟨v, hv, ?_⟩
  dsimp only
  have hrawG :
      DensePoly.gcd raw (DensePoly.derivative raw) =
        DensePoly.C v * g := by
    simpa [raw, g, hder_raw] using hgcd
  constructor
  · exact hrawG
  · have hg_ne : g ≠ 0 := by
      apply ne_zero_of_isZero_false
      exact gcd_isZero_false_of_right_isZero_false
        f (DensePoly.derivative f) hder
    have hquot :=
      div_C_mul_C_mul_of_dvd hp hu hv f g
        (by
          simpa [g] using
            DensePoly.gcd_dvd_left f (DensePoly.derivative f))
        hg_ne
    rw [hrawG]
    simpa [raw, g] using hquot

/--
Asymmetric scalar step bridge for the inner Yun recursion. Threads
independent nonzero scalars `u_c`, `u_w` on `c`, `w` through one
`yunFactorsContributionWithLevel` step: the executable `DensePoly.gcd`
output picks up a single asymmetric scalar `v ≠ 0`, and both the quotient
`c_raw / y_raw` and the descent tail `w_raw / y_raw` rescale by
unit-paired prefactors `C (u_c · v⁻¹)` and `C (u_w · v⁻¹)`. Used by the
recursive contribution sync as the induction step.
-/
private theorem yunFactorsContributionWithLevel_scalar_step_bridge
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (hg_ne : DensePoly.gcd c w ≠ 0) :
    ∃ v : ZMod64 p, v ≠ 0 ∧
      DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) =
          DensePoly.C v * DensePoly.gcd c w ∧
        (DensePoly.C u_c * c) /
            DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) =
          DensePoly.C (u_c * v⁻¹) * (c / DensePoly.gcd c w) ∧
        (DensePoly.C u_w * w) /
            DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) =
          DensePoly.C (u_w * v⁻¹) * (w / DensePoly.gcd c w) := by
  obtain ⟨v, hv_ne, hgcd⟩ :=
    gcd_C_mul_left_C_mul_right_eq_C_mul_gcd hp u_c u_w hu_c hu_w c w
  refine ⟨v, hv_ne, hgcd, ?_, ?_⟩
  · rw [hgcd]
    have hc_dvd : DensePoly.gcd c w ∣ c := DensePoly.gcd_dvd_left c w
    exact div_C_mul_C_mul_of_dvd hp hu_c hv_ne c (DensePoly.gcd c w) hc_dvd hg_ne
  · rw [hgcd]
    have hw_dvd : DensePoly.gcd c w ∣ w := DensePoly.gcd_dvd_right c w
    exact div_C_mul_C_mul_of_dvd hp hu_w hv_ne w (DensePoly.gcd c w) hw_dvd hg_ne

private theorem pow_C_form
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {a : ZMod64 p} (ha : a ≠ 0) :
    ∀ n : Nat, ∃ b : ZMod64 p, b ≠ 0 ∧
      pow (DensePoly.C a : FpPoly p) n = DensePoly.C b
  | 0 =>
      ⟨1, zmod64_one_ne_zero_of_prime hp, by
        rw [pow_eq_powLinear]
        rfl⟩
  | n + 1 =>
      by
        obtain ⟨b, hb, hpow⟩ := pow_C_form hp ha n
        refine ⟨b * a, ?_, ?_⟩
        · intro hzero
          rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hb_zero | ha_zero
          · exact hb hb_zero
          · exact ha ha_zero
        · rw [pow_succ, hpow, fpPoly_C_mul_C_eq]

private theorem pow_C_mul_sync
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {a : ZMod64 p} (ha : a ≠ 0) (f : FpPoly p) (n : Nat) :
    ∃ b : ZMod64 p, b ≠ 0 ∧
      pow (DensePoly.C a * f : FpPoly p) n = DensePoly.C b * pow f n := by
  obtain ⟨b, hb, hpow⟩ := pow_C_form hp ha n
  refine ⟨b, hb, ?_⟩
  calc
    pow (DensePoly.C a * f : FpPoly p) n =
        pow (DensePoly.C a : FpPoly p) n * pow f n := by
          rw [pow_mul_base]
    _ = DensePoly.C b * pow f n := by rw [hpow]

private theorem C_mul_eq_one_inv_form
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {a : ZMod64 p} (ha : a ≠ 0) {f : FpPoly p}
    (h : (DensePoly.C a : FpPoly p) * f = 1) :
    f = DensePoly.C a⁻¹ := by
  have ha_inv_a : a⁻¹ * a = (1 : ZMod64 p) := by
    have hcomm : a * a⁻¹ = a⁻¹ * a := by grind
    rw [← hcomm]
    exact zmod64_mul_inv_eq_one_of_prime_ne_zero hp ha
  calc
    f = (1 : FpPoly p) * f := (one_mul f).symm
    _ = (DensePoly.C a⁻¹ * DensePoly.C a : FpPoly p) * f := by
          rw [fpPoly_C_mul_C_eq, ha_inv_a]
          rfl
    _ = DensePoly.C a⁻¹ * ((DensePoly.C a : FpPoly p) * f) :=
          DensePoly.mul_assoc_poly _ _ _
    _ = DensePoly.C a⁻¹ := by rw [h, mul_one]

private theorem C_mul_C_mul_cancel_right
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {a b : ZMod64 p} (hb : b ≠ 0) (f : FpPoly p) :
    DensePoly.C (a * b⁻¹) * (DensePoly.C b * f : FpPoly p) =
      DensePoly.C a * f := by
  have hb_inv : b⁻¹ * b = (1 : ZMod64 p) := by
    have hcomm : b * b⁻¹ = b⁻¹ * b := by grind
    rw [← hcomm]
    exact zmod64_mul_inv_eq_one_of_prime_ne_zero hp hb
  have hab : (a * b⁻¹) * b = a := by
    calc (a * b⁻¹) * b
        = a * (b⁻¹ * b) := by grind
      _ = a * 1 := by rw [hb_inv]
      _ = a := by grind
  calc
    DensePoly.C (a * b⁻¹) * (DensePoly.C b * f : FpPoly p) =
        (DensePoly.C (a * b⁻¹) * DensePoly.C b : FpPoly p) * f :=
          (DensePoly.mul_assoc_poly _ _ _).symm
    _ = DensePoly.C a * f := by rw [fpPoly_C_mul_C_eq, hab]

private theorem yunFactorsContributionWithLevel_scalar_branch_sync
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {z zScaled tail₁ tail₂ tailScaled₁ tailScaled₂ : FpPoly p}
    {u_z s_tail u_tail : ZMod64 p} (hu_z : u_z ≠ 0)
    (hs_tail : s_tail ≠ 0) (hu_tail : u_tail ≠ 0)
    (hzScaled : zScaled = DensePoly.C u_z * z)
    (htail₁ : tailScaled₁ = DensePoly.C s_tail * tail₁)
    (htail₂ : tailScaled₂ = DensePoly.C u_tail * tail₂)
    (n : Nat) :
    ∃ s u : ZMod64 p, s ≠ 0 ∧ u ≠ 0 ∧
      (if isOne zScaled then tailScaled₁ else pow zScaled n * tailScaled₁) =
        DensePoly.C s *
          (if isOne z then tail₁ else pow z n * tail₁) ∧
      tailScaled₂ = DensePoly.C u * tail₂ := by
  by_cases hz : isOne z = true
  · have hz_eq : z = 1 := eq_one_of_isOne_true z hz
    by_cases hzs : isOne zScaled = true
    · refine ⟨s_tail, u_tail, hs_tail, hu_tail, ?_, htail₂⟩
      simp [hz, hzs, htail₁]
    · have hzs_false : isOne zScaled = false := by
        cases h : isOne zScaled
        · rfl
        · exact False.elim (hzs h)
      have hzScaled_C : zScaled = DensePoly.C u_z := by
        rw [hzScaled, hz_eq, mul_one]
      obtain ⟨s_pow, hs_pow, hpow⟩ := pow_C_form hp hu_z n
      refine ⟨s_pow * s_tail, u_tail, ?_, hu_tail, ?_, htail₂⟩
      · intro hzero
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hpow_zero | htail_zero
        · exact hs_pow hpow_zero
        · exact hs_tail htail_zero
      · have hC_false : isOne (DensePoly.C u_z : FpPoly p) = false := by
          simpa [hzScaled_C] using hzs_false
        have hmain :
            pow (DensePoly.C u_z : FpPoly p) n *
                (DensePoly.C s_tail * tail₁) =
              DensePoly.C (s_pow * s_tail) * tail₁ := by
          calc
            pow (DensePoly.C u_z : FpPoly p) n *
                (DensePoly.C s_tail * tail₁) =
                DensePoly.C s_pow * (DensePoly.C s_tail * tail₁) := by
                  rw [hpow]
            _ = (DensePoly.C s_pow * DensePoly.C s_tail : FpPoly p) * tail₁ :=
                  (DensePoly.mul_assoc_poly _ _ _).symm
            _ = DensePoly.C (s_pow * s_tail) * tail₁ := by
                  rw [fpPoly_C_mul_C_eq]
        simpa [hz, hC_false, htail₁, hzScaled_C] using hmain
  · have hz_false : isOne z = false := by
      cases h : isOne z
      · rfl
      · exact False.elim (hz h)
    by_cases hzs : isOne zScaled = true
    · have hzs_eq : zScaled = 1 := eq_one_of_isOne_true zScaled hzs
      have hz_unit : z = DensePoly.C u_z⁻¹ := by
        apply C_mul_eq_one_inv_form hp hu_z
        simpa [hzScaled] using hzs_eq
      have hu_z_inv : u_z⁻¹ ≠ 0 :=
        zmod64_inv_ne_zero_of_prime_ne_zero hp hu_z
      obtain ⟨s_pow, hs_pow, hpow⟩ := pow_C_form hp hu_z_inv n
      refine ⟨s_tail * s_pow⁻¹, u_tail, ?_, hu_tail, ?_, htail₂⟩
      · intro hzero
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with htail_zero | hinv_zero
        · exact hs_tail htail_zero
        · exact zmod64_inv_ne_zero_of_prime_ne_zero hp hs_pow hinv_zero
      · have hraw_pow : pow z n = DensePoly.C s_pow := by
          simpa [hz_unit] using hpow
        simp [hz_false, hzs, htail₁, hraw_pow]
        exact (C_mul_C_mul_cancel_right hp hs_pow tail₁).symm
    · have hzs_false : isOne zScaled = false := by
        cases h : isOne zScaled
        · rfl
        · exact False.elim (hzs h)
      obtain ⟨s_pow, hs_pow, hpow⟩ :=
        pow_C_mul_sync hp hu_z z n
      refine ⟨s_pow * s_tail, u_tail, ?_, hu_tail, ?_, htail₂⟩
      · intro hzero
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hpow_zero | htail_zero
        · exact hs_pow hpow_zero
        · exact hs_tail htail_zero
      · have hmain :
            pow zScaled n * (DensePoly.C s_tail * tail₁) =
              DensePoly.C (s_pow * s_tail) * (pow z n * tail₁) := by
          calc
            pow zScaled n * (DensePoly.C s_tail * tail₁) =
                (DensePoly.C s_pow * pow z n : FpPoly p) *
                  (DensePoly.C s_tail * tail₁) := by
                  rw [hzScaled, hpow]
            _ = DensePoly.C s_pow *
                  (pow z n * (DensePoly.C s_tail * tail₁)) :=
                  DensePoly.mul_assoc_poly _ _ _
            _ = DensePoly.C s_pow *
                  ((pow z n * DensePoly.C s_tail : FpPoly p) * tail₁) := by
                  exact congrArg (fun q => DensePoly.C s_pow * q)
                    ((DensePoly.mul_assoc_poly (pow z n)
                      (DensePoly.C s_tail : FpPoly p) tail₁).symm)
            _ = DensePoly.C s_pow *
                  ((DensePoly.C s_tail * pow z n : FpPoly p) * tail₁) := by
                  exact congrArg
                    (fun q : FpPoly p => DensePoly.C s_pow * (q * tail₁))
                    (DensePoly.mul_comm_poly (pow z n)
                      (DensePoly.C s_tail : FpPoly p))
            _ = DensePoly.C s_pow *
                  (DensePoly.C s_tail * (pow z n * tail₁)) := by
                  exact congrArg (fun q => DensePoly.C s_pow * q)
                    (DensePoly.mul_assoc_poly
                      (DensePoly.C s_tail : FpPoly p) (pow z n) tail₁)
            _ = (DensePoly.C s_pow * DensePoly.C s_tail : FpPoly p) *
                  (pow z n * tail₁) :=
                  (DensePoly.mul_assoc_poly _ _ _).symm
            _ = DensePoly.C (s_pow * s_tail) * (pow z n * tail₁) := by
                  rw [fpPoly_C_mul_C_eq]
        simpa [hz_false, hzs_false, htail₁] using hmain

private theorem constant_divisor_eq_C
    [ZMod64.PrimeModulus p]
    {d : FpPoly p} {k : ZMod64 p} (hk : k ≠ 0)
    (hdvd : d ∣ (DensePoly.C k : FpPoly p)) :
    ∃ v : ZMod64 p, v ≠ 0 ∧ d = DensePoly.C v := by
  have hCk_ne : (DensePoly.C k : FpPoly p) ≠ 0 := C_ne_zero_of_ne_zero hk
  have hd_ne : d ≠ 0 := by
    intro hd_zero
    rcases hdvd with ⟨q, hq⟩
    apply hCk_ne
    rw [hq, hd_zero, zero_mul]
  have hd_size_le : d.size ≤ (DensePoly.C k : FpPoly p).size :=
    size_le_of_dvd_of_ne_zero hdvd hCk_ne
  have hCk_size : (DensePoly.C k : FpPoly p).size = 1 := by
    have hcoeffs :
        (DensePoly.C k : FpPoly p).coeffs = #[k] :=
      DensePoly.coeffs_C_of_ne_zero hk
    simpa [DensePoly.size] using congrArg Array.size hcoeffs
  have hd_pos : 0 < d.size := size_pos_of_ne_zero hd_ne
  have hd_size : d.size = 1 := by omega
  exact ⟨d.coeff 0, coeff_zero_ne_zero_of_size_one hd_size, eq_C_of_size_one hd_size⟩

private theorem div_C_ne_zero_eq_C_inv_mul
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {v : ZMod64 p} (hv : v ≠ 0) (w : FpPoly p) :
    w / (DensePoly.C v : FpPoly p) = DensePoly.C v⁻¹ * w := by
  have hCv_ne : (DensePoly.C v : FpPoly p) ≠ 0 := C_ne_zero_of_ne_zero hv
  have hCv_zero : (DensePoly.C v : FpPoly p).isZero = false := by
    cases hzero : (DensePoly.C v : FpPoly p).isZero
    · rfl
    · exact False.elim (hv ((DensePoly.isZero_C_eq_true_iff v).mp hzero))
  have hvinv_v : v⁻¹ * v = (1 : ZMod64 p) := by
    have hcomm : v * v⁻¹ = v⁻¹ * v := by grind
    rw [← hcomm]
    exact zmod64_mul_inv_eq_one_of_prime_ne_zero hp hv
  have hcand_mul :
      (DensePoly.C v⁻¹ * w : FpPoly p) * (DensePoly.C v : FpPoly p) = w := by
    calc (DensePoly.C v⁻¹ * w : FpPoly p) * (DensePoly.C v : FpPoly p)
        = DensePoly.C v⁻¹ * (w * DensePoly.C v) :=
            DensePoly.mul_assoc_poly _ _ _
      _ = DensePoly.C v⁻¹ * (DensePoly.C v * w) := by
            exact congrArg (fun q => DensePoly.C v⁻¹ * q)
              (DensePoly.mul_comm_poly w (DensePoly.C v : FpPoly p))
      _ = (DensePoly.C v⁻¹ * DensePoly.C v : FpPoly p) * w :=
            (DensePoly.mul_assoc_poly _ _ _).symm
      _ = (DensePoly.C (v⁻¹ * v) : FpPoly p) * w := by
            rw [fpPoly_C_mul_C_eq]
      _ = (1 : FpPoly p) * w := by rw [hvinv_v]; rfl
      _ = w := one_mul w
  have hCv_dvd : (DensePoly.C v : FpPoly p) ∣ w :=
    ⟨DensePoly.C v⁻¹ * w, by
      calc w
          = (DensePoly.C v⁻¹ * w : FpPoly p) * DensePoly.C v := hcand_mul.symm
        _ = DensePoly.C v * (DensePoly.C v⁻¹ * w : FpPoly p) :=
            DensePoly.mul_comm_poly _ _⟩
  have hmod : w % (DensePoly.C v : FpPoly p) = 0 :=
    DensePoly.mod_eq_zero_of_dvd w (DensePoly.C v : FpPoly p) hCv_dvd
  have hrec :
      (w / (DensePoly.C v : FpPoly p)) * (DensePoly.C v : FpPoly p) +
          (w % (DensePoly.C v : FpPoly p)) = w :=
    DensePoly.div_mul_add_mod w (DensePoly.C v : FpPoly p)
  have hquot_mul :
      (w / (DensePoly.C v : FpPoly p)) * (DensePoly.C v : FpPoly p) = w := by
    rw [hmod, add_zero] at hrec
    exact hrec
  apply mul_right_cancel_of_ne_zero hCv_ne
  rw [hquot_mul, hcand_mul]

/--
If the active Yun state has a nonzero constant first component, the whole
`yunFactorsContributionWithLevel` excursion only emits a nonzero constant
contribution and leaves a residual that is explicitly a nonzero scalar
multiple of another polynomial.
This packages the constant-state TF/FT branch used by the recursive scalar
synchronization proof.
-/
private theorem yunFactorsContributionWithLevel_constant_scalar_form
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {k : ZMod64 p} (hk : k ≠ 0) (w : FpPoly p)
    (base level fuel : Nat) :
    ∃ s t : ZMod64 p, ∃ w0 : FpPoly p, s ≠ 0 ∧ t ≠ 0 ∧
      (yunFactorsContributionWithLevel (DensePoly.C k : FpPoly p) w base level fuel).1 =
        DensePoly.C s ∧
      (yunFactorsContributionWithLevel (DensePoly.C k : FpPoly p) w base level fuel).2 =
        DensePoly.C t * w0 := by
  induction fuel generalizing k w level with
  | zero =>
      refine ⟨1, 1, w, zmod64_one_ne_zero_of_prime hp,
        zmod64_one_ne_zero_of_prime hp, ?_, ?_⟩
      · simp [yunFactorsContributionWithLevel]
        rfl
      · simp [yunFactorsContributionWithLevel]
        change w = (1 : FpPoly p) * w
        rw [one_mul]
  | succ fuel ih =>
      by_cases hc : isOne (DensePoly.C k : FpPoly p)
      · refine ⟨1, 1, w, zmod64_one_ne_zero_of_prime hp,
          zmod64_one_ne_zero_of_prime hp, ?_, ?_⟩
        · simp [yunFactorsContributionWithLevel, hc]
          rfl
        · simp [yunFactorsContributionWithLevel, hc]
          change w = (1 : FpPoly p) * w
          rw [one_mul]
      · let y : FpPoly p := DensePoly.gcd (DensePoly.C k : FpPoly p) w
        let z : FpPoly p := (DensePoly.C k : FpPoly p) / y
        have hy_dvd : y ∣ (DensePoly.C k : FpPoly p) :=
          DensePoly.gcd_dvd_left (DensePoly.C k : FpPoly p) w
        obtain ⟨v, hv, hy_eq⟩ := constant_divisor_eq_C hk hy_dvd
        have hz_const : ∃ a : ZMod64 p, a ≠ 0 ∧ z = DensePoly.C a := by
          have hquot_dvd : z ∣ (DensePoly.C k : FpPoly p) := by
            refine ⟨y, ?_⟩
            have hmod : (DensePoly.C k : FpPoly p) % y = 0 :=
              DensePoly.mod_eq_zero_of_dvd (DensePoly.C k : FpPoly p) y hy_dvd
            have hrec : z * y + (DensePoly.C k : FpPoly p) % y =
                (DensePoly.C k : FpPoly p) := by
              simpa [z] using
                (DensePoly.div_mul_add_mod (DensePoly.C k : FpPoly p) y)
            rw [hmod, add_zero] at hrec
            exact hrec.symm
          exact constant_divisor_eq_C hk hquot_dvd
        obtain ⟨sTail, tTail, wTail, hsTail, htTail, htail₁, htail₂⟩ :=
          ih hv (w / y) (level + 1)
        have htail₁_y :
            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 =
              DensePoly.C sTail := by
          simpa [hy_eq] using htail₁
        have htail₂_y :
            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 =
              DensePoly.C tTail * wTail := by
          simpa [hy_eq] using htail₂
        by_cases hz_one : isOne z
        · refine ⟨sTail, tTail, wTail, hsTail, htTail, ?_, ?_⟩
          · have hz_true_y :
                isOne ((DensePoly.C k : FpPoly p) / y) = true := by
              simpa [z] using hz_one
            simpa [yunFactorsContributionWithLevel, hc, y, z, hz_true_y] using htail₁_y
          · have hz_true_y :
                isOne ((DensePoly.C k : FpPoly p) / y) = true := by
              simpa [z] using hz_one
            simpa [yunFactorsContributionWithLevel, hc, y, z, hz_true_y] using htail₂_y
        · obtain ⟨a, ha, hz_eq⟩ := hz_const
          have hz_false : isOne z = false := by
            cases h : isOne z
            · rfl
            · exfalso
              exact hz_one h
          have hz_false_y :
              isOne ((DensePoly.C k : FpPoly p) / y) = false := by
            simpa [z] using hz_false
          have hz_eq_y : ((DensePoly.C k : FpPoly p) / y) = DensePoly.C a := by
            simpa [z] using hz_eq
          have hza_false : isOne (DensePoly.C a : FpPoly p) = false := by
            simpa [hz_eq] using hz_false
          obtain ⟨sPow, hsPow, hpow⟩ := pow_C_form hp ha (base * level)
          refine ⟨sPow * sTail, tTail, wTail, ?_, htTail, ?_, ?_⟩
          · intro hzero
            rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hsp_zero | hst_zero
            · exact hsPow hsp_zero
            · exact hsTail hst_zero
          · simp [yunFactorsContributionWithLevel, hc, y, hz_eq_y,
              hza_false, hpow, htail₁_y, fpPoly_C_mul_C_eq]
          · simpa [yunFactorsContributionWithLevel, hc, y, z, hz_false_y] using htail₂_y

private theorem yunFactorsContributionWithLevel_constant_scalar_sync
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {k : ZMod64 p} (hk : k ≠ 0) (w : FpPoly p)
    (base level fuel : Nat) :
    ∃ s t : ZMod64 p, s ≠ 0 ∧ t ≠ 0 ∧
      (yunFactorsContributionWithLevel (DensePoly.C k : FpPoly p) w base level fuel).1 =
        DensePoly.C s ∧
      (yunFactorsContributionWithLevel (DensePoly.C k : FpPoly p) w base level fuel).2 =
        DensePoly.C t * w := by
  induction fuel generalizing k w level with
  | zero =>
      refine ⟨1, 1, zmod64_one_ne_zero_of_prime hp,
        zmod64_one_ne_zero_of_prime hp, ?_, ?_⟩
      · simp [yunFactorsContributionWithLevel]
        rfl
      · simp [yunFactorsContributionWithLevel]
        change w = (1 : FpPoly p) * w
        rw [one_mul]
  | succ fuel ih =>
      by_cases hc : isOne (DensePoly.C k : FpPoly p)
      · refine ⟨1, 1, zmod64_one_ne_zero_of_prime hp,
          zmod64_one_ne_zero_of_prime hp, ?_, ?_⟩
        · simp [yunFactorsContributionWithLevel, hc]
          rfl
        · simp [yunFactorsContributionWithLevel, hc]
          change w = (1 : FpPoly p) * w
          rw [one_mul]
      · let y : FpPoly p := DensePoly.gcd (DensePoly.C k : FpPoly p) w
        let z : FpPoly p := (DensePoly.C k : FpPoly p) / y
        have hy_dvd : y ∣ (DensePoly.C k : FpPoly p) :=
          DensePoly.gcd_dvd_left (DensePoly.C k : FpPoly p) w
        obtain ⟨v, hv, hy_eq⟩ := constant_divisor_eq_C hk hy_dvd
        have hw_div_y :
            w / y = DensePoly.C v⁻¹ * w := by
          simpa [y, hy_eq] using div_C_ne_zero_eq_C_inv_mul hp hv w
        have hv_inv_ne : v⁻¹ ≠ 0 :=
          zmod64_inv_ne_zero_of_prime_ne_zero hp hv
        have hz_const : ∃ a : ZMod64 p, a ≠ 0 ∧ z = DensePoly.C a := by
          have hquot_dvd : z ∣ (DensePoly.C k : FpPoly p) := by
            refine ⟨y, ?_⟩
            have hmod : (DensePoly.C k : FpPoly p) % y = 0 :=
              DensePoly.mod_eq_zero_of_dvd (DensePoly.C k : FpPoly p) y hy_dvd
            have hrec : z * y + (DensePoly.C k : FpPoly p) % y =
                (DensePoly.C k : FpPoly p) := by
              simpa [z] using
                (DensePoly.div_mul_add_mod (DensePoly.C k : FpPoly p) y)
            rw [hmod, add_zero] at hrec
            exact hrec.symm
          exact constant_divisor_eq_C hk hquot_dvd
        obtain ⟨sTail, tTail, hsTail, htTail, htail₁, htail₂⟩ :=
          ih hv (w / y) (level + 1)
        have htail₁_y :
            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 =
              DensePoly.C sTail := by
          simpa [hy_eq] using htail₁
        have htail₂_y :
            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 =
              DensePoly.C (tTail * v⁻¹) * w := by
          calc
            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2
                = DensePoly.C tTail * (w / y) := by
                    simpa [hy_eq] using htail₂
            _ = DensePoly.C tTail * (DensePoly.C v⁻¹ * w) := by rw [hw_div_y]
            _ = (DensePoly.C tTail * DensePoly.C v⁻¹ : FpPoly p) * w :=
                    (DensePoly.mul_assoc_poly _ _ _).symm
            _ = DensePoly.C (tTail * v⁻¹) * w := by rw [fpPoly_C_mul_C_eq]
        have htTail_v_inv_ne : tTail * v⁻¹ ≠ 0 := by
          intro hzero
          rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with ht | hv'
          · exact htTail ht
          · exact hv_inv_ne hv'
        by_cases hz_one : isOne z
        · refine ⟨sTail, tTail * v⁻¹, hsTail, htTail_v_inv_ne, ?_, ?_⟩
          · have hz_true_y :
                isOne ((DensePoly.C k : FpPoly p) / y) = true := by
              simpa [z] using hz_one
            simpa [yunFactorsContributionWithLevel, hc, y, z, hz_true_y] using htail₁_y
          · have hz_true_y :
                isOne ((DensePoly.C k : FpPoly p) / y) = true := by
              simpa [z] using hz_one
            simpa [yunFactorsContributionWithLevel, hc, y, z, hz_true_y] using htail₂_y
        · obtain ⟨a, ha, hz_eq⟩ := hz_const
          have hz_false : isOne z = false := by
            cases h : isOne z
            · rfl
            · exfalso
              exact hz_one h
          have hz_false_y :
              isOne ((DensePoly.C k : FpPoly p) / y) = false := by
            simpa [z] using hz_false
          have hz_eq_y : ((DensePoly.C k : FpPoly p) / y) = DensePoly.C a := by
            simpa [z] using hz_eq
          have hza_false : isOne (DensePoly.C a : FpPoly p) = false := by
            simpa [hz_eq] using hz_false
          obtain ⟨sPow, hsPow, hpow⟩ := pow_C_form hp ha (base * level)
          refine ⟨sPow * sTail, tTail * v⁻¹, ?_, htTail_v_inv_ne, ?_, ?_⟩
          · intro hzero
            rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hsp_zero | hst_zero
            · exact hsPow hsp_zero
            · exact hsTail hst_zero
          · simp [yunFactorsContributionWithLevel, hc, y, hz_eq_y,
              hza_false, hpow, htail₁_y, fpPoly_C_mul_C_eq]
          · simpa [yunFactorsContributionWithLevel, hc, y, z, hz_false_y] using htail₂_y

private theorem coeff_derivative (f : FpPoly p) (n : Nat) :
    (DensePoly.derivative f).coeff n =
      ((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1) := by
  unfold DensePoly.derivative
  rw [DensePoly.coeff_ofCoeffs_list]
  change
    ((List.range (f.size - 1)).map
        (fun i => ((i + 1 : Nat) : ZMod64 p) * f.coeff (i + 1))).getD n 0 =
      ((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1)
  by_cases hn : n < f.size - 1
  · simp [hn, List.getD]
  · have hf : f.size ≤ n + 1 := by omega
    have hcoeff : f.coeff (n + 1) = 0 :=
      DensePoly.coeff_eq_zero_of_size_le f hf
    simp [hn, List.getD, hcoeff]

private theorem derivative_isZero_true_of_pthRoot_frobenius
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hfrob : pow (pthRoot f) p = f) :
    (DensePoly.derivative f).isZero = true := by
  have hder_zero : DensePoly.derivative f = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [coeff_derivative]
    rw [← hfrob, pthRoot_pow_prime_coeff hp f (n + 1)]
    by_cases hmod : (n + 1) % p = 0
    · have hcast : (((n + 1 : Nat) : Nat) : ZMod64 p) = 0 := by
        rw [ZMod64.natCast_eq_zero_iff_dvd]
        exact Nat.dvd_of_mod_eq_zero hmod
      rw [hmod, hcast, DensePoly.coeff_zero]
      grind
    · rw [if_neg hmod, DensePoly.coeff_zero]
      exact zmod64_mul_zero ((n + 1 : Nat) : ZMod64 p)
  rw [hder_zero]
  rfl

private theorem yunFactorsContribution_terminal_residual_pthRoot_witness
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hresidual :
      yunFactorsContributionResidualDerivativeZero c w multiplicity fuel) :
    let contribution := yunFactorsContribution c w multiplicity fuel
    isOne contribution.2 = false →
      pow (pthRoot contribution.2) p = contribution.2 := by
  intro contribution hone
  exact pthRoot_frobenius_of_derivative_zero' hp contribution.2
    (hresidual hone)

private theorem yunFactorsContributionResidualDerivativeZero_of_terminal_residual_pthRoot_witness
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hwitness :
      let contribution := yunFactorsContribution c w multiplicity fuel
      isOne contribution.2 = false →
        pow (pthRoot contribution.2) p = contribution.2) :
    yunFactorsContributionResidualDerivativeZero c w multiplicity fuel := by
  intro hone
  exact derivative_isZero_true_of_pthRoot_frobenius hp
    (yunFactorsContribution c w multiplicity fuel).2
    (hwitness hone)

private theorem yunFactorsContribution_terminal_residual_pthRoot_witness_of_complete
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hcomplete :
      yunFactorsContributionResidualComplete c w multiplicity fuel) :
    let contribution := yunFactorsContribution c w multiplicity fuel
    isOne contribution.2 = false →
      pow (pthRoot contribution.2) p = contribution.2 := by
  exact
    yunFactorsContribution_terminal_residual_pthRoot_witness hp
      c w multiplicity fuel
      (yunFactorsContributionResidualDerivativeZero_of_complete
        c w multiplicity fuel hcomplete)

private theorem derivative_degree?_lt_self_of_ne_zero
    (f : FpPoly p) (hder_ne : DensePoly.derivative f ≠ 0) :
    (DensePoly.derivative f).degree?.getD 0 < f.degree?.getD 0 := by
  have hder_pos : 0 < (DensePoly.derivative f).size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hder_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le (DensePoly.derivative f) (by omega)
  let n := (DensePoly.derivative f).size - 1
  have hlast :
      (DensePoly.derivative f).coeff n ≠ 0 := by
    simpa [n] using
      DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.derivative f) hder_pos
  have hn_lt : n + 1 < f.size := by
    by_cases hlt : n + 1 < f.size
    · exact hlt
    · have hf_le : f.size ≤ n + 1 := Nat.le_of_not_gt hlt
      have hcoeff : f.coeff (n + 1) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f hf_le
      exfalso
      apply hlast
      rw [coeff_derivative f n, hcoeff]
      exact (Lean.Grind.Semiring.mul_zero ((n + 1 : Nat) : ZMod64 p)).symm
  have hf_pos : 0 < f.size := by omega
  have hder_degree :
      (DensePoly.derivative f).degree? =
        some ((DensePoly.derivative f).size - 1) := by
    unfold DensePoly.degree?
    simp [Nat.ne_of_gt hder_pos]
  have hf_degree : f.degree? = some (f.size - 1) := by
    unfold DensePoly.degree?
    simp [Nat.ne_of_gt hf_pos]
  rw [hder_degree, hf_degree]
  simp
  omega

private theorem derivative_isZero_true_of_dvd_self_derivative
    [ZMod64.PrimeModulus p] (f : FpPoly p)
    (hdvd : f ∣ DensePoly.derivative f) :
    (DensePoly.derivative f).isZero = true := by
  cases hder : (DensePoly.derivative f).isZero with
  | true => rfl
  | false =>
      have hder_ne : DensePoly.derivative f ≠ 0 :=
        ne_zero_of_isZero_false hder
      have hf_ne : f ≠ 0 := by
        intro hf_zero
        apply hder_ne
        rw [hf_zero]
        exact DensePoly.derivative_zero
      rcases hdvd with ⟨q, hq⟩
      have hq_ne : q ≠ 0 := by
        intro hq_zero
        apply hder_ne
        rw [hq, hq_zero, mul_zero]
      have hdeg_mul := degree?_mul_eq_add_degree? f q hf_ne hq_ne
      have hdeg_lt := derivative_degree?_lt_self_of_ne_zero f hder_ne
      have hdeg_eq :
          (DensePoly.derivative f).degree?.getD 0 = (f * q).degree?.getD 0 := by
        rw [hq]
      rw [hdeg_mul] at hdeg_eq
      omega

private theorem right_factor_derivative_isZero_of_mul_derivative_isZero_of_common_dvd_one
    [ZMod64.PrimeModulus p] (y z : FpPoly p)
    (hder : (DensePoly.derivative (z * y)).isZero = true)
    (hcommon :
      ∀ d : FpPoly p, d ∣ y → d ∣ z → d ∣ (1 : FpPoly p)) :
    (DensePoly.derivative z).isZero = true := by
  have hsum_zero :
      DensePoly.derivative z * y + z * DensePoly.derivative y = 0 := by
    have hzero : DensePoly.derivative (z * y) = 0 :=
      eq_zero_of_isZero_true _ hder
    calc
      DensePoly.derivative z * y + z * DensePoly.derivative y =
          DensePoly.derivative (z * y) := (DensePoly.derivative_mul z y).symm
      _ = 0 := hzero
  have hz_dvd_sum :
      z ∣ DensePoly.derivative z * y + z * DensePoly.derivative y := by
    rw [hsum_zero]
    exact ⟨0, by rw [mul_zero]⟩
  have hz_dvd_right : z ∣ z * DensePoly.derivative y := by
    exact ⟨DensePoly.derivative y, rfl⟩
  have hz_dvd_left : z ∣ DensePoly.derivative z * y := by
    have hsub := dvd_sub_poly hz_dvd_sum hz_dvd_right
    have hsub_eq :
        (DensePoly.derivative z * y + z * DensePoly.derivative y) -
            z * DensePoly.derivative y =
          DensePoly.derivative z * y := by
      rw [sub_eq_add_neg]
      calc
        (DensePoly.derivative z * y + z * DensePoly.derivative y) +
            -(z * DensePoly.derivative y)
            = DensePoly.derivative z * y +
                (z * DensePoly.derivative y + -(z * DensePoly.derivative y)) := by
              exact DensePoly.add_assoc_poly
                (DensePoly.derivative z * y)
                (z * DensePoly.derivative y)
                (-(z * DensePoly.derivative y))
        _ = DensePoly.derivative z * y + 0 := by rw [add_right_neg]
        _ = DensePoly.derivative z * y := add_zero _
    simpa [hsub_eq] using hsub
  have hz_dvd_y_dz : z ∣ y * DensePoly.derivative z := by
    have hcomm : y * DensePoly.derivative z = DensePoly.derivative z * y :=
      DensePoly.mul_comm_poly y (DensePoly.derivative z)
    rw [hcomm]
    exact hz_dvd_left
  have hz_dvd_dz : z ∣ DensePoly.derivative z := by
    exact dvd_of_dvd_mul_of_common_dvd_one
      (g := z) (c := y) (h := DensePoly.derivative z)
      hz_dvd_y_dz
      hcommon
  exact derivative_isZero_true_of_dvd_self_derivative z hz_dvd_dz

private theorem powLinear_ne_zero
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) :
    ∀ n, powLinear d n ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro hone
      have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hone
      change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
      change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
      rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
      exact zmod64_one_ne_zero_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hcoeff
  | succ n ih =>
      change powLinear d n * d ≠ 0
      exact mul_ne_zero_of_ne_zero ih hd

private theorem pow_ne_zero
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) (n : Nat) :
    pow d n ≠ 0 := by
  rw [pow_eq_powLinear]
  exact powLinear_ne_zero hd n

private theorem powLinear_degree?_getD
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) :
    ∀ n, (powLinear d n).degree?.getD 0 = n * d.degree?.getD 0 := by
  intro n
  induction n with
  | zero =>
      change (1 : FpPoly p).degree?.getD 0 = 0 * d.degree?.getD 0
      change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 = 0 * d.degree?.getD 0
      rw [DensePoly.degree?_C_getD]
      simp
  | succ n ih =>
      change (powLinear d n * d).degree?.getD 0 =
        (n + 1) * d.degree?.getD 0
      rw [degree?_mul_eq_add_degree? (powLinear d n) d
        (powLinear_ne_zero hd n) hd, ih, Nat.succ_mul]

private theorem pow_degree?_getD
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) (n : Nat) :
    (pow d n).degree?.getD 0 = n * d.degree?.getD 0 := by
  rw [pow_eq_powLinear]
  exact powLinear_degree?_getD hd n

private theorem dvd_one_of_all_powers_dvd_nonzero
    [ZMod64.PrimeModulus p] {d g : FpPoly p}
    (hg : g.isZero = false)
    (hall : ∀ n : Nat, pow d n ∣ g) :
    d ∣ (1 : FpPoly p) := by
  have hg_ne : g ≠ 0 := ne_zero_of_isZero_false hg
  have hd_ne : d ≠ 0 := by
    intro hd
    rcases hall 1 with ⟨q, hq⟩
    apply hg_ne
    rw [pow_one, hd, zero_mul] at hq
    exact hq
  have hd_degree_zero : d.degree?.getD 0 = 0 := by
    by_cases hdeg_zero : d.degree?.getD 0 = 0
    · exact hdeg_zero
    · have hdeg_pos : 0 < d.degree?.getD 0 := Nat.pos_of_ne_zero hdeg_zero
      let n := g.degree?.getD 0 + 1
      rcases hall n with ⟨q, hq⟩
      have hq_ne : q ≠ 0 := by
        intro hq_zero
        apply hg_ne
        rw [hq, hq_zero, mul_zero]
      have hpow_ne : pow d n ≠ 0 := pow_ne_zero hd_ne n
      have hdeg_mul := degree?_mul_eq_add_degree? (pow d n) q hpow_ne hq_ne
      have hdeg_pow := pow_degree?_getD hd_ne n
      have hdeg_eq :
          g.degree?.getD 0 = (pow d n * q).degree?.getD 0 := by
        rw [hq]
      rw [hdeg_mul, hdeg_pow] at hdeg_eq
      have hpow_large : g.degree?.getD 0 < n * d.degree?.getD 0 := by
        have hmul_ge :
            g.degree?.getD 0 + 1 ≤
              (g.degree?.getD 0 + 1) * d.degree?.getD 0 := by
          exact Nat.le_mul_of_pos_right (g.degree?.getD 0 + 1) hdeg_pos
        dsimp [n]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hmul_ge
      have hpow_le : n * d.degree?.getD 0 ≤ g.degree?.getD 0 := by
        omega
      exact False.elim ((Nat.not_lt_of_ge hpow_le) hpow_large)
  have hd_size_pos : 0 < d.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hd_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le d (by omega)
  have hd_size_ne : d.size ≠ 0 := Nat.pos_iff_ne_zero.mp hd_size_pos
  have hd_degree : d.degree? = some (d.size - 1) := by
    unfold DensePoly.degree?
    simp [hd_size_ne]
  have hd_size_one : d.size = 1 := by
    rw [hd_degree] at hd_degree_zero
    simp at hd_degree_zero
    omega
  have hcoeff_ne : d.coeff 0 ≠ 0 := by
    have hlast := DensePoly.coeff_last_ne_zero_of_pos_size d hd_size_pos
    simpa [hd_size_one] using hlast
  have hd_const : d = DensePoly.C (d.coeff 0) := by
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        rw [DensePoly.coeff_C]
        simp
    | succ n =>
        have hsize_le : d.size ≤ n + 1 := by
          rw [hd_size_one]
          omega
        rw [DensePoly.coeff_eq_zero_of_size_le d hsize_le, DensePoly.coeff_C]
        simp
  rw [hd_const, ← scale_one_poly]
  exact dvd_scale_self_of_ne_zero hcoeff_ne (1 : FpPoly p)

private theorem derivativeSplit_quotient_common_dvd_derivative_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    ∀ d : FpPoly p,
      d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) := by
  dsimp
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro d hdc hddc
  let g := DensePoly.gcd f (DensePoly.derivative f)
  have hdf_false : (DensePoly.derivative f).isZero = false := by
    cases h : (DensePoly.derivative f).isZero
    · rfl
    · exact False.elim (hdf h)
  have hg_nonzero : g.isZero = false := by
    simpa [g] using
      gcd_isZero_false_of_right_isZero_false f (DensePoly.derivative f) hdf_false
  have hbase : pow d 0 ∣ g := by
    rw [pow_eq_powLinear]
    change (1 : FpPoly p) ∣ g
    exact ⟨g, by rw [one_mul]⟩
  have hstep :
      ∀ n, pow d n ∣ g → pow d (n + 1) ∣ g := by
    intro n hpow
    simpa [g] using
      derivativeSplit_quotient_pow_succ_dvd_gcd f d hdc hddc n (by simpa [g] using hpow)
  have hall : ∀ n : Nat, pow d n ∣ g := by
    intro n
    induction n with
    | zero =>
        exact hbase
    | succ n ih =>
        exact hstep n ih
  exact dvd_one_of_all_powers_dvd_nonzero hg_nonzero hall

private theorem derivativeSplit_residual_derivative_zero_of_coprime
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (_hdf : (DensePoly.derivative f).isZero = false)
    (hcoprime : ∀ d : FpPoly p,
      d ∣ (f / DensePoly.gcd f (DensePoly.derivative f)) →
      d ∣ DensePoly.gcd f (DensePoly.derivative f) →
      d ∣ (1 : FpPoly p)) :
    (DensePoly.derivative (DensePoly.gcd f (DensePoly.derivative f))).isZero = true := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  have hprod : c * g = f := by
    simpa [c, g] using div_gcd_mul_reconstruct f (DensePoly.derivative f)
  have hg_dvd_df : g ∣ DensePoly.derivative f := by
    simpa [g] using DensePoly.gcd_dvd_right f (DensePoly.derivative f)
  have hdf_prod :
      DensePoly.derivative f =
        DensePoly.derivative c * g + c * DensePoly.derivative g := by
    rw [← hprod]
    exact DensePoly.derivative_mul c g
  have hg_dvd_left : g ∣ DensePoly.derivative c * g := by
    exact ⟨DensePoly.derivative c, DensePoly.mul_comm_poly (DensePoly.derivative c) g⟩
  have hg_dvd_sum :
      g ∣ DensePoly.derivative c * g + c * DensePoly.derivative g := by
    simpa [hdf_prod] using hg_dvd_df
  have hg_dvd_cdg : g ∣ c * DensePoly.derivative g := by
    have hsub := dvd_sub_poly hg_dvd_sum hg_dvd_left
    have hsub_eq :
        (DensePoly.derivative c * g + c * DensePoly.derivative g) -
            DensePoly.derivative c * g =
          c * DensePoly.derivative g := by
      rw [sub_eq_add_neg]
      calc
        (DensePoly.derivative c * g + c * DensePoly.derivative g) +
            -(DensePoly.derivative c * g)
            = (c * DensePoly.derivative g + DensePoly.derivative c * g) +
                -(DensePoly.derivative c * g) := by
              exact congrArg (fun x => x + -(DensePoly.derivative c * g))
                (DensePoly.add_comm_poly (DensePoly.derivative c * g)
                  (c * DensePoly.derivative g))
        _ = c * DensePoly.derivative g +
                (DensePoly.derivative c * g + -(DensePoly.derivative c * g)) := by
              exact DensePoly.add_assoc_poly
                (c * DensePoly.derivative g)
                (DensePoly.derivative c * g)
                (-(DensePoly.derivative c * g))
        _ = c * DensePoly.derivative g + 0 := by rw [add_right_neg]
        _ = c * DensePoly.derivative g := add_zero _
    simpa [hsub_eq] using hsub
  have hg_dvd_dg : g ∣ DensePoly.derivative g := by
    exact dvd_of_dvd_mul_of_common_dvd_one
      (g := g) (c := c) (h := DensePoly.derivative g)
      hg_dvd_cdg
      (by
        intro d hdc hdg
        exact hcoprime d (by simpa [c, g] using hdc) (by simpa [g] using hdg))
  exact derivative_isZero_true_of_dvd_self_derivative g hg_dvd_dg

private theorem yunFactorsPairwiseReachable_common_dvd_one_derivativeSplit
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (_fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let y := DensePoly.gcd c g
    let z := c / y
    ∀ d : FpPoly p, d ∣ z → d ∣ y → d ∣ (1 : FpPoly p) := by
  dsimp
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro d hdz hdy
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  let y := DensePoly.gcd c g
  let z := c / y
  have hdc : d ∣ c := by
    have hprod : z * y = c := by
      simpa [z, y, c, g] using div_gcd_mul_reconstruct c g
    rw [← hprod]
    exact dvd_mul_right_of_dvd (a := z) (b := y) (d := d)
      (by simpa [z, y, c, g] using hdz)
  have hddc : d ∣ DensePoly.derivative c := by
    simpa [c, g, y, z] using
      yunStep_common_dvd_derivative_current c g d
        (by simpa [z, y, c, g] using hdz)
        (by simpa [y, c, g] using hdy)
  exact derivativeSplit_quotient_common_dvd_derivative_one hp f hdf d
    (by simpa [c, g] using hdc)
    (by simpa [c, g] using hddc)

private theorem squarefree_factor_of_squarefree
    {c y : FpPoly p}
    (hyc : y ∣ c)
    (hsquarefree :
      ∀ d : FpPoly p, d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p)) :
    ∀ d : FpPoly p,
      d ∣ y → d ∣ DensePoly.derivative y → d ∣ (1 : FpPoly p) := by
  intro d hdy hdderiv
  rcases hyc with ⟨q, hq⟩
  apply hsquarefree d
  · exact dvd_trans_poly hdy ⟨q, hq⟩
  · have hderiv :
        DensePoly.derivative c =
          DensePoly.derivative y * q + y * DensePoly.derivative q := by
      rw [hq]
      exact DensePoly.derivative_mul y q
    rw [hderiv]
    exact dvd_add_poly
      (dvd_mul_right_of_dvd (a := DensePoly.derivative y) (b := q) (d := d) hdderiv)
      (dvd_mul_right_of_dvd (a := y) (b := DensePoly.derivative q) (d := d) hdy)

private theorem yunFactorsPairwiseReachable_current_squarefree
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    ∀ d : FpPoly p,
      d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) := by
  induction hreachable with
  | derivativeSplit hp f fuel hdf =>
      intro d hdc hddc
      exact derivativeSplit_quotient_common_dvd_derivative_one hp f hdf d hdc hddc
  | step c w fuel _ ih =>
      exact squarefree_factor_of_squarefree
        (DensePoly.gcd_dvd_left c w) ih

private theorem yunFactorsPairwiseReachable_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    ∀ d : FpPoly p,
      d ∣ c / DensePoly.gcd c w →
        d ∣ DensePoly.gcd c w →
          d ∣ (1 : FpPoly p) := by
  intro d hdz hdy
  have hsquarefree :
      ∀ d : FpPoly p,
        d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) :=
    yunFactorsPairwiseReachable_current_squarefree c w (fuel + 1) hreachable
  apply hsquarefree d
  · let y := DensePoly.gcd c w
    let z := c / y
    have hprod : z * y = c := by
      simpa [z, y] using div_gcd_mul_reconstruct c w
    rw [← hprod]
    exact dvd_mul_right_of_dvd (a := z) (b := y) (d := d)
        (by simpa [z, y] using hdz)
  · exact yunStep_common_dvd_derivative_current c w d hdz hdy

private theorem dvd_mul_derivative_right_of_dvd_derivative_product
    (c w : FpPoly p)
    (hprev : w ∣ DensePoly.derivative (c * w)) :
    w ∣ c * DensePoly.derivative w := by
  have hw_dvd_left : w ∣ DensePoly.derivative c * w :=
    ⟨DensePoly.derivative c, DensePoly.mul_comm_poly (DensePoly.derivative c) w⟩
  have hder :
      DensePoly.derivative (c * w) =
        DensePoly.derivative c * w + c * DensePoly.derivative w :=
    DensePoly.derivative_mul c w
  have hsub := dvd_sub_poly (by simpa [hder] using hprev) hw_dvd_left
  have hsub_eq :
      (DensePoly.derivative c * w + c * DensePoly.derivative w) -
          DensePoly.derivative c * w =
        c * DensePoly.derivative w := by
    rw [sub_eq_add_neg]
    calc
      (DensePoly.derivative c * w + c * DensePoly.derivative w) +
          -(DensePoly.derivative c * w)
          = (c * DensePoly.derivative w + DensePoly.derivative c * w) +
              -(DensePoly.derivative c * w) := by
            exact congrArg (fun x => x + -(DensePoly.derivative c * w))
              (DensePoly.add_comm_poly
                (DensePoly.derivative c * w)
                (c * DensePoly.derivative w))
      _ = c * DensePoly.derivative w +
              (DensePoly.derivative c * w + -(DensePoly.derivative c * w)) := by
            exact DensePoly.add_assoc_poly
              (c * DensePoly.derivative w)
              (DensePoly.derivative c * w)
              (-(DensePoly.derivative c * w))
      _ = c * DensePoly.derivative w + 0 := by rw [add_right_neg]
      _ = c * DensePoly.derivative w := add_zero _
  simpa [hsub_eq] using hsub

private theorem yunStep_quotient_tail_common_dvd_one_of_reachable
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    ∀ d : FpPoly p,
      d ∣ c / DensePoly.gcd c w →
        d ∣ w / DensePoly.gcd c w →
          d ∣ (1 : FpPoly p) := by
  intro d hda hdz
  let y := DensePoly.gcd c w
  let a := c / y
  let z := w / y
  have hcy : a * y = c := by
    simpa [a, y] using div_gcd_mul_reconstruct c w
  have hwy : z * y = w := by
    simpa [z, y] using div_gcd_right_mul_reconstruct c w
  have hz_dvd_w : z ∣ w := ⟨y, by simpa [z, y] using hwy.symm⟩
  have hdy : d ∣ y := by
    apply DensePoly.dvd_gcd
    · rw [← hcy]
      exact dvd_mul_right_of_dvd (a := a) (b := y) (d := d)
        (by simpa [a, y] using hda)
    · exact dvd_trans_poly (by simpa [z, y] using hdz) hz_dvd_w
  exact
    yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable d
      hda
      (by simpa [y] using hdy)

private theorem quotient_dvd_of_mul_right_dvd_mul_right
    [ZMod64.PrimeModulus p]
    {a c w y z h : FpPoly p}
    (hy : y ≠ 0)
    (hcy : a * y = c)
    (hwy : z * y = w)
    (hdvd : w ∣ c * h) :
    z ∣ a * h := by
  rcases hdvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply FpPoly.mul_right_cancel_of_ne_zero hy
  calc
    (a * h) * y
        = (a * y) * h := by
          calc
            (a * h) * y = a * (h * y) := DensePoly.mul_assoc_poly a h y
            _ = a * (y * h) := by
                  exact congrArg (fun x => a * x) (DensePoly.mul_comm_poly h y)
            _ = (a * y) * h := (DensePoly.mul_assoc_poly a y h).symm
    _ = c * h := by rw [hcy]
    _ = w * q := hq
    _ = (z * y) * q := by rw [hwy]
    _ = (z * q) * y := by
          calc
            (z * y) * q = z * (y * q) := DensePoly.mul_assoc_poly z y q
            _ = z * (q * y) := by
                  exact congrArg (fun x => z * x) (DensePoly.mul_comm_poly y q)
            _ = (z * q) * y := (DensePoly.mul_assoc_poly z q y).symm

set_option maxHeartbeats 800000 in
private theorem yunStep_residual_dvd_derivative_product_core
    [ZMod64.PrimeModulus p]
    (c w y a z : FpPoly p)
    (hcy : a * y = c)
    (hwy : z * y = w)
    (hcommon_az :
      ∀ d : FpPoly p, d ∣ a → d ∣ z → d ∣ (1 : FpPoly p))
    (hprev : w ∣ DensePoly.derivative (c * w)) :
    z ∣ DensePoly.derivative (y * z) := by
  have hw_dvd_cdw : w ∣ c * DensePoly.derivative w :=
    dvd_mul_derivative_right_of_dvd_derivative_product c w hprev
  have hz_dvd_adw : z ∣ a * DensePoly.derivative w := by
    by_cases hy_zero : y = 0
    · rw [← hwy, hy_zero, mul_zero] at hw_dvd_cdw
      rw [← hwy, hy_zero, mul_zero]
      exact ⟨0, by rw [DensePoly.derivative_zero, mul_zero, mul_zero]⟩
    · exact
        quotient_dvd_of_mul_right_dvd_mul_right
          (a := a) (c := c) (w := w) (y := y) (z := z)
          (h := DensePoly.derivative w) hy_zero hcy hwy hw_dvd_cdw
  have hz_dvd_dw : z ∣ DensePoly.derivative w :=
    dvd_of_dvd_mul_of_common_dvd_one
      (g := z) (c := a) (h := DensePoly.derivative w)
      hz_dvd_adw
      hcommon_az
  have hyz : y * z = w := by
    calc
      y * z = z * y := DensePoly.mul_comm_poly y z
      _ = w := hwy
  simpa [hyz] using hz_dvd_dw

private theorem yunStep_residual_dvd_derivative_product_of_previous
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1))
    (hprev : w ∣ DensePoly.derivative (c * w)) :
    let y := DensePoly.gcd c w
    let z := w / y
    z ∣ DensePoly.derivative (y * z) := by
  dsimp
  let y := DensePoly.gcd c w
  let a := c / y
  let z := w / y
  have hcy : a * y = c := by
    simpa [a, y] using div_gcd_mul_reconstruct c w
  have hwy : z * y = w := by
    simpa [z, y] using div_gcd_right_mul_reconstruct c w
  have hcommon_az :
      ∀ d : FpPoly p, d ∣ a → d ∣ z → d ∣ (1 : FpPoly p) := by
    intro d hda hdz
    exact
      yunStep_quotient_tail_common_dvd_one_of_reachable c w fuel hreachable d
        (by simpa [a, y] using hda)
        (by simpa [z, y] using hdz)
  exact
    yunStep_residual_dvd_derivative_product_core
      c w y a z hcy hwy hcommon_az hprev

private theorem yunFactorsPairwiseReachable_residual_dvd_derivative_product
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    w ∣ DensePoly.derivative (c * w) := by
  induction hreachable with
  | derivativeSplit hp f fuel hdf =>
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      have hprod : c * g = f := by
        simpa [c, g] using div_gcd_mul_reconstruct f (DensePoly.derivative f)
      have hg_dvd_df : g ∣ DensePoly.derivative f := by
        simpa [g] using DensePoly.gcd_dvd_right f (DensePoly.derivative f)
      simpa [c, g, hprod] using hg_dvd_df
  | step c w fuel hprev ih =>
      exact
        yunStep_residual_dvd_derivative_product_of_previous
          c w fuel hprev ih

private theorem yunFactorsPairwiseReachable_terminal_residual_derivative_zero
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hc : isOne c = true) :
    (DensePoly.derivative w).isZero = true := by
  have hprod_dvd :
      w ∣ DensePoly.derivative (c * w) :=
    yunFactorsPairwiseReachable_residual_dvd_derivative_product c w fuel hreachable
  have hc_eq : c = 1 := eq_one_of_isOne_true c hc
  have hw_dvd_dw : w ∣ DensePoly.derivative w := by
    simpa [hc_eq, one_mul] using hprod_dvd
  exact derivative_isZero_true_of_dvd_self_derivative w hw_dvd_dw

private theorem one_lt_size_of_isOne_false_of_reachable
    [ZMod64.PrimeModulus p]
    (c : FpPoly p)
    (hzero : c.isZero = false)
    (hc : isOne c = false)
    (hreachable : squareFreeContributionReachable c) :
    1 < c.size := by
  have hpos : 0 < c.size := size_pos_of_isZero_false c hzero
  by_cases hsize : c.size = 1
  · have hc_eq_one : c = 1 := hreachable hsize
    rw [hc_eq_one, isOne_one] at hc
    cases hc
  · omega

private theorem pthRoot_valid_of_derivative_zero_nontrivial
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hone : isOne f = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeContributionReachable (pthRoot f) ∧
      (pthRoot f).isZero = false ∧
        (pthRoot f).size < fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hsize : 1 < f.size :=
    one_lt_size_of_isOne_false_of_reachable f hzero hone hreachable
  exact ⟨
    pthRoot_reachable_of_derivative_zero hp f hzero hdf hreachable,
    pthRoot_nonzero_of_derivative_zero_nonconstant hp f hzero hdf hsize,
    pthRoot_fuel_decrease_of_derivative_zero_nonconstant hp f hfuel hsize⟩

private theorem normalizeMonic_nonzero_size_eq
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false) :
    (normalizeMonic f).2.size = f.size := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  rw [normalizeMonic_nonzero f hzero]
  have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hinv_ne := zmod64_inv_ne_zero_of_prime_ne_zero hp hlead_ne
  exact scale_size_eq_of_ne_zero (p := p) hinv_ne f

private theorem normalizeMonic_derivative_zero_of_derivative_zero
    (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (DensePoly.derivative (normalizeMonic f).2).isZero = true := by
  rw [normalizeMonic_nonzero f hzero]
  have hderiv_zero : DensePoly.derivative f = 0 :=
    eq_zero_of_isZero_true (DensePoly.derivative f) hdf
  have hzero_poly :
      DensePoly.derivative
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    have hcoeff_deriv :
        ((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1) = 0 := by
      have h := congrArg (fun g : FpPoly p => g.coeff n) hderiv_zero
      change (DensePoly.derivative f).coeff n = (0 : FpPoly p).coeff n at h
      rw [coeff_derivative, DensePoly.coeff_zero] at h
      simpa using h
    change
      (DensePoly.derivative
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f)).coeff n =
        (0 : FpPoly p).coeff n
    rw [coeff_derivative, DensePoly.coeff_zero]
    have hscale_coeff :
        (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n + 1) =
          (DensePoly.leadingCoeff f)⁻¹ * f.coeff (n + 1) := by
      exact DensePoly.coeff_scale_semiring (DensePoly.leadingCoeff f)⁻¹ f (n + 1)
    rw [hscale_coeff]
    calc
      ((n + 1 : Nat) : ZMod64 p) *
          ((DensePoly.leadingCoeff f)⁻¹ * f.coeff (n + 1)) =
          (DensePoly.leadingCoeff f)⁻¹ *
            (((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1)) := by
            grind
      _ = 0 := by
            rw [hcoeff_deriv]
            grind
  rw [hzero_poly]
  rfl

private theorem pthRoot_normalizeMonic_frobenius_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot (normalizeMonic f).2) p = (normalizeMonic f).2 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hnorm_zero :=
    normalizeMonic_nonzero_isZero_false (p := p) f hzero
  have hnorm_deriv :=
    normalizeMonic_derivative_zero_of_derivative_zero f hzero hdf
  exact pthRoot_frobenius_of_derivative_zero
    hp (normalizeMonic f).2 hnorm_zero hnorm_deriv

private theorem pthRoot_normalizeMonic_reconstruct_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    DensePoly.C (normalizeMonic f).1 *
        pow (pthRoot (normalizeMonic f).2) p = f := by
  rw [pthRoot_normalizeMonic_frobenius_of_derivative_zero hp f hzero hdf]
  exact normalizeMonic_reconstruct hp f

private theorem pow_normalized_pthRoot_reconstruct_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity : Nat)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (DensePoly.C (normalizeMonic f).1) multiplicity *
        pow (pthRoot (normalizeMonic f).2) (multiplicity * p) =
      pow f multiplicity := by
  have hreconstruct :=
    pthRoot_normalizeMonic_reconstruct_of_derivative_zero hp f hzero hdf
  calc
    pow (DensePoly.C (normalizeMonic f).1) multiplicity *
        pow (pthRoot (normalizeMonic f).2) (multiplicity * p) =
        pow (DensePoly.C (normalizeMonic f).1) multiplicity *
          pow (pow (pthRoot (normalizeMonic f).2) p) multiplicity := by
          rw [pow_pow_mul']
    _ = pow (DensePoly.C (normalizeMonic f).1 *
          pow (pthRoot (normalizeMonic f).2) p) multiplicity := by
          exact (pow_mul_base
            (DensePoly.C (normalizeMonic f).1)
            (pow (pthRoot (normalizeMonic f).2) p)
            multiplicity).symm
    _ = pow f multiplicity := by
          rw [hreconstruct]

/--
The raw repeated tail emitted by the scaled Yun contribution loop is recovered
from its normalized tail together with the explicit leading scalar. This is the
local synchronization fact used by the derivative-active proof path; it keeps
the scalar ambiguity of executable `DensePoly.gcd` visible rather than treating
raw gcd output as monic.
-/
private theorem yunFactorsContributionWithLevel_normalized_tail_reconstruct
    (hp : Hex.Nat.Prime p) (c w : FpPoly p) (base level fuel : Nat) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    DensePoly.C (normalizeMonic contribution.2).1 *
        (normalizeMonic contribution.2).2 =
      contribution.2 := by
  exact normalizeMonic_reconstruct hp
    (yunFactorsContributionWithLevel c w base level fuel).2

/--
Product-state synchronization for the raw scaled Yun split and its normalized
tail. If the raw contribution and residual reconstruct `pow f multiplicity`,
then replacing the residual power by the normalized residual power and the
explicit scalar power preserves the same product.

This lemma deliberately does not assume `DensePoly.gcd` is monic: all scalar
ambiguity is isolated in `DensePoly.C (normalizeMonic contribution.2).1`.
-/
private theorem yunFactorsContributionWithLevel_normalized_tail_product_bridge
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p)
    (base level fuel multiplicity : Nat)
    (hproduct :
      let contribution := yunFactorsContributionWithLevel c w base level fuel
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    contribution.1 *
        (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
          pow (normalizeMonic contribution.2).2 multiplicity) =
      pow f multiplicity := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  have htail_reconstruct :
      DensePoly.C (normalizeMonic contribution.2).1 *
          (normalizeMonic contribution.2).2 =
        contribution.2 := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_normalized_tail_reconstruct
        hp c w base level fuel
  calc
    contribution.1 *
        (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
          pow (normalizeMonic contribution.2).2 multiplicity) =
        contribution.1 *
          pow (DensePoly.C (normalizeMonic contribution.2).1 *
            (normalizeMonic contribution.2).2) multiplicity := by
          rw [pow_mul_base]
    _ = contribution.1 * pow contribution.2 multiplicity := by
          rw [htail_reconstruct]
    _ = pow f multiplicity := by
          simpa [contribution] using hproduct

private theorem squareFreeAuxRevContribution_pthRoot_normalized_tail_bridge
    (hp : Hex.Nat.Prime p) (tail : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (hraw :
      squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p))
    (hnormalized :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
      pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
        squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel := by
  calc
    squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p) := hraw
    _ = pow tail multiplicity := by
          exact pthRoot_pow_mul_prime_of_derivative_zero
            hp tail multiplicity hmultiplicity hzero hdf
    _ = pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          pow (pthRoot (normalizeMonic tail).2) (multiplicity * p) := by
          exact (pow_normalized_pthRoot_reconstruct_of_derivative_zero
            hp tail multiplicity hzero hdf).symm
    _ = pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
            (multiplicity * p) fuel := by
          rw [hnormalized]

private theorem derivative_active_normalized_tail_weighted_product_bridge
    (hp : Hex.Nat.Prime p) (f tail contribution : FpPoly p)
    (multiplicity fuel : Nat)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (htail :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p))
    (hproduct : contribution * pow tail multiplicity = pow f multiplicity) :
    contribution *
        (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
            (multiplicity * p) fuel) =
      pow f multiplicity := by
  have htail_pow :=
    pow_normalized_pthRoot_reconstruct_of_derivative_zero
      hp tail multiplicity hzero hdf
  calc
    contribution *
        (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
            (multiplicity * p) fuel) =
        contribution *
          (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
            pow (pthRoot (normalizeMonic tail).2) (multiplicity * p)) := by
          rw [htail]
    _ = contribution * pow tail multiplicity := by
          rw [htail_pow]
    _ = pow f multiplicity := hproduct

private theorem derivative_active_raw_tail_weighted_product_bridge_via_normalized
    (hp : Hex.Nat.Prime p) (f tail contribution : FpPoly p)
    (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (hrawReachable : squareFreeContributionReachable (pthRoot tail))
    (hrawZero : (pthRoot tail).isZero = false)
    (hrawFuel : (pthRoot tail).size < fuel)
    (hrawResidual :
      squareFreeAuxRevResidualSatisfied (pthRoot tail) (multiplicity * p) fuel)
    (hcorrect :
      ∀ (f : FpPoly p) (multiplicity : Nat),
        0 < multiplicity →
          f.size < fuel →
            f.isZero = false →
              squareFreeContributionReachable f →
                squareFreeAuxRevResidualSatisfied f multiplicity fuel →
                  squareFreeAuxRevContribution f multiplicity fuel =
                    pow f multiplicity)
    (hnormalized :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p))
    (hproduct : contribution * pow tail multiplicity = pow f multiplicity) :
    contribution *
        squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
      pow f multiplicity := by
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hmultiplicity_tail : 0 < multiplicity * p :=
    Nat.mul_pos hmultiplicity hp_pos
  have hraw :
      squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p) :=
    hcorrect (pthRoot tail) (multiplicity * p)
      hmultiplicity_tail hrawFuel hrawZero hrawReachable hrawResidual
  have htail_bridge :=
    squareFreeAuxRevContribution_pthRoot_normalized_tail_bridge
      hp tail multiplicity fuel hmultiplicity hzero hdf hraw hnormalized
  calc
    contribution *
        squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        contribution *
          (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
            squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
              (multiplicity * p) fuel) := by
          rw [htail_bridge]
    _ = pow f multiplicity := by
          exact derivative_active_normalized_tail_weighted_product_bridge
            hp f tail contribution multiplicity fuel hzero hdf hnormalized hproduct

private theorem pthRoot_size_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (pthRoot f).size = (f.size - 1) / p + 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hmod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
  have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hjp : (f.size - 1) / p * p = f.size - 1 := by
    have h := Nat.mod_add_div (f.size - 1) p
    rw [hmod, Nat.zero_add] at h
    rw [Nat.mul_comm]
    exact h
  have hlead_ne : DensePoly.leadingCoeff f ≠ 0 :=
    fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hcoeff_jp : f.coeff ((f.size - 1) / p * p) = DensePoly.leadingCoeff f := by
    rw [DensePoly.leadingCoeff_eq_coeff_last f hpos, hjp]
  have hroot_coeff_j :
      (pthRoot f).coeff ((f.size - 1) / p) = DensePoly.leadingCoeff f := by
    rw [pthRoot_coeff]
    exact hcoeff_jp
  have hcoeff_above :
      ∀ i, (f.size - 1) / p < i → (pthRoot f).coeff i = 0 := by
    intro i hi
    rw [pthRoot_coeff]
    apply DensePoly.coeff_eq_zero_of_size_le
    have hmul : ((f.size - 1) / p + 1) * p ≤ i * p := Nat.mul_le_mul_right p hi
    have hexp : ((f.size - 1) / p + 1) * p = (f.size - 1) / p * p + p := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hexp, hjp] at hmul
    omega
  have hsize_le : (pthRoot f).size ≤ (f.size - 1) / p + 1 := by
    by_cases hgt : (pthRoot f).size ≤ (f.size - 1) / p + 1
    · exact hgt
    · exfalso
      have hbig : (f.size - 1) / p + 2 ≤ (pthRoot f).size :=
        Nat.lt_of_not_ge hgt
      have hpos' : 0 < (pthRoot f).size :=
        Nat.lt_of_lt_of_le (Nat.succ_pos _) hbig
      have hidx_succ : (f.size - 1) / p + 1 ≤ (pthRoot f).size - 1 := by
        have h1 : (pthRoot f).size - 1 + 1 = (pthRoot f).size :=
          Nat.sub_add_cancel hpos'
        have h2 : (f.size - 1) / p + 2 ≤ (pthRoot f).size - 1 + 1 := h1 ▸ hbig
        omega
      have hidx : (f.size - 1) / p < (pthRoot f).size - 1 :=
        Nat.lt_of_succ_le hidx_succ
      have hzero_top : (pthRoot f).coeff ((pthRoot f).size - 1) = 0 :=
        hcoeff_above _ hidx
      have hne : (pthRoot f).coeff ((pthRoot f).size - 1) ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (pthRoot f) hpos'
      exact hne hzero_top
  have hsize_ge : (f.size - 1) / p + 1 ≤ (pthRoot f).size := by
    by_cases hge : (f.size - 1) / p + 1 ≤ (pthRoot f).size
    · exact hge
    · exfalso
      have hzero_at_j : (pthRoot f).coeff ((f.size - 1) / p) = 0 := by
        apply DensePoly.coeff_eq_zero_of_size_le
        omega
      rw [hzero_at_j] at hroot_coeff_j
      exact hlead_ne hroot_coeff_j.symm
  omega

private theorem leadingCoeff_pthRoot_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    DensePoly.leadingCoeff (pthRoot f) = DensePoly.leadingCoeff f := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
  have hmod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hroot_size := pthRoot_size_of_derivative_zero hp f hzero hdf
  have hroot_pos : 0 < (pthRoot f).size := by rw [hroot_size]; exact Nat.succ_pos _
  rw [DensePoly.leadingCoeff_eq_coeff_last (pthRoot f) hroot_pos,
      DensePoly.leadingCoeff_eq_coeff_last f hpos]
  rw [hroot_size, pthRoot_coeff]
  congr 1
  have hdivmul : (f.size - 1) / p * p = f.size - 1 := by
    have h := Nat.mod_add_div (f.size - 1) p
    rw [hmod, Nat.zero_add] at h
    rw [Nat.mul_comm]
    exact h
  have hsub : (f.size - 1) / p + 1 - 1 = (f.size - 1) / p := by omega
  rw [hsub]
  exact hdivmul

/--
For a nonzero polynomial `f` with derivative zero, normalising commutes with
the formal `p`-th root: `(normalizeMonic (pthRoot f)).2 = pthRoot (normalizeMonic f).2`.

The identity is the coefficient-level fact that scaling by an inverse
commutes with `pthRoot` (since `pthRoot` is linear on stored coefficients),
combined with `leadingCoeff (pthRoot f) = leadingCoeff f` for derivative-zero
inputs. It is the computation-level bridge needed by the normalized-provider
weighted-product chain refactor; it is *not* a normalized-to-raw reachability
bridge (which is the route ruled out by the counterexample on #6125).
-/
private theorem normalizeMonic_pthRoot_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (normalizeMonic (pthRoot f)).2 = pthRoot (normalizeMonic f).2 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hroot_size := pthRoot_size_of_derivative_zero hp f hzero hdf
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hroot_nonzero : (pthRoot f).isZero = false := by
    have hpos : 0 < (pthRoot f).size := by rw [hroot_size]; exact Nat.succ_pos _
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
      Nat.pos_iff_ne_zero] using hpos
  have hlead_ne : DensePoly.leadingCoeff f ≠ 0 :=
    fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hlead_root_eq := leadingCoeff_pthRoot_of_derivative_zero hp f hzero hdf
  apply DensePoly.ext_coeff
  intro n
  rw [normalizeMonic_nonzero (pthRoot f) hroot_nonzero,
      normalizeMonic_nonzero f hzero]
  show (DensePoly.scale (DensePoly.leadingCoeff (pthRoot f))⁻¹ (pthRoot f)).coeff n =
    (pthRoot (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f)).coeff n
  have hscale_pthRoot :
      (DensePoly.scale (DensePoly.leadingCoeff (pthRoot f))⁻¹ (pthRoot f)).coeff n =
        (DensePoly.leadingCoeff (pthRoot f))⁻¹ * (pthRoot f).coeff n :=
    DensePoly.coeff_scale_semiring _ (pthRoot f) n
  have hpthRoot_lhs :
      (pthRoot f).coeff n = f.coeff (n * p) := pthRoot_coeff f n
  have hpthRoot_rhs :
      (pthRoot (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f)).coeff n =
        (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n * p) :=
    pthRoot_coeff (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) n
  have hscale_f :
      (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n * p) =
        (DensePoly.leadingCoeff f)⁻¹ * f.coeff (n * p) :=
    DensePoly.coeff_scale_semiring _ f (n * p)
  rw [hscale_pthRoot, hpthRoot_lhs, hpthRoot_rhs, hscale_f, hlead_root_eq]

private theorem pthRoot_normalized_valid_of_derivative_zero_nontrivial
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hone : isOne f = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeContributionReachable (pthRoot (normalizeMonic f).2) ∧
      (pthRoot (normalizeMonic f).2).isZero = false ∧
        (pthRoot (normalizeMonic f).2).size < fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hsize : 1 < f.size :=
    one_lt_size_of_isOne_false_of_reachable f hzero hone hreachable
  have hnorm_size : (normalizeMonic f).2.size = f.size :=
    normalizeMonic_nonzero_size_eq hp f hzero
  have hnorm_nonzero : (normalizeMonic f).2.isZero = false :=
    normalizeMonic_nonzero_isZero_false f hzero
  have hnorm_deriv :
      (DensePoly.derivative (normalizeMonic f).2).isZero = true :=
    normalizeMonic_derivative_zero_of_derivative_zero f hzero hdf
  have hnorm_monic : DensePoly.Monic (normalizeMonic f).2 :=
    normalizeMonic_nonzero_monic f hzero
  have hnorm_reachable :
      squareFreeContributionReachable (normalizeMonic f).2 :=
    squareFreeContributionReachable_of_monic (normalizeMonic f).2 hnorm_monic
  have hnorm_fuel : (normalizeMonic f).2.size < fuel + 1 := by
    omega
  have hnorm_size_gt : 1 < (normalizeMonic f).2.size := by
    omega
  exact ⟨
    pthRoot_reachable_of_derivative_zero
      hp (normalizeMonic f).2 hnorm_nonzero hnorm_deriv hnorm_reachable,
    pthRoot_nonzero_of_derivative_zero_nonconstant
      hp (normalizeMonic f).2 hnorm_nonzero hnorm_deriv hnorm_size_gt,
    pthRoot_fuel_decrease_of_derivative_zero_nonconstant
      hp (normalizeMonic f).2 hnorm_fuel hnorm_size_gt⟩

private theorem normalizeMonic_squareFreeContributionReachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    squareFreeContributionReachable (normalizeMonic f).2 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro hsize
  by_cases hzero : f.isZero = false
  · rw [normalizeMonic_nonzero f hzero] at hsize ⊢
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hscale_size :
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = f.size := by
          have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
          have hinv_ne := zmod64_inv_ne_zero_of_prime_ne_zero hp hlead_ne
          exact scale_size_eq_of_ne_zero (p := p) hinv_ne f
        have hf_size : f.size = 1 := by
          rw [← hscale_size]
          exact hsize
        have hunit_inv :
            (DensePoly.leadingCoeff f)⁻¹ * f.coeff 0 = 1 := by
          have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
          have hlead : DensePoly.leadingCoeff f = f.coeff 0 := by
            have hlead_last :
                DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
              unfold DensePoly.leadingCoeff DensePoly.coeff
              rw [Array.back?_eq_getElem?]
              have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
              have hidx : f.coeffs.size - 1 < f.coeffs.size := by
                simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
              simp [Array.getD, DensePoly.size, hidx]
            simpa [hf_size] using hlead_last
          rw [← hlead]
          have h := zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne
          have hcomm :
              (DensePoly.leadingCoeff f)⁻¹ * DensePoly.leadingCoeff f =
                DensePoly.leadingCoeff f * (DensePoly.leadingCoeff f)⁻¹ := by
            grind
          rw [hcomm]
          exact h
        change
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff 0 =
            (DensePoly.C (1 : ZMod64 p)).coeff 0
        have hcoeff :
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff 0 =
              (DensePoly.leadingCoeff f)⁻¹ * f.coeff 0 := by
          exact DensePoly.coeff_scale (DensePoly.leadingCoeff f)⁻¹ f 0
            (zmod64_mul_zero _)
        rw [hcoeff, hunit_inv]
        exact (DensePoly.coeff_C (1 : ZMod64 p) 0).symm
    | succ n =>
        have hcoeff_zero :
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) (by
              have hs :
                  (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = 1 := hsize
              omega)
        change
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n + 1) =
            (DensePoly.C (1 : ZMod64 p)).coeff (n + 1)
        rw [hcoeff_zero]
        exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm
  · have hzero_true : f.isZero = true := by
      cases h : f.isZero
      · exact False.elim (hzero h)
      · rfl
    rw [normalizeMonic_zero f hzero_true] at hsize
    simp at hsize

private theorem normalizeMonic_squareFreeContributionPayload
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false) :
    squareFreeContributionReachable (normalizeMonic f).2 ∧
      (normalizeMonic f).2.isZero = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact
    ⟨normalizeMonic_squareFreeContributionReachable hp f,
      normalizeMonic_nonzero_isZero_false f hzero⟩

private theorem normalizeMonic_isOne_false_of_isOne_false
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (hone : isOne f = false) :
    isOne (normalizeMonic f).2 = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  by_cases hnorm_one : isOne (normalizeMonic f).2 = true
  · have hnorm_eq_one : (normalizeMonic f).2 = 1 :=
      eq_one_of_isOne_true (normalizeMonic f).2 hnorm_one
    have hnorm_size : (normalizeMonic f).2.size = 1 := by
      rw [hnorm_eq_one]
      exact DensePoly.size_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
    have hf_size : f.size = 1 := by
      have hsize_eq := normalizeMonic_nonzero_size_eq hp f hzero
      omega
    have hf_eq_one : f = 1 := hreachable hf_size
    rw [hf_eq_one, isOne_one] at hone
    cases hone
  · cases h : isOne (normalizeMonic f).2
    · rfl
    · exact False.elim (hnorm_one h)

private abbrev YunDerivativeActiveNormalizedStateProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      squareFreeContributionReachable (normalizeMonic c).2 ∧
        (normalizeMonic c).2.isZero = false ∧
          squareFreeContributionReachable (normalizeMonic w).2 ∧
            (normalizeMonic w).2.isZero = false

private abbrev YunDerivativeActiveLevelStateProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      squareFreeContributionReachable c ∧
        c.isZero = false ∧
          w.isZero = false

private abbrev YunDerivativeActiveRawStateProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      squareFreeContributionReachable c ∧
        c.isZero = false ∧
          squareFreeContributionReachable w ∧
            w.isZero = false

private abbrev YunDerivativeActiveRawTailProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ base level fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      let contribution := yunFactorsContributionWithLevel c w base level fuel
      squareFreeContributionReachable contribution.2 ∧
        contribution.2.isZero = false ∧
          ((contribution.2.size < fuel + 1) →
            (isOne contribution.2 = false) →
              ((DensePoly.derivative contribution.2).isZero = true) →
                squareFreeContributionReachable (pthRoot contribution.2) ∧
                  (pthRoot contribution.2).isZero = false ∧
                    (pthRoot contribution.2).size < fuel)

private theorem YunDerivativeActiveRawStateProvider.levelState
    (hp : Hex.Nat.Prime p)
    (hstate : YunDerivativeActiveRawStateProvider hp) :
    YunDerivativeActiveLevelStateProvider hp := by
  intro f' c w fuel hreachable
  have hcurrent := hstate f' c w fuel hreachable
  exact ⟨hcurrent.1, hcurrent.2.1, hcurrent.2.2.2⟩

private theorem pthRoot_normalized_valid_of_derivative_zero_nontrivial_of_monic
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hone : isOne f = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hmonic : DensePoly.Monic f) :
    squareFreeContributionReachable (pthRoot f) ∧
      (pthRoot f).isZero = false ∧
        (pthRoot f).size < fuel := by
  have hreachable : squareFreeContributionReachable f :=
    squareFreeContributionReachable_of_monic f hmonic
  have hvalid :=
    pthRoot_normalized_valid_of_derivative_zero_nontrivial
      hp f hfuel hzero hone hdf hreachable
  have hnorm : (normalizeMonic f).2 = f :=
    normalizeMonic_eq_self_of_monic hp f hmonic
  simpa [hnorm] using hvalid

private theorem pthRoot_fuel_bound_or_one_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (_hdf : (DensePoly.derivative f).isZero = true)
    (hreachable : squareFreeContributionReachable f) :
    f = 1 ∨ (pthRoot f).size < fuel := by
  by_cases hsize : f.size = 1
  · exact Or.inl (hreachable hsize)
  · have hnonconstant : 1 < f.size := by
      have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
    exact Or.inr
      (pthRoot_fuel_decrease_of_derivative_zero_nonconstant
        hp f hfuel hnonconstant)

private theorem yunLevel_measure_lt_of_reachable_gcd_nonconstant
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hreachable : squareFreeContributionReachable c)
    (hc : isOne c = false)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false)
    (_hy_nonconstant : 1 < (DensePoly.gcd c w).size) :
    (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
      c.size + w.size := by
  have hc_size : 1 < c.size :=
    one_lt_size_of_isOne_false_of_reachable c hc_zero hc hreachable
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    rw [hw_eq] at hw_zero
    exact (Bool.eq_not_self _).mp hw_zero.symm
  have hsize :=
    size_div_add_size_eq_size_add_one_of_dvd
      (DensePoly.gcd_dvd_right c w) hw_ne
  omega

private theorem yunStep_tail_common_dvd_one_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hcommon :
      ∀ d : FpPoly p, d ∣ c → d ∣ w → d ∣ (1 : FpPoly p)) :
    ∀ d : FpPoly p,
      d ∣ DensePoly.gcd c w →
        d ∣ w / DensePoly.gcd c w →
          d ∣ (1 : FpPoly p) := by
  intro d hdy hdz
  apply hcommon d
  · exact dvd_trans_poly hdy (DensePoly.gcd_dvd_left c w)
  · have hprod : (w / DensePoly.gcd c w) * DensePoly.gcd c w = w := by
      exact div_gcd_right_mul_reconstruct c w
    rw [← hprod]
    exact dvd_mul_right_of_dvd
      (a := w / DensePoly.gcd c w)
      (b := DensePoly.gcd c w)
      (d := d)
      hdz

private theorem yunStep_tail_derivative_isZero_of_derivative_isZero_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hder : (DensePoly.derivative w).isZero = true)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ DensePoly.gcd c w →
          d ∣ w / DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    (DensePoly.derivative (w / DensePoly.gcd c w)).isZero = true := by
  let y := DensePoly.gcd c w
  let z := w / y
  have hprod : z * y = w := by
    simpa [y, z] using div_gcd_right_mul_reconstruct c w
  have hder_prod : (DensePoly.derivative (z * y)).isZero = true := by
    rw [hprod]
    exact hder
  exact
    right_factor_derivative_isZero_of_mul_derivative_isZero_of_common_dvd_one
      y z hder_prod
      (by
        intro d hdy hdz
        exact hcommon d (by simpa [y] using hdy) (by simpa [y, z] using hdz))

private theorem yunStep_tail_derivative_isZero_of_source_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hder : (DensePoly.derivative w).isZero = true)
    (hcommon :
      ∀ d : FpPoly p, d ∣ c → d ∣ w → d ∣ (1 : FpPoly p)) :
    (DensePoly.derivative (w / DensePoly.gcd c w)).isZero = true := by
  exact
    yunStep_tail_derivative_isZero_of_derivative_isZero_of_common_dvd_one
      c w hder
      (yunStep_tail_common_dvd_one_of_common_dvd_one c w hcommon)

private theorem yunFactorsContributionResidualComplete_of_derivative_zero_common
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hder : (DensePoly.derivative w).isZero = true)
    (hcommon : ∀ d : FpPoly p, d ∣ c → d ∣ w → d ∣ (1 : FpPoly p)) :
    yunFactorsContributionResidualComplete c w multiplicity fuel := by
  induction fuel generalizing c w multiplicity with
  | zero =>
      intro _hone
      simpa [yunFactorsContributionResidualComplete] using hder
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · simpa [yunFactorsContributionResidualComplete, hc] using
          (fun _hone : isOne w = false => hder)
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        let y := DensePoly.gcd c w
        have htail_der :
            (DensePoly.derivative (w / y)).isZero = true := by
          simpa [y] using
            yunStep_tail_derivative_isZero_of_source_common_dvd_one
              c w hder hcommon
        have htail_common :
            ∀ d : FpPoly p, d ∣ y → d ∣ w / y → d ∣ (1 : FpPoly p) := by
          simpa [y] using
            yunStep_tail_common_dvd_one_of_common_dvd_one c w hcommon
        have htail :
            yunFactorsContributionResidualComplete
              y (w / y) (multiplicity + 1) fuel :=
          ih y (w / y) (multiplicity + 1) htail_der htail_common
        simpa [yunFactorsContributionResidualComplete, hc_false, y] using htail

private theorem yunFactorsContributionResidualDerivativeZero_of_derivative_zero_common
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hder : (DensePoly.derivative w).isZero = true)
    (hcommon : ∀ d : FpPoly p, d ∣ c → d ∣ w → d ∣ (1 : FpPoly p)) :
    yunFactorsContributionResidualDerivativeZero c w multiplicity fuel := by
  exact
    yunFactorsContributionResidualDerivativeZero_of_complete
      c w multiplicity fuel
      (yunFactorsContributionResidualComplete_of_derivative_zero_common
        c w multiplicity fuel hder hcommon)

private theorem yunFactorsContributionResidualDerivativeZero_of_derivative_split_coprime
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hcoprime :
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      ∀ d : FpPoly p, d ∣ c → d ∣ g → d ∣ (1 : FpPoly p)) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsContributionResidualDerivativeZero c g multiplicity fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  have hder_g : (DensePoly.derivative g).isZero = true := by
    exact derivativeSplit_residual_derivative_zero_of_coprime hp f hdf hcoprime
  exact
    yunFactorsContributionResidualDerivativeZero_of_derivative_zero_common
      c g multiplicity fuel hder_g hcoprime

private theorem yunFactorsResidualDerivativeZero_of_derivative_active_coprime
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hcoprime :
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      ∀ d : FpPoly p, d ∣ c → d ∣ g → d ∣ (1 : FpPoly p)) :
    yunFactorsResidualDerivativeZero
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel := by
  apply yunFactorsResidualDerivativeZero_of_derivative_split_contribution
    hp f multiplicity fuel hdf
  exact
    yunFactorsContributionResidualDerivativeZero_of_derivative_split_coprime
      hp f multiplicity fuel hdf hcoprime

private theorem normalizeMonic_eq_one_of_dvd_one
    [ZMod64.PrimeModulus p] {g : FpPoly p}
    (hdiv : g ∣ (1 : FpPoly p)) :
    (normalizeMonic g).2 = 1 := by
  have hg_nonzero : g.isZero = false := by
    cases hzero : g.isZero with
    | false => rfl
    | true =>
        exfalso
        rcases hdiv with ⟨u, hu⟩
        have hone_ne : (1 : FpPoly p) ≠ 0 := by
          intro h
          have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
          change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
          change (DensePoly.C (1 : ZMod64 p)).coeff 0 =
            (0 : FpPoly p).coeff 0 at hcoeff
          rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
          exact zmod64_one_ne_zero_of_prime
            (ZMod64.PrimeModulus.prime (p := p)) hcoeff
        apply hone_ne
        rw [hu, eq_zero_of_isZero_true g hzero, zero_mul]
  apply eq_one_of_monic_dvd_one
  · exact normalizeMonic_nonzero_monic g hg_nonzero
  · have hnorm_dvd_g : (normalizeMonic g).2 ∣ g := by
      refine ⟨DensePoly.C (normalizeMonic g).1, ?_⟩
      calc
        g = DensePoly.C (normalizeMonic g).1 * (normalizeMonic g).2 := by
          exact (normalizeMonic_reconstruct
            (ZMod64.PrimeModulus.prime (p := p)) g).symm
        _ = (normalizeMonic g).2 * DensePoly.C (normalizeMonic g).1 := by
          exact DensePoly.mul_comm_poly _ _
    exact dvd_trans_poly hnorm_dvd_g hdiv

private theorem dvd_one_of_normalizeMonic_eq_one
    [ZMod64.PrimeModulus p] (g : FpPoly p)
    (hnorm : (normalizeMonic g).2 = 1) :
    g ∣ (1 : FpPoly p) := by
  by_cases hzero : g.isZero = true
  · exfalso
    rw [normalizeMonic_zero g hzero] at hnorm
    have hone_ne : (1 : FpPoly p) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
      change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
      change (DensePoly.C (1 : ZMod64 p)).coeff 0 =
        (0 : FpPoly p).coeff 0 at hcoeff
      rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
      exact zmod64_one_ne_zero_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hcoeff
    exact hone_ne hnorm.symm
  · have hzero_false : g.isZero = false := by
      cases h : g.isZero with
      | false => rfl
      | true => exact False.elim (hzero h)
    have hnonzero := normalizeMonic_nonzero g hzero_false
    have h_scale :
        DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g = 1 := by
      have heq :
          (normalizeMonic g).2 = DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g := by
        rw [hnonzero]
      rw [← heq]
      exact hnorm
    refine ⟨DensePoly.C (DensePoly.leadingCoeff g)⁻¹, ?_⟩
    calc (1 : FpPoly p)
        = DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g := h_scale.symm
      _ = DensePoly.C (DensePoly.leadingCoeff g)⁻¹ * g :=
          (C_mul_eq_scale _ _).symm
      _ = g * DensePoly.C (DensePoly.leadingCoeff g)⁻¹ :=
          DensePoly.mul_comm_poly _ _

private theorem yunStep_gcd_normalized_one_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hcommon :
      ∀ d : FpPoly p, d ∣ c → d ∣ w → d ∣ (1 : FpPoly p)) :
    (normalizeMonic (DensePoly.gcd c w)).2 = 1 := by
  have hgcd_dvd_one :
      DensePoly.gcd c w ∣ (1 : FpPoly p) :=
    hcommon (DensePoly.gcd c w)
      (DensePoly.gcd_dvd_left c w)
      (DensePoly.gcd_dvd_right c w)
  exact normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one

private theorem yunStep_tail_common_dvd_one_of_gcd_normalized_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hnormalized : (normalizeMonic (DensePoly.gcd c w)).2 = 1) :
    ∀ d : FpPoly p,
      d ∣ DensePoly.gcd c w →
        d ∣ w / DensePoly.gcd c w →
          d ∣ (1 : FpPoly p) := by
  intro d hdy _hdv
  exact dvd_trans_poly hdy
    (dvd_one_of_normalizeMonic_eq_one (DensePoly.gcd c w) hnormalized)

private theorem constant_nonzero_dvd
    [ZMod64.PrimeModulus p] {g f : FpPoly p}
    (hg_zero : g.isZero = false)
    (hg_const : ¬ 1 < g.size) :
    g ∣ f := by
  have hg_pos : 0 < g.size := size_pos_of_isZero_false g hg_zero
  have hg_size : g.size = 1 := by omega
  let unit := DensePoly.leadingCoeff g
  have hunit_ne : unit ≠ 0 := fpPoly_leadingCoeff_ne_zero_of_isZero_false g hg_zero
  have hg_eq_C : g = DensePoly.C unit := by
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hlead : unit = g.coeff 0 := by
          have hlead_last : DensePoly.leadingCoeff g = g.coeff (g.size - 1) := by
            unfold DensePoly.leadingCoeff DensePoly.coeff
            rw [Array.back?_eq_getElem?]
            have hidx : g.coeffs.size - 1 < g.coeffs.size := by
              simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hg_pos
            simp [Array.getD, DensePoly.size, hidx]
          simpa [unit, hg_size] using hlead_last
        rw [← hlead]
        exact (DensePoly.coeff_C unit 0).symm
    | succ n =>
        have hg_coeff_zero : g.coeff (n + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le g (by omega)
        rw [hg_coeff_zero]
        exact (DensePoly.coeff_C unit (n + 1)).symm
  refine ⟨DensePoly.scale unit⁻¹ f, ?_⟩
  rw [hg_eq_C, C_mul_eq_scale, scale_scale]
  rw [zmod64_mul_inv_eq_one_of_prime_ne_zero (ZMod64.PrimeModulus.prime (p := p)) hunit_ne]
  exact (scale_one_left f).symm

private theorem normalizeMonic_C_ne_zero_eq_one
    [ZMod64.PrimeModulus p] (k : ZMod64 p) (hk : k ≠ 0) :
    (normalizeMonic (DensePoly.C k : FpPoly p)).2 = 1 := by
  apply normalizeMonic_eq_one_of_dvd_one
  apply constant_nonzero_dvd
  · cases hzero : (DensePoly.C k : FpPoly p).isZero
    · rfl
    · exact False.elim (hk ((DensePoly.isZero_C_eq_true_iff k).mp hzero))
  · rw [DensePoly.size_C_of_ne_zero hk]
    omega

private theorem eq_C_of_normalizeMonic_isOne
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hone : isOne (normalizeMonic f).2 = true) :
    ∃ k : ZMod64 p, k ≠ 0 ∧ f = DensePoly.C k := by
  refine ⟨(normalizeMonic f).1, ?_, ?_⟩
  · rw [normalizeMonic_nonzero f hzero]
    exact fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  · have hnorm_eq : (normalizeMonic f).2 = 1 :=
      eq_one_of_isOne_true (normalizeMonic f).2 hone
    have hreconstruct := normalizeMonic_reconstruct hp f
    rw [hnorm_eq] at hreconstruct
    simpa using hreconstruct.symm

private theorem pow_eq_C_of_normalizeMonic_isOne
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (n : Nat)
    (hzero : f.isZero = false)
    (hone : isOne (normalizeMonic f).2 = true) :
    ∃ k : ZMod64 p, k ≠ 0 ∧ pow f n = DensePoly.C k := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  obtain ⟨u, hu, hf⟩ := eq_C_of_normalizeMonic_isOne hp f hzero hone
  rw [hf]
  exact pow_C_form hp hu n

private theorem yunStep_gcd_nonzero_of_left_nonzero
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false) :
    (DensePoly.gcd c w).isZero = false := by
  cases hy_zero : (DensePoly.gcd c w).isZero with
  | false => rfl
  | true =>
      exfalso
      have hy_eq_zero : DensePoly.gcd c w = 0 :=
        eq_zero_of_isZero_true (DensePoly.gcd c w) hy_zero
      rcases DensePoly.gcd_dvd_left c w with ⟨q, hq⟩
      have hc_eq_zero : c = 0 := by
        rw [hy_eq_zero, zero_mul] at hq
        exact hq
      rw [hc_eq_zero] at hc_zero
      cases hc_zero

private theorem gcd_C_ne_zero_dvd_one
    [ZMod64.PrimeModulus p] (k : ZMod64 p) (hk : k ≠ 0) (w : FpPoly p) :
    DensePoly.gcd (DensePoly.C k : FpPoly p) w ∣ (1 : FpPoly p) := by
  have hC_zero : (DensePoly.C k : FpPoly p).isZero = false := by
    cases hzero : (DensePoly.C k : FpPoly p).isZero
    · rfl
    · exact False.elim (hk ((DensePoly.isZero_C_eq_true_iff k).mp hzero))
  have hC_ne : (DensePoly.C k : FpPoly p) ≠ 0 :=
    ne_zero_of_isZero_false hC_zero
  have hg_zero :
      (DensePoly.gcd (DensePoly.C k : FpPoly p) w).isZero = false :=
    yunStep_gcd_nonzero_of_left_nonzero (DensePoly.C k : FpPoly p) w hC_zero
  apply constant_nonzero_dvd hg_zero
  have hsize_le :
      (DensePoly.gcd (DensePoly.C k : FpPoly p) w).size ≤
        (DensePoly.C k : FpPoly p).size :=
    size_le_of_dvd_of_ne_zero
      (DensePoly.gcd_dvd_left (DensePoly.C k : FpPoly p) w) hC_ne
  rw [DensePoly.size_C_of_ne_zero hk] at hsize_le
  omega

private theorem normalizeMonic_gcd_C_ne_zero_eq_one
    [ZMod64.PrimeModulus p] (k : ZMod64 p) (hk : k ≠ 0) (w : FpPoly p) :
    (normalizeMonic (DensePoly.gcd (DensePoly.C k : FpPoly p) w)).2 = 1 :=
  normalizeMonic_eq_one_of_dvd_one (gcd_C_ne_zero_dvd_one k hk w)

private theorem yunStep_gcd_dvd_one_of_constant_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false)
    (hy_constant : ¬ 1 < (DensePoly.gcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    DensePoly.gcd c w ∣ (1 : FpPoly p) := by
  have hy_zero : (DensePoly.gcd c w).isZero = false :=
    yunStep_gcd_nonzero_of_left_nonzero c w hc_zero
  apply hcommon (DensePoly.gcd c w)
  · exact constant_nonzero_dvd hy_zero hy_constant
  · exact DensePoly.dvd_refl_poly (DensePoly.gcd c w)

private theorem yunStep_gcd_normalized_one_of_constant_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false)
    (hy_constant : ¬ 1 < (DensePoly.gcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    (normalizeMonic (DensePoly.gcd c w)).2 = 1 := by
  exact normalizeMonic_eq_one_of_dvd_one
    (yunStep_gcd_dvd_one_of_constant_common_dvd_one
      c w hc_zero hy_constant hcommon)

private theorem yunStep_tail_common_dvd_one_of_constant_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false)
    (hy_constant : ¬ 1 < (DensePoly.gcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    ∀ d : FpPoly p,
      d ∣ DensePoly.gcd c w →
        d ∣ w / DensePoly.gcd c w →
          d ∣ (1 : FpPoly p) := by
  exact yunStep_tail_common_dvd_one_of_gcd_normalized_one c w
    (yunStep_gcd_normalized_one_of_constant_common_dvd_one
      c w hc_zero hy_constant hcommon)

private theorem yunLevel_measure_lt_of_reachable_gcd_constant
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hreachable : squareFreeContributionReachable c)
    (hc : isOne c = false)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false)
    (hy_constant : ¬ 1 < (DensePoly.gcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
      c.size + w.size := by
  have _htail_common :
      ∀ d : FpPoly p,
        d ∣ DensePoly.gcd c w →
          d ∣ w / DensePoly.gcd c w →
            d ∣ (1 : FpPoly p) :=
    yunStep_tail_common_dvd_one_of_constant_common_dvd_one
      c w hc_zero hy_constant hcommon
  have hc_size : 1 < c.size :=
    one_lt_size_of_isOne_false_of_reachable c hc_zero hc hreachable
  have hy_zero : (DensePoly.gcd c w).isZero = false :=
    yunStep_gcd_nonzero_of_left_nonzero c w hc_zero
  have hy_size : (DensePoly.gcd c w).size = 1 := by
    have hy_pos : 0 < (DensePoly.gcd c w).size :=
      size_pos_of_isZero_false (DensePoly.gcd c w) hy_zero
    omega
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    rw [hw_eq] at hw_zero
    exact (Bool.eq_not_self _).mp hw_zero.symm
  have hsize :
      (w / DensePoly.gcd c w).size + (DensePoly.gcd c w).size =
        w.size + 1 :=
    size_div_add_size_eq_size_add_one_of_dvd
      (DensePoly.gcd_dvd_right c w) hw_ne
  omega

private theorem yunLevel_measure_lt_of_reachable_step
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hstate :
      squareFreeContributionReachable c ∧
        c.isZero = false ∧
          w.isZero = false)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1))
    (hc : isOne c = false) :
    (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
      c.size + w.size := by
  rcases hstate with ⟨hcontribution_reachable, hc_zero, hw_zero⟩
  by_cases hy_nonconstant : 1 < (DensePoly.gcd c w).size
  · exact
      yunLevel_measure_lt_of_reachable_gcd_nonconstant
        c w hcontribution_reachable hc hc_zero hw_zero hy_nonconstant
  · exact
      yunLevel_measure_lt_of_reachable_gcd_constant
        c w hcontribution_reachable hc hc_zero hw_zero hy_nonconstant
        (yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable)

private theorem yunLevel_measure_lt_of_nonconstant_step
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hc_size : 1 < c.size)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
      c.size + w.size := by
  by_cases hy_nonconstant : 1 < (DensePoly.gcd c w).size
  · have hw_ne : w ≠ 0 := by
      intro hw_eq
      rw [hw_eq] at hw_zero
      exact (Bool.eq_not_self _).mp hw_zero.symm
    have hsize :=
      size_div_add_size_eq_size_add_one_of_dvd
        (DensePoly.gcd_dvd_right c w) hw_ne
    omega
  · have hcommon :
        ∀ d : FpPoly p,
          d ∣ c / DensePoly.gcd c w →
            d ∣ DensePoly.gcd c w →
              d ∣ (1 : FpPoly p) :=
      yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable
    have _htail_common :
        ∀ d : FpPoly p,
          d ∣ DensePoly.gcd c w →
            d ∣ w / DensePoly.gcd c w →
              d ∣ (1 : FpPoly p) :=
      yunStep_tail_common_dvd_one_of_constant_common_dvd_one
        c w hc_zero hy_nonconstant hcommon
    have hy_zero : (DensePoly.gcd c w).isZero = false :=
      yunStep_gcd_nonzero_of_left_nonzero c w hc_zero
    have hy_size : (DensePoly.gcd c w).size = 1 := by
      have hy_pos : 0 < (DensePoly.gcd c w).size :=
        size_pos_of_isZero_false (DensePoly.gcd c w) hy_zero
      omega
    have hw_ne : w ≠ 0 := by
      intro hw_eq
      rw [hw_eq] at hw_zero
      exact (Bool.eq_not_self _).mp hw_zero.symm
    have hsize :
        (w / DensePoly.gcd c w).size + (DensePoly.gcd c w).size =
          w.size + 1 :=
      size_div_add_size_eq_size_add_one_of_dvd
        (DensePoly.gcd_dvd_right c w) hw_ne
    omega

private theorem yunFactorsLevelCompletes_of_size_bound
    [ZMod64.PrimeModulus p] (c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hbound : c.size + w.size ≤ fuel + 1) :
    yunFactorsLevelCompletes c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate c w 0 hreachable
      have hc_pos : 0 < c.size :=
        size_pos_of_isZero_false c hcurrent.2.1
      have hw_pos : 0 < w.size :=
        size_pos_of_isZero_false w hcurrent.2.2
      exfalso
      omega
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · exact Or.inl hc
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsPairwiseReachable
              (DensePoly.gcd c w)
              (w / DensePoly.gcd c w)
              fuel :=
          yunFactorsPairwiseReachable_step c w fuel hreachable
        have hmeasure :
            (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
              c.size + w.size :=
          yunLevel_measure_lt_of_reachable_step
            c w fuel (hstate c w (fuel + 1) hreachable) hreachable hc_false
        have htail_bound :
            (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size ≤
              fuel + 1 := by
          omega
        exact Or.inr
          (ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
            htail_reachable htail_bound)

private theorem yunFactorsLevelCompletes_of_derivative_active_state
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsLevelCompletes c g multiplicity 1 fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  cases fuel with
  | zero =>
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      have hreachable :
          yunFactorsPairwiseReachable c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsPairwiseReachable_of_derivative_split hp f (fuel + 1) hdf_ne_true
      have hbound : c.size + g.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize :
            c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (DensePoly.gcd_dvd_left f (DensePoly.derivative f)) hf_ne
        omega
      simpa [c, g] using
        yunFactorsLevelCompletes_of_size_bound
          c g multiplicity 1 (fuel + 1) hstate hreachable hbound

private theorem yunFactorsDerivativeActiveReachable_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsDerivativeActiveReachable hp f
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      fuel :=
  yunFactorsDerivativeActiveReachable.derivativeSplit fuel hdf

private theorem yunFactorsDerivativeActiveReachable_step
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w (fuel + 1)) :
    yunFactorsDerivativeActiveReachable hp f
      (DensePoly.gcd c w)
      (w / DensePoly.gcd c w)
      fuel :=
  yunFactorsDerivativeActiveReachable.step c w fuel hreachable

private theorem yunFactorsContributionWithLevel_tail_valid_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              squareFreeContributionReachable w ∧
                w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    squareFreeContributionReachable contribution.2 ∧
      contribution.2.isZero = false := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate c w 0 hreachable
      simpa [yunFactorsContributionWithLevel] using
        And.intro hcurrent.2.2.1 hcurrent.2.2.2
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hcurrent := hstate c w (fuel + 1) hreachable
        simpa [yunFactorsContributionWithLevel, hc] using
          And.intro hcurrent.2.2.1 hcurrent.2.2.2
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (DensePoly.gcd c w)
              (w / DensePoly.gcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        simpa [yunFactorsContributionWithLevel, hc_false] using
          ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
            htail_reachable

private theorem yunFactorsContributionWithLevel_pthRoot_tail_valid
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              squareFreeContributionReachable w ∧
                w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel :
      (yunFactorsContributionWithLevel c w base level fuel).2.size < fuel + 1)
    (htail_nontrivial :
      isOne (yunFactorsContributionWithLevel c w base level fuel).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative
        (yunFactorsContributionWithLevel c w base level fuel).2).isZero = true) :
    squareFreeContributionReachable
        (pthRoot (yunFactorsContributionWithLevel c w base level fuel).2) ∧
      (pthRoot (yunFactorsContributionWithLevel c w base level fuel).2).isZero = false ∧
        (pthRoot (yunFactorsContributionWithLevel c w base level fuel).2).size < fuel := by
  have htail_valid :=
    yunFactorsContributionWithLevel_tail_valid_of_derivative_active_reachable
      hp f c w base level fuel hstate hreachable
  exact
    pthRoot_valid_of_derivative_zero_nontrivial hp
      (yunFactorsContributionWithLevel c w base level fuel).2
      htail_fuel htail_valid.2 htail_nontrivial htail_derivative_zero htail_valid.1

private theorem yunFactorsWithLevel_pthRoot_tail_fuel_bound
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              squareFreeContributionReachable w ∧
                w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel : (yunFactorsWithLevel c w base level fuel []).2.size < fuel + 1)
    (htail_nontrivial : isOne (yunFactorsWithLevel c w base level fuel []).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative (yunFactorsWithLevel c w base level fuel []).2).isZero = true) :
    (pthRoot (yunFactorsWithLevel c w base level fuel []).2).size < fuel := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  let loop := yunFactorsWithLevel c w base level fuel []
  have hloop_eq : loop.2 = contribution.2 := by
    have hrec := yunFactorsWithLevel_reconstruction_invariant c w base level fuel []
    simpa [loop, contribution] using hrec.1
  have hvalid :=
    yunFactorsContributionWithLevel_pthRoot_tail_valid
      hp f c w base level fuel hstate hreachable
      (by simpa [loop, contribution, hloop_eq] using htail_fuel)
      (by simpa [loop, contribution, hloop_eq] using htail_nontrivial)
      (by simpa [loop, contribution, hloop_eq] using htail_derivative_zero)
  simpa [loop, contribution, hloop_eq] using hvalid.2.2

private theorem YunDerivativeActiveRawStateProvider.rawTail
    (hp : Hex.Nat.Prime p)
    (hstate : YunDerivativeActiveRawStateProvider hp) :
    YunDerivativeActiveRawTailProvider hp := by
  intro f' c w base level fuel hreachable
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  have htail_valid :
      squareFreeContributionReachable contribution.2 ∧
        contribution.2.isZero = false := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_tail_valid_of_derivative_active_reachable
        hp f' c w base level fuel
        (fun c w fuel hreachable => hstate f' c w fuel hreachable)
        hreachable
  refine ⟨htail_valid.1, htail_valid.2, ?_⟩
  intro htail_fuel htail_nontrivial htail_derivative_zero
  simpa [contribution] using
    yunFactorsContributionWithLevel_pthRoot_tail_valid
      hp f' c w base level fuel
      (fun c w fuel hreachable => hstate f' c w fuel hreachable)
      hreachable htail_fuel
      htail_nontrivial htail_derivative_zero

private theorem yunFactorsPairwiseReachable_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    yunFactorsPairwiseReachable c w fuel := by
  induction hreachable with
  | derivativeSplit fuel hdf =>
      exact yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf
  | step c w fuel _ ih =>
      exact yunFactorsPairwiseReachable_step c w fuel ih

private theorem yunFactorsDerivativeActiveReachable_nonzero
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    c.isZero = false ∧ w.isZero = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction hreachable with
  | derivativeSplit fuel hdf =>
      let g := DensePoly.gcd f (DensePoly.derivative f)
      let c := f / g
      have hdf_false : (DensePoly.derivative f).isZero = false := by
        cases h : (DensePoly.derivative f).isZero
        · rfl
        · exact False.elim (hdf h)
      have hf_ne : f ≠ 0 := by
        intro hf
        apply hdf
        rw [hf, DensePoly.derivative_zero]
        rfl
      have hg_nonzero : g.isZero = false := by
        simpa [g] using
          gcd_isZero_false_of_right_isZero_false f (DensePoly.derivative f) hdf_false
      have hc_nonzero : c.isZero = false := by
        cases hc : c.isZero
        · rfl
        · have hc_zero : c = 0 := eq_zero_of_isZero_true c hc
          have hprod : c * g = f := by
            simpa [c, g] using div_gcd_mul_reconstruct f (DensePoly.derivative f)
          apply False.elim
          apply hf_ne
          rw [← hprod, hc_zero, zero_mul]
      simpa [c, g] using And.intro hc_nonzero hg_nonzero
  | step c w fuel _ ih =>
      let y := DensePoly.gcd c w
      let z := w / y
      have hy_nonzero : y.isZero = false := by
        simpa [y] using gcd_isZero_false_of_right_isZero_false c w ih.2
      have hz_nonzero : z.isZero = false := by
        cases hz : z.isZero
        · rfl
        · have hz_zero : z = 0 := eq_zero_of_isZero_true z hz
          have hprod : z * y = w := by
            simpa [z, y] using div_gcd_right_mul_reconstruct c w
          have hw_zero : w = 0 := by
            rw [← hprod, hz_zero, zero_mul]
          rw [hw_zero] at ih
          cases ih.2
      simpa [y, z] using And.intro hy_nonzero hz_nonzero

private theorem yunContribution_scalarSync_raw_one
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {c w : FpPoly p} {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (base level fuel : Nat) (hc : isOne c = true) :
    ∃ s u_tail : ZMod64 p, s ≠ 0 ∧ u_tail ≠ 0 ∧
      yunFactorsContributionWithLevel
          (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level (fuel + 1) =
        (DensePoly.C s *
            (yunFactorsContributionWithLevel c w base level (fuel + 1)).1,
          DensePoly.C u_tail *
            (yunFactorsContributionWithLevel c w base level (fuel + 1)).2) := by
  have hc_eq : c = 1 := eq_one_of_isOne_true c hc
  obtain ⟨s, t, hs, ht, hscaled₁, hscaled₂⟩ :=
    yunFactorsContributionWithLevel_constant_scalar_sync hp hu_c
      (DensePoly.C u_w * w : FpPoly p) base level (fuel + 1)
  refine ⟨s, t * u_w, hs, ?_, ?_⟩
  · intro hzero
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with ht_zero | huw_zero
    · exact ht ht_zero
    · exact hu_w huw_zero
  · have htail :
        DensePoly.C t * (DensePoly.C u_w * w : FpPoly p) =
          DensePoly.C (t * u_w) * w := by
      calc
        DensePoly.C t * (DensePoly.C u_w * w : FpPoly p) =
            (DensePoly.C t * DensePoly.C u_w : FpPoly p) * w :=
              (DensePoly.mul_assoc_poly _ _ _).symm
        _ = DensePoly.C (t * u_w) * w := by rw [fpPoly_C_mul_C_eq]
    have hscaled₂' :
        (yunFactorsContributionWithLevel
              (DensePoly.C u_c * c) (DensePoly.C u_w * w)
              base level (fuel + 1)).2 =
          DensePoly.C (t * u_w) * w := by
      simpa [hc_eq, htail] using hscaled₂
    have hscaled₁' :
        (yunFactorsContributionWithLevel
              (DensePoly.C u_c * c) (DensePoly.C u_w * w)
              base level (fuel + 1)).1 =
          DensePoly.C s := by
      simpa [hc_eq] using hscaled₁
    apply Prod.ext
    · calc
        (yunFactorsContributionWithLevel
              (DensePoly.C u_c * c) (DensePoly.C u_w * w)
              base level (fuel + 1)).1 =
            DensePoly.C s := hscaled₁'
        _ = DensePoly.C s *
              (yunFactorsContributionWithLevel c w base level (fuel + 1)).1 := by
            simp [yunFactorsContributionWithLevel, hc]
    · calc
        (yunFactorsContributionWithLevel
              (DensePoly.C u_c * c) (DensePoly.C u_w * w)
              base level (fuel + 1)).2 =
            DensePoly.C (t * u_w) * w := hscaled₂'
        _ = DensePoly.C (t * u_w) *
              (yunFactorsContributionWithLevel c w base level (fuel + 1)).2 := by
            simp [yunFactorsContributionWithLevel, hc]

private theorem yunContribution_scalarSync_scaled_one
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {c w : FpPoly p} {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (base level fuel : Nat) (_hc_false : isOne c = false)
    (hscaled_c : isOne (DensePoly.C u_c * c : FpPoly p) = true) :
    ∃ s u_tail : ZMod64 p, s ≠ 0 ∧ u_tail ≠ 0 ∧
      yunFactorsContributionWithLevel
          (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level (fuel + 1) =
        (DensePoly.C s *
            (yunFactorsContributionWithLevel c w base level (fuel + 1)).1,
          DensePoly.C u_tail *
            (yunFactorsContributionWithLevel c w base level (fuel + 1)).2) := by
  have hc_unit : c = DensePoly.C u_c⁻¹ := by
    apply C_mul_eq_one_inv_form hp hu_c
    exact eq_one_of_isOne_true (DensePoly.C u_c * c : FpPoly p) hscaled_c
  have hu_c_inv : u_c⁻¹ ≠ 0 :=
    zmod64_inv_ne_zero_of_prime_ne_zero hp hu_c
  obtain ⟨sRaw, tRaw, hsRaw, htRaw, hraw₁, hraw₂⟩ :=
    yunFactorsContributionWithLevel_constant_scalar_sync hp hu_c_inv
      w base level (fuel + 1)
  refine ⟨sRaw⁻¹, u_w * tRaw⁻¹, ?_, ?_, ?_⟩
  · exact zmod64_inv_ne_zero_of_prime_ne_zero hp hsRaw
  · intro hzero
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with huw_zero | ht_zero
    · exact hu_w huw_zero
    · exact zmod64_inv_ne_zero_of_prime_ne_zero hp htRaw ht_zero
  · have hraw₁' :
        (yunFactorsContributionWithLevel c w base level (fuel + 1)).1 =
          DensePoly.C sRaw := by
      simpa [hc_unit] using hraw₁
    have hraw₂' :
        (yunFactorsContributionWithLevel c w base level (fuel + 1)).2 =
          DensePoly.C tRaw * w := by
      simpa [hc_unit] using hraw₂
    have hs_inv_mul : sRaw⁻¹ * sRaw = (1 : ZMod64 p) := by
      have hcomm : sRaw * sRaw⁻¹ = sRaw⁻¹ * sRaw := by grind
      rw [← hcomm]
      exact zmod64_mul_inv_eq_one_of_prime_ne_zero hp hsRaw
    have hfirst :
        (1 : FpPoly p) =
          DensePoly.C sRaw⁻¹ *
            (yunFactorsContributionWithLevel c w base level (fuel + 1)).1 := by
      rw [hraw₁']
      calc
        (1 : FpPoly p) = DensePoly.C (1 : ZMod64 p) := rfl
        _ = DensePoly.C (sRaw⁻¹ * sRaw) := by rw [hs_inv_mul]
        _ = DensePoly.C sRaw⁻¹ * DensePoly.C sRaw := by
              rw [fpPoly_C_mul_C_eq]
    have htail :
        DensePoly.C u_w * w =
          DensePoly.C (u_w * tRaw⁻¹) *
            (yunFactorsContributionWithLevel c w base level (fuel + 1)).2 := by
      rw [hraw₂']
      exact (C_mul_C_mul_cancel_right hp htRaw w).symm
    apply Prod.ext
    · simpa [yunFactorsContributionWithLevel, hscaled_c] using hfirst
    · simpa [yunFactorsContributionWithLevel, hscaled_c] using htail

private theorem yunFactorsContributionWithLevel_scalar_sync
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (base level fuel : Nat) :
    ∃ s u_tail : ZMod64 p, s ≠ 0 ∧ u_tail ≠ 0 ∧
      yunFactorsContributionWithLevel
          (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel =
        (DensePoly.C s *
            (yunFactorsContributionWithLevel c w base level fuel).1,
          DensePoly.C u_tail *
            (yunFactorsContributionWithLevel c w base level fuel).2) := by
  induction fuel generalizing c w u_c u_w level with
  | zero =>
      refine ⟨1, u_w, zmod64_one_ne_zero_of_prime hp, hu_w, ?_⟩
      change (1, DensePoly.C u_w * w) =
        (DensePoly.C (1 : ZMod64 p) * (1 : FpPoly p), DensePoly.C u_w * w)
      rw [show (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 from rfl]
      simp
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · exact yunContribution_scalarSync_raw_one hp hu_c hu_w
          base level fuel hc
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        by_cases hscaled_c : isOne (DensePoly.C u_c * c : FpPoly p) = true
        · exact yunContribution_scalarSync_scaled_one hp hu_c hu_w
            base level fuel hc_false hscaled_c
        · have hscaled_c_false :
              isOne (DensePoly.C u_c * c : FpPoly p) = false := by
            cases h : isOne (DensePoly.C u_c * c : FpPoly p)
            · rfl
            · exact False.elim (hscaled_c h)
          let y : FpPoly p := DensePoly.gcd c w
          let yScaled : FpPoly p :=
            DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w)
          let z : FpPoly p := c / y
          let zScaled : FpPoly p := (DensePoly.C u_c * c) / yScaled
          by_cases hy_zero : y = 0
          · have hg_zero : DensePoly.gcd c w = 0 := by simpa [y] using hy_zero
            have hc_zero : c = 0 := (gcd_eq_zero_forces_zero c w hg_zero).1
            have hw_zero : w = 0 := (gcd_eq_zero_forces_zero c w hg_zero).2
            have hyScaled_zero : yScaled = 0 := by
              simpa [yScaled] using
                scaled_gcd_eq_zero u_c u_w c w hg_zero
            obtain ⟨sTail, uTail, hsTail, huTail, htail_sync⟩ :=
              ih (c := y) (w := w / y) (u_c := (1 : ZMod64 p))
                (u_w := u_w) (level := level + 1)
                (zmod64_one_ne_zero_of_prime hp) hu_w
            have htail₁ :
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1 =
                  DensePoly.C sTail *
                    (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
              calc
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1 =
                    (yunFactorsContributionWithLevel (DensePoly.C (1 : ZMod64 p) * y)
                      (DensePoly.C u_w * (w / y)) base (level + 1) fuel).1 := by
                      simp [hy_zero, hyScaled_zero, hw_zero, div_zero_eq_zero]
                _ = DensePoly.C sTail *
                      (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                      exact congrArg Prod.fst htail_sync
            have htail₂ :
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2 =
                  DensePoly.C uTail *
                    (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 := by
              calc
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2 =
                    (yunFactorsContributionWithLevel (DensePoly.C (1 : ZMod64 p) * y)
                      (DensePoly.C u_w * (w / y)) base (level + 1) fuel).2 := by
                      simp [hy_zero, hyScaled_zero, hw_zero, div_zero_eq_zero]
                _ = DensePoly.C uTail *
                      (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 := by
                      exact congrArg Prod.snd htail_sync
            have hzScaled_eq :
                zScaled = DensePoly.C u_c * z := by
              simp [z, zScaled, y, yScaled, hc_zero, hy_zero, hyScaled_zero,
                div_zero_eq_zero]
            obtain ⟨s, uTail', hs, huTail', hbranch₁, hbranch₂⟩ :=
              yunFactorsContributionWithLevel_scalar_branch_sync hp
                (z := z) (zScaled := zScaled)
                (tail₁ :=
                  (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1)
                (tail₂ :=
                  (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2)
                (tailScaled₁ :=
                  (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1)
                (tailScaled₂ :=
                  (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2)
                (u_z := u_c) (s_tail := sTail) (u_tail := uTail)
                hu_c hsTail huTail hzScaled_eq htail₁ htail₂ (base * level)
            refine ⟨s, uTail', hs, huTail', ?_⟩
            apply Prod.ext
            · simpa [yunFactorsContributionWithLevel, hc_false, hscaled_c_false,
                y, yScaled, z, zScaled] using hbranch₁
            · simpa [yunFactorsContributionWithLevel, hc_false, hscaled_c_false,
                y, yScaled, z, zScaled] using hbranch₂
          · have hy_ne : y ≠ 0 := hy_zero
            obtain ⟨v, hv, hyScaled_eq, hzScaled_eq, hwScaled_eq⟩ :=
              yunFactorsContributionWithLevel_scalar_step_bridge
                hp c w hu_c hu_w hy_ne
            have hu_c_v : u_c * v⁻¹ ≠ 0 := by
              intro hzero
              rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with huc_zero | hv_zero
              · exact hu_c huc_zero
              · exact zmod64_inv_ne_zero_of_prime_ne_zero hp hv hv_zero
            have hu_w_v : u_w * v⁻¹ ≠ 0 := by
              intro hzero
              rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with huw_zero | hv_zero
              · exact hu_w huw_zero
              · exact zmod64_inv_ne_zero_of_prime_ne_zero hp hv hv_zero
            obtain ⟨sTail, uTail, hsTail, huTail, htail_sync⟩ :=
              ih (c := y) (w := w / y) (u_c := v)
                (u_w := u_w * v⁻¹) (level := level + 1)
                hv hu_w_v
            have hwScaled_eq_y :
                (DensePoly.C u_w * w) / yScaled =
                  DensePoly.C (u_w * v⁻¹) * (w / y) := by
              simpa [y, yScaled] using hwScaled_eq
            have hyScaled_eq_y : yScaled = DensePoly.C v * y := by
              simpa [y, yScaled] using hyScaled_eq
            have hwScaled_eq_v :
                (DensePoly.C u_w * w) / (DensePoly.C v * y) =
                  DensePoly.C (u_w * v⁻¹) * (w / y) := by
              simpa [hyScaled_eq_y] using hwScaled_eq_y
            have htail₁ :
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1 =
                  DensePoly.C sTail *
                    (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
              calc
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1 =
                    (yunFactorsContributionWithLevel (DensePoly.C v * y)
                      (DensePoly.C (u_w * v⁻¹) * (w / y)) base (level + 1) fuel).1 := by
                      rw [hyScaled_eq_y, hwScaled_eq_v]
                _ = DensePoly.C sTail *
                      (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                      exact congrArg Prod.fst htail_sync
            have htail₂ :
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2 =
                  DensePoly.C uTail *
                    (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 := by
              calc
                (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2 =
                    (yunFactorsContributionWithLevel (DensePoly.C v * y)
                      (DensePoly.C (u_w * v⁻¹) * (w / y)) base (level + 1) fuel).2 := by
                      rw [hyScaled_eq_y, hwScaled_eq_v]
                _ = DensePoly.C uTail *
                      (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 := by
                      exact congrArg Prod.snd htail_sync
            obtain ⟨s, uTail', hs, huTail', hbranch₁, hbranch₂⟩ :=
              yunFactorsContributionWithLevel_scalar_branch_sync hp
                (z := z) (zScaled := zScaled)
                (tail₁ :=
                  (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1)
                (tail₂ :=
                  (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2)
                (tailScaled₁ :=
                  (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1)
                (tailScaled₂ :=
                  (yunFactorsContributionWithLevel yScaled
                      ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2)
                (u_z := u_c * v⁻¹) (s_tail := sTail) (u_tail := uTail)
                hu_c_v hsTail huTail
                (by simpa [z, zScaled, y, yScaled] using hzScaled_eq)
                htail₁ htail₂ (base * level)
            refine ⟨s, uTail', hs, huTail', ?_⟩
            apply Prod.ext
            · simpa [yunFactorsContributionWithLevel, hc_false, hscaled_c_false,
                y, yScaled, z, zScaled] using hbranch₁
            · simpa [yunFactorsContributionWithLevel, hc_false, hscaled_c_false,
                y, yScaled, z, zScaled] using hbranch₂

private theorem yunFactorsContributionWithLevel_scalar_sync_of_derivative_active_reachable
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {f c w : FpPoly p} {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (base level fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    ∃ s u_tail : ZMod64 p, s ≠ 0 ∧ u_tail ≠ 0 ∧
      yunFactorsContributionWithLevel
          (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel =
        (DensePoly.C s *
            (yunFactorsContributionWithLevel c w base level fuel).1,
          DensePoly.C u_tail *
            (yunFactorsContributionWithLevel c w base level fuel).2) := by
  induction fuel generalizing c w u_c u_w level with
  | zero =>
      refine ⟨1, u_w, zmod64_one_ne_zero_of_prime hp, hu_w, ?_⟩
      change (1, DensePoly.C u_w * w) =
        (DensePoly.C (1 : ZMod64 p) * (1 : FpPoly p), DensePoly.C u_w * w)
      rw [show (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 from rfl]
      simp
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · exact yunContribution_scalarSync_raw_one hp hu_c hu_w
          base level fuel hc
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        by_cases hscaled_c : isOne (DensePoly.C u_c * c : FpPoly p) = true
        · exact yunContribution_scalarSync_scaled_one hp hu_c hu_w
            base level fuel hc_false hscaled_c
        · have hscaled_c_false :
              isOne (DensePoly.C u_c * c : FpPoly p) = false := by
            cases h : isOne (DensePoly.C u_c * c : FpPoly p)
            · rfl
            · exact False.elim (hscaled_c h)
          let y : FpPoly p := DensePoly.gcd c w
          let yScaled : FpPoly p :=
            DensePoly.gcd (DensePoly.C u_c * c) (DensePoly.C u_w * w)
          let z : FpPoly p := c / y
          let zScaled : FpPoly p := (DensePoly.C u_c * c) / yScaled
          have hcurrent :=
            yunFactorsDerivativeActiveReachable_nonzero hp f c w (fuel + 1)
              hreachable
          have hy_ne : y ≠ 0 := by
            have hy_zero : y.isZero = false :=
              yunStep_gcd_nonzero_of_left_nonzero c w hcurrent.1
            intro hy_eq
            rw [hy_eq] at hy_zero
            cases hy_zero
          obtain ⟨v, hv, hyScaled_eq, hzScaled_eq, hwScaled_eq⟩ :=
            yunFactorsContributionWithLevel_scalar_step_bridge
              hp c w hu_c hu_w hy_ne
          have hu_c_v : u_c * v⁻¹ ≠ 0 := by
            intro hzero
            rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with huc_zero | hv_zero
            · exact hu_c huc_zero
            · exact zmod64_inv_ne_zero_of_prime_ne_zero hp hv hv_zero
          have hu_w_v : u_w * v⁻¹ ≠ 0 := by
            intro hzero
            rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with huw_zero | hv_zero
            · exact hu_w huw_zero
            · exact zmod64_inv_ne_zero_of_prime_ne_zero hp hv hv_zero
          have htail_reachable :
              yunFactorsDerivativeActiveReachable hp f y (w / y) fuel := by
            simpa [y] using
              yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
          obtain ⟨sTail, uTail, hsTail, huTail, htail_sync⟩ :=
            ih (c := y) (w := w / y) (u_c := v)
              (u_w := u_w * v⁻¹) (level := level + 1)
              hv hu_w_v htail_reachable
          have hwScaled_eq_y :
              (DensePoly.C u_w * w) / yScaled =
                DensePoly.C (u_w * v⁻¹) * (w / y) := by
            simpa [y, yScaled] using hwScaled_eq
          have hyScaled_eq_y : yScaled = DensePoly.C v * y := by
            simpa [y, yScaled] using hyScaled_eq
          have hwScaled_eq_v :
              (DensePoly.C u_w * w) / (DensePoly.C v * y) =
                DensePoly.C (u_w * v⁻¹) * (w / y) := by
            simpa [hyScaled_eq_y] using hwScaled_eq_y
          have htail₁ :
              (yunFactorsContributionWithLevel yScaled
                    ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1 =
                DensePoly.C sTail *
                  (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
            calc
              (yunFactorsContributionWithLevel yScaled
                    ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1 =
                  (yunFactorsContributionWithLevel (DensePoly.C v * y)
                    (DensePoly.C (u_w * v⁻¹) * (w / y)) base (level + 1) fuel).1 := by
                    rw [hyScaled_eq_y, hwScaled_eq_v]
              _ = DensePoly.C sTail *
                    (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                    exact congrArg Prod.fst htail_sync
          have htail₂ :
              (yunFactorsContributionWithLevel yScaled
                    ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2 =
                DensePoly.C uTail *
                  (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 := by
            calc
              (yunFactorsContributionWithLevel yScaled
                    ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2 =
                  (yunFactorsContributionWithLevel (DensePoly.C v * y)
                    (DensePoly.C (u_w * v⁻¹) * (w / y)) base (level + 1) fuel).2 := by
                    rw [hyScaled_eq_y, hwScaled_eq_v]
              _ = DensePoly.C uTail *
                    (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2 := by
                    exact congrArg Prod.snd htail_sync
          obtain ⟨s, uTail', hs, huTail', hbranch₁, hbranch₂⟩ :=
            yunFactorsContributionWithLevel_scalar_branch_sync hp
              (z := z) (zScaled := zScaled)
              (tail₁ :=
                (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1)
              (tail₂ :=
                (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).2)
              (tailScaled₁ :=
                (yunFactorsContributionWithLevel yScaled
                    ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).1)
              (tailScaled₂ :=
                (yunFactorsContributionWithLevel yScaled
                    ((DensePoly.C u_w * w) / yScaled) base (level + 1) fuel).2)
              (u_z := u_c * v⁻¹) (s_tail := sTail) (u_tail := uTail)
              hu_c_v hsTail huTail
              (by simpa [z, zScaled, y, yScaled] using hzScaled_eq)
              htail₁ htail₂ (base * level)
          refine ⟨s, uTail', hs, huTail', ?_⟩
          apply Prod.ext
          · simpa [yunFactorsContributionWithLevel, hc_false, hscaled_c_false,
              y, yScaled, z, zScaled] using hbranch₁
          · simpa [yunFactorsContributionWithLevel, hc_false, hscaled_c_false,
              y, yScaled, z, zScaled] using hbranch₂

private theorem yunFactorsContributionWithLevel_scaled_normalized_tail_reconstruct
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {f c w : FpPoly p} {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (base level fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    ∃ u_tail : ZMod64 p, u_tail ≠ 0 ∧
      let raw := yunFactorsContributionWithLevel c w base level fuel
      let scaled :=
        yunFactorsContributionWithLevel
          (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel
      DensePoly.C (normalizeMonic scaled.2).1 *
          (normalizeMonic scaled.2).2 =
        DensePoly.C u_tail * raw.2 := by
  obtain ⟨_s, u_tail, _hs, hu_tail, hsync⟩ :=
    yunFactorsContributionWithLevel_scalar_sync_of_derivative_active_reachable
      hp hu_c hu_w base level fuel hreachable
  refine ⟨u_tail, hu_tail, ?_⟩
  let raw := yunFactorsContributionWithLevel c w base level fuel
  let scaled :=
    yunFactorsContributionWithLevel
      (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel
  have hscaled_tail : scaled.2 = DensePoly.C u_tail * raw.2 := by
    exact congrArg Prod.snd hsync
  have hreconstruct :
      DensePoly.C (normalizeMonic scaled.2).1 * (normalizeMonic scaled.2).2 =
        scaled.2 := by
    simpa [scaled] using
      yunFactorsContributionWithLevel_normalized_tail_reconstruct
        hp (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel
  dsimp only
  exact hreconstruct.trans hscaled_tail

private theorem yunFactorsContributionWithLevel_scaled_normalized_tail_product_sync
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {f c w : FpPoly p} {u_c u_w : ZMod64 p}
    (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0)
    (base level fuel multiplicity : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (hproduct :
      let raw := yunFactorsContributionWithLevel c w base level fuel
      raw.1 * pow raw.2 multiplicity = pow f multiplicity) :
    ∃ s : ZMod64 p, s ≠ 0 ∧
      let scaled :=
        yunFactorsContributionWithLevel
          (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel
      scaled.1 *
          (pow (DensePoly.C (normalizeMonic scaled.2).1) multiplicity *
            pow (normalizeMonic scaled.2).2 multiplicity) =
        DensePoly.C s * pow f multiplicity := by
  obtain ⟨s, u_tail, hs, hu_tail, hsync⟩ :=
    yunFactorsContributionWithLevel_scalar_sync_of_derivative_active_reachable
      hp hu_c hu_w base level fuel hreachable
  let raw := yunFactorsContributionWithLevel c w base level fuel
  let scaled :=
    yunFactorsContributionWithLevel
      (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel
  have hscaled₁ : scaled.1 = DensePoly.C s * raw.1 := by
    exact congrArg Prod.fst hsync
  have hscaled₂ : scaled.2 = DensePoly.C u_tail * raw.2 := by
    exact congrArg Prod.snd hsync
  obtain ⟨u_pow, hu_pow, hpow_tail⟩ :=
    pow_C_mul_sync hp hu_tail raw.2 multiplicity
  refine ⟨s * u_pow, ?_, ?_⟩
  · intro hzero
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hs_zero | hupow_zero
    · exact hs hs_zero
    · exact hu_pow hupow_zero
  · have hraw_product :
        raw.1 * pow raw.2 multiplicity = pow f multiplicity := by
      simpa [raw] using hproduct
    have hreconstruct :
        DensePoly.C (normalizeMonic scaled.2).1 * (normalizeMonic scaled.2).2 =
          scaled.2 := by
      simpa [scaled] using
        yunFactorsContributionWithLevel_normalized_tail_reconstruct
          hp (DensePoly.C u_c * c) (DensePoly.C u_w * w) base level fuel
    calc
      scaled.1 *
          (pow (DensePoly.C (normalizeMonic scaled.2).1) multiplicity *
            pow (normalizeMonic scaled.2).2 multiplicity) =
          scaled.1 *
            pow (DensePoly.C (normalizeMonic scaled.2).1 *
              (normalizeMonic scaled.2).2) multiplicity := by
            rw [pow_mul_base]
      _ = scaled.1 * pow scaled.2 multiplicity := by
            rw [hreconstruct]
      _ = (DensePoly.C s * raw.1) *
            pow (DensePoly.C u_tail * raw.2 : FpPoly p) multiplicity := by
            rw [hscaled₁, hscaled₂]
      _ = (DensePoly.C s * raw.1) *
            (DensePoly.C u_pow * pow raw.2 multiplicity) := by
            rw [hpow_tail]
      _ = DensePoly.C (s * u_pow) *
            (raw.1 * pow raw.2 multiplicity) := by
            calc
              (DensePoly.C s * raw.1) *
                  (DensePoly.C u_pow * pow raw.2 multiplicity) =
                  DensePoly.C s *
                    (raw.1 * (DensePoly.C u_pow * pow raw.2 multiplicity)) :=
                    DensePoly.mul_assoc_poly _ _ _
              _ = DensePoly.C s *
                    ((DensePoly.C u_pow * pow raw.2 multiplicity) * raw.1) := by
                    exact congrArg (fun t => DensePoly.C s * t)
                      (DensePoly.mul_comm_poly raw.1
                        (DensePoly.C u_pow * pow raw.2 multiplicity))
              _ = DensePoly.C s *
                    (DensePoly.C u_pow *
                      (pow raw.2 multiplicity * raw.1)) := by
                    exact congrArg (fun t => DensePoly.C s * t)
                      (DensePoly.mul_assoc_poly
                        (DensePoly.C u_pow : FpPoly p)
                        (pow raw.2 multiplicity) raw.1)
              _ = DensePoly.C s *
                    (DensePoly.C u_pow *
                      (raw.1 * pow raw.2 multiplicity)) := by
                    exact congrArg
                      (fun t => DensePoly.C s * (DensePoly.C u_pow * t))
                      (DensePoly.mul_comm_poly (pow raw.2 multiplicity) raw.1)
              _ = (DensePoly.C s * DensePoly.C u_pow : FpPoly p) *
                    (raw.1 * pow raw.2 multiplicity) := by
                    exact (DensePoly.mul_assoc_poly
                      (DensePoly.C s : FpPoly p) (DensePoly.C u_pow)
                      (raw.1 * pow raw.2 multiplicity)).symm
              _ = DensePoly.C (s * u_pow) *
                    (raw.1 * pow raw.2 multiplicity) := by
                    rw [fpPoly_C_mul_C_eq]
      _ = DensePoly.C (s * u_pow) * pow f multiplicity := by
            rw [hraw_product]

private theorem yunFactorsContributionWithLevel_tail_nonzero_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    (yunFactorsContributionWithLevel c w base level fuel).2.isZero = false := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent :=
        yunFactorsDerivativeActiveReachable_nonzero hp f c w 0 hreachable
      simpa [yunFactorsContributionWithLevel] using hcurrent.2
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hcurrent :=
          yunFactorsDerivativeActiveReachable_nonzero hp f c w (fuel + 1) hreachable
        simpa [yunFactorsContributionWithLevel, hc] using hcurrent.2
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (DensePoly.gcd c w)
              (w / DensePoly.gcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        simpa [yunFactorsContributionWithLevel, hc_false] using
          ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
            htail_reachable

private theorem yunFactorsContributionWithLevel_normalized_tail_valid_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    squareFreeContributionReachable (normalizeMonic contribution.2).2 ∧
      (normalizeMonic contribution.2).2.isZero = false := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate f c w 0 hreachable
      simpa [yunFactorsContributionWithLevel] using
        And.intro hcurrent.2.2.1 hcurrent.2.2.2
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hcurrent := hstate f c w (fuel + 1) hreachable
        simpa [yunFactorsContributionWithLevel, hc] using
          And.intro hcurrent.2.2.1 hcurrent.2.2.2
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (DensePoly.gcd c w)
              (w / DensePoly.gcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        simpa [yunFactorsContributionWithLevel, hc_false] using
          ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
            htail_reachable

private theorem yunFactorsContributionWithLevel_normalized_pthRoot_tail_valid
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel :
      (yunFactorsContributionWithLevel c w base level fuel).2.size < fuel + 1)
    (htail_nontrivial :
      isOne (normalizeMonic
        (yunFactorsContributionWithLevel c w base level fuel).2).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative
        (yunFactorsContributionWithLevel c w base level fuel).2).isZero = true) :
    squareFreeContributionReachable
        (pthRoot (normalizeMonic
          (yunFactorsContributionWithLevel c w base level fuel).2).2) ∧
      (pthRoot (normalizeMonic
        (yunFactorsContributionWithLevel c w base level fuel).2).2).isZero = false ∧
        (pthRoot (normalizeMonic
          (yunFactorsContributionWithLevel c w base level fuel).2).2).size < fuel := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  have htail_valid :=
    yunFactorsContributionWithLevel_normalized_tail_valid_of_derivative_active_reachable
      hp f c w base level fuel hstate hreachable
  have htail_raw_nonzero : contribution.2.isZero = false := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_tail_nonzero_of_derivative_active_reachable
        hp f c w base level fuel hreachable
  have hnorm_derivative_zero :
      (DensePoly.derivative (normalizeMonic contribution.2).2).isZero = true :=
    normalizeMonic_derivative_zero_of_derivative_zero
      contribution.2 htail_raw_nonzero (by
        simpa [contribution] using htail_derivative_zero)
  have hnorm_fuel : (normalizeMonic contribution.2).2.size < fuel + 1 := by
    have hsize :=
      normalizeMonic_nonzero_size_eq hp contribution.2 htail_raw_nonzero
    rw [hsize]
    simpa [contribution] using htail_fuel
  exact
    pthRoot_valid_of_derivative_zero_nontrivial hp
      (normalizeMonic contribution.2).2 hnorm_fuel htail_valid.2
      (by simpa [contribution] using htail_nontrivial)
      hnorm_derivative_zero htail_valid.1

private theorem yunFactorsWithLevel_normalized_pthRoot_tail_fuel_bound
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel : (yunFactorsWithLevel c w base level fuel []).2.size < fuel + 1)
    (htail_nontrivial :
      isOne (normalizeMonic (yunFactorsWithLevel c w base level fuel []).2).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative (yunFactorsWithLevel c w base level fuel []).2).isZero = true) :
    (pthRoot (normalizeMonic (yunFactorsWithLevel c w base level fuel []).2).2).size <
      fuel := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  let loop := yunFactorsWithLevel c w base level fuel []
  have hloop_eq : loop.2 = contribution.2 := by
    have hrec := yunFactorsWithLevel_reconstruction_invariant c w base level fuel []
    simpa [loop, contribution] using hrec.1
  have hvalid :=
    yunFactorsContributionWithLevel_normalized_pthRoot_tail_valid
      hp f c w base level fuel hstate hreachable
      (by simpa [loop, contribution, hloop_eq] using htail_fuel)
      (by simpa [loop, contribution, hloop_eq] using htail_nontrivial)
      (by simpa [loop, contribution, hloop_eq] using htail_derivative_zero)
  simpa [loop, contribution, hloop_eq] using hvalid.2.2

private theorem yunFactorsDerivativeActiveReachable_normalized_stateProvider
    (hp : Hex.Nat.Prime p) :
    YunDerivativeActiveNormalizedStateProvider hp := by
  intro f' c w fuel hreachable
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hnonzero := yunFactorsDerivativeActiveReachable_nonzero hp f' c w fuel hreachable
  have hc := normalizeMonic_squareFreeContributionPayload hp c hnonzero.1
  have hw := normalizeMonic_squareFreeContributionPayload hp w hnonzero.2
  exact ⟨hc.1, hc.2, hw.1, hw.2⟩

private theorem yunFactorsNormalizedLevelCompletes_of_size_bound_derivative_active
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (f c w : FpPoly p)
    (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (hbound : (normalizeMonic c).2.size + (normalizeMonic w).2.size ≤ fuel + 1) :
    yunFactorsNormalizedLevelCompletes c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate f c w 0 hreachable
      have hc_pos : 0 < (normalizeMonic c).2.size :=
        size_pos_of_isZero_false (normalizeMonic c).2 hcurrent.2.1
      have hw_pos : 0 < (normalizeMonic w).2.size :=
        size_pos_of_isZero_false (normalizeMonic w).2 hcurrent.2.2.2
      exfalso
      omega
  | succ fuel ih =>
      by_cases hc_norm : isOne (normalizeMonic c).2 = true
      · exact Or.inl hc_norm
      · have hc_norm_false : isOne (normalizeMonic c).2 = false := by
          cases h : isOne (normalizeMonic c).2
          · rfl
          · exact False.elim (hc_norm h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (DensePoly.gcd c w)
              (w / DensePoly.gcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        have hpairwise :
            yunFactorsPairwiseReachable c w (fuel + 1) :=
          yunFactorsPairwiseReachable_of_derivative_active_reachable
            hp f c w (fuel + 1) hreachable
        have hcurrent := hstate f c w (fuel + 1) hreachable
        have hraw_nonzero :=
          yunFactorsDerivativeActiveReachable_nonzero hp f c w (fuel + 1) hreachable
        have hnorm_c_size : 1 < (normalizeMonic c).2.size :=
          one_lt_size_of_isOne_false_of_reachable
            (normalizeMonic c).2 hcurrent.2.1 hc_norm_false hcurrent.1
        have hc_size : 1 < c.size := by
          have hsize := normalizeMonic_nonzero_size_eq hp c hraw_nonzero.1
          omega
        have hmeasure :
            (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
              c.size + w.size :=
          yunLevel_measure_lt_of_nonconstant_step
            c w fuel hc_size hraw_nonzero.1 hraw_nonzero.2 hpairwise
        have htail_nonzero :=
          yunFactorsDerivativeActiveReachable_nonzero hp f
            (DensePoly.gcd c w) (w / DensePoly.gcd c w) fuel htail_reachable
        have hcurrent_c_size :
            (normalizeMonic c).2.size = c.size :=
          normalizeMonic_nonzero_size_eq hp c hraw_nonzero.1
        have hcurrent_w_size :
            (normalizeMonic w).2.size = w.size :=
          normalizeMonic_nonzero_size_eq hp w hraw_nonzero.2
        have htail_g_size :
            (normalizeMonic (DensePoly.gcd c w)).2.size =
              (DensePoly.gcd c w).size :=
          normalizeMonic_nonzero_size_eq hp (DensePoly.gcd c w) htail_nonzero.1
        have htail_w_size :
            (normalizeMonic (w / DensePoly.gcd c w)).2.size =
              (w / DensePoly.gcd c w).size :=
          normalizeMonic_nonzero_size_eq hp
            (w / DensePoly.gcd c w) htail_nonzero.2
        have htail_bound :
            (normalizeMonic (DensePoly.gcd c w)).2.size +
                (normalizeMonic (w / DensePoly.gcd c w)).2.size ≤ fuel + 1 := by
          omega
        exact Or.inr
          (ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
            htail_reachable htail_bound)

private theorem yunFactorsLevelCompletes_of_size_bound_derivative_active
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (f c w : FpPoly p)
    (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (hbound : c.size + w.size ≤ fuel + 1) :
    yunFactorsLevelCompletes c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate c w 0 hreachable
      have hc_pos : 0 < c.size :=
        size_pos_of_isZero_false c hcurrent.2.1
      have hw_pos : 0 < w.size :=
        size_pos_of_isZero_false w hcurrent.2.2
      exfalso
      omega
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · exact Or.inl hc
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (DensePoly.gcd c w)
              (w / DensePoly.gcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        have hpairwise :
            yunFactorsPairwiseReachable c w (fuel + 1) :=
          yunFactorsPairwiseReachable_of_derivative_active_reachable
            hp f c w (fuel + 1) hreachable
        have hmeasure :
            (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size <
              c.size + w.size :=
          yunLevel_measure_lt_of_reachable_step
            c w fuel (hstate c w (fuel + 1) hreachable) hpairwise hc_false
        have htail_bound :
            (DensePoly.gcd c w).size + (w / DensePoly.gcd c w).size ≤
              fuel + 1 := by
          omega
        exact Or.inr
          (ih (DensePoly.gcd c w) (w / DensePoly.gcd c w) (level + 1)
            htail_reachable htail_bound)

private theorem yunFactorsLevelCompletes_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsLevelCompletes c g multiplicity 1 fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  cases fuel with
  | zero =>
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      have hreachable :
          yunFactorsDerivativeActiveReachable hp f c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsDerivativeActiveReachable_of_derivative_split hp f (fuel + 1) hdf_ne_true
      have hbound : c.size + g.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize :
            c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (DensePoly.gcd_dvd_left f (DensePoly.derivative f)) hf_ne
        omega
      simpa [c, g] using
        yunFactorsLevelCompletes_of_size_bound_derivative_active
          hp f c g multiplicity 1 (fuel + 1) hstate hreachable hbound

/-- Initial-split completion wrapper for the derivative-active branch.

The state payload is restricted to states reachable from the normalized
derivative-active call path: the initial split `g = gcd f f'`, `c = f / g`,
followed by Yun tail steps. Callers do not need, and this theorem does not
assume, a universal provider for arbitrary raw Yun states. -/
private theorem yunFactorsLevelCompletes_of_derivative_active_initial_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsLevelCompletes c g multiplicity 1 fuel := by
  exact
    yunFactorsLevelCompletes_of_derivative_active_reachable
      hp f multiplicity fuel hmultiplicity hfuel hzero hdf hstate

/-- Initial-split completion wrapper for the normalized derivative-active branch.

This is the scalar-aware analogue of
`yunFactorsLevelCompletes_of_derivative_active_initial_split`: it consumes the
normalized state provider and proves the normalized completion predicate, so raw
nonzero scalar-unit states do not need to satisfy `isOne c = true`. -/
private theorem yunFactorsNormalizedLevelCompletes_of_derivative_active_initial_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsNormalizedLevelCompletes c g multiplicity 1 fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  cases fuel with
  | zero =>
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      have hreachable :
          yunFactorsDerivativeActiveReachable hp f c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsDerivativeActiveReachable_of_derivative_split hp f (fuel + 1) hdf_ne_true
      have hnonzero :=
        yunFactorsDerivativeActiveReachable_nonzero hp f c g (fuel + 1) hreachable
      have hbound :
          (normalizeMonic c).2.size + (normalizeMonic g).2.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize :
            c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (DensePoly.gcd_dvd_left f (DensePoly.derivative f)) hf_ne
        have hc_size : (normalizeMonic c).2.size = c.size :=
          normalizeMonic_nonzero_size_eq hp c hnonzero.1
        have hg_size : (normalizeMonic g).2.size = g.size :=
          normalizeMonic_nonzero_size_eq hp g hnonzero.2
        omega
      simpa [c, g] using
        yunFactorsNormalizedLevelCompletes_of_size_bound_derivative_active
          hp f c g multiplicity 1 (fuel + 1) hstate hreachable hbound

/--
Scalar-aware derivative-active product invariant for the scaled Yun contribution
loop. The first conjunct is the raw contribution identity needed by existing
callers; the second conjunct is the normalized-tail form needed by the provider
refactor, with the residual scalar retained explicitly as
`DensePoly.C (normalizeMonic contribution.2).1`.
-/
private theorem yunFactorsContributionWithLevel_normalized_pow_invariant
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hlevelState : YunDerivativeActiveLevelStateProvider hp)
    (hnormalizedState : YunDerivativeActiveNormalizedStateProvider hp) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
    contribution.1 * pow contribution.2 multiplicity = pow f multiplicity ∧
      contribution.1 *
          (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
            pow (normalizeMonic contribution.2).2 multiplicity) =
        pow f multiplicity := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
  have hstate_level :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false := by
    intro c w fuel hreach
    exact hlevelState f c w fuel hreach
  have hnormalized_completes :
      yunFactorsNormalizedLevelCompletes c g multiplicity 1 fuel := by
    simpa [c, g] using
      yunFactorsNormalizedLevelCompletes_of_derivative_active_initial_split
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hnormalizedState
  have hcompletes :
      yunFactorsLevelCompletes c g multiplicity 1 fuel := by
    simpa [c, g] using
      yunFactorsLevelCompletes_of_derivative_active_initial_split
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hstate_level
  have hpow_raw :
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity := by
    have hpow :=
      yunFactorsContributionWithLevel_pow_invariant_of_completes
        c g multiplicity 1 fuel hcompletes
    have hcg : c * g = f := by
      simpa [c, g] using div_gcd_mul_reconstruct f (DensePoly.derivative f)
    calc
      contribution.1 * pow contribution.2 multiplicity =
          pow c (multiplicity * 1) * pow g multiplicity := by
            simpa [contribution, Nat.mul_one] using hpow
      _ = pow c multiplicity * pow g multiplicity := by rw [Nat.mul_one]
      _ = pow (c * g) multiplicity := by
            exact (pow_mul_base c g multiplicity).symm
      _ = pow f multiplicity := by rw [hcg]
  have hpow_normalized :
      contribution.1 *
          (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
            pow (normalizeMonic contribution.2).2 multiplicity) =
        pow f multiplicity := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_normalized_tail_product_bridge
        hp f c g multiplicity 1 fuel multiplicity (by
          simpa [contribution] using hpow_raw)
  exact ⟨hpow_raw, hpow_normalized⟩

/--
Combined provider for `yunFactorsContributionResidualComplete` driven by a
`yunFactorsLevelCompletes` termination witness and a pairwise reachability
chain. Walks the recursion through the `LevelCompletes` predicate; at each
state where `isOne c = true` the residual derivative-zero fact comes from
`yunFactorsPairwiseReachable_terminal_residual_derivative_zero`.
-/
private theorem yunFactorsContributionResidualComplete_of_pairwise_reachable_levelCompletes
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hcompletes : yunFactorsLevelCompletes c w base level fuel) :
    yunFactorsContributionResidualComplete c w multiplicity fuel := by
  induction fuel generalizing c w multiplicity level with
  | zero =>
      intro _hone
      have hc : isOne c = true := by
        simpa [yunFactorsLevelCompletes] using hcompletes
      exact
        yunFactorsPairwiseReachable_terminal_residual_derivative_zero
          c w 0 hreachable hc
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · simpa [yunFactorsContributionResidualComplete, hc] using
          (fun _hone : isOne w = false =>
            yunFactorsPairwiseReachable_terminal_residual_derivative_zero
              c w (fuel + 1) hreachable hc)
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        let y := DensePoly.gcd c w
        have htail_reachable :
            yunFactorsPairwiseReachable y (w / y) fuel := by
          simpa [y] using yunFactorsPairwiseReachable_step c w fuel hreachable
        have htail_completes :
            yunFactorsLevelCompletes y (w / y) base (level + 1) fuel := by
          have hcompletes_unfold :
              isOne c = true ∨
                yunFactorsLevelCompletes y (w / y) base (level + 1) fuel := by
            simpa [y, yunFactorsLevelCompletes] using hcompletes
          rcases hcompletes_unfold with hone | htail
          · exact False.elim (hc hone)
          · exact htail
        have htail :
            yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel :=
          ih y (w / y) (multiplicity + 1) (level + 1) htail_reachable htail_completes
        simpa [yunFactorsContributionResidualComplete, hc_false, y] using htail

/--
Unscaled derivative-active provider for the contribution residual derivative-zero
fact. Discharges the `yunFactorsContributionResidualDerivativeZero` hypothesis
on `(c, g) = (f / gcd f f', gcd f f')` purely from the size bound, the
nonzero/derivative-active hypotheses on `f`, and a derivative-active state
provider, by combining `yunFactorsLevelCompletes_of_size_bound_derivative_active`
with the pairwise-reachable terminal residual derivative-zero lemma.
-/
private theorem yunFactorsContributionResidualDerivativeZero_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsContributionResidualDerivativeZero c g multiplicity fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
    intro htrue
    rw [htrue] at hdf
    cases hdf
  have hreachable : yunFactorsPairwiseReachable c g fuel := by
    simpa [c, g] using
      yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf_ne_true
  cases fuel with
  | zero =>
      exfalso
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hda_reachable :
          yunFactorsDerivativeActiveReachable hp f c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsDerivativeActiveReachable_of_derivative_split
            hp f (fuel + 1) hdf_ne_true
      have hbound : c.size + g.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize_eq : c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (DensePoly.gcd_dvd_left f (DensePoly.derivative f)) hf_ne
        omega
      have hcompletes :
          yunFactorsLevelCompletes c g multiplicity 1 (fuel + 1) :=
        yunFactorsLevelCompletes_of_size_bound_derivative_active
          hp f c g multiplicity 1 (fuel + 1) hstate hda_reachable hbound
      have hresidual_complete :
          yunFactorsContributionResidualComplete c g multiplicity (fuel + 1) :=
        yunFactorsContributionResidualComplete_of_pairwise_reachable_levelCompletes
          c g multiplicity multiplicity 1 (fuel + 1) hreachable hcompletes
      exact
        yunFactorsContributionResidualDerivativeZero_of_complete
          c g multiplicity (fuel + 1) hresidual_complete

/--
Chained loop residual corollary: the unscaled `yunFactors` loop residual at
`(c, g) = (f / gcd f f', gcd f f')` has zero derivative when not trivial,
proved by composing the contribution-level provider with
`yunFactorsResidualDerivativeZero_of_derivative_split_contribution`.
-/
private theorem yunFactorsResidualDerivativeZero_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    yunFactorsResidualDerivativeZero
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      multiplicity
      fuel := by
  apply yunFactorsResidualDerivativeZero_of_derivative_split_contribution
    hp f multiplicity fuel hdf
  exact
    yunFactorsContributionResidualDerivativeZero_of_derivative_split
      hp f multiplicity fuel hfuel hzero hdf hstate

/--
Scaled-loop residual derivative-zero invariant for the derivative-active
branch. Composes the unscaled witness
`yunFactorsContributionResidualDerivativeZero_of_derivative_split` with the
equality `yunFactorsContributionWithLevel_residual_derivative_zero_of_unscaled`:
the residual `.2` of `yunFactorsContributionWithLevel` agrees with that of
`yunFactorsContribution`, so derivative-zero transports directly.
-/
private theorem yunFactorsContributionWithLevel_residual_derivative_zero_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    isOne
        (yunFactorsContributionWithLevel
          (f / DensePoly.gcd f (DensePoly.derivative f))
          (DensePoly.gcd f (DensePoly.derivative f))
          base level fuel).2 = false →
      (DensePoly.derivative
          (yunFactorsContributionWithLevel
            (f / DensePoly.gcd f (DensePoly.derivative f))
            (DensePoly.gcd f (DensePoly.derivative f))
            base level fuel).2).isZero = true := by
  apply yunFactorsContributionWithLevel_residual_derivative_zero_of_unscaled
  exact
    yunFactorsContributionResidualDerivativeZero_of_derivative_split
      hp f level fuel hfuel hzero hdf hstate

private theorem squareFreeAuxRevResidualSatisfied_of_invariant
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) (multiplicity fuel : Nat) :
    squareFreeAuxRevResidualSatisfied f multiplicity fuel := by
  induction fuel generalizing f multiplicity with
  | zero =>
      simp only [squareFreeAuxRevResidualSatisfied]
  | succ fuel ih =>
      by_cases hzero : f.isZero = true
      · simp only [squareFreeAuxRevResidualSatisfied]
        rw [if_pos hzero]
        exact trivial
      · have hzero_false : f.isZero = false := by
          cases h : f.isZero
          · rfl
          · exact False.elim (hzero h)
        by_cases hdf : (DensePoly.derivative f).isZero = true
        · simp only [squareFreeAuxRevResidualSatisfied]
          rw [if_neg (by simp [hzero_false]), if_pos hdf]
          exact ih (pthRoot f) (multiplicity * p)
        · have hdf_false : (DensePoly.derivative f).isZero = false := by
            cases h : (DensePoly.derivative f).isZero
            · rfl
            · exact False.elim (hdf h)
          exact residualInvariant f multiplicity (fuel + 1) hdf_false

/--
Remaining assembly obligation for the derivative-active branch: the level-form
Yun invariant identifies the local contribution and residual product, while
the recursive IH closes the nontrivial repeated tail.
-/
private theorem squareFreeAuxRevContribution_derivative_active_pow_obligation
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (_hreachable : squareFreeContributionReachable f)
    (_hresidual : squareFreeAuxRevResidualSatisfied f multiplicity (fuel + 1))
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hrawState : YunDerivativeActiveRawStateProvider hp)
    (ih :
      ∀ (f : FpPoly p) (multiplicity : Nat),
        0 < multiplicity →
          f.size < fuel →
            f.isZero = false →
              squareFreeContributionReachable f →
                squareFreeAuxRevResidualSatisfied f multiplicity fuel →
                  squareFreeAuxRevContribution f multiplicity fuel =
                    pow f multiplicity) :
    squareFreeAuxRevContribution f multiplicity (fuel + 1) = pow f multiplicity := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := DensePoly.gcd f (DensePoly.derivative f)
  let c := f / g
  let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
  have hlevelState : YunDerivativeActiveLevelStateProvider hp :=
    YunDerivativeActiveRawStateProvider.levelState hp hrawState
  have hrawTail : YunDerivativeActiveRawTailProvider hp :=
    YunDerivativeActiveRawStateProvider.rawTail hp hrawState
  have hpow_pair :
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity ∧
        contribution.1 *
            (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
              pow (normalizeMonic contribution.2).2 multiplicity) =
          pow f multiplicity := by
    simpa [c, g, contribution] using
      yunFactorsContributionWithLevel_normalized_pow_invariant
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hlevelState
        (yunFactorsDerivativeActiveReachable_normalized_stateProvider hp)
  have hpow_contribution :
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity :=
    hpow_pair.1
  have hresidual_unpacked :
      let loop := yunFactorsWithLevel c g multiplicity 1 fuel []
      ((isOne loop.2 = true) ∨ (DensePoly.derivative loop.2).isZero = true) ∧
        ((isOne loop.2 = false) →
          squareFreeAuxRevResidualSatisfied
            (pthRoot loop.2) (multiplicity * p) fuel) := by
    have h := _hresidual
    simp only [squareFreeAuxRevResidualSatisfied] at h
    rw [if_neg (by simp [hzero]), if_neg (by simp [hdf])] at h
    simpa [c, g, Nat.mul_one] using h
  have hloop_eq :
      (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = contribution.2 := by
    have hrec :=
      yunFactorsWithLevel_reconstruction_invariant c g multiplicity 1 fuel []
    simpa [contribution] using hrec.1
  simp only [squareFreeAuxRevContribution]
  rw [if_neg (by simp [hzero]), if_neg (by simp [hdf])]
  by_cases hone : isOne contribution.2 = true
  · have hcontribution_eq_one : contribution.2 = 1 :=
      eq_one_of_isOne_true contribution.2 hone
    rw [hcontribution_eq_one, isOne_one]
    simp [c, g, contribution, hcontribution_eq_one, pow_one_base] at hpow_contribution ⊢
    exact hpow_contribution
  · have hone_false : isOne contribution.2 = false := by
      cases h : isOne contribution.2
      · rfl
      · exact False.elim (hone h)
    rw [hone_false]
    have hloop_one_false :
        isOne (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = false := by
      rw [hloop_eq]
      exact hone_false
    have htail_residual :
        squareFreeAuxRevResidualSatisfied
          (pthRoot contribution.2) (multiplicity * p) fuel := by
      have h := hresidual_unpacked.2 hloop_one_false
      simpa [hloop_eq] using h
    have htail_derivative :
        (DensePoly.derivative contribution.2).isZero = true := by
      rcases hresidual_unpacked.1 with hloop_one | hloop_derivative
      · rw [hloop_eq] at hloop_one
        rw [hloop_one] at hone_false
        cases hone_false
      · simpa [hloop_eq] using hloop_derivative
    have hinitial_reachable :
        yunFactorsDerivativeActiveReachable hp f c g fuel := by
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      simpa [c, g] using
        yunFactorsDerivativeActiveReachable_of_derivative_split hp f fuel hdf_ne_true
    have htail_fuel : contribution.2.size < fuel + 1 := by
      have hloop_dvd_g :
          (yunFactorsWithLevel c g multiplicity 1 fuel []).2 ∣ g := by
        exact yunFactorsWithLevel_repeated_dvd_repeated c g multiplicity 1 fuel
      have hg_dvd_f : g ∣ f := by
        simpa [g] using DensePoly.gcd_dvd_left f (DensePoly.derivative f)
      have hcontribution_dvd_f : contribution.2 ∣ f := by
        rw [← hloop_eq]
        exact dvd_trans_poly hloop_dvd_g hg_dvd_f
      have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
      have hsize_le : contribution.2.size ≤ f.size :=
        size_le_of_dvd_of_ne_zero hcontribution_dvd_f hf_ne
      omega
    have htail_raw_valid :=
      hrawTail f c g multiplicity 1 fuel hinitial_reachable
    have htail_nonzero : contribution.2.isZero = false :=
      htail_raw_valid.2.1
    have htail_valid :=
      htail_raw_valid.2.2 htail_fuel hone_false htail_derivative
    have htail_normalized_nontrivial :
        isOne (normalizeMonic contribution.2).2 = false :=
      normalizeMonic_isOne_false_of_isOne_false
        hp contribution.2 htail_nonzero htail_raw_valid.1 hone_false
    have htail_normalized_valid :=
      yunFactorsContributionWithLevel_normalized_pthRoot_tail_valid
        hp f c g multiplicity 1 fuel
        (yunFactorsDerivativeActiveReachable_normalized_stateProvider hp)
        hinitial_reachable htail_fuel htail_normalized_nontrivial htail_derivative
    have hmultiplicity_tail : 0 < multiplicity * p := by
      have hp_pos : 0 < p := by
        have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
        omega
      exact Nat.mul_pos hmultiplicity hp_pos
    have htail_normalized_residual :
        squareFreeAuxRevResidualSatisfied
          (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p) fuel :=
      squareFreeAuxRevResidualSatisfied_of_invariant residualInvariant
        (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p) fuel
    have htail_normalized_correct :
        squareFreeAuxRevContribution (pthRoot (normalizeMonic contribution.2).2)
            (multiplicity * p) fuel =
          pow (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p) :=
      ih (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p)
        hmultiplicity_tail htail_normalized_valid.2.2 htail_normalized_valid.2.1
        htail_normalized_valid.1 htail_normalized_residual
    exact
      derivative_active_raw_tail_weighted_product_bridge_via_normalized
        hp f contribution.2 contribution.1 multiplicity fuel hmultiplicity
        htail_nonzero htail_derivative htail_valid.1 htail_valid.2.1
        htail_valid.2.2 htail_residual ih htail_normalized_correct hpow_contribution

private theorem squareFreeAuxRevContribution_correct_pow_of_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel)
    (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hresidual : squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    squareFreeAuxRevContribution f multiplicity fuel = pow f multiplicity := by
  induction fuel generalizing f multiplicity with
  | zero =>
      omega
  | succ fuel ih =>
      simp only [squareFreeAuxRevContribution]
      simp [hzero]
      by_cases hdf : (DensePoly.derivative f).isZero
      · simpa [hdf] using
          squareFreeAuxRevContribution_derivative_zero_correct
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf (by
              have hmultiplicity_root : 0 < multiplicity * p := by
                have hp_pos : 0 < p := by
                  have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
                  omega
                exact Nat.mul_pos hmultiplicity hp_pos
              by_cases hconstant : f.size = 1
              · have hf_one : f = 1 := hreachable hconstant
                subst f
                exact squareFreeAuxRevContribution_pthRoot_constant_correct
                  hp (multiplicity * p) fuel
              · have hnonconstant : 1 < f.size := by
                  have hpos := size_pos_of_isZero_false f hzero
                  omega
                have hroot_fuel : (pthRoot f).size < fuel :=
                  pthRoot_fuel_decrease_of_derivative_zero_nonconstant
                    hp f hfuel hnonconstant
                have hroot_zero : (pthRoot f).isZero = false :=
                  pthRoot_nonzero_of_derivative_zero_nonconstant
                    hp f hzero hdf hnonconstant
                have hroot_reachable : squareFreeContributionReachable (pthRoot f) :=
                  pthRoot_reachable_of_derivative_zero
                    hp f hzero hdf hreachable
                have hroot_residual :
                    squareFreeAuxRevResidualSatisfied (pthRoot f) (multiplicity * p) fuel := by
                  have h := hresidual
                  simp only [squareFreeAuxRevResidualSatisfied] at h
                  rw [if_neg (by simp [hzero]), if_pos hdf] at h
                  exact h
                exact ih (pthRoot f) (multiplicity * p)
                  hmultiplicity_root hroot_fuel hroot_zero hroot_reachable hroot_residual)
      · have hdf_false : (DensePoly.derivative f).isZero = false := by
          cases h : (DensePoly.derivative f).isZero <;> simp [h] at hdf ⊢
        simpa [squareFreeAuxRevContribution, hzero, hdf_false] using
          squareFreeAuxRevContribution_derivative_active_pow_obligation
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf_false hreachable hresidual
            residualInvariant hrawState ih

private theorem squareFreeAuxRevContribution_pthRoot_normalized_tail_bridge_of_nontrivial
    (hp : Hex.Nat.Prime p) (tail : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (_hnontrivial : isOne (normalizeMonic tail).2 = false)
    (hrawReachable : squareFreeContributionReachable (pthRoot tail))
    (hrawZero : (pthRoot tail).isZero = false)
    (hrawFuel : (pthRoot tail).size < fuel)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hrawResidual :
      squareFreeAuxRevResidualSatisfied (pthRoot tail) (multiplicity * p) fuel)
    (hrawState : YunDerivativeActiveRawStateProvider hp)
    (hnormalized :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
      pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
        squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hmultiplicity_tail : 0 < multiplicity * p :=
    Nat.mul_pos hmultiplicity hp_pos
  have hraw :
      squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p) :=
    squareFreeAuxRevContribution_correct_pow_of_nonzero
      hp (pthRoot tail) (multiplicity * p) fuel hmultiplicity_tail hrawFuel
      hrawZero hrawReachable residualInvariant hrawResidual hrawState
  exact
    squareFreeAuxRevContribution_pthRoot_normalized_tail_bridge
      hp tail multiplicity fuel hmultiplicity hzero hdf hraw hnormalized

private theorem yunFactorsWithLevel_factor_mem_acc_or_dvd_current
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel accRev).1,
      sf ∈ accRev ∨ sf.factor ∣ c := by
  induction fuel generalizing c w level accRev with
  | zero =>
      intro sf hsf
      exact Or.inl hsf
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
        intro sf hsf
        exact Or.inl hsf
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        have hy_dvd_c : y ∣ c := by
          simpa [y] using DensePoly.gcd_dvd_left c w
        have hz_dvd_c : z ∣ c := by
          refine ⟨y, ?_⟩
          simpa [y, z] using (div_gcd_mul_reconstruct c w).symm
        by_cases hz : isOne z
        · intro sf hsf
          have htail :=
            ih y (w / y) (level + 1) accRev sf (by
              simpa [y, z, hz] using hsf)
          rcases htail with hacc | hsf_y
          · exact Or.inl hacc
          · exact Or.inr (dvd_trans_poly hsf_y hy_dvd_c)
        · let current : SquareFreeFactor p :=
            { factor := z, multiplicity := base * level }
          intro sf hsf
          have htail :=
            ih y (w / y) (level + 1) (current :: accRev) sf (by
              simpa [y, z, hz, current] using hsf)
          rcases htail with hacc | hsf_y
          · simp only [List.mem_cons] at hacc
            rcases hacc with hcurrent | haccRev
            · subst sf
              exact Or.inr hz_dvd_c
            · exact Or.inl haccRev
          · exact Or.inr (dvd_trans_poly hsf_y hy_dvd_c)

private theorem yunFactorsWithLevel_factor_dvd_current
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel []).1.reverse,
      sf.factor ∣ c := by
  intro sf hsf
  have hsf' : sf ∈ (yunFactorsWithLevel c w base level fuel []).1 :=
    List.mem_reverse.mp hsf
  have h := yunFactorsWithLevel_factor_mem_acc_or_dvd_current
    c w base level fuel [] sf hsf'
  simpa using h

private theorem yunStep_quotient_factor_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (z y factor : FpPoly p) (multiplicity tailMultiplicity : Nat)
    (hfactor_dvd_y : factor ∣ y)
    (hcommon :
      ∀ d : FpPoly p, d ∣ z → d ∣ y → d ∣ (1 : FpPoly p)) :
    squareFreeFactorCoprimeRel
      { factor := z, multiplicity := multiplicity }
      { factor := factor, multiplicity := tailMultiplicity } := by
  have hgcd_dvd_one :
      DensePoly.gcd z factor ∣ (1 : FpPoly p) :=
    hcommon (DensePoly.gcd z factor)
      (DensePoly.gcd_dvd_left z factor)
      (dvd_trans_poly (DensePoly.gcd_dvd_right z factor) hfactor_dvd_y)
  have hnormalized := normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
  simpa [squareFreeFactorCoprimeRel] using hnormalized

private theorem yunStep_quotient_right_factor_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w factor : FpPoly p) (multiplicity tailMultiplicity : Nat)
    (hfactor_dvd_w : factor ∣ w)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    squareFreeFactorCoprimeRel
      { factor := c / DensePoly.gcd c w, multiplicity := multiplicity }
      { factor := factor, multiplicity := tailMultiplicity } := by
  let z := c / DensePoly.gcd c w
  let y := DensePoly.gcd c w
  have hz_dvd_c : z ∣ c := by
    refine ⟨y, ?_⟩
    simpa [z, y] using (div_gcd_mul_reconstruct c w).symm
  have hgcd_dvd_y :
      DensePoly.gcd z factor ∣ y := by
    apply DensePoly.dvd_gcd
    · exact dvd_trans_poly (DensePoly.gcd_dvd_left z factor) hz_dvd_c
    · exact dvd_trans_poly (DensePoly.gcd_dvd_right z factor) hfactor_dvd_w
  have hgcd_dvd_one :
      DensePoly.gcd z factor ∣ (1 : FpPoly p) :=
    hcommon (DensePoly.gcd z factor)
      (DensePoly.gcd_dvd_left z factor)
      (by simpa [z, y] using hgcd_dvd_y)
  have hnormalized := normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
  simpa [squareFreeFactorCoprimeRel, z, y] using hnormalized

private theorem yunFactorsWithLevel_current_tail_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    yunFactorsCurrentTailCoprime c w base level fuel := by
  intro sf hsf
  have hsf_dvd_current :
      sf.factor ∣ DensePoly.gcd c w := by
    exact yunFactorsWithLevel_factor_dvd_current
      (DensePoly.gcd c w) (w / DensePoly.gcd c w) base (level + 1) fuel sf hsf
  exact
    yunStep_quotient_factor_coprime_of_common_dvd_one
      (c / DensePoly.gcd c w) (DensePoly.gcd c w) sf.factor (base * level) sf.multiplicity
      hsf_dvd_current
      hcommon

private theorem yunFactorsWithLevel_current_repeated_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    let tail :=
      yunFactorsWithLevel
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        base
        (level + 1)
        fuel
        []
    squareFreeFactorCoprimeRel
      { factor := c / DensePoly.gcd c w, multiplicity := base * level }
      { factor := tail.2, multiplicity := base * level * p } := by
  dsimp
  have htail_dvd :
      (yunFactorsWithLevel
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        base
        (level + 1)
        fuel
        []).2 ∣ w / DensePoly.gcd c w := by
    exact yunFactorsWithLevel_repeated_dvd_repeated
      (DensePoly.gcd c w)
      (w / DensePoly.gcd c w)
      base
      (level + 1)
      fuel
  have hright_dvd : w / DensePoly.gcd c w ∣ w := by
    exact ⟨DensePoly.gcd c w, (div_gcd_right_mul_reconstruct c w).symm⟩
  exact
    yunStep_quotient_right_factor_coprime_of_common_dvd_one
      c w
      (yunFactorsWithLevel
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        base
        (level + 1)
        fuel
        []).2
      (base * level)
      (base * level * p)
      (dvd_trans_poly htail_dvd hright_dvd)
      hcommon

set_option maxHeartbeats 800000 in
private theorem yunFactorsWithLevel_factors_coprime_repeated_of_reachable
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    let loop := yunFactorsWithLevel c w base level fuel []
    ∀ a ∈ loop.1.reverse,
      squareFreeFactorCoprimeRel
        a { factor := loop.2, multiplicity := base * level * p } := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
        let tail := yunFactorsWithLevel y (w / y) base (level + 1) fuel []
        have htail_reachable :
            yunFactorsPairwiseReachable y (w / y) fuel := by
          simpa [y] using yunFactorsPairwiseReachable_step c w fuel hreachable
        have htail_cross :
            ∀ a ∈ tail.1.reverse,
              squareFreeFactorCoprimeRel
                a { factor := tail.2, multiplicity := base * (level + 1) * p } := by
          simpa [tail] using ih y (w / y) (level + 1) htail_reachable
        by_cases hz : isOne z
        · simpa [y, z, tail, hz] using htail_cross
        · have hrev :
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse =
                [sf] ++ tail.1.reverse := by
            simpa [sf, tail] using
              yunFactorsWithLevel_reverse_append y (w / y) base (level + 1) fuel [sf]
          have hrepeated :
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).2 = tail.2 := by
            simpa [sf, tail] using
              yunFactorsWithLevel_repeated_eq_nil y (w / y) base (level + 1) fuel [sf]
          have hsf_cross :
              squareFreeFactorCoprimeRel
                sf { factor := tail.2, multiplicity := base * level * p } := by
            simpa [y, z, sf, tail] using
              yunFactorsWithLevel_current_repeated_coprime_of_common_dvd_one
                c w base level fuel
                (yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable)
          intro a ha
          have ha_rev :
              a ∈ (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse := by
            apply List.mem_reverse.mpr
            simpa [y, z, sf, hz] using ha
          rw [hrev] at ha_rev
          rcases List.mem_append.mp ha_rev with ha | ha
          · simp only [List.mem_singleton] at ha
            subst a
            simpa [y, z, sf, hz, hrepeated] using hsf_cross
          · have htail_a := htail_cross a ha
            simpa [y, z, sf, hz, hrepeated, squareFreeFactorCoprimeRel] using htail_a

private theorem yunFactorsPairwiseReady_succ_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (htail :
      yunFactorsPairwiseReady
        (DensePoly.gcd c w)
        (w / DensePoly.gcd c w)
        base
        (level + 1)
        fuel)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / DensePoly.gcd c w →
          d ∣ DensePoly.gcd c w →
            d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseReady c w base level (fuel + 1) := by
  apply yunFactorsPairwiseReady_succ_of_current_tail c w base level fuel htail
  intro _hc _hz
  exact yunFactorsWithLevel_current_tail_coprime_of_common_dvd_one
    c w base level fuel hcommon

private theorem yunFactorsPairwiseReady_of_reachable_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hcommon :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w (fuel + 1) →
          ∀ d : FpPoly p,
            d ∣ c / DensePoly.gcd c w →
              d ∣ DensePoly.gcd c w →
                d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseReady c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsPairwiseReady]
  | succ fuel ih =>
      have htail :
          yunFactorsPairwiseReady
            (DensePoly.gcd c w)
            (w / DensePoly.gcd c w)
            base
            (level + 1)
            fuel := by
        exact ih
          (DensePoly.gcd c w)
          (w / DensePoly.gcd c w)
          (level + 1)
          (yunFactorsPairwiseReachable_step c w fuel hreachable)
      exact
        yunFactorsPairwiseReady_succ_of_common_dvd_one
          c w base level fuel htail
          (hcommon c w fuel hreachable)

private theorem yunFactorsPairwiseReady_of_derivative_split_common_dvd_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hcommon :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w (fuel + 1) →
          ∀ d : FpPoly p,
            d ∣ c / DensePoly.gcd c w →
              d ∣ DensePoly.gcd c w →
                d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseReady
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      base
      level
      fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact
    yunFactorsPairwiseReady_of_reachable_common_dvd_one
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      base level fuel
      (yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf)
      hcommon

private theorem yunFactorsPairwiseInvariant_of_derivative_split_common_dvd_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hcommon :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w (fuel + 1) →
          ∀ d : FpPoly p,
            d ∣ c / DensePoly.gcd c w →
              d ∣ DensePoly.gcd c w →
                d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseInvariant
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      base
      level
      fuel where
  reachable := yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf
  ready :=
    yunFactorsPairwiseReady_of_derivative_split_common_dvd_one
      hp f base level fuel hdf hcommon

private theorem yunFactorsPairwiseInvariant_of_derivative_split_reachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsPairwiseInvariant
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      base
      level
      fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact
    yunFactorsPairwiseInvariant_of_derivative_split_common_dvd_one
      hp f base level fuel hdf
      (fun c w fuel hreachable =>
        yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable)

private theorem squareFreeAuxRev_reverse_append
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (squareFreeAuxRev f multiplicity fuel accRev).reverse =
      accRev.reverse ++ (squareFreeAuxRev f multiplicity fuel []).reverse := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simp [squareFreeAuxRev]
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          let loopNil := yunFactorsWithLevel c g multiplicity 1 fuel []
          have hloop_rev :
              loop.1.reverse = accRev.reverse ++ loopNil.1.reverse := by
            simpa [loop, loopNil] using
              yunFactorsWithLevel_reverse_append c g multiplicity 1 fuel accRev
          have hloop_repeated : loop.2 = loopNil.2 := by
            simpa [loop, loopNil] using
              yunFactorsWithLevel_repeated_eq_nil c g multiplicity 1 fuel accRev
          by_cases hrepeated : isOne loop.2
          · have hrepeated_nil : isOne loopNil.2 := by
              simpa [hloop_repeated] using hrepeated
            simpa [g, c, loop, loopNil, hrepeated, hrepeated_nil] using hloop_rev
          · have hrepeated_nil : isOne loopNil.2 = false := by
              cases h : isOne loopNil.2
              · exact rfl
              · exfalso
                apply hrepeated
                simpa [hloop_repeated] using h
            have hrec_loop :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  loop.1.reverse ++
                    (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
              exact ih (pthRoot loop.2) (multiplicity * p) loop.1
            have hrec_nil :
                (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel loopNil.1).reverse =
                  loopNil.1.reverse ++
                    (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse := by
              exact ih (pthRoot loopNil.2) (multiplicity * p) loopNil.1
            have htail :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse =
                  (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse := by
              rw [hloop_repeated]
            simpa [g, c, loop, loopNil, hrepeated, hrepeated_nil] using
              (calc
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse
                    = loop.1.reverse ++
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse :=
                      hrec_loop
                _ = (accRev.reverse ++ loopNil.1.reverse) ++
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
                      rw [hloop_rev]
                _ = accRev.reverse ++
                      (loopNil.1.reverse ++
                        (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse) := by
                      rw [htail]
                      simp [List.append_assoc]
                _ = accRev.reverse ++
                      (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel loopNil.1).reverse := by
                      rw [hrec_nil])

/--
Under the recursive residual derivative-zero invariant, every output factor
of `squareFreeAuxRev g m fuel []` divides `g`. The proof tracks the loop
through both the `pthRoot`-direct branch and the Yun-then-`pthRoot` branch,
relying on `pthRoot_dvd_self_of_derivative_zero` for the `pthRoot` steps and
on `yunFactorsWithLevel_factor_dvd_current` /
`yunFactorsWithLevel_repeated_dvd_repeated` for the Yun steps.
-/
private theorem squareFreeAuxRev_factor_dvd_input
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m fuel : Nat)
    (hresidual : squareFreeAuxRevResidualSatisfied g m fuel) :
    ∀ b ∈ (squareFreeAuxRev g m fuel []).reverse, b.factor ∣ g := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing g m with
  | zero =>
      intro b hb
      simp [squareFreeAuxRev] at hb
  | succ fuel ih =>
      intro b hb
      simp only [squareFreeAuxRev] at hb
      by_cases hzero : g.isZero = true
      · simp [hzero] at hb
      · have hzero_false : g.isZero = false := by
          cases h : g.isZero
          · rfl
          · exact False.elim (hzero h)
        rw [if_neg (by simp [hzero_false])] at hb
        by_cases hdf : (DensePoly.derivative g).isZero = true
        · rw [if_pos hdf] at hb
          have hres_pth :
              squareFreeAuxRevResidualSatisfied (pthRoot g) (m * p) fuel := by
            have h := hresidual
            simp only [squareFreeAuxRevResidualSatisfied] at h
            rw [if_neg (by simp [hzero_false]), if_pos hdf] at h
            exact h
          have hb_pth : b.factor ∣ pthRoot g :=
            ih (pthRoot g) (m * p) hres_pth b hb
          have hpth_dvd_g : pthRoot g ∣ g :=
            pthRoot_dvd_self_of_derivative_zero hp g hzero_false hdf
          exact dvd_trans_poly hb_pth hpth_dvd_g
        · have hdf_false : (DensePoly.derivative g).isZero = false := by
            cases h : (DensePoly.derivative g).isZero
            · rfl
            · exact False.elim (hdf h)
          rw [if_neg (by simp [hdf_false])] at hb
          let g_inner := DensePoly.gcd g (DensePoly.derivative g)
          let c_inner := g / g_inner
          let loop := yunFactorsWithLevel c_inner g_inner m 1 fuel []
          have hres_unpack :
              ((isOne loop.2 = true) ∨ (DensePoly.derivative loop.2).isZero = true) ∧
                ((isOne loop.2 = false) →
                  squareFreeAuxRevResidualSatisfied
                    (pthRoot loop.2) (m * p) fuel) := by
            have h := hresidual
            simp only [squareFreeAuxRevResidualSatisfied] at h
            rw [if_neg (by simp [hzero_false]), if_neg (by simp [hdf_false])] at h
            exact h
          have hg_inner_dvd_g : g_inner ∣ g :=
            DensePoly.gcd_dvd_left g (DensePoly.derivative g)
          have hloop_dvd_g_inner : loop.2 ∣ g_inner := by
            simpa [loop] using
              yunFactorsWithLevel_repeated_dvd_repeated c_inner g_inner m 1 fuel
          have hloop_dvd_g : loop.2 ∣ g :=
            dvd_trans_poly hloop_dvd_g_inner hg_inner_dvd_g
          have hc_inner_dvd_g : c_inner ∣ g := by
            refine ⟨g_inner, ?_⟩
            simpa [c_inner, g_inner] using
              (div_gcd_mul_reconstruct g (DensePoly.derivative g)).symm
          have hg_inner_ne : g_inner.isZero = false :=
            gcd_isZero_false_of_right_isZero_false g
              (DensePoly.derivative g) hdf_false
          have hloop_ne : loop.2.isZero = false := by
            cases hl : loop.2.isZero
            · rfl
            · exfalso
              have hloop_zero : loop.2 = 0 :=
                eq_zero_of_isZero_true loop.2 hl
              rcases hloop_dvd_g_inner with ⟨q, hq⟩
              have hg_inner_zero : g_inner = 0 := by
                rw [hq, hloop_zero, zero_mul]
              have hg_inner_isZero : g_inner.isZero = true := by
                rw [hg_inner_zero]; rfl
              rw [hg_inner_isZero] at hg_inner_ne
              cases hg_inner_ne
          by_cases hrep : isOne loop.2 = true
          · have hb_loop : b ∈ loop.1.reverse := by
              simpa [g_inner, c_inner, loop, hrep] using hb
            have hb_dvd_c : b.factor ∣ c_inner :=
              yunFactorsWithLevel_factor_dvd_current
                c_inner g_inner m 1 fuel b hb_loop
            exact dvd_trans_poly hb_dvd_c hc_inner_dvd_g
          · have hrep_false : isOne loop.2 = false := by
              cases h : isOne loop.2
              · rfl
              · exact False.elim (hrep h)
            have hres_inner :
                squareFreeAuxRevResidualSatisfied
                  (pthRoot loop.2) (m * p) fuel := hres_unpack.2 hrep_false
            have hb' :
                b ∈ (squareFreeAuxRev (pthRoot loop.2) (m * p) fuel loop.1).reverse := by
              simpa [g_inner, c_inner, loop, hrep_false] using hb
            rw [squareFreeAuxRev_reverse_append] at hb'
            rcases List.mem_append.mp hb' with hb_loop | hb_rec
            · have hb_dvd_c : b.factor ∣ c_inner :=
                yunFactorsWithLevel_factor_dvd_current
                  c_inner g_inner m 1 fuel b hb_loop
              exact dvd_trans_poly hb_dvd_c hc_inner_dvd_g
            · have hb_pth : b.factor ∣ pthRoot loop.2 :=
                ih (pthRoot loop.2) (m * p) hres_inner b hb_rec
              have hdf_loop : (DensePoly.derivative loop.2).isZero = true := by
                rcases hres_unpack.1 with h | h
                · rw [h] at hrep_false; cases hrep_false
                · exact h
              have hpth_dvd_loop : pthRoot loop.2 ∣ loop.2 :=
                pthRoot_dvd_self_of_derivative_zero hp loop.2 hloop_ne hdf_loop
              exact dvd_trans_poly hb_pth (dvd_trans_poly hpth_dvd_loop hloop_dvd_g)

/--
Coprime-transfer corollary of `squareFreeAuxRev_factor_dvd_input`: any common
divisor of `a` and an output factor of `squareFreeAuxRev g m fuel []` is a
common divisor of `a` and `g`, and thus divides `1` if `a` and `g` are
coprime.
-/
private theorem squareFreeAuxRev_factors_coprime_of_input_coprime
    (hp : Hex.Nat.Prime p) (g a : FpPoly p) (m fuel : Nat)
    (hcoprime : ∀ d : FpPoly p, d ∣ a → d ∣ g → d ∣ (1 : FpPoly p))
    (hresidual : squareFreeAuxRevResidualSatisfied g m fuel) :
    ∀ b ∈ (squareFreeAuxRev g m fuel []).reverse,
      ∀ d : FpPoly p, d ∣ a → d ∣ b.factor → d ∣ (1 : FpPoly p) := by
  intro b hb d hda hdb
  have hbg : b.factor ∣ g :=
    squareFreeAuxRev_factor_dvd_input hp g m fuel hresidual b hb
  exact hcoprime d hda (dvd_trans_poly hdb hbg)

private theorem yunFactorsWithLevel_pairwise_coprime_nil_of_ready
    (c w : FpPoly p) (base level fuel : Nat)
    (hready : yunFactorsPairwiseReady c w base level fuel) :
    (yunFactorsWithLevel c w base level fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        have hc_false : isOne c = false := by
          cases h : isOne c with
          | false => rfl
          | true => exact False.elim (hc h)
        let y := DensePoly.gcd c w
        let z := c / y
        have hready_unpack :
            yunFactorsPairwiseReady y (w / y) base (level + 1) fuel ∧
              (isOne c = false →
                isOne z = false →
                  yunFactorsCurrentTailCoprime c w base level fuel) := by
          simpa [yunFactorsPairwiseReady, y, z] using hready
        have htail :
            (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse.Pairwise
              squareFreeFactorCoprimeRel :=
          ih y (w / y) (level + 1) hready_unpack.1
        by_cases hz : isOne z
        · simpa [y, z, hz] using htail
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          have hz_false : isOne z = false := by
            cases h : isOne z with
            | false => rfl
            | true => exact False.elim (hz h)
          have hcross :
              ∀ tailSf ∈
                  (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse,
                squareFreeFactorCoprimeRel sf tailSf := by
            simpa [yunFactorsCurrentTailCoprime, y, z, sf] using
              hready_unpack.2 hc_false hz_false
          have hsingle :
              [sf].Pairwise squareFreeFactorCoprimeRel := by
            simp
          have hcombined :
              ([sf] ++
                  (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse).Pairwise
                squareFreeFactorCoprimeRel := by
            apply pairwise_append_of_cross squareFreeFactorCoprimeRel hsingle htail
            intro headSf hhead tailSf htailSf
            simp only [List.mem_singleton] at hhead
            subst headSf
            exact hcross tailSf htailSf
          have hrev :
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse =
                [sf] ++
                  (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse := by
            simpa [sf] using
              yunFactorsWithLevel_reverse_append y (w / y) base (level + 1) fuel [sf]
          simpa [y, z, hz, sf, hrev] using hcombined

private theorem yunFactorsWithLevel_pairwise_coprime_nil_of_invariant
    (c w : FpPoly p) (base level fuel : Nat)
    (hinv : yunFactorsPairwiseInvariant c w base level fuel) :
    (yunFactorsWithLevel c w base level fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact yunFactorsWithLevel_pairwise_coprime_nil_of_ready c w base level fuel hinv.ready

private theorem yunFactorsWithLevel_pairwise_coprime_nil
    (c w : FpPoly p) (base level fuel : Nat)
    (hinv : yunFactorsPairwiseInvariant c w base level fuel) :
    (yunFactorsWithLevel c w base level fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact yunFactorsWithLevel_pairwise_coprime_nil_of_invariant c w base level fuel hinv

/--
The residual invariant holds trivially on the unit polynomial: every recursive
step descends through the derivative-zero branch (since `derivative 1 = 0`)
into `pthRoot 1 = 1`, so the predicate is preserved until fuel runs out.
-/
private theorem squareFreeAuxRevResidualSatisfied_one
    (hp : Hex.Nat.Prime p) (m fuel : Nat) :
    squareFreeAuxRevResidualSatisfied (1 : FpPoly p) m fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing m with
  | zero => trivial
  | succ fuel ih =>
      simp only [squareFreeAuxRevResidualSatisfied]
      have hone_ne : (1 : FpPoly p).isZero = false := by
        have hcoeffs : (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        simp [DensePoly.isZero, hcoeffs]
      have hdf_one : (DensePoly.derivative (1 : FpPoly p)).isZero = true := by
        have hcoeffs : (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        have hsize : (1 : FpPoly p).size = 1 := by
          simpa [DensePoly.size] using congrArg Array.size hcoeffs
        unfold DensePoly.derivative
        simp [hsize, DensePoly.isZero, DensePoly.ofCoeffs, DensePoly.trimTrailingZeros]
        rfl
      rw [if_neg (by simp [hone_ne]), if_pos hdf_one, pthRoot_one hp]
      exact ih (m * p)

private theorem yunFactorsWithLevel_squareFreeAuxRev_tail_cross_coprime
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hresidual :
      ((isOne (yunFactorsWithLevel c w base level fuel []).2 = true) ∨
        (DensePoly.derivative
            (yunFactorsWithLevel c w base level fuel []).2).isZero = true) ∧
        ((isOne (yunFactorsWithLevel c w base level fuel []).2 = false) →
          squareFreeAuxRevResidualSatisfied
            (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
            (base * level * p) fuel)) :
    ∀ a ∈ (yunFactorsWithLevel c w base level fuel []).1.reverse,
      ∀ b ∈ (squareFreeAuxRev
              (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
              (base * level * p) fuel []).reverse,
        squareFreeFactorCoprimeRel a b := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro a ha b hb
  have ha_coprime :
      squareFreeFactorCoprimeRel
        a { factor := (yunFactorsWithLevel c w base level fuel []).2,
            multiplicity := base * level * p } :=
    yunFactorsWithLevel_factors_coprime_repeated_of_reachable
      c w base level fuel hreachable a ha
  have ha_gcd_dvd_one :
      DensePoly.gcd a.factor (yunFactorsWithLevel c w base level fuel []).2
        ∣ (1 : FpPoly p) := by
    apply dvd_one_of_normalizeMonic_eq_one
    simpa [squareFreeFactorCoprimeRel] using ha_coprime
  have hb_dvd_loop :
      b.factor ∣ (yunFactorsWithLevel c w base level fuel []).2 := by
    by_cases hone :
        isOne (yunFactorsWithLevel c w base level fuel []).2 = true
    · have hloop_eq_one :
          (yunFactorsWithLevel c w base level fuel []).2 = 1 :=
        eq_one_of_isOne_true _ hone
      have hres_one :
          squareFreeAuxRevResidualSatisfied
            (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
            (base * level * p) fuel := by
        rw [hloop_eq_one, pthRoot_one hp]
        exact squareFreeAuxRevResidualSatisfied_one hp (base * level * p) fuel
      have hb_dvd_pth :
          b.factor ∣ pthRoot (yunFactorsWithLevel c w base level fuel []).2 :=
        squareFreeAuxRev_factor_dvd_input hp _ _ _ hres_one b hb
      rw [hloop_eq_one] at hb_dvd_pth
      rw [pthRoot_one hp] at hb_dvd_pth
      rw [hloop_eq_one]
      exact hb_dvd_pth
    · have hone_false :
          isOne (yunFactorsWithLevel c w base level fuel []).2 = false := by
        cases h : isOne (yunFactorsWithLevel c w base level fuel []).2 with
        | false => rfl
        | true => exact False.elim (hone h)
      have hres_satisfied :
          squareFreeAuxRevResidualSatisfied
            (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
            (base * level * p) fuel := hresidual.2 hone_false
      have hloop_deriv_zero :
          (DensePoly.derivative
            (yunFactorsWithLevel c w base level fuel []).2).isZero = true := by
        rcases hresidual.1 with h | h
        · rw [h] at hone_false; cases hone_false
        · exact h
      have hb_dvd_pth :
          b.factor ∣ pthRoot (yunFactorsWithLevel c w base level fuel []).2 :=
        squareFreeAuxRev_factor_dvd_input hp _ _ _ hres_satisfied b hb
      have hpth_dvd_loop :
          pthRoot (yunFactorsWithLevel c w base level fuel []).2
            ∣ (yunFactorsWithLevel c w base level fuel []).2 := by
        by_cases hloop_zero :
            (yunFactorsWithLevel c w base level fuel []).2.isZero = true
        · have hloop_eq_zero :
              (yunFactorsWithLevel c w base level fuel []).2 = 0 :=
            eq_zero_of_isZero_true _ hloop_zero
          rw [hloop_eq_zero]
          refine ⟨0, ?_⟩
          rw [mul_zero]
        · have hloop_ne :
              (yunFactorsWithLevel c w base level fuel []).2.isZero = false := by
            cases h : (yunFactorsWithLevel c w base level fuel []).2.isZero with
            | false => rfl
            | true => exact False.elim (hloop_zero h)
          exact pthRoot_dvd_self_of_derivative_zero hp _ hloop_ne hloop_deriv_zero
      exact dvd_trans_poly hb_dvd_pth hpth_dvd_loop
  have hgcd_dvd :
      DensePoly.gcd a.factor b.factor
        ∣ DensePoly.gcd a.factor (yunFactorsWithLevel c w base level fuel []).2 := by
    apply DensePoly.dvd_gcd
    · exact DensePoly.gcd_dvd_left a.factor b.factor
    · exact dvd_trans_poly (DensePoly.gcd_dvd_right a.factor b.factor) hb_dvd_loop
  have hgcd_dvd_one :
      DensePoly.gcd a.factor b.factor ∣ (1 : FpPoly p) :=
    dvd_trans_poly hgcd_dvd ha_gcd_dvd_one
  have hnormalized := normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
  simpa [squareFreeFactorCoprimeRel] using hnormalized

private theorem squareFreeAuxRev_pairwise_coprime_one
    (hp : Hex.Nat.Prime p) (multiplicity fuel : Nat) :
    (squareFreeAuxRev (1 : FpPoly p) multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  induction fuel generalizing multiplicity with
  | zero =>
      simp [squareFreeAuxRev]
  | succ fuel ih =>
      have hone_ne : (1 : FpPoly p).isZero = false := by
        have hcoeffs :
            (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        simp [DensePoly.isZero, hcoeffs]
      have hdf_one : (DensePoly.derivative (1 : FpPoly p)).isZero = true := by
        have hcoeffs :
            (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        have hsize : (1 : FpPoly p).size = 1 := by
          simpa [DensePoly.size] using congrArg Array.size hcoeffs
        unfold DensePoly.derivative
        simp [hsize, DensePoly.isZero, DensePoly.ofCoeffs, DensePoly.trimTrailingZeros]
        rfl
      simp only [squareFreeAuxRev]
      rw [if_neg (by simp [hone_ne]), if_pos hdf_one, pthRoot_one hp]
      exact ih (multiplicity * p)

private theorem squareFreeAuxRev_pairwise_coprime_nil_core_of_residual_invariant
    (hp : Hex.Nat.Prime p)
    (yunInvariant :
      ∀ f : FpPoly p, ∀ base fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          yunFactorsPairwiseInvariant
            (f / DensePoly.gcd f (DensePoly.derivative f))
            (DensePoly.gcd f (DensePoly.derivative f))
            base
            1
            fuel)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) (multiplicity fuel : Nat) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  induction fuel generalizing f multiplicity with
  | zero =>
      simp [squareFreeAuxRev]
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p)
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel []
          have hzero_false : f.isZero = false := by
            cases h : f.isZero
            · rfl
            · exact False.elim (hzero h)
          have hdf_false : (DensePoly.derivative f).isZero = false := by
            cases h : (DensePoly.derivative f).isZero
            · rfl
            · exact False.elim (hdf h)
          have hinv :
              yunFactorsPairwiseInvariant c g multiplicity 1 fuel := by
            simpa [c, g] using yunInvariant f multiplicity fuel hdf_false
          have hres_unfolded :
              ((isOne (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = true) ∨
                (DensePoly.derivative
                  (yunFactorsWithLevel c g multiplicity 1 fuel []).2).isZero = true) ∧
                ((isOne (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = false) →
                  squareFreeAuxRevResidualSatisfied
                    (pthRoot (yunFactorsWithLevel c g multiplicity 1 fuel []).2)
                    (multiplicity * 1 * p) fuel) := by
            have hres_full :
                squareFreeAuxRevResidualSatisfied f multiplicity (fuel + 1) :=
              residualInvariant f multiplicity (fuel + 1) hdf_false
            simp only [squareFreeAuxRevResidualSatisfied] at hres_full
            rw [if_neg (by simp [hzero_false]),
                if_neg (by simp [hdf_false])] at hres_full
            refine ⟨?_, ?_⟩
            · simpa [c, g, Nat.mul_one] using hres_full.1
            · intro hone_false
              simpa [c, g, Nat.mul_one] using hres_full.2 hone_false
          by_cases hrepeated : isOne loop.2
          · simpa [g, c, loop, hrepeated] using
              yunFactorsWithLevel_pairwise_coprime_nil c g multiplicity 1 fuel hinv
          · have hloop :
                loop.1.reverse.Pairwise squareFreeFactorCoprimeRel := by
              simpa [loop] using
                yunFactorsWithLevel_pairwise_coprime_nil c g multiplicity 1 fuel hinv
            have htail :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse.Pairwise
                  squareFreeFactorCoprimeRel :=
              ih (pthRoot loop.2) (multiplicity * p)
            have hcross :
                ∀ a ∈ loop.1.reverse,
                  ∀ b ∈
                      (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse,
                    squareFreeFactorCoprimeRel a b := by
              have h :=
                yunFactorsWithLevel_squareFreeAuxRev_tail_cross_coprime
                  hp c g multiplicity 1 fuel hinv.reachable hres_unfolded
              simpa [loop, Nat.mul_one] using h
            have hcombined :
                (loop.1.reverse ++
                    (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse).Pairwise
                  squareFreeFactorCoprimeRel := by
              exact pairwise_append_of_cross
                squareFreeFactorCoprimeRel hloop htail hcross
            have hrev :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  loop.1.reverse ++
                    (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
              exact squareFreeAuxRev_reverse_append (pthRoot loop.2) (multiplicity * p) fuel loop.1
            simpa [g, c, loop, hrepeated, hrev] using hcombined

private theorem squareFreeAuxRev_pairwise_coprime_nil_core
    (hp : Hex.Nat.Prime p)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (_hfuel : f.size < fuel)
    (_hreachable : squareFreeContributionReachable f) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact squareFreeAuxRev_pairwise_coprime_nil_core_of_residual_invariant
    hp
    (fun f' base fuel' hdf =>
      yunFactorsPairwiseInvariant_of_derivative_split_reachable
        hp f' base 1 fuel'
        (by intro htrue; rw [htrue] at hdf; cases hdf))
    residualInvariant f multiplicity fuel

private theorem squareFreeAuxRev_pairwise_coprime_core
    (hp : Hex.Nat.Prime p)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (hreachable : squareFreeContributionReachable f)
    (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  intro hacc hcross
  rw [squareFreeAuxRev_reverse_append f multiplicity fuel accRev]
  apply pairwise_append_of_cross
  · exact hacc
  · exact squareFreeAuxRev_pairwise_coprime_nil_core hp residualInvariant
      f multiplicity fuel hfuel hreachable
  · exact hcross

private theorem squareFreeAuxRev_pairwise_coprime_of_acc
    (hp : Hex.Nat.Prime p)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (hreachable : squareFreeContributionReachable f)
    (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact squareFreeAuxRev_pairwise_coprime_core hp residualInvariant
    f multiplicity fuel hfuel hreachable accRev

private theorem squareFreeAuxRev_pairwise_coprime_nil
    (hp : Hex.Nat.Prime p)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (hreachable : squareFreeContributionReachable f) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  apply squareFreeAuxRev_pairwise_coprime_of_acc hp residualInvariant
    f multiplicity fuel hfuel hreachable
  · simp
  · intro a ha
    simp at ha

private def yunFactorsStepsSquareFree (c w : FpPoly p) : Nat → Prop
  | 0 => True
  | fuel + 1 =>
      if isOne c then
        True
      else
        let y := DensePoly.gcd c w
        let z := c / y
        (if isOne z then
          True
        else
          (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1) ∧
          yunFactorsStepsSquareFree y (w / y) fuel

private theorem yunFactorsStepsSquareFree_of_reachable
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    yunFactorsStepsSquareFree c w fuel := by
  induction fuel generalizing c w with
  | zero =>
      simp [yunFactorsStepsSquareFree]
  | succ fuel ih =>
      by_cases hc : isOne c
      · simp [yunFactorsStepsSquareFree, hc]
      · let y := DensePoly.gcd c w
        let z := c / y
        have hcurrent :
            ∀ d : FpPoly p,
              d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) :=
          yunFactorsPairwiseReachable_current_squarefree c w (fuel + 1) hreachable
        have hz_dvd_c : z ∣ c := by
          refine ⟨y, ?_⟩
          simpa [z, y] using (div_gcd_mul_reconstruct c w).symm
        have hz_squarefree :
            ∀ d : FpPoly p,
              d ∣ z → d ∣ DensePoly.derivative z → d ∣ (1 : FpPoly p) :=
          squarefree_factor_of_squarefree hz_dvd_c hcurrent
        have hgcd_dvd_one :
            DensePoly.gcd z (DensePoly.derivative z) ∣ (1 : FpPoly p) :=
          hz_squarefree (DensePoly.gcd z (DensePoly.derivative z))
            (DensePoly.gcd_dvd_left z (DensePoly.derivative z))
            (DensePoly.gcd_dvd_right z (DensePoly.derivative z))
        have hnormalized :
            (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1 :=
          normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
        have htail_reachable :
            yunFactorsPairwiseReachable y (w / y) fuel := by
          simpa [y] using yunFactorsPairwiseReachable_step c w fuel hreachable
        have htail : yunFactorsStepsSquareFree y (w / y) fuel :=
          ih y (w / y) htail_reachable
        by_cases hz : isOne z
        · simpa [yunFactorsStepsSquareFree, hc, y, z, hz] using htail
        · simpa [yunFactorsStepsSquareFree, hc, y, z, hz] using
            And.intro hnormalized htail

private theorem yunFactorsStepsSquareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsStepsSquareFree
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact yunFactorsStepsSquareFree_of_reachable
    (f / DensePoly.gcd f (DensePoly.derivative f))
    (DensePoly.gcd f (DensePoly.derivative f))
    fuel
    (yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf)

private theorem yunFactorsWithLevel_factors_squareFree_of_steps
    (c w : FpPoly p) (base level fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hsteps : yunFactorsStepsSquareFree c w fuel)
    (hacc : ∀ sf ∈ accRev.reverse, squareFreeFactorSquareFreeRel sf) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel accRev).1.reverse,
      squareFreeFactorSquareFreeRel sf := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simpa [yunFactorsWithLevel] using hacc
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simpa [hc] using hacc
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        have hsteps_nonone :
            (if isOne z then
              True
            else
              (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1) ∧
              yunFactorsStepsSquareFree y (w / y) fuel := by
          simpa [yunFactorsStepsSquareFree, hc, y, z] using hsteps
        have hsteps_tail : yunFactorsStepsSquareFree y (w / y) fuel := by
          exact hsteps_nonone.2
        by_cases hz : isOne z
        · simpa [y, z, hz] using
            ih y (w / y) (level + 1) accRev hsteps_tail hacc
        · have hacc' :
              ∀ sf ∈ ({ factor := z, multiplicity := base * level } :: accRev).reverse,
                squareFreeFactorSquareFreeRel sf := by
            intro sf hsf
            rw [List.reverse_cons] at hsf
            rcases List.mem_append.mp hsf with hsf | hsf
            · exact hacc sf hsf
            · simp only [List.mem_singleton] at hsf
              subst sf
              have hstep :
                  (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1 := by
                simpa [hz] using hsteps_nonone.1
              simpa [squareFreeFactorSquareFreeRel, z, y] using hstep
          simpa [y, z, hz] using
            ih y (w / y) (level + 1)
              ({ factor := z, multiplicity := base * level } :: accRev) hsteps_tail hacc'

private theorem yunFactorsWithLevel_factors_squareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hacc : ∀ sf ∈ accRev.reverse, squareFreeFactorSquareFreeRel sf) :
    ∀ sf ∈
        (yunFactorsWithLevel (f / DensePoly.gcd f (DensePoly.derivative f))
          (DensePoly.gcd f (DensePoly.derivative f)) base level fuel accRev).1.reverse,
      squareFreeFactorSquareFreeRel sf := by
  apply yunFactorsWithLevel_factors_squareFree_of_steps
  · exact yunFactorsStepsSquareFree_of_derivative_split hp f fuel hdf
  · exact hacc

private theorem squareFreeAuxRev_factors_squareFree
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hacc : ∀ sf ∈ accRev.reverse, squareFreeFactorSquareFreeRel sf) :
    ∀ sf ∈ (squareFreeAuxRev f multiplicity fuel accRev).reverse,
      squareFreeFactorSquareFreeRel sf := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simpa [squareFreeAuxRev] using hacc
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simpa [hzero] using hacc
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev hacc
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          have hloop :
              ∀ sf ∈ loop.1.reverse,
                squareFreeFactorSquareFreeRel sf := by
            simpa [loop, c, g] using
              yunFactorsWithLevel_factors_squareFree_of_derivative_split hp f multiplicity 1 fuel
                accRev hdf hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1 hloop

private theorem squareFreeAuxRevContribution_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hresidual : squareFreeAuxRevResidualSatisfied f 1 (f.size + 1))
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    squareFreeAuxRevContribution f 1 (f.size + 1) = f := by
  rw [squareFreeAuxRevContribution_correct_pow_of_nonzero hp f 1 (f.size + 1)
    (by omega) (by omega) hzero hreachable residualInvariant hresidual hrawState]
  exact pow_one f

private theorem squareFreeAux_zero_weightedProduct
    (f : FpPoly p) (hzero : f.isZero = true) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = 1 := by
  unfold squareFreeAux
  simp [squareFreeAuxRev, hzero, weightedProduct_nil]

/--
Compute a square-free decomposition by normalizing away the leading scalar and
running Yun's algorithm on the resulting monic polynomial.
-/
def squareFreeDecomposition (hp : Hex.Nat.Prime p) (f : FpPoly p) : SquareFreeDecomposition p :=
  let _ := hp
  let normalized := normalizeMonic f
  let unit := normalized.1
  let monicPart := normalized.2
  let factors := squareFreeAux monicPart 1 (monicPart.size + 1)
  { unit, factors }

private theorem squareFreeAux_weightedProduct_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hresidual : squareFreeAuxRevResidualSatisfied f 1 (f.size + 1))
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = f := by
  unfold squareFreeAux
  have hinvariant := squareFreeAuxRev_reconstruction_invariant f 1 (f.size + 1) []
  rw [hinvariant]
  simp [weightedProduct_nil]
  exact squareFreeAuxRevContribution_correct
    hp f hzero hreachable residualInvariant hresidual hrawState

/--
Normalized gcd monicity for the Yun derivative-active transition. Whenever the
right gcd operand is nonzero, the normalized gcd value
`(normalizeMonic (DensePoly.gcd c w)).2` is monic.

The raw executable `DensePoly.gcd c w` is not in general monic even when
`c, w` are monic: over `F_5`, `gcd (x^2 + 1) (x + 1)` follows an Euclidean
remainder path and returns the constant `2`, not a monic value. So the gcd
side of the Yun derivative-active monic invariant tracked in #6155 must route
through the normalized gcd value rather than the raw output.
-/
private theorem normalizeMonic_gcd_monic_of_right_nonzero
    [ZMod64.PrimeModulus p] (c w : FpPoly p)
    (hw : w.isZero = false) :
    DensePoly.Monic (normalizeMonic (DensePoly.gcd c w)).2 :=
  normalizeMonic_nonzero_monic (DensePoly.gcd c w)
    (gcd_isZero_false_of_right_isZero_false c w hw)

/--
Normalized monicity at every Yun derivative-active reachable state. From the
reachability hypothesis, `(normalizeMonic c).2`, `(normalizeMonic w).2`, and
the next-step normalized gcd `(normalizeMonic (DensePoly.gcd c w)).2` are all
monic.

This is the gcd-side substrate for the residual monic invariant tracked in
#6155. Combined with the exact-quotient lemmas from #6164
(`monic_div_gcd_left_of_monic`, `monic_div_gcd_right_of_monic`), the
derivative-active induction step can dispatch monicity at the normalized state
without asserting raw executable gcd monicity.
-/
private theorem yunFactorsDerivativeActiveReachable_normalizeMonic_monic
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    DensePoly.Monic (normalizeMonic c).2 ∧
      DensePoly.Monic (normalizeMonic w).2 ∧
        DensePoly.Monic (normalizeMonic (DensePoly.gcd c w)).2 := by
  have hnonzero :=
    yunFactorsDerivativeActiveReachable_nonzero hp f c w fuel hreachable
  exact
    ⟨normalizeMonic_nonzero_monic c hnonzero.1,
      normalizeMonic_nonzero_monic w hnonzero.2,
      normalizeMonic_gcd_monic_of_right_nonzero c w hnonzero.2⟩

private theorem normalizeMonic_zero_squareFree_weightedProduct
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : (normalizeMonic f).2.isZero = true) :
    DensePoly.C (normalizeMonic f).1 *
      weightedProduct
        (squareFreeAux (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)) =
        f := by
  rw [squareFreeAux_zero_weightedProduct (normalizeMonic f).2 hzero]
  have hmonic_zero : (normalizeMonic f).2 = 0 :=
    eq_zero_of_isZero_true (normalizeMonic f).2 hzero
  have hreconstruct := normalizeMonic_reconstruct hp f
  rw [hmonic_zero] at hreconstruct
  simp at hreconstruct
  rw [← hreconstruct]
  rfl

private theorem yunFactorsWithLevel_multiplicity_pos_raw
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p))
    (hbase : 0 < base) (hlevel : 0 < level)
    (hacc : ∀ sf ∈ accRev, 0 < sf.multiplicity) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel accRev).1,
      0 < sf.multiplicity := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simpa [yunFactorsWithLevel] using hacc
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simpa [hc] using hacc
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using
            ih y (w / y) (level + 1) accRev (Nat.succ_pos level) hacc
        · have hacc' :
              ∀ sf ∈ ({ factor := z, multiplicity := base * level } :: accRev),
                0 < sf.multiplicity := by
            intro sf hsf
            rcases List.mem_cons.mp hsf with hsf | hsf
            · subst sf
              exact Nat.mul_pos hbase hlevel
            · exact hacc sf hsf
          simpa [y, z, hz] using
            ih y (w / y) (level + 1)
              ({ factor := z, multiplicity := base * level } :: accRev)
              (Nat.succ_pos level) hacc'

private theorem squareFreeAuxRev_multiplicity_pos_raw
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hmultiplicity : 0 < multiplicity)
    (hacc : ∀ sf ∈ accRev, 0 < sf.multiplicity) :
    ∀ sf ∈ squareFreeAuxRev f multiplicity fuel accRev,
      0 < sf.multiplicity := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simpa [squareFreeAuxRev] using hacc
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simpa [hzero] using hacc
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · have hp_pos : 0 < p := by
            have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
            omega
          simpa [hdf] using
            ih (pthRoot f) (multiplicity * p) accRev
              (Nat.mul_pos hmultiplicity hp_pos) hacc
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          have hloop :
              ∀ sf ∈ loop.1, 0 < sf.multiplicity := by
            simpa [loop, c, g] using
              yunFactorsWithLevel_multiplicity_pos_raw
                c g multiplicity 1 fuel accRev hmultiplicity (by omega) hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · have hp_pos : 0 < p := by
              have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
              omega
            simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1
                (Nat.mul_pos hmultiplicity hp_pos) hloop

theorem squareFree_pairwise_coprime (hp : Hex.Nat.Prime p)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise
      (fun a b => (normalizeMonic (DensePoly.gcd a.factor b.factor)).2 = 1) := by
  unfold squareFreeDecomposition squareFreeAux
  exact squareFreeAuxRev_pairwise_coprime_nil hp
    residualInvariant
    (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)
    (Nat.lt_succ_self _)
    (normalizeMonic_squareFreeContributionReachable hp f)

theorem squareFree_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (residualInvariant :
      ∀ f : FpPoly p, ∀ multiplicity fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f := by
  dsimp [squareFreeDecomposition]
  by_cases hzero : (normalizeMonic f).2.isZero
  · exact normalizeMonic_zero_squareFree_weightedProduct hp f hzero
  · have hnonzero : (normalizeMonic f).2.isZero = false := by
      cases h : (normalizeMonic f).2.isZero <;> simp [h] at hzero ⊢
    have hresidual :
        squareFreeAuxRevResidualSatisfied
          (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1) :=
      squareFreeAuxRevResidualSatisfied_of_invariant residualInvariant
        (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)
    rw [squareFreeAux_weightedProduct_nonzero hp (normalizeMonic f).2 hnonzero
      (normalizeMonic_squareFreeContributionReachable hp f)
      residualInvariant hresidual hrawState]
    exact normalizeMonic_reconstruct hp f

theorem squareFree_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors,
      (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 = 1 := by
  unfold squareFreeDecomposition squareFreeAux
  apply squareFreeAuxRev_factors_squareFree hp
  intro sf hsf
  simp at hsf

theorem squareFreeDecomposition_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors,
      (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 = 1 :=
  squareFree_factors_squareFree hp f

theorem squareFreeDecomposition_multiplicity_pos (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors, 0 < sf.multiplicity := by
  dsimp [squareFreeDecomposition, squareFreeAux]
  intro sf hsf
  have hraw :
      ∀ sf ∈ squareFreeAuxRev (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1) [],
        0 < sf.multiplicity := by
    apply squareFreeAuxRev_multiplicity_pos_raw hp
    · omega
    · intro sf hsf
      simp at hsf
  exact hraw sf (by simpa using hsf)

private instance squareFreeGuardBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem prime_five_squareFree_guard : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private def polyFiveSquareFreeGuard (coeffs : Array Nat) : FpPoly 5 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNatsSquareFreeGuard (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

#guard
  let f := polyFiveSquareFreeGuard #[1, 1, 1]
  let d := squareFreeDecomposition prime_five_squareFree_guard f
  d.factors.all (fun sf =>
    coeffNatsSquareFreeGuard
      (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 == [1])

private instance squareFreeGuardBoundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private theorem prime_two_squareFree_guard : Hex.Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · exact Or.inr rfl

private def polyTwoSquareFreeGuard (coeffs : Array Nat) : FpPoly 2 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))

private def coeffNatsSquareFreeGuardTwo (f : FpPoly 2) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

#guard
  let f := polyTwoSquareFreeGuard #[1, 0, 1, 0, 1, 0, 1]
  let d := squareFreeDecomposition prime_two_squareFree_guard f
  coeffNatsSquareFreeGuardTwo (weightedProduct d.factors) ==
    coeffNatsSquareFreeGuardTwo f

private theorem linearPow_eq_powLinear (f : FpPoly p) (n : Nat) :
    FpPoly.linearPow f n = powLinear f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : FpPoly.linearPow f (n + 1) = FpPoly.linearPow f n * f := rfl
      have h2 : powLinear f (n + 1) = powLinear f n * f := rfl
      rw [h1, h2, ih]

/-- Freshman's dream for `FpPoly.linearPow`: in characteristic `p`, raising to
the prime power is additive. -/
theorem linearPow_add_prime
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) :
    FpPoly.linearPow (f + g) p =
      FpPoly.linearPow f p + FpPoly.linearPow g p := by
  rw [linearPow_eq_powLinear, linearPow_eq_powLinear, linearPow_eq_powLinear]
  exact powLinear_add_prime hp f g

/-- `FpPoly.linearPow` of a product factors over the base. -/
theorem linearPow_mul_base (f g : FpPoly p) (n : Nat) :
    FpPoly.linearPow (f * g) n =
      FpPoly.linearPow f n * FpPoly.linearPow g n := by
  rw [linearPow_eq_powLinear, linearPow_eq_powLinear, linearPow_eq_powLinear]
  exact powLinear_mul_base f g n

end FpPoly
end Hex
