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
  have hzero_add : (0 : ZMod64 p) + 0 = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_cd]
  rw [DensePoly.coeff_add _ _ _ hzero_add]
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

private theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) :
    Hex.Nat.choose n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp [Hex.Nat.choose]
          by_cases hk : n < k
          · simp [ih hk]
            exact ih (by omega)
          · exfalso
            omega

private theorem choose_self (n : Nat) : Hex.Nat.choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Hex.Nat.choose, ih, choose_eq_zero_of_lt (by omega : n < n + 1)]

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
    choose_eq_zero_of_lt (by omega)
  rw [hzero_choose]
  rw [choose_self]
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
      calc
        0 + f * powLinearBinomTerm f g n 0 =
            f * powLinearBinomTerm f g n 0 := DensePoly.zero_add _
        _ = f * (0 + powLinearBinomTerm f g n 0) + 0 := by
              have hz : (0 : FpPoly p) + powLinearBinomTerm f g n 0 =
                  powLinearBinomTerm f g n 0 := DensePoly.zero_add _
              rw [hz]
              exact (DensePoly.add_zero_poly _).symm
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
      have hzero_add : (0 : ZMod64 p) + 0 = 0 := by grind
      repeat rw [DensePoly.coeff_add _ _ _ hzero_add]
      grind

private theorem powLinearBinomTerm_above
    (f g : FpPoly p) {n k : Nat} (hk : n < k) :
    powLinearBinomTerm f g n k = 0 := by
  unfold powLinearBinomTerm
  rw [choose_eq_zero_of_lt hk]
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
      calc
        (1 : FpPoly p) = DensePoly.scale (1 : ZMod64 p) (1 : FpPoly p) := by
          exact (powLinearBinom_scalar_one (1 : FpPoly p)).symm
        _ = 0 + DensePoly.scale (1 : ZMod64 p) (1 : FpPoly p) := by
          exact (DensePoly.zero_add _).symm
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
  rw [choose_self]
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
      grind
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
      rw [DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff]

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
        if n = 0 then (g.coeff i) ^ 0 else 0
      rw [DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn, Lean.Grind.Semiring.pow_zero (g.coeff i)]
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
      rw [DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff]
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
              grind
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
        DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff,
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
  exact DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff

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

private theorem leadingCoeff_ne_zero_of_isZero_false
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
  have hlead_ne := leadingCoeff_ne_zero_of_isZero_false f hzero
  rw [zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne]
  exact scale_one_left f

private theorem normalizeMonic_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  cases hzero : f.isZero
  · exact normalizeMonic_nonzero_reconstruct hp f hzero
  · exact normalizeMonic_zero_reconstruct f hzero

/--
Yun's inner loop: peel off the factors with multiplicities `i`, `i + 1`, ...
from the coprime/repeated split `(c, w)`, consing each discovered factor onto
the reverse-order accumulator.
-/
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
          let contribution := yunFactorsContribution c g multiplicity fuel
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

private theorem yunFactorsContribution_step_split
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) :
    let y := DensePoly.gcd c w
    let z := c / y
    z * y = c ∧ (w / y) * y = w := by
  constructor
  · exact div_gcd_mul_reconstruct c w
  · exact div_gcd_right_mul_reconstruct c w

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
Remaining assembly obligation for the derivative-active branch: the new
offset-form Yun invariant below identifies the local contribution with the
emitted weighted product, while this theorem is the later factorisation step
that upgrades that weighted product back to the outer `pow f multiplicity`
contract.
-/
private theorem squareFreeAuxRevContribution_derivative_active_pow_obligation
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeAuxRevContribution f multiplicity (fuel + 1) = pow f multiplicity := by
  have hoffset :=
    yunFactorsContribution_reconstruct
      hp f multiplicity fuel hmultiplicity hfuel hzero hdf
  sorry

private theorem squareFreeAuxRevContribution_correct_pow_of_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel)
    (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f) :
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
                exact ih (pthRoot f) (multiplicity * p)
                  hmultiplicity_root hroot_fuel hroot_zero hroot_reachable)
      · have hdf_false : (DensePoly.derivative f).isZero = false := by
          cases h : (DensePoly.derivative f).isZero <;> simp [h] at hdf ⊢
        simpa [squareFreeAuxRevContribution, hzero, hdf_false] using
          squareFreeAuxRevContribution_derivative_active_pow_obligation
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf_false hreachable

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
          let loop := yunFactors c g multiplicity fuel accRev
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
          let loop := yunFactors c g multiplicity fuel accRev
          let contribution := yunFactorsContribution c g multiplicity fuel
          have hloop := yunFactors_reconstruction_invariant c g multiplicity fuel accRev
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
  fun a b => DensePoly.gcd a.factor b.factor = 1

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

private theorem yunFactors_reverse_append
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactors c w i fuel accRev).1.reverse =
      accRev.reverse ++ (yunFactors c w i fuel []).1.reverse := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors]
  | succ fuel ih =>
      simp only [yunFactors]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := i }
          have hacc := ih y (w / y) (i + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (i + 1) [sf]
          simpa [y, z, hz, sf] using
            (calc
              (yunFactors y (w / y) (i + 1) fuel (sf :: accRev)).1.reverse
                  = (sf :: accRev).reverse ++
                      (yunFactors y (w / y) (i + 1) fuel []).1.reverse := hacc
              _ = accRev.reverse ++
                    (yunFactors y (w / y) (i + 1) fuel [sf]).1.reverse := by
                  rw [hsingle]
                  simp [List.reverse_cons, List.append_assoc])

private theorem yunFactors_repeated_eq_nil
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactors c w i fuel accRev).2 = (yunFactors c w i fuel []).2 := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors]
  | succ fuel ih =>
      simp only [yunFactors]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := i }
          have hacc := ih y (w / y) (i + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (i + 1) [sf]
          simpa [y, z, hz, sf] using hacc.trans hsingle.symm

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
          let loop := yunFactors c g multiplicity fuel accRev
          let loopNil := yunFactors c g multiplicity fuel []
          have hloop_rev :
              loop.1.reverse = accRev.reverse ++ loopNil.1.reverse := by
            simpa [loop, loopNil] using
              yunFactors_reverse_append c g multiplicity fuel accRev
          have hloop_repeated : loop.2 = loopNil.2 := by
            simpa [loop, loopNil] using
              yunFactors_repeated_eq_nil c g multiplicity fuel accRev
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

private theorem yunFactors_pairwise_coprime_nil
    (c w : FpPoly p) (multiplicity fuel : Nat) :
    (yunFactors c w multiplicity fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  sorry

private theorem yunFactors_squareFreeAuxRev_tail_cross_coprime
    (c w : FpPoly p) (multiplicity fuel : Nat) :
    let loop := yunFactors c w multiplicity fuel []
    ∀ a ∈ loop.1.reverse,
      ∀ b ∈ (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse,
        squareFreeFactorCoprimeRel a b := by
  sorry

private theorem squareFreeAuxRev_pairwise_coprime_nil_core
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
          let loop := yunFactors c g multiplicity fuel []
          by_cases hrepeated : isOne loop.2
          · simpa [g, c, loop, hrepeated] using
              yunFactors_pairwise_coprime_nil c g multiplicity fuel
          · have hloop :
                loop.1.reverse.Pairwise squareFreeFactorCoprimeRel := by
              simpa [loop] using yunFactors_pairwise_coprime_nil c g multiplicity fuel
            have htail :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse.Pairwise
                  squareFreeFactorCoprimeRel :=
              ih (pthRoot loop.2) (multiplicity * p)
            have hcross :
                ∀ a ∈ loop.1.reverse,
                  ∀ b ∈
                      (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse,
                    squareFreeFactorCoprimeRel a b := by
              simpa [loop] using
                yunFactors_squareFreeAuxRev_tail_cross_coprime c g multiplicity fuel
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

private theorem squareFreeAuxRev_pairwise_coprime_core
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
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
  · exact squareFreeAuxRev_pairwise_coprime_nil_core f multiplicity fuel
  · exact hcross

private theorem squareFreeAuxRev_pairwise_coprime_of_acc
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact squareFreeAuxRev_pairwise_coprime_core f multiplicity fuel accRev

private theorem squareFreeAuxRev_pairwise_coprime_nil
    (f : FpPoly p) (multiplicity fuel : Nat) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  apply squareFreeAuxRev_pairwise_coprime_of_acc
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
          DensePoly.gcd z (DensePoly.derivative z) = 1) ∧
          yunFactorsStepsSquareFree y (w / y) fuel

private theorem yunFactorsStepsSquareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsStepsSquareFree
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      fuel := by
  sorry

private theorem yunFactors_factors_squareFree_of_steps
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hsteps : yunFactorsStepsSquareFree c w fuel)
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈ (yunFactors c w multiplicity fuel accRev).1.reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  induction fuel generalizing c w multiplicity accRev with
  | zero =>
      simpa [yunFactors] using hacc
  | succ fuel ih =>
      simp only [yunFactors]
      by_cases hc : isOne c
      · simpa [hc] using hacc
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        have hsteps_nonone :
            (if isOne z then
              True
            else
              DensePoly.gcd z (DensePoly.derivative z) = 1) ∧
              yunFactorsStepsSquareFree y (w / y) fuel := by
          simpa [yunFactorsStepsSquareFree, hc, y, z] using hsteps
        have hsteps_tail : yunFactorsStepsSquareFree y (w / y) fuel := by
          exact hsteps_nonone.2
        by_cases hz : isOne z
        · simpa [y, z, hz] using
            ih y (w / y) (multiplicity + 1) accRev hsteps_tail hacc
        · have hacc' :
              ∀ sf ∈ ({ factor := z, multiplicity := multiplicity } :: accRev).reverse,
                DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
            intro sf hsf
            rw [List.reverse_cons] at hsf
            rcases List.mem_append.mp hsf with hsf | hsf
            · exact hacc sf hsf
            · simp only [List.mem_singleton] at hsf
              subst sf
              have hstep : DensePoly.gcd z (DensePoly.derivative z) = 1 := by
                simpa [hz] using hsteps_nonone.1
              simpa [z, y] using hstep
          simpa [y, z, hz] using
            ih y (w / y) (multiplicity + 1)
              ({ factor := z, multiplicity := multiplicity } :: accRev) hsteps_tail hacc'

private theorem yunFactors_factors_squareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈
        (yunFactors (f / DensePoly.gcd f (DensePoly.derivative f))
          (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel accRev).1.reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  apply yunFactors_factors_squareFree_of_steps
  · exact yunFactorsStepsSquareFree_of_derivative_split hp f fuel hdf
  · exact hacc

private theorem squareFreeAuxRev_factors_squareFree
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈ (squareFreeAuxRev f multiplicity fuel accRev).reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
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
          let loop := yunFactors c g multiplicity fuel accRev
          have hloop :
              ∀ sf ∈ loop.1.reverse,
                DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
            simpa [loop, c, g] using
              yunFactors_factors_squareFree_of_derivative_split hp f multiplicity fuel
                accRev hdf hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1 hloop

private theorem squareFreeAuxRevContribution_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeAuxRevContribution f 1 (f.size + 1) = f := by
  rw [squareFreeAuxRevContribution_correct_pow_of_nonzero hp f 1 (f.size + 1)
    (by omega) (by omega) hzero hreachable]
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
    (hreachable : squareFreeContributionReachable f) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = f := by
  unfold squareFreeAux
  have hinvariant := squareFreeAuxRev_reconstruction_invariant f 1 (f.size + 1) []
  rw [hinvariant]
  simp [weightedProduct_nil]
  exact squareFreeAuxRevContribution_correct hp f hzero hreachable

private theorem normalizeMonic_squareFreeContributionReachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    squareFreeContributionReachable (normalizeMonic f).2 := by
  intro hsize
  cases hzero : f.isZero
  · rw [normalizeMonic_nonzero f hzero] at hsize ⊢
    change DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f = 1
    change (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = 1 at hsize
    let unit := DensePoly.leadingCoeff f
    have hunit_ne : unit ≠ 0 := leadingCoeff_ne_zero_of_isZero_false f hzero
    have hinv_ne : unit⁻¹ ≠ 0 :=
      zmod64_inv_ne_zero_of_prime_ne_zero hp hunit_ne
    have hunit_inv : unit⁻¹ * unit = 1 := by
      have h := zmod64_mul_inv_eq_one_of_prime_ne_zero hp hunit_ne
      have hcomm : unit⁻¹ * unit = unit * unit⁻¹ := by grind
      rw [hcomm]
      exact h
    have hscale_size : f.size = 1 := by
      have hpos : 0 < f.size := by
        simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
          Nat.pos_iff_ne_zero] using hzero
      by_cases hle : f.size ≤ 1
      · omega
      · exfalso
        have hgt : 1 < f.size := by omega
        let i := f.size - 1
        have hi_ge : 1 ≤ i := by omega
        have hscaled_zero :
            (DensePoly.scale unit⁻¹ f).coeff i = 0 :=
          DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale unit⁻¹ f) (by
            have hs : (DensePoly.scale unit⁻¹ f).size = 1 := by
              simpa [unit] using hsize
            omega)
        have hscaled_coeff :
            (DensePoly.scale unit⁻¹ f).coeff i = unit⁻¹ * f.coeff i := by
          exact DensePoly.coeff_scale unit⁻¹ f i (zmod64_mul_zero unit⁻¹)
        have hlast : f.coeff i ≠ 0 := by
          simpa [i] using DensePoly.coeff_last_ne_zero_of_pos_size f hpos
        have hmul : unit⁻¹ * f.coeff i = 0 := by
          rw [← hscaled_coeff]
          exact hscaled_zero
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hmul with hinv_zero | hcoeff_zero
        · exact hinv_ne hinv_zero
        · exact hlast hcoeff_zero
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hcoeff :
            (DensePoly.scale unit⁻¹ f).coeff 0 = unit⁻¹ * f.coeff 0 := by
          exact DensePoly.coeff_scale unit⁻¹ f 0 (zmod64_mul_zero unit⁻¹)
        have hlead : unit = f.coeff 0 := by
          have hlead_last : DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
            unfold DensePoly.leadingCoeff DensePoly.coeff
            rw [Array.back?_eq_getElem?]
            have hidx : f.coeffs.size - 1 < f.coeffs.size := by
              simpa [DensePoly.size] using Nat.sub_one_lt_of_lt (by omega : 0 < f.size)
            simp [Array.getD, DensePoly.size, hidx]
          simpa [unit, hscale_size] using hlead_last
        rw [hcoeff, ← hlead, hunit_inv]
        exact (DensePoly.coeff_C (1 : ZMod64 p) 0).symm
    | succ n =>
        have hcoeff_zero :
            (DensePoly.scale unit⁻¹ f).coeff (n + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale unit⁻¹ f) (by
            have hs : (DensePoly.scale unit⁻¹ f).size = 1 := by
              simpa [unit] using hsize
            omega)
        rw [hcoeff_zero]
        exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm
  · rw [normalizeMonic_zero f hzero] at hsize
    simp at hsize

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

theorem squareFree_pairwise_coprime (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise (fun a b => DensePoly.gcd a.factor b.factor = 1) := by
  unfold squareFreeDecomposition squareFreeAux
  exact squareFreeAuxRev_pairwise_coprime_nil
    (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)

theorem squareFree_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f := by
  dsimp [squareFreeDecomposition]
  by_cases hzero : (normalizeMonic f).2.isZero
  · exact normalizeMonic_zero_squareFree_weightedProduct hp f hzero
  · have hnonzero : (normalizeMonic f).2.isZero = false := by
      cases h : (normalizeMonic f).2.isZero <;> simp [h] at hzero ⊢
    rw [squareFreeAux_weightedProduct_nonzero hp (normalizeMonic f).2 hnonzero
      (normalizeMonic_squareFreeContributionReachable hp f)]
    exact normalizeMonic_reconstruct hp f

theorem squareFree_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  unfold squareFreeDecomposition squareFreeAux
  apply squareFreeAuxRev_factors_squareFree hp
  intro sf hsf
  simp at hsf

end FpPoly
end Hex
