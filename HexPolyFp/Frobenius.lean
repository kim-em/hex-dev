/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Degree

public section

/-!
Frobenius-style power maps in `F_p[x]`.

The executable API here computes `X^p mod f` and `X^(p^k) mod f` by
repeated squaring with reduction modulo a monic polynomial, matching the
specialized polynomial layer expected by Berlekamp- and Hensel-style
callers. Modular composition lives separately in `HexPolyFp.ModCompose`.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/--
Exponentiation by squaring in the quotient `F_p[x] / (f)`, reducing after
every multiplication with the executable `DensePoly.modByMonic` routine.
-/
@[expose]
def powModMonicAux
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Nat → FpPoly p → FpPoly p → FpPoly p
  | 0, _, acc => acc
  | n + 1, base, acc =>
      let acc' :=
        if (n + 1) % 2 = 0 then
          acc
        else
          modByMonic f (acc * base) hmonic
      let base' := modByMonic f (base * base) hmonic
      powModMonicAux f hmonic ((n + 1) / 2) base' acc'
termination_by n => n
decreasing_by
  simpa using Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)

/-- Compute `base^n mod f` for monic `f`. -/
@[expose]
def powModMonic (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) :
    FpPoly p :=
  powModMonicAux f hmonic n (modByMonic f base hmonic) 1

/-- The zeroth modular power is `1`. -/
@[simp, grind =] theorem powModMonic_zero
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) :
    powModMonic base f hmonic 0 = 1 := by
  simp [powModMonic, powModMonicAux]

/--
Structurally recursive modular exponentiation. This is intentionally linear in
the exponent: unlike `powModMonic`, it reduces by kernel computation on small
closed terms.
-/
@[expose]
def powModMonicLinear (base f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Nat → FpPoly p
  | 0 => 1
  | n + 1 => modByMonic f (powModMonicLinear base f hmonic n * base) hmonic

/-- Compute `X^p mod f`, the basic Frobenius generator used downstream. -/
@[expose]
def frobeniusXMod (f : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  powModMonic X f hmonic p

/-- Kernel-reducible variant of `frobeniusXMod` for small closed terms. -/
@[expose]
def frobeniusXModLinear (f : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  powModMonicLinear X f hmonic p

/-- Compute `X^(p^k) mod f` for arbitrary `k`. -/
@[expose]
def frobeniusXPowMod (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    FpPoly p :=
  powModMonic X f hmonic (p ^ k)

/-- Kernel-reducible variant of `frobeniusXPowMod` for small closed terms. -/
@[expose]
def frobeniusXPowModLinear (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    FpPoly p :=
  powModMonicLinear X f hmonic (p ^ k)

/-- The zeroth Frobenius power is the canonical representative of `X` modulo `f`. -/
@[simp, grind =] theorem frobeniusXPowMod_zero
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    frobeniusXPowMod f hmonic 0 = modByMonic f X hmonic := by
  simp [frobeniusXPowMod, powModMonic, powModMonicAux, modByMonic,
    DensePoly.modByMonic_eq_mod, DensePoly.mod_mod]

/-! ### Successor step lemma for `frobeniusXPowMod`

The bucket-invariant proof in `HexBerlekamp.DistinctDegree` needs the identity

    `frobeniusXPowMod f hmonic (k + 1) =`
    `  powModMonic (frobeniusXPowMod f hmonic k) f hmonic p`

We derive it from a generic `powModMonic` characterization in terms of
`powLinear`, a right-fold version of polynomial exponentiation, reduced
modulo `f`.  These helpers stay private to this file. -/

private theorem powModMonicAux_zero
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (base acc : FpPoly p) :
    powModMonicAux f hmonic 0 base acc = acc := by
  rw [powModMonicAux.eq_def]

private theorem powModMonicAux_succ_eq
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) (base acc : FpPoly p) :
    powModMonicAux f hmonic (n + 1) base acc =
      powModMonicAux f hmonic ((n + 1) / 2)
        (modByMonic f (base * base) hmonic)
        (if (n + 1) % 2 = 0 then acc else modByMonic f (acc * base) hmonic) := by
  rw [powModMonicAux.eq_def]

/-- `FpPoly.modByMonic` is just the polynomial `%` operator. -/
private theorem modByMonic_eq_mod_swap
    [ZMod64.PrimeModulus p]
    (f g : FpPoly p) (hmonic : DensePoly.Monic f) :
    modByMonic f g hmonic = g % f :=
  DensePoly.modByMonic_eq_mod g f hmonic

private def powLinear (f : FpPoly p) : Nat → FpPoly p
  | 0 => 1
  | n + 1 => powLinear f n * f

private theorem powLinear_succ (f : FpPoly p) (n : Nat) :
    powLinear f (n + 1) = powLinear f n * f := rfl

private theorem powLinear_succ_left (f : FpPoly p) (n : Nat) :
    powLinear f (n + 1) = f * powLinear f n := by
  induction n with
  | zero =>
      change (1 : FpPoly p) * f = f * 1
      rw [one_mul, mul_one]
  | succ n ih =>
      calc powLinear f ((n + 1) + 1)
          = powLinear f (n + 1) * f := rfl
        _ = (f * powLinear f n) * f := by rw [ih]
        _ = f * (powLinear f n * f) := mul_assoc f (powLinear f n) f
        _ = f * powLinear f (n + 1) := rfl

private theorem powLinear_add (f : FpPoly p) (m n : Nat) :
    powLinear f (m + n) = powLinear f m * powLinear f n := by
  induction n with
  | zero =>
      change powLinear f m = powLinear f m * 1
      rw [mul_one]
  | succ n ih =>
      calc powLinear f (m + (n + 1))
          = powLinear f ((m + n) + 1) := by rw [Nat.add_succ]
        _ = powLinear f (m + n) * f := rfl
        _ = (powLinear f m * powLinear f n) * f := by rw [ih]
        _ = powLinear f m * (powLinear f n * f) := mul_assoc _ _ _
        _ = powLinear f m * powLinear f (n + 1) := rfl

private theorem powLinear_double (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n) = powLinear (f * f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      calc powLinear f (2 * (n + 1))
          = powLinear f ((2 * n + 1) + 1) := by rw [h2]
        _ = powLinear f (2 * n + 1) * f := rfl
        _ = (powLinear f (2 * n) * f) * f := rfl
        _ = (powLinear (f * f) n * f) * f := by rw [ih]
        _ = powLinear (f * f) n * (f * f) := mul_assoc _ _ _
        _ = powLinear (f * f) (n + 1) := rfl

private theorem powLinear_double_add_one (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n + 1) = f * powLinear (f * f) n := by
  calc powLinear f (2 * n + 1)
      = powLinear f (2 * n) * f := rfl
    _ = powLinear (f * f) n * f := by rw [powLinear_double]
    _ = f * powLinear (f * f) n := mul_comm _ _

private theorem powLinear_powLinear_mul (f : FpPoly p) (m n : Nat) :
    powLinear (powLinear f n) m = powLinear f (m * n) := by
  induction m with
  | zero =>
      show (1 : FpPoly p) = powLinear f (0 * n)
      rw [Nat.zero_mul]
      rfl
  | succ m ih =>
      calc powLinear (powLinear f n) (m + 1)
          = powLinear (powLinear f n) m * powLinear f n := rfl
        _ = powLinear f (m * n) * powLinear f n := by rw [ih]
        _ = powLinear f (m * n + n) := (powLinear_add f (m * n) n).symm
        _ = powLinear f ((m + 1) * n) := by rw [Nat.succ_mul]

/-- Reducing the base of `powLinear` modulo `f` does not change the result
modulo `f`. -/
private theorem mod_powLinear_mod_eq
    [ZMod64.PrimeModulus p]
    (f base : FpPoly p) (_hmonic : DensePoly.Monic f) (n : Nat) :
    powLinear (base % f) n % f = powLinear base n % f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (powLinear (base % f) n * (base % f)) % f =
        (powLinear base n * base) % f
      rw [DensePoly.DivModLaws.mod_mul_mod (powLinear (base % f) n) (base % f) f,
        ih, DensePoly.mod_mod base f, ← DensePoly.DivModLaws.mod_mul_mod (powLinear base n) base f]

private theorem linearPow_eq_powLinear (f : FpPoly p) (n : Nat) :
    FpPoly.linearPow f n = powLinear f n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [FpPoly.linearPow_succ, powLinear_succ, ih]

/-- `linearPow` has the same canonical remainder for bases with the same
canonical remainder. -/
theorem linearPow_mod_eq_of_mod_eq_mod (f h r : FpPoly p) (n : Nat)
    [ZMod64.PrimeModulus p]
    (hmod : h % f = r % f) :
    FpPoly.linearPow h n % f = FpPoly.linearPow r n % f := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        FpPoly.linearPow h (n + 1) % f
            = (FpPoly.linearPow h n * h) % f := by rw [FpPoly.linearPow_succ]
        _ = ((FpPoly.linearPow h n % f) * (h % f)) % f :=
              @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance
                inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ f
        _ = ((FpPoly.linearPow r n % f) * (r % f)) % f := by rw [ih, hmod]
        _ = (FpPoly.linearPow r n * r) % f :=
              (@DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance
                inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ f).symm
        _ = FpPoly.linearPow r (n + 1) % f := by rw [FpPoly.linearPow_succ]

/-- The structural power loop computes the same remainder as `powLinear`. -/
private theorem powModMonicLinear_mod_eq
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) :
    (powModMonicLinear base f hmonic n) % f = (powLinear base n) % f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (modByMonic f (powModMonicLinear base f hmonic n * base) hmonic) % f =
        (powLinear base n * base) % f
      rw [show modByMonic f (powModMonicLinear base f hmonic n * base) hmonic =
            (powModMonicLinear base f hmonic n * base) % f from
          DensePoly.modByMonic_eq_mod _ _ hmonic]
      rw [DensePoly.mod_mod,
        DensePoly.DivModLaws.mod_mul_mod (powModMonicLinear base f hmonic n) base f, ih,
        ← DensePoly.DivModLaws.mod_mul_mod (powLinear base n) base f]

/-- Positive structural powers are already reduced modulo the monic modulus. -/
private theorem powModMonicLinear_pos_self_mod
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) (hn : 0 < n) :
    (powModMonicLinear base f hmonic n) % f = powModMonicLinear base f hmonic n := by
  cases n with
  | zero => cases hn
  | succ n =>
      change (modByMonic f (powModMonicLinear base f hmonic n * base) hmonic) % f =
        modByMonic f (powModMonicLinear base f hmonic n * base) hmonic
      rw [show modByMonic f (powModMonicLinear base f hmonic n * base) hmonic =
            (powModMonicLinear base f hmonic n * base) % f from
          DensePoly.modByMonic_eq_mod _ _ hmonic]
      rw [DensePoly.mod_mod]

/-- Loop invariant for `powModMonicAux`: `acc * base^k` modulo `f`. -/
private theorem powModMonicAux_mod_eq
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ (k : Nat) (base acc : FpPoly p),
      (powModMonicAux f hmonic k base acc) % f = (acc * powLinear base k) % f := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro base acc
    cases k with
    | zero =>
        rw [powModMonicAux_zero]
        show acc % f = (acc * powLinear base 0) % f
        change acc % f = (acc * (1 : FpPoly p)) % f
        rw [mul_one]
    | succ m =>
        have hlt : (m + 1) / 2 < m + 1 :=
          Nat.div_lt_self (Nat.succ_pos m) (by decide)
        rw [powModMonicAux_succ_eq, ih ((m + 1) / 2) hlt]
        rw [show modByMonic f (base * base) hmonic = (base * base) % f from
              DensePoly.modByMonic_eq_mod _ _ hmonic]
        rcases Nat.mod_two_eq_zero_or_one (m + 1) with hmod | hmod
        · -- (m + 1) is even
          rw [if_pos hmod]
          have hk : 2 * ((m + 1) / 2) = m + 1 := by
            have h := Nat.mod_add_div (m + 1) 2
            omega
          calc (acc * powLinear ((base * base) % f) ((m + 1) / 2)) % f
              = (acc % f *
                  (powLinear ((base * base) % f) ((m + 1) / 2) % f)) % f := by
                  rw [DensePoly.DivModLaws.mod_mul_mod acc
                        (powLinear ((base * base) % f) ((m + 1) / 2)) f]
            _ = (acc % f *
                  (powLinear (base * base) ((m + 1) / 2) % f)) % f := by
                  rw [mod_powLinear_mod_eq f (base * base) hmonic ((m + 1) / 2)]
            _ = (acc * powLinear (base * base) ((m + 1) / 2)) % f := by
                  rw [← DensePoly.DivModLaws.mod_mul_mod acc
                        (powLinear (base * base) ((m + 1) / 2)) f]
            _ = (acc * powLinear base (2 * ((m + 1) / 2))) % f := by
                  rw [powLinear_double]
            _ = (acc * powLinear base (m + 1)) % f := by rw [hk]
        · -- (m + 1) is odd
          rw [if_neg (by omega)]
          rw [show modByMonic f (acc * base) hmonic = (acc * base) % f from
                DensePoly.modByMonic_eq_mod _ _ hmonic]
          have hk : 2 * ((m + 1) / 2) + 1 = m + 1 := by
            have h := Nat.mod_add_div (m + 1) 2
            omega
          calc ((acc * base) % f *
                  powLinear ((base * base) % f) ((m + 1) / 2)) % f
              = ((acc * base) % f *
                  (powLinear ((base * base) % f) ((m + 1) / 2) % f)) % f := by
                  rw [DensePoly.DivModLaws.mod_mul_mod ((acc * base) % f)
                        (powLinear ((base * base) % f) ((m + 1) / 2)) f]
                  rw [DensePoly.mod_mod (acc * base) f]
            _ = ((acc * base) % f *
                  (powLinear (base * base) ((m + 1) / 2) % f)) % f := by
                  rw [mod_powLinear_mod_eq f (base * base) hmonic ((m + 1) / 2)]
            _ = ((acc * base) *
                  powLinear (base * base) ((m + 1) / 2)) % f := by
                  rw [← DensePoly.DivModLaws.mod_mul_mod (acc * base)
                        (powLinear (base * base) ((m + 1) / 2)) f]
            _ = (acc * (base * powLinear (base * base) ((m + 1) / 2))) % f := by
                  rw [mul_assoc]
            _ = (acc * powLinear base (2 * ((m + 1) / 2) + 1)) % f := by
                  rw [powLinear_double_add_one]
            _ = (acc * powLinear base (m + 1)) % f := by rw [hk]

/-- For positive fuel, the auxiliary loop's output is already reduced. -/
private theorem powModMonicAux_pos_self_mod
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    ∀ (n : Nat), 0 < n → ∀ (base acc : FpPoly p),
      (powModMonicAux f hmonic n base acc) % f =
        powModMonicAux f hmonic n base acc := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hpos base acc
    match n, hpos with
    | k + 1, _ =>
        rw [powModMonicAux_succ_eq]
        rcases Nat.eq_zero_or_pos ((k + 1) / 2) with h0 | hpos2
        · -- The next call has fuel 0, so it returns its acc'.
          rw [h0, powModMonicAux_zero]
          have hkz : k = 0 := by
            have h := Nat.mod_add_div (k + 1) 2
            omega
          subst hkz
          rw [if_neg (by decide : ¬ ((1 : Nat)) % 2 = 0)]
          rw [modByMonic_eq_mod_swap f (acc * base) hmonic,
              DensePoly.mod_mod (acc * base) f]
        · -- Recurse via IH with strictly smaller fuel.
          have hlt : (k + 1) / 2 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos k) (by decide)
          exact ih ((k + 1) / 2) hlt hpos2 _ _

/-- For a positive exponent, `powModMonic` returns an already-reduced value. -/
theorem powModMonic_pos_self_mod
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) (hn : 0 < n) :
    (powModMonic base f hmonic n) % f = powModMonic base f hmonic n := by
  unfold powModMonic
  exact powModMonicAux_pos_self_mod f hmonic n hn _ _

/--
The `modByMonic` spelling of `powModMonic_pos_self_mod`, useful for callers
working entirely with the executable monic-reduction API.
-/
@[simp, grind =] theorem modByMonic_powModMonic_pos_eq_self
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) (hn : 0 < n) :
    modByMonic f (powModMonic base f hmonic n) hmonic =
      powModMonic base f hmonic n := by
  rw [modByMonic, DensePoly.modByMonic_eq_mod]
  exact powModMonic_pos_self_mod base f hmonic n hn

/-- `powModMonic` characterization in terms of `powLinear` mod `f`. -/
private theorem powModMonic_mod_eq
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) :
    (powModMonic base f hmonic n) % f = (powLinear base n) % f := by
  unfold powModMonic
  rw [powModMonicAux_mod_eq f hmonic n (modByMonic f base hmonic) 1]
  rw [show modByMonic f base hmonic = base % f from
        DensePoly.modByMonic_eq_mod _ _ hmonic]
  rw [one_mul, mod_powLinear_mod_eq f base hmonic n]

/-- `powModMonic` computes the same residue as `linearPow`. -/
theorem powModMonic_mod_eq_linearPow
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) :
    (powModMonic base f hmonic n) % f = (linearPow base n) % f := by
  rw [powModMonic_mod_eq, linearPow_eq_powLinear]

/--
The kernel-reducible linear exponentiation path agrees with the production
square-and-multiply implementation. It is intentionally not a global simp rule:
some conformance proofs unfold the linear evaluator to get kernel-reduced closed
terms.
-/
theorem powModMonicLinear_eq_powModMonic
    [ZMod64.PrimeModulus p]
    (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) :
    powModMonicLinear base f hmonic n = powModMonic base f hmonic n := by
  cases n with
  | zero =>
      simp [powModMonicLinear, powModMonic, powModMonicAux]
  | succ n =>
      have hlinear_self :
          (powModMonicLinear base f hmonic (n + 1)) % f =
            powModMonicLinear base f hmonic (n + 1) :=
        powModMonicLinear_pos_self_mod base f hmonic (n + 1) (Nat.succ_pos n)
      have hpow_self :
          (powModMonic base f hmonic (n + 1)) % f =
            powModMonic base f hmonic (n + 1) :=
        powModMonic_pos_self_mod base f hmonic (n + 1) (Nat.succ_pos n)
      calc
        powModMonicLinear base f hmonic (n + 1)
            = (powModMonicLinear base f hmonic (n + 1)) % f := hlinear_self.symm
        _ = (powLinear base (n + 1)) % f :=
            powModMonicLinear_mod_eq base f hmonic (n + 1)
        _ = (powModMonic base f hmonic (n + 1)) % f :=
            (powModMonic_mod_eq base f hmonic (n + 1)).symm
        _ = powModMonic base f hmonic (n + 1) := hpow_self

/--
The kernel-reducible `X^p mod f` evaluator agrees with the production
Frobenius generator.
-/
theorem frobeniusXModLinear_eq_frobeniusXMod
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    frobeniusXModLinear f hmonic = frobeniusXMod f hmonic := by
  exact powModMonicLinear_eq_powModMonic X f hmonic p

/--
The kernel-reducible `X^(p^k) mod f` evaluator agrees with the production
Frobenius power routine.
-/
theorem frobeniusXPowModLinear_eq_frobeniusXPowMod
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    frobeniusXPowModLinear f hmonic k = frobeniusXPowMod f hmonic k := by
  exact powModMonicLinear_eq_powModMonic X f hmonic (p ^ k)

/-- The basic Frobenius generator is the first indexed Frobenius power. -/
theorem frobeniusXMod_eq_frobeniusXPowMod_one
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    frobeniusXMod f hmonic =
      frobeniusXPowMod f hmonic 1 := by
  unfold frobeniusXMod frobeniusXPowMod
  rw [Nat.pow_one]

/-- `frobeniusXMod` outputs an already-reduced polynomial. -/
@[simp, grind =] theorem frobeniusXMod_mod_self
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    (frobeniusXMod f hmonic) % f = frobeniusXMod f hmonic := by
  unfold frobeniusXMod
  have hp_pos : 0 < p := by
    have h2 : 2 ≤ p := Hex.Nat.Prime.two_le ZMod64.PrimeModulus.prime
    omega
  exact powModMonic_pos_self_mod X f hmonic p hp_pos

/-- The `modByMonic` spelling of `frobeniusXMod_mod_self`. -/
@[simp, grind =] theorem modByMonic_frobeniusXMod_eq_self
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    modByMonic f (frobeniusXMod f hmonic) hmonic = frobeniusXMod f hmonic := by
  rw [modByMonic, DensePoly.modByMonic_eq_mod]
  exact frobeniusXMod_mod_self f hmonic

/-- Successor step for `frobeniusXPowMod`: raising the previous Frobenius
image to the `p`-th power (mod `f`) advances the index by one. -/
theorem frobeniusXPowMod_succ
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    frobeniusXPowMod f hmonic (k + 1) =
      powModMonic (frobeniusXPowMod f hmonic k) f hmonic p := by
  have hp_pos : 0 < p := by
    have h2 : 2 ≤ p := Hex.Nat.Prime.two_le ZMod64.PrimeModulus.prime
    omega
  have hLHS : (frobeniusXPowMod f hmonic (k + 1)) % f =
      frobeniusXPowMod f hmonic (k + 1) := by
    unfold frobeniusXPowMod
    apply powModMonic_pos_self_mod
    exact Nat.pow_pos hp_pos
  have hRHS : (powModMonic (frobeniusXPowMod f hmonic k) f hmonic p) % f =
      powModMonic (frobeniusXPowMod f hmonic k) f hmonic p :=
    powModMonic_pos_self_mod _ _ hmonic _ hp_pos
  rw [← hLHS, ← hRHS]
  unfold frobeniusXPowMod
  rw [powModMonic_mod_eq, powModMonic_mod_eq]
  have hbridge :
      (powLinear (powModMonic X f hmonic (p ^ k)) p) % f =
        (powLinear (powLinear X (p ^ k)) p) % f := by
    have hmod : (powModMonic X f hmonic (p ^ k)) % f =
        (powLinear X (p ^ k)) % f := powModMonic_mod_eq X f hmonic (p ^ k)
    calc (powLinear (powModMonic X f hmonic (p ^ k)) p) % f
        = (powLinear ((powModMonic X f hmonic (p ^ k)) % f) p) % f := by
            rw [mod_powLinear_mod_eq f (powModMonic X f hmonic (p ^ k)) hmonic p]
      _ = (powLinear ((powLinear X (p ^ k)) % f) p) % f := by rw [hmod]
      _ = (powLinear (powLinear X (p ^ k)) p) % f := by
            rw [mod_powLinear_mod_eq f (powLinear X (p ^ k)) hmonic p]
  rw [hbridge, powLinear_powLinear_mul]
  -- Goal: `powLinear X (p^(k+1)) % f = powLinear X (p * p^k) % f`.
  rw [show (p : Nat) * p ^ k = p ^ (k + 1) from by
        rw [Nat.pow_succ]; exact Nat.mul_comm _ _]

/-! ### Reduction to the absolute monomial

Connect `frobeniusXPowMod` to the absolute polynomial `X^(p^k)` via
`monomial (p^k) 1`, modulo `f`. This is consumed by the project-side
Rabin soundness proof in `HexBerlekamp.RabinSoundness`. -/

private theorem powLinear_X_eq_monomial (n : Nat) :
    powLinear (FpPoly.X (p := p)) n = DensePoly.monomial n (1 : ZMod64 p) := by
  induction n with
  | zero =>
      show (1 : FpPoly p) = DensePoly.monomial 0 (1 : ZMod64 p)
      apply DensePoly.ext_coeff
      intro i
      show (DensePoly.C (1 : ZMod64 p)).coeff i =
        (DensePoly.monomial 0 (1 : ZMod64 p)).coeff i
      rw [DensePoly.coeff_C, DensePoly.coeff_monomial]
  | succ n ih =>
      have hX : (FpPoly.X (p := p)) = DensePoly.monomial 1 (1 : ZMod64 p) := rfl
      rw [powLinear_succ, ih, hX]
      have hmm := DensePoly.monomial_mul_monomial (S := ZMod64 p) n 1 (1 : ZMod64 p) 1
      have h1 : ((1 : ZMod64 p) * 1) = 1 := by grind
      rw [h1] at hmm
      exact hmm

/--
`frobeniusXPowMod f hmonic k` reduces modulo `f` to the absolute monomial
`X^(p^k)` reduced modulo `f`. This is the key identity relating the executable
Frobenius computation to the absolute polynomial it represents.
-/
theorem frobeniusXPowMod_mod_eq_monomial_mod
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    (frobeniusXPowMod f hmonic k) % f =
      (DensePoly.monomial (p ^ k) (1 : ZMod64 p)) % f := by
  unfold frobeniusXPowMod
  rw [powModMonic_mod_eq, powLinear_X_eq_monomial]

/-- `frobeniusXPowMod` outputs an already-reduced polynomial. -/
@[simp, grind =] theorem frobeniusXPowMod_mod_self
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    (frobeniusXPowMod f hmonic k) % f = frobeniusXPowMod f hmonic k := by
  have hp_pos : 0 < p := by
    have h2 : 2 ≤ p := Hex.Nat.Prime.two_le ZMod64.PrimeModulus.prime
    omega
  unfold frobeniusXPowMod
  exact powModMonic_pos_self_mod _ _ hmonic _ (Nat.pow_pos hp_pos)

/-- The `modByMonic` spelling of `frobeniusXPowMod_mod_self`. -/
@[simp, grind =] theorem modByMonic_frobeniusXPowMod_eq_self
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    modByMonic f (frobeniusXPowMod f hmonic k) hmonic =
      frobeniusXPowMod f hmonic k := by
  rw [modByMonic, DensePoly.modByMonic_eq_mod]
  exact frobeniusXPowMod_mod_self f hmonic k

end FpPoly
end Hex
