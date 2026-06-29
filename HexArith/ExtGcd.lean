/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
Extended GCD algorithms and specifications.

This module defines pure-`Nat`, `Int`, and `UInt64` extended-GCD
operations together with the core gcd and Bezout-certificate theorems
used by the arithmetic library.
-/

namespace HexArith

/--
Quotient/remainder pairing used by `extGcd`.

Lean 4.30's stdlib exposes `Nat.div` and `Nat.mod`, but not a public fused
`Nat.divMod`; keep the pairing local so the Euclidean step can switch to a
fused primitive once one is available.
-/
@[expose]
def natDivMod (a b : Nat) : Nat × Nat :=
  (a / b, a % b)

/--
Pure natural-number extended GCD.

`HexArith.extGcd a b` returns `(g, s, t)` with `g = Nat.gcd a b` and
`s * a + t * b = g` after coercing the inputs to `Int`. Use
`HexArith.Int.extGcd` for the GMP-backed integer API and
`HexArith.UInt64.extGcd` for machine-word inputs.
-/
@[expose]
def extGcd (a b : Nat) : Nat × Int × Int :=
  if hb : b = 0 then
    (a, 1, 0)
  else
    let _ := hb
    let qr := natDivMod a b
    let (g, s, t) := extGcd b qr.2
    (g, t, s - t * Int.ofNat qr.1)
termination_by b
decreasing_by
  simp_wf
  simpa [natDivMod] using (Nat.mod_lt a (Nat.pos_iff_ne_zero.2 hb))

/-- Integer form of `Nat.mod_add_div`, matching the Bezout-step algebra. -/
private theorem int_ofNat_mod_add_div (a b : Nat) :
    ((a % b : Nat) : Int) + ((a / b : Nat) : Int) * (b : Int) = (a : Int) := by
  have h := Nat.mod_add_div a b
  rw [Nat.mul_comm] at h
  exact_mod_cast h

/--
One Euclidean unwind step for the natural-number Bezout certificate.

If the recursive call proves a linear combination for `(b, r)`, this rewrites
it into the corresponding certificate for `(a, b)` using `a = r + q * b`.
-/
private theorem extGcd_bezout_step
    (a b q r : Nat) (s t g : Int)
    (hqr : ((r : Nat) : Int) + ((q : Nat) : Int) * (b : Int) = (a : Int))
    (hrec : s * (b : Int) + t * (r : Int) = g) :
    t * (a : Int) + (s - t * (q : Int)) * (b : Int) = g := by
  rw [← hqr]
  calc
    t * (((r : Nat) : Int) + ((q : Nat) : Int) * (b : Int)) +
        (s - t * (q : Int)) * (b : Int)
        = s * (b : Int) + t * (r : Int) := by
          simp only [Int.mul_add, Int.sub_mul, Int.mul_assoc]
          omega
    _ = g := hrec

/--
The gcd component returned by the pure `Nat` extended-GCD algorithm is
Lean's `Nat.gcd`.
-/
@[simp, grind =] theorem extGcd_fst (a b : Nat) : (extGcd a b).1 = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
      rw [extGcd]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, ↓reduceDIte, natDivMod]
        have hrec :
            (extGcd b (a % b)).1 = Nat.gcd b (a % b) :=
          ih (a % b) (Nat.mod_lt a (Nat.pos_iff_ne_zero.2 hb)) b
        have hgcd : Nat.gcd b (a % b) = Nat.gcd a b := by
          rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a % b) b]
        exact hrec.trans hgcd

/--
The coefficient components returned by the pure `Nat` extended-GCD algorithm
form a Bezout certificate for the inputs.
-/
@[simp] theorem extGcd_bezout (a b : Nat) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
      rw [extGcd]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, ↓reduceDIte, natDivMod]
        have hrec :
            let (g, s, t) := extGcd b (a % b)
            s * (b : Int) + t * ((a % b : Nat) : Int) = g :=
          ih (a % b) (Nat.mod_lt a (Nat.pos_iff_ne_zero.2 hb)) b
        rcases hstep : extGcd b (a % b) with ⟨g, s, t⟩
        simp [hstep] at hrec
        exact extGcd_bezout_step a b (a / b) (a % b) s t g
          (int_ofNat_mod_add_div a b) hrec

/--
Bezout certificate for the pure `Nat` `extGcd`, stated on the returned
triple's projections: the cofactors `s = (extGcd a b).2.1` and
`t = (extGcd a b).2.2` satisfy `s * a + t * b = (extGcd a b).1` after
coercing `a` and `b` to `Int`. The `_proj` form keeps the right-hand side
as the routine's own returned gcd component; see `extGcd_bezout_gcd` for
the variant phrased against `Nat.gcd a b`.
-/
@[simp, grind =] theorem extGcd_bezout_proj (a b : Nat) :
    (extGcd a b).2.1 * (a : Int) + (extGcd a b).2.2 * (b : Int) =
      (extGcd a b).1 := by
  simpa using extGcd_bezout a b

/--
Bezout certificate for the pure `Nat` `extGcd` with the gcd resolved to
`Nat.gcd a b`: the returned cofactors satisfy `s * a + t * b = Nat.gcd a b`
over `Int`. Same identity as `extGcd_bezout_proj`, with the right-hand side
rewritten through `extGcd_fst`.
-/
@[simp, grind =] theorem extGcd_bezout_gcd (a b : Nat) :
    (extGcd a b).2.1 * (a : Int) + (extGcd a b).2.2 * (b : Int) =
      Nat.gcd a b := by
  rw [extGcd_bezout_proj, extGcd_fst]

/--
Combined correctness theorem for `extGcd`.

Use this when a caller needs both the gcd projection and the Bezout
certificate after destructuring the returned triple.
-/
@[simp] theorem extGcd_spec (a b : Nat) :
    let (g, s, t) := extGcd a b
    g = Nat.gcd a b ∧ s * a + t * b = g := by
  rcases h : extGcd a b with ⟨g, s, t⟩
  have hfst := extGcd_fst a b
  have hbez := extGcd_bezout a b
  simp [h] at hfst hbez
  exact ⟨hfst, hbez⟩

end HexArith

namespace Hex

/--
Pure Lean reference implementation of extended GCD over integers.

This runs the Euclidean algorithm directly on `Int`, carrying Bezout
coefficients through the usual quotient/remainder updates.
-/
@[expose]
def pureIntExtGcd.go (old_r r old_s s old_t t : Int) : Nat × Int × Int :=
  match r with
  | 0 =>
      if old_r < 0 then
        (old_r.natAbs, -old_s, -old_t)
      else
        (old_r.natAbs, old_s, old_t)
  | .ofNat (n + 1) =>
      let q := old_r / Int.ofNat (n + 1)
      pureIntExtGcd.go (Int.ofNat (n + 1)) (old_r % Int.ofNat (n + 1))
        s (old_s - q * s) t (old_t - q * t)
  | .negSucc n =>
      let r := Int.negSucc n
      let q := old_r / r
      pureIntExtGcd.go r (old_r % r) s (old_s - q * s) t (old_t - q * t)
termination_by r.natAbs
decreasing_by
  · have hmod_nonneg : 0 ≤ old_r % Int.ofNat (n + 1) := by
      exact Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero _))
    have hpos : (0 : Int) < Int.ofNat (n + 1) := by
      exact Int.ofNat_lt.mpr (Nat.succ_pos _)
    have hmod_lt : old_r % Int.ofNat (n + 1) < Int.ofNat (n + 1) := by
      exact Int.emod_lt_of_pos _ hpos
    have hnatAbs_lt :
        ((old_r % Int.ofNat (n + 1)).natAbs : Int) < (Int.ofNat (n + 1)).natAbs := by
      rw [Int.ofNat_natAbs_of_nonneg hmod_nonneg]
      omega
    exact Int.ofNat_lt.mp hnatAbs_lt
  · have hmod_nonneg : 0 ≤ old_r % Int.negSucc n := by
      exact Int.emod_nonneg _ (by simp)
    have hpos : (0 : Int) < Int.ofNat (n + 1) := by
      exact Int.ofNat_lt.mpr (Nat.succ_pos _)
    have hmod_lt : old_r % Int.negSucc n < Int.ofNat (n + 1) := by
      simpa [Int.negSucc_eq, Int.emod_neg] using (Int.emod_lt_of_pos old_r hpos)
    have hnatAbs_lt :
        ((old_r % Int.negSucc n).natAbs : Int) < (Int.negSucc n).natAbs := by
      rw [Int.ofNat_natAbs_of_nonneg hmod_nonneg, Int.natAbs_negSucc]
      exact hmod_lt
    exact Int.ofNat_lt.mp hnatAbs_lt

/--
Pure Lean integer extended GCD.

`Hex.pureIntExtGcd` is the proof reference and portable fallback for
`HexArith.Int.extGcd`; callers that want the project public integer API should
use `HexArith.Int.extGcd` instead.
-/
@[expose]
def pureIntExtGcd (a b : Int) : Nat × Int × Int :=
  pureIntExtGcd.go a b 1 0 0 1

/-- Remainder step for the gcd component of the pure integer algorithm. -/
private theorem pureIntExtGcd_gcd_step (a b : Int) :
    Int.gcd b (a % b) = Int.gcd a b := by
  rw [← Int.ediv_mul_add_emod a b]
  simp [Int.gcd_comm]

/--
One Euclidean update for the integer Bezout coefficients.

The loop invariant stores two linear combinations, one for `old_r` and one for
`r`; subtracting `q` times the second row gives the invariant for `old_r % r`.
-/
private theorem pureIntExtGcd_linear_step
    (old_r r old_s s old_t t a b q : Int)
    (hold : old_s * a + old_t * b = old_r)
    (hr : s * a + t * b = r)
    (hq : q = old_r / r) :
    (old_s - q * s) * a + (old_t - q * t) * b = old_r % r := by
  have hdiv : old_r / r * r + old_r % r = old_r := Int.ediv_mul_add_emod old_r r
  calc
    (old_s - q * s) * a + (old_t - q * t) * b =
        (old_s * a + old_t * b) - q * (s * a + t * b) := by
          simp only [Int.sub_mul, Int.mul_add, Int.mul_assoc]
          omega
    _ = old_r - (old_r / r) * r := by
          rw [hold, hr, hq]
    _ = old_r % r := by
          omega

/--
Loop invariant for `pureIntExtGcd.go`.

The accumulator rows encode linear combinations of the original inputs `a` and
`b`; the result normalizes the gcd to a natural number while preserving the
returned Bezout certificate.
-/
private theorem pureIntExtGcd_go_spec
    (old_r r old_s s old_t t a b : Int)
    (hold : old_s * a + old_t * b = old_r)
    (hr : s * a + t * b = r) :
    let (g, u, v) := pureIntExtGcd.go old_r r old_s s old_t t
    g = Int.gcd old_r r ∧ u * a + v * b = g := by
  induction hmeasure : r.natAbs using Nat.strongRecOn generalizing old_r r old_s s old_t t with
  | ind n ih =>
      cases r with
      | ofNat m =>
          cases m with
          | zero =>
              by_cases hneg : old_r < 0
              · have hneg_coeff :
                    (-old_s) * a + (-old_t) * b = (old_r.natAbs : Int) := by
                  have hnat : (old_r.natAbs : Int) = -old_r := by
                    rw [← Int.natAbs_neg old_r]
                    exact Int.ofNat_natAbs_of_nonneg (by omega)
                  calc
                    (-old_s) * a + (-old_t) * b = -(old_s * a + old_t * b) := by
                      simp only [Int.neg_mul, Int.neg_add]
                    _ = -old_r := by rw [hold]
                    _ = (old_r.natAbs : Int) := hnat.symm
                simp [pureIntExtGcd.go, hneg, hneg_coeff]
              · have hnonneg : 0 ≤ old_r := by omega
                have hcoeff : old_s * a + old_t * b = (old_r.natAbs : Int) := by
                  rw [Int.ofNat_natAbs_of_nonneg hnonneg]
                  exact hold
                simp [pureIntExtGcd.go, hneg, hcoeff]
          | succ m =>
              simp only [pureIntExtGcd.go]
              let r' : Int := Int.ofNat (m + 1)
              let q := old_r / r'
              have hlt : (old_r % r').natAbs < r'.natAbs := by
                have hmod_nonneg : 0 ≤ old_r % r' := by
                  exact Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero _))
                have hpos : (0 : Int) < r' := by
                  exact Int.ofNat_lt.mpr (Nat.succ_pos _)
                have hmod_lt : old_r % r' < r' := by
                  exact Int.emod_lt_of_pos _ hpos
                have hnatAbs_lt : ((old_r % r').natAbs : Int) < r'.natAbs := by
                  rw [Int.ofNat_natAbs_of_nonneg hmod_nonneg]
                  omega
                exact Int.ofNat_lt.mp hnatAbs_lt
              have hn : r'.natAbs = n := by
                simpa [r'] using hmeasure
              have hrec := ih (old_r % r').natAbs (by simpa [hn] using hlt)
                r' (old_r % r') s (old_s - q * s) t (old_t - q * t)
                (by simpa [r'] using hr)
                (pureIntExtGcd_linear_step old_r r' old_s s old_t t a b q
                  hold (by simpa [r'] using hr) rfl)
                rfl
              exact ⟨hrec.1.trans (pureIntExtGcd_gcd_step old_r r'), hrec.2⟩
      | negSucc m =>
          simp only [pureIntExtGcd.go]
          let r' : Int := Int.negSucc m
          let q := old_r / r'
          have hlt : (old_r % r').natAbs < r'.natAbs := by
            have hmod_nonneg : 0 ≤ old_r % r' := by
              exact Int.emod_nonneg _ (by simp [r'])
            have hpos : (0 : Int) < Int.ofNat (m + 1) := by
              exact Int.ofNat_lt.mpr (Nat.succ_pos _)
            have hmod_lt : old_r % r' < Int.ofNat (m + 1) := by
              simpa [r', Int.negSucc_eq, Int.emod_neg] using
                (Int.emod_lt_of_pos old_r hpos)
            have hnatAbs_lt : ((old_r % r').natAbs : Int) < r'.natAbs := by
              rw [Int.ofNat_natAbs_of_nonneg hmod_nonneg, Int.natAbs_negSucc]
              exact hmod_lt
            exact Int.ofNat_lt.mp hnatAbs_lt
          have hn : r'.natAbs = n := by
            simpa [r'] using hmeasure
          have hrec := ih (old_r % r').natAbs (by simpa [hn] using hlt)
            r' (old_r % r') s (old_s - q * s) t (old_t - q * t)
            (by simpa [r'] using hr)
            (pureIntExtGcd_linear_step old_r r' old_s s old_t t a b q
              hold (by simpa [r'] using hr) rfl)
            rfl
          exact ⟨hrec.1.trans (pureIntExtGcd_gcd_step old_r r'), hrec.2⟩

/--
The gcd component returned by the pure integer reference implementation is
Lean's `Int.gcd`.
-/
@[simp, grind =] theorem pureIntExtGcd_fst (a b : Int) :
    (pureIntExtGcd a b).1 = Int.gcd a b := by
  have hspec := pureIntExtGcd_go_spec a b 1 0 0 1 a b (by omega) (by omega)
  simpa [pureIntExtGcd] using hspec.1

/--
The coefficient components returned by the pure integer reference
implementation form a Bezout certificate for the inputs.
-/
@[simp] theorem pureIntExtGcd_bezout (a b : Int) :
    let (g, s, t) := pureIntExtGcd a b
    s * a + t * b = g := by
  have hspec := pureIntExtGcd_go_spec a b 1 0 0 1 a b (by omega) (by omega)
  simpa [pureIntExtGcd] using hspec.2

/--
Bezout certificate for the pure integer reference `pureIntExtGcd`, stated on
the returned triple's projections: the cofactors `(pureIntExtGcd a b).2.1`
and `(pureIntExtGcd a b).2.2` satisfy `s * a + t * b = (pureIntExtGcd a b).1`.
Inputs are already `Int`, so no coercion is involved.
-/
@[simp, grind =] theorem pureIntExtGcd_bezout_proj (a b : Int) :
    (pureIntExtGcd a b).2.1 * a + (pureIntExtGcd a b).2.2 * b =
      (pureIntExtGcd a b).1 := by
  simpa using pureIntExtGcd_bezout a b

/--
Combined correctness theorem for the pure integer reference implementation.

Use this when a proof needs both the gcd projection and the Bezout certificate
without unfolding the recursive reference implementation.
-/
@[simp] theorem pureIntExtGcd_spec (a b : Int) :
    let (g, s, t) := pureIntExtGcd a b
    g = Int.gcd a b ∧ s * a + t * b = g := by
  rcases h : pureIntExtGcd a b with ⟨g, s, t⟩
  have hfst := pureIntExtGcd_fst a b
  have hbez := pureIntExtGcd_bezout a b
  simp [h] at hfst hbez
  exact ⟨hfst, hbez⟩

end Hex

namespace HexArith

namespace Int

/--
Public extended GCD on integers.

Trusted runtime contract: the `lean_hex_mpz_gcdext` attachment may replace this
pure Lean reference with a GMP-backed implementation that returns the same
`(g, s, t)` triple, where `g = Int.gcd a b` and `s * a + t * b = g`.
-/
@[expose, extern "lean_hex_mpz_gcdext"]
def extGcd (a b : @& Int) : Nat × Int × Int :=
  Hex.pureIntExtGcd a b

/--
The gcd component returned by the public integer extended-GCD API is Lean's
`Int.gcd`.
-/
@[simp, grind =] theorem extGcd_fst (a b : Int) : (extGcd a b).1 = Int.gcd a b := by
  simp [extGcd]

/--
The coefficient components returned by the public integer extended-GCD API
form a Bezout certificate for the inputs.
-/
@[simp] theorem extGcd_bezout (a b : Int) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g := by
  simp [extGcd]

/--
Projection form of the integer Bezout certificate: the coefficient components,
addressed directly as `(extGcd a b).2.1` and `(extGcd a b).2.2`, combine to the
returned gcd component `(extGcd a b).1`. Lets callers rewrite a Bezout identity
without first destructuring the `(g, s, t)` triple.
-/
@[simp, grind =] theorem extGcd_bezout_proj (a b : Int) :
    (extGcd a b).2.1 * a + (extGcd a b).2.2 * b =
      (extGcd a b).1 := by
  simpa using extGcd_bezout a b

/--
Bezout certificate stated against `Int.gcd a b` directly: the coefficient
projections combine to the canonical gcd rather than the returned `(extGcd a b).1`
component. Lets callers rewrite a Bezout identity straight to `Int.gcd`, skipping
the intermediate `extGcd_fst` step.
-/
@[simp, grind =] theorem extGcd_bezout_gcd (a b : Int) :
    (extGcd a b).2.1 * a + (extGcd a b).2.2 * b =
      Int.gcd a b := by
  rw [extGcd_bezout_proj, extGcd_fst]

/--
Combined correctness theorem for the GMP-backed integer extended GCD surface.

The executable may run through the `mpz_gcdext` extern, while this theorem
characterises the same public triple used by proofs.
-/
@[simp] theorem extGcd_spec (a b : Int) :
    let (g, s, t) := extGcd a b
    g = Int.gcd a b ∧ s * a + t * b = g := by
  rcases h : extGcd a b with ⟨g, s, t⟩
  have hfst := extGcd_fst a b
  have hbez := extGcd_bezout a b
  simp [h] at hfst hbez
  exact ⟨hfst, hbez⟩

/--
The integer extended-GCD API agrees with `Nat.gcd` on nonnegative inputs.
-/
@[simp, grind =] theorem extGcd_fst_ofNat (a b : Nat) :
    (extGcd (Int.ofNat a) (Int.ofNat b)).1 = Nat.gcd a b := by
  simp [Int.gcd]

/--
Combined correctness theorem for the integer extended-GCD API specialised to
nonnegative inputs.
-/
@[simp] theorem extGcd_spec_ofNat (a b : Nat) :
    let (g, s, t) := extGcd (Int.ofNat a) (Int.ofNat b)
    g = Nat.gcd a b ∧ s * Int.ofNat a + t * Int.ofNat b = g := by
  rcases h : extGcd (Int.ofNat a) (Int.ofNat b) with ⟨g, s, t⟩
  have hspec := extGcd_spec (Int.ofNat a) (Int.ofNat b)
  rw [h] at hspec
  simpa [Int.gcd] using hspec

/--
For a positive natural modulus, the Bezout coefficient of the zero input in
`Int.extGcd 0 p` is zero.
-/
theorem extGcd_zero_left_s_ofNat (p : Nat) (hp : 0 < p) :
    (extGcd 0 (Int.ofNat p)).2.1 = 0 := by
  cases p with
  | zero =>
      omega
  | succ p =>
      simp [extGcd, Hex.pureIntExtGcd]
      rw [show (↑p + 1 : Int) = Int.ofNat (p + 1) by simp]
      rw [Hex.pureIntExtGcd.go.eq_def]
      simp
      rw [Hex.pureIntExtGcd.go.eq_def]
      simp [show ¬ (↑p + 1 : Int) < 0 by omega]

end Int

namespace UInt64

/--
Extended GCD on machine words.

The input words are interpreted by their natural representatives. The gcd is
returned as a `UInt64`, while the Bezout coefficients remain signed integers so
the certificate can be stated over `Int.ofNat a.toNat` and `Int.ofNat b.toNat`.
-/
@[expose]
def extGcd (a b : UInt64) : UInt64 × Int × Int :=
  let (g, s, t) := HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  (UInt64.ofNat g, s, t)

/--
The gcd component returned by the `UInt64` extended-GCD API represents the
gcd of the natural values of the input words.
-/
@[simp, grind =] theorem extGcd_fst (a b : UInt64) :
    (extGcd a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  rw [extGcd]
  have hfst := HexArith.Int.extGcd_fst (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  rcases h : HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat b.toNat) with ⟨g, s, t⟩
  rw [h] at hfst
  simp [Int.gcd] at hfst
  have hbound : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
    by_cases ha : a.toNat = 0
    · simp [ha, UInt64.toNat_lt b]
    · exact Nat.lt_of_le_of_lt (Nat.gcd_le_left b.toNat (Nat.pos_of_ne_zero ha)) (UInt64.toNat_lt a)
  simp [hfst, Nat.mod_eq_of_lt hbound]

/--
The coefficient components returned by the `UInt64` extended-GCD API form a
Bezout certificate for the natural values of the input words.
-/
@[simp] theorem extGcd_bezout (a b : UInt64) :
    let (g, s, t) := extGcd a b
    s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat := by
  rw [extGcd]
  have hfst := HexArith.Int.extGcd_fst (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  have hbez := HexArith.Int.extGcd_bezout (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  rcases h : HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat b.toNat) with ⟨g, s, t⟩
  rw [h] at hfst hbez
  simp [Int.gcd] at hfst hbez
  have hbound : Nat.gcd a.toNat b.toNat < 2 ^ 64 := by
    by_cases ha : a.toNat = 0
    · simp [ha, UInt64.toNat_lt b]
    · exact Nat.lt_of_le_of_lt (Nat.gcd_le_left b.toNat (Nat.pos_of_ne_zero ha)) (UInt64.toNat_lt a)
  simpa [hfst, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hbound] using hbez

/--
Bezout certificate for the `UInt64` `extGcd`, stated on the returned triple's
projections: the cofactors satisfy
`s * a.toNat + t * b.toNat = (extGcd a b).1.toNat`, with each word coerced to
`Int` via `Int.ofNat ·.toNat`. The `_proj` form keeps the right-hand side as
the routine's own returned gcd word; see `extGcd_bezout_gcd` for the variant
phrased against `Nat.gcd a.toNat b.toNat`.
-/
@[simp, grind =] theorem extGcd_bezout_proj (a b : UInt64) :
    (extGcd a b).2.1 * Int.ofNat a.toNat +
        (extGcd a b).2.2 * Int.ofNat b.toNat =
      Int.ofNat (extGcd a b).1.toNat := by
  simpa using extGcd_bezout a b

/--
Bezout certificate for the `UInt64` `extGcd` with the gcd resolved to
`Nat.gcd a.toNat b.toNat`: the returned cofactors satisfy
`s * a.toNat + t * b.toNat = Nat.gcd a.toNat b.toNat`, coerced to `Int` via
`Int.ofNat ·.toNat`. Same identity as `extGcd_bezout_proj`, with the
right-hand side rewritten through `extGcd_fst`.
-/
@[simp, grind =] theorem extGcd_bezout_gcd (a b : UInt64) :
    (extGcd a b).2.1 * Int.ofNat a.toNat +
        (extGcd a b).2.2 * Int.ofNat b.toNat =
      Int.ofNat (Nat.gcd a.toNat b.toNat) := by
  rw [extGcd_bezout_proj, extGcd_fst]

/--
Combined correctness theorem for the `UInt64` extended-GCD API.

The gcd component is stored as a word, so the gcd equality is stated after
`toNat`; the Bezout certificate is stated over the natural representatives of
the input words.
-/
@[simp] theorem extGcd_spec (a b : UInt64) :
    let (g, s, t) := extGcd a b
    g.toNat = Nat.gcd a.toNat b.toNat ∧
      s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat := by
  rcases h : extGcd a b with ⟨g, s, t⟩
  have hfst := extGcd_fst a b
  have hbez := extGcd_bezout a b
  simp [h] at hfst hbez
  exact ⟨hfst, hbez⟩

end UInt64

end HexArith
