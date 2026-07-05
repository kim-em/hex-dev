/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.Irreducibility
public import HexBerlekamp.Factor
public import HexPolyFp.Compose
public import HexPolyFp.Quotient
public import HexPolyFp.QuotientFrobenius
public import HexArith.Nat.Pow
public import HexBerlekamp.RabinSoundness.RabinShape
import all HexBerlekamp.RabinSoundness.RabinCore
import all HexBerlekamp.RabinSoundness.RabinShape

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Distinct-degree saturation and square-free kernel-witness
infrastructure, including the Bezout-coefficient route for square-free
monic splits.
-/
namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
/-! ### Distinct-degree saturation infrastructure

These lemmas package the Leibniz-rule consequence used by the distinct-degree
factorization assembly: if `r` is square-free (i.e. `gcd r r' = 1`) and
`c = gcd r d`, then `r/c` is coprime to `d`. The proof goes through the
"strong square-free" characterization that any squared divisor of `r` is a
unit. -/

/-- The constant polynomial `1 : FpPoly p` is recognised as a unit by
`isUnitPolynomial`. -/
theorem isUnitPolynomial_one_FpPoly : isUnitPolynomial (1 : FpPoly p) = true := by
  unfold isUnitPolynomial
  change (match DensePoly.degree? (DensePoly.C (1 : ZMod64 p)) with
    | some 0 => true
    | _ => false) = true
  have hone_ne_zero : (1 : ZMod64 p) ≠ 0 := by
    intro h
    have : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat := congrArg ZMod64.toNat h
    rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
        show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
        Nat.mod_eq_of_lt (by
          have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
          omega : 1 < p)] at this
    exact absurd this (by omega)
  have hcoeffs : (DensePoly.C (1 : ZMod64 p)).coeffs = #[(1 : ZMod64 p)] :=
    DensePoly.coeffs_C_of_ne_zero hone_ne_zero
  simp [DensePoly.degree?, DensePoly.size, hcoeffs]

/-- A polynomial accepted by `isUnitPolynomial` (degree-zero, hence a
nonzero constant) divides `1 : FpPoly p`. -/
theorem dvd_one_of_isUnitPolynomial
    {u : FpPoly p} (hu : isUnitPolynomial u = true) :
    u ∣ (1 : FpPoly p) := by
  have hu_deg : u.degree? = some 0 := by
    unfold isUnitPolynomial at hu
    cases hdeg : u.degree? with
    | none =>
        rw [hdeg] at hu
        simp at hu
    | some k =>
        rw [hdeg] at hu
        cases k with
        | zero => rfl
        | succ _ => simp at hu
  have hu_size_ne_zero : u.size ≠ 0 := by
    intro hsize
    unfold DensePoly.degree? at hu_deg
    simp [hsize] at hu_deg
  have hu_size : u.size = 1 := by
    unfold DensePoly.degree? at hu_deg
    simp [hu_size_ne_zero] at hu_deg
    omega
  have hmod : (1 : FpPoly p) % u = 0 := by
    show (DensePoly.divMod (1 : FpPoly p) u).2 = 0
    apply DensePoly.divMod_remainder_eq_zero_of_degree_zero_core
    · exact hu_size
    · intro a
      have hpos : 0 < u.size := by omega
      have hidx : u.coeffs.size - 1 < u.coeffs.size := by
        simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
      have hlead_eq : u.leadingCoeff = u.coeff (u.size - 1) := by
        simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
      have hlead_ne : u.leadingCoeff ≠ (Zero.zero : ZMod64 p) := by
        rw [hlead_eq]
        exact DensePoly.coeff_last_ne_zero_of_pos_size u hpos
      have hinv : ZMod64.inv u.leadingCoeff * u.leadingCoeff = (1 : ZMod64 p) :=
        ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
      have hmul : (a / u.leadingCoeff) * u.leadingCoeff = a := by
        change (ZMod64.mul a (ZMod64.inv u.leadingCoeff)) * u.leadingCoeff = a
        calc
          (ZMod64.mul a (ZMod64.inv u.leadingCoeff)) * u.leadingCoeff
              = a * (ZMod64.inv u.leadingCoeff * u.leadingCoeff) := by
                  exact Lean.Grind.Semiring.mul_assoc a (ZMod64.inv u.leadingCoeff)
                    u.leadingCoeff
          _ = a * (1 : ZMod64 p) := by rw [hinv]
          _ = a := Lean.Grind.Semiring.mul_one a
      change a - (a / u.leadingCoeff) * u.leadingCoeff = (Zero.zero : ZMod64 p)
      rw [hmul]
      change ZMod64.sub a a = (Zero.zero : ZMod64 p)
      apply ZMod64.ext
      apply UInt64.toNat_inj.mp
      change (ZMod64.sub a a).toNat = (Zero.zero : ZMod64 p).toNat
      rw [ZMod64.toNat_sub]
      have hsum : a.toNat + (p - a.toNat) = p := by
        have ha : a.toNat < p := a.toNat_lt
        omega
      rw [hsum, Nat.mod_self]
      exact ZMod64.toNat_zero.symm
  refine ⟨(1 : FpPoly p) / u, ?_⟩
  have hspec := DensePoly.div_mul_add_mod (1 : FpPoly p) u
  rw [hmod] at hspec
  exact ((DensePoly.mul_comm_poly u ((1 : FpPoly p) / u)).trans
    ((DensePoly.add_zero_poly (((1 : FpPoly p) / u) * u)).symm.trans hspec)).symm

omit [ZMod64.PrimeModulus p] in
private theorem dvd_derivative_self_mul_self (g : FpPoly p) :
    g ∣ DensePoly.derivative (g * g) := by
  refine ⟨DensePoly.derivative g + DensePoly.derivative g, ?_⟩
  -- Use calc-style with `:=` proofs (which check up to defeq) to avoid
  -- rw's syntactic-match limitations across instance diamond.
  calc DensePoly.derivative (g * g)
      = DensePoly.derivative g * g + g * DensePoly.derivative g :=
        DensePoly.derivative_mul g g
    _ = g * DensePoly.derivative g + g * DensePoly.derivative g :=
        congrArg (· + g * DensePoly.derivative g)
          (DensePoly.mul_comm_poly (DensePoly.derivative g) g)
    _ = g * (DensePoly.derivative g + DensePoly.derivative g) :=
        (DensePoly.mul_add_right_poly g
          (DensePoly.derivative g) (DensePoly.derivative g)).symm

omit [ZMod64.PrimeModulus p] in
private theorem dvd_derivative_of_squared_dvd
    {r g : FpPoly p} (hgg : g * g ∣ r) :
    g ∣ DensePoly.derivative r := by
  rcases hgg with ⟨h, hr⟩
  rcases dvd_derivative_self_mul_self g with ⟨k, hk⟩
  refine ⟨k * h + g * DensePoly.derivative h, ?_⟩
  calc DensePoly.derivative r
      = DensePoly.derivative (g * g * h) := by rw [hr]
    _ = DensePoly.derivative (g * g) * h + (g * g) * DensePoly.derivative h :=
        DensePoly.derivative_mul (g * g) h
    _ = (g * k) * h + (g * g) * DensePoly.derivative h := by rw [hk]
    _ = g * (k * h) + g * (g * DensePoly.derivative h) := by
        congr 1
        · exact DensePoly.mul_assoc_poly g k h
        · exact DensePoly.mul_assoc_poly g g (DensePoly.derivative h)
    _ = g * (k * h + g * DensePoly.derivative h) :=
        (DensePoly.mul_add_right_poly g (k * h) (g * DensePoly.derivative h)).symm

/-- Adapter from the strict executable-gcd form of square-freeness
(`DensePoly.gcd r r' = 1`) to the relaxed common-divisor form
(`∀ d, d ∣ r → d ∣ r' → isUnitPolynomial d`).  The relaxed form is the
shape the soundness chain culminating in `berlekampFactor_singleton_irreducible`
consumes; the strict form is what existing in-tree callers carry, so this
adapter lets them feed the chain unchanged. -/
theorem squareFree_common_of_gcd_eq_one
    {r : FpPoly p}
    (hsf : DensePoly.gcd r (DensePoly.derivative r) = 1) :
    ∀ d, d ∣ r → d ∣ DensePoly.derivative r → isUnitPolynomial d = true := by
  intro d hda hdb
  have hd_dvd_gcd : d ∣ DensePoly.gcd r (DensePoly.derivative r) :=
    DensePoly.dvd_gcd d r (DensePoly.derivative r) hda hdb
  rw [hsf] at hd_dvd_gcd
  exact isUnitPolynomial_of_dvd_isUnitPolynomial hd_dvd_gcd isUnitPolynomial_one_FpPoly

omit [ZMod64.PrimeModulus p] in
/-- Strong square-free characterization: if every common divisor of `r` and
its derivative is a unit, then any `g` with `g * g ∣ r` is itself a unit
(via `isUnitPolynomial`). -/
theorem isUnitPolynomial_of_squareFree_of_squared_dvd
    {r g : FpPoly p}
    (hsf : ∀ d, d ∣ r → d ∣ DensePoly.derivative r → isUnitPolynomial d = true)
    (hgg : g * g ∣ r) :
    isUnitPolynomial g = true := by
  have hgr : g ∣ r := by
    rcases hgg with ⟨b, hb⟩
    refine ⟨g * b, ?_⟩
    rw [hb]
    exact DensePoly.mul_assoc_poly g g b
  have hgr' : g ∣ DensePoly.derivative r := dvd_derivative_of_squared_dvd hgg
  exact hsf g hgr hgr'

/-- Helper: `c ∣ r → r = c * (r / c)` for FpPoly. -/
private theorem fp_eq_mul_div_of_dvd
    {r c : FpPoly p} (hc_dvd_r : c ∣ r) :
    r = c * (r / c) := by
  have hmod : r % c = 0 := DensePoly.mod_eq_zero_of_dvd r c hc_dvd_r
  have hspec := DensePoly.div_mul_add_mod r c
  rw [hmod] at hspec
  -- `hspec : r / c * c + 0 = r`. Need `r = c * (r / c)`.
  have hcomm : (r / c) * c = c * (r / c) := DensePoly.mul_comm_poly _ _
  -- `r / c * c + 0 = r / c * c`
  have hadd : (r / c) * c + 0 = (r / c) * c := DensePoly.add_zero_poly _
  exact (hspec.symm.trans hadd).trans hcomm

omit [ZMod64.PrimeModulus p] in
/-- Ring rearrangement: `(g * e) * (g * a) = (g * g) * (e * a)`. -/
private theorem fp_swap_inner_mul (g e a : FpPoly p) :
    (g * e) * (g * a) = (g * g) * (e * a) := by
  calc (g * e) * (g * a)
      = g * (e * (g * a)) := DensePoly.mul_assoc_poly g e (g * a)
    _ = g * ((e * g) * a) :=
        congrArg (g * ·) (DensePoly.mul_assoc_poly e g a).symm
    _ = g * ((g * e) * a) :=
        congrArg (fun x => g * (x * a)) (DensePoly.mul_comm_poly e g)
    _ = g * (g * (e * a)) :=
        congrArg (g * ·) (DensePoly.mul_assoc_poly g e a)
    _ = (g * g) * (e * a) := (DensePoly.mul_assoc_poly g g (e * a)).symm

omit [ZMod64.PrimeModulus p] in
/-- Ring rearrangement: `c * (g * a) = g * (c * a)`. -/
private theorem fp_swap_left_mul (c g a : FpPoly p) :
    c * (g * a) = g * (c * a) := by
  calc c * (g * a)
      = (c * g) * a := (DensePoly.mul_assoc_poly c g a).symm
    _ = (g * c) * a :=
        congrArg (· * a) (DensePoly.mul_comm_poly c g)
    _ = g * (c * a) := DensePoly.mul_assoc_poly g c a

/-- If the product `a * b` is square-free, then any common divisor `d` of the
two factors `a` and `b` divides `1`, since `d * d ∣ a * b` forces `d` to be a
unit. -/
theorem common_dvd_one_of_squareFree_mul
    {a b d : FpPoly p}
    (hsquareFree : ∀ e, e ∣ (a * b) → e ∣ DensePoly.derivative (a * b) →
      isUnitPolynomial e = true)
    (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ (1 : FpPoly p) := by
  have hdd_dvd_ab : d * d ∣ a * b := by
    rcases hda with ⟨a', ha'⟩
    rcases hdb with ⟨b', hb'⟩
    refine ⟨a' * b', ?_⟩
    calc a * b
        = (d * a') * (d * b') := by rw [ha', hb']
      _ = (d * d) * (a' * b') := fp_swap_inner_mul d a' b'
  exact dvd_one_of_isUnitPolynomial
    (isUnitPolynomial_of_squareFree_of_squared_dvd hsquareFree hdd_dvd_ab)

/--
Square-free product specialization of
`exists_reduced_crtZeroOne_kernelWitness_of_coprime_split`.  The extra monicity
hypothesis on the executable gcd connects the common-divisor form supplied by
square-freeness to the `gcd a b = 1` surface used by the XGCD-backed CRT
candidate.
-/
theorem exists_reduced_crtZeroOne_kernelWitness_of_squareFree_split
    (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hsquareFree : ∀ d, d ∣ (a * b) → d ∣ DensePoly.derivative (a * b) →
      isUnitPolynomial d = true)
    (hgcd_monic : DensePoly.Monic (DensePoly.gcd a b)) :
    ∃ h : FpPoly p,
      h = crtZeroOneXGCDCandidate a b % (a * b) ∧
      (a * b) ∣ (FpPoly.linearPow h (p ^ 1) - h) ∧
      ∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b) := by
  have hgcd : DensePoly.gcd a b = 1 :=
    FpPoly.gcd_eq_one_of_monic_of_common_dvd_one a b hgcd_monic
      (fun d hda hdb => common_dvd_one_of_squareFree_mul hsquareFree hda hdb)
  exact exists_reduced_crtZeroOne_kernelWitness_of_coprime_split
    a b ha hb ha_pos hb_pos hgcd

/-- For square-free `r` (`gcd r r' = 1`), the gcd of `d` with the cofactor
`r / gcd r d` is a unit, the gcd-quotient unit recognition used by the
square-free distinct-degree check. -/
theorem isUnitPolynomial_gcd_quotient_of_squareFree
    (r d : FpPoly p)
    (hsf : DensePoly.gcd r (DensePoly.derivative r) = 1) :
    isUnitPolynomial (DensePoly.gcd (r / DensePoly.gcd r d) d) = true := by
  have hc_dvd_r : DensePoly.gcd r d ∣ r := DensePoly.gcd_dvd_left r d
  have hr_eq : r = DensePoly.gcd r d * (r / DensePoly.gcd r d) :=
    fp_eq_mul_div_of_dvd hc_dvd_r
  have hg_dvd_quot :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r / DensePoly.gcd r d :=
    DensePoly.gcd_dvd_left _ _
  have hg_dvd_d :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ d :=
    DensePoly.gcd_dvd_right _ _
  -- `g ∣ r` via `g ∣ r/c ∣ r`.
  have hg_dvd_r :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r := by
    rcases hg_dvd_quot with ⟨a, ha⟩
    refine ⟨DensePoly.gcd r d * a, ?_⟩
    calc r
        = DensePoly.gcd r d * (r / DensePoly.gcd r d) := hr_eq
      _ = DensePoly.gcd r d *
            (DensePoly.gcd (r / DensePoly.gcd r d) d * a) := by
          exact congrArg (DensePoly.gcd r d * ·) ha
      _ = DensePoly.gcd (r / DensePoly.gcd r d) d *
            (DensePoly.gcd r d * a) :=
          fp_swap_left_mul _ _ _
  -- `g ∣ gcd r d = c`.
  have hg_dvd_c :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ DensePoly.gcd r d :=
    DensePoly.dvd_gcd _ r d hg_dvd_r hg_dvd_d
  -- Hence `g * g ∣ r` (since `r = c * (r/c)` and `g ∣ c`, `g ∣ r/c`).
  have hg2_dvd_r :
      DensePoly.gcd (r / DensePoly.gcd r d) d *
        DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r := by
    rcases hg_dvd_c with ⟨e, he⟩
    rcases hg_dvd_quot with ⟨a, ha⟩
    refine ⟨e * a, ?_⟩
    have hstep2 :
        DensePoly.gcd r d * (r / DensePoly.gcd r d) =
        (DensePoly.gcd (r / DensePoly.gcd r d) d * e) *
          (DensePoly.gcd (r / DensePoly.gcd r d) d * a) := by
      -- Use congrArg with two-argument function to avoid rw's recursive substitution.
      have h := congrArg
        (fun (xy : FpPoly p × FpPoly p) => xy.1 * xy.2)
        (Prod.ext he ha :
          (DensePoly.gcd r d, r / DensePoly.gcd r d) =
            (DensePoly.gcd (r / DensePoly.gcd r d) d * e,
             DensePoly.gcd (r / DensePoly.gcd r d) d * a))
      exact h
    exact hr_eq.trans (hstep2.trans
      (fp_swap_inner_mul (DensePoly.gcd (r / DensePoly.gcd r d) d) e a))
  exact isUnitPolynomial_of_squareFree_of_squared_dvd
    (squareFree_common_of_gcd_eq_one hsf) hg2_dvd_r

/-! ### Square-free divisor distribution across kernel-witness gcds

These lemmas package Step 3 of the Berlekamp completeness argument
(see `SPEC/Libraries/hex-berlekamp-mathlib.md`). Working from the
witness-level product/divisibility form `f ∣ Π_{c ∈ F_p} (w - C c)`,
they distribute the divisibility across the pairwise-coprime gcd
factors `gcd f (w - C c)`. Combined with a non-constancy hypothesis on
the witness (no single `(w - C c)` is divisible by `f`), this yields a
nontrivial Berlekamp split candidate.

The witness-level divisibility hypothesis is the caller-facing
interface; deriving it from `f ∣ FpPoly.linearPow w p - w` via the
prime-field product identity is tracked separately (see #4160). -/

omit [ZMod64.PrimeModulus p] in
/-- The difference of two distinct witness linear factors collapses to
the constant `C (d - c)`. -/
private theorem witnessLinearFactor_sub_eq
    (w : FpPoly p) (c d : ZMod64 p) :
    (w - FpPoly.C c) - (w - FpPoly.C d)
      = (DensePoly.C (d - c) : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring]
  show w.coeff n - (FpPoly.C c).coeff n - (w.coeff n - (FpPoly.C d).coeff n)
    = (DensePoly.C (d - c) : FpPoly p).coeff n
  rw [show (FpPoly.C c).coeff n = (DensePoly.C c : FpPoly p).coeff n from rfl,
      show (FpPoly.C d).coeff n = (DensePoly.C d : FpPoly p).coeff n from rfl]
  rw [DensePoly.coeff_C, DensePoly.coeff_C, DensePoly.coeff_C]
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  rw [h0]
  by_cases hn : n = 0
  · simp [hn]; grind
  · simp [hn]; grind

/-- Distinct witness linear factors `(w - C c)` and `(w - C d)` are
coprime: their difference is a nonzero constant, so any common divisor
divides `1`. -/
theorem witnessLinearFactor_distinct_common_dvd_one
    {w : FpPoly p} {c d : ZMod64 p} (hcd : c ≠ d) (e : FpPoly p)
    (hec : e ∣ (w - FpPoly.C c))
    (hed : e ∣ (w - FpPoly.C d)) :
    e ∣ (1 : FpPoly p) := by
  have hdiff : e ∣ ((w - FpPoly.C c) - (w - FpPoly.C d)) :=
    DensePoly.dvd_sub_poly hec hed
  rw [witnessLinearFactor_sub_eq w c d] at hdiff
  have hdc_ne : (d - c) ≠ (0 : ZMod64 p) := by
    intro hzero
    apply hcd
    have : c = d := by grind
    exact this
  exact dvd_trans_local hdiff (C_ne_zero_dvd_one hdc_ne)

/-- Bezout-style cancellation through one witness linear factor: if `f`
divides `acc * (w - C c)` and `gcd(f, w - C c)` is a unit polynomial,
then `f ∣ acc`. -/
private theorem dvd_of_witness_mul_of_gcd_isUnit
    {f w acc : FpPoly p} {c : ZMod64 p}
    (hdvd : f ∣ acc * (w - FpPoly.C c))
    (hgcd : isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true) :
    f ∣ acc := by
  have hdvd' : f ∣ (w - FpPoly.C c) * acc := by
    rw [FpPoly.mul_comm] at hdvd
    exact hdvd
  apply FpPoly.dvd_of_dvd_mul_of_common_dvd_one hdvd'
  intro d hd_lin hd_f
  exact dvd_one_of_isUnitPolynomial
    (isUnitPolynomial_of_dvd_isUnitPolynomial
      (DensePoly.dvd_gcd d f (w - FpPoly.C c) hd_f hd_lin) hgcd)

/-- Coprime-cancellation through the foldl shape of the witness product:
if every gcd `gcd(f, w - C c)` along the list `cs` is a unit polynomial,
then `f` divides the accumulator. -/
private theorem dvd_acc_of_foldl_witness_dvd_of_all_gcd_isUnit
    (f w : FpPoly p) :
    ∀ (cs : List (ZMod64 p)) (acc : FpPoly p),
      f ∣ cs.foldl (fun a c => a * (w - FpPoly.C c)) acc →
      (∀ c ∈ cs,
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true) →
      f ∣ acc := by
  intro cs
  induction cs with
  | nil =>
      intro acc hdvd _
      simpa using hdvd
  | cons c rest ih =>
      intro acc hdvd hcoprime
      simp only [List.foldl_cons] at hdvd
      have hcoprime_rest :
          ∀ c' ∈ rest,
            isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c')) = true :=
        fun c' hmem => hcoprime c' (List.mem_cons_of_mem _ hmem)
      have hdvd_step : f ∣ acc * (w - FpPoly.C c) :=
        ih _ hdvd hcoprime_rest
      exact dvd_of_witness_mul_of_gcd_isUnit hdvd_step
        (hcoprime c (List.mem_cons.mpr (Or.inl rfl)))

/-- If `f` divides the witness product and every witness gcd is a unit,
then `f ∣ 1`. -/
private theorem dvd_one_of_witnessProduct_dvd_of_all_gcd_isUnit
    {f w : FpPoly p}
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1)
    (hgcd :
      ∀ c : ZMod64 p,
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true) :
    f ∣ (1 : FpPoly p) :=
  dvd_acc_of_foldl_witness_dvd_of_all_gcd_isUnit f w (ZMod64.values p) 1 hdvd
    (fun c _ => hgcd c)

/-- If `f` has positive degree, then `gcd(f, a)` is nonzero for any `a`. -/
private theorem gcd_isZero_false_of_left_pos_degree
    {f : FpPoly p} (a : FpPoly p) (hf_pos : 0 < f.degree?.getD 0) :
    (DensePoly.gcd f a).isZero = false := by
  have hf_ne : f ≠ 0 := ne_zero_of_pos_degree hf_pos
  cases hg : (DensePoly.gcd f a).isZero with
  | false => rfl
  | true =>
      exfalso
      apply hf_ne
      have hg_zero : DensePoly.gcd f a = 0 := by
        apply DensePoly.ext_coeff
        intro n
        have hsize : (DensePoly.gcd f a).size = 0 := by
          simpa [DensePoly.isZero, DensePoly.size,
            Array.isEmpty_iff_size_eq_zero] using hg
        rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega : (DensePoly.gcd f a).size ≤ n),
          DensePoly.coeff_zero]
        rfl
      rcases DensePoly.gcd_dvd_left f a with ⟨q, hq⟩
      rw [hq, hg_zero, FpPoly.zero_mul]

/-- Square-free divisor distribution (non-unit existence): if `f` has
positive degree and divides the canonical witness product over `F_p`,
some `gcd(f, w - C c)` is non-unit. This is the coprime-cancellation
core of Step 3, working purely from the divisibility hypothesis. -/
theorem exists_gcd_not_isUnit_of_witnessProduct_dvd_of_pos_degree
    {f w : FpPoly p}
    (hf_pos : 0 < f.degree?.getD 0)
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1) :
    ∃ c : ZMod64 p,
      isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = false := by
  apply Classical.byContradiction
  intro hno
  have hcoprime :
      ∀ c : ZMod64 p,
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true := by
    intro c
    cases hC : isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) with
    | true => rfl
    | false => exact absurd ⟨c, hC⟩ hno
  have hf_dvd_one : f ∣ (1 : FpPoly p) :=
    dvd_one_of_witnessProduct_dvd_of_all_gcd_isUnit hdvd hcoprime
  have hf_unit : isUnitPolynomial f = true :=
    isUnitPolynomial_of_dvd_isUnitPolynomial hf_dvd_one isUnitPolynomial_one_FpPoly
  have hf_not_unit : isUnitPolynomial f = false :=
    isUnitPolynomial_eq_false_of_pos_degree hf_pos
  rw [hf_not_unit] at hf_unit
  exact Bool.noConfusion hf_unit

/-- Square-free divisor distribution (nontrivial split): under the
non-constancy hypothesis that no single `(w - C c)` is divisible by `f`,
some witness gcd is nonzero, nonconstant, and not equal to `f`. This is
the form consumed by the executable Berlekamp split surface (see
`HexBerlekamp.Berlekamp.kernelWitnessSplit?_some_of_nontrivial_splitFactorAt`).

`f` does not need to be square-free for this statement; the deliverable
shape exposes the square-freeness hypothesis at the call site, where
the witness-level divisibility hypothesis itself is derived from
square-freeness (#4160). -/
theorem exists_nontrivial_gcd_of_witnessProduct_dvd_of_pos_degree
    {f w : FpPoly p}
    (hf_pos : 0 < f.degree?.getD 0)
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1)
    (hnonconst : ∀ c : ZMod64 p, ¬ (f ∣ (w - FpPoly.C c))) :
    ∃ c : ZMod64 p,
      (DensePoly.gcd f (w - FpPoly.C c)).isZero = false ∧
      (DensePoly.gcd f (w - FpPoly.C c)).degree? ≠ some 0 ∧
      DensePoly.gcd f (w - FpPoly.C c) ≠ f := by
  obtain ⟨c, hnotUnit⟩ :=
    exists_gcd_not_isUnit_of_witnessProduct_dvd_of_pos_degree hf_pos hdvd
  refine ⟨c, gcd_isZero_false_of_left_pos_degree _ hf_pos, ?_, ?_⟩
  · intro hdeg
    have hunit :
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true := by
      unfold isUnitPolynomial
      rw [hdeg]
      rfl
    rw [hunit] at hnotUnit
    exact Bool.noConfusion hnotUnit
  · intro hgcd_eq_f
    apply hnonconst c
    rw [← hgcd_eq_f]
    exact DensePoly.gcd_dvd_right f (w - FpPoly.C c)

/--
Executable composition of the square-free distribution step: once the
witness-product divisibility hypothesis is available and the witness is not
constant modulo `f`, the Berlekamp split search finds a concrete split result.

The upstream derivation of `hdvd` from a fixed-space/kernel hypothesis is kept
separate; this theorem only packages the local distribution result with the
executable search reflection.
-/
theorem exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree
    {f w : FpPoly p}
    (hf_pos : 0 < f.degree?.getD 0)
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1)
    (hnonconst : ∀ c : ZMod64 p, ¬ (f ∣ (w - FpPoly.C c))) :
    ∃ r : SplitResult p, kernelWitnessSplit? f w = some r := by
  obtain ⟨c, hnotZero, hdegree, _hne_input⟩ :=
    exists_nontrivial_gcd_of_witnessProduct_dvd_of_pos_degree hf_pos hdvd hnonconst
  have hsize_lt : (DensePoly.gcd f (w - FpPoly.C c)).size < f.size := by
    have hf_ne : f ≠ 0 := ne_zero_of_pos_degree hf_pos
    have hgcd_dvd_f : DensePoly.gcd f (w - FpPoly.C c) ∣ f :=
      DensePoly.gcd_dvd_left _ _
    have hgcd_dvd_h : DensePoly.gcd f (w - FpPoly.C c) ∣ (w - FpPoly.C c) :=
      DensePoly.gcd_dvd_right _ _
    apply Classical.byContradiction
    intro hge
    have hge : f.size ≤ (DensePoly.gcd f (w - FpPoly.C c)).size := Nat.le_of_not_lt hge
    have hsize_le : (DensePoly.gcd f (w - FpPoly.C c)).size ≤ f.size :=
      FpPoly.size_le_of_dvd_of_ne_zero hgcd_dvd_f hf_ne
    have hquot_size : (f / DensePoly.gcd f (w - FpPoly.C c)).size = 1 := by
      have hsplit :=
        FpPoly.size_div_add_size_eq_size_add_one_of_dvd hgcd_dvd_f hf_ne
      omega
    have hquot_unit :
        isUnitPolynomial (f / DensePoly.gcd f (w - FpPoly.C c)) = true := by
      unfold isUnitPolynomial
      have hquot_deg : (f / DensePoly.gcd f (w - FpPoly.C c)).degree? = some 0 := by
        unfold DensePoly.degree?
        simp [hquot_size]
      rw [hquot_deg]
      rfl
    have hquot_dvd_one :
        (f / DensePoly.gcd f (w - FpPoly.C c)) ∣ (1 : FpPoly p) :=
      dvd_one_of_isUnitPolynomial hquot_unit
    rcases hquot_dvd_one with ⟨e, he⟩
    have hf_eq :
        f = DensePoly.gcd f (w - FpPoly.C c) *
            (f / DensePoly.gcd f (w - FpPoly.C c)) :=
      fp_eq_mul_div_of_dvd hgcd_dvd_f
    have hke : (f / DensePoly.gcd f (w - FpPoly.C c)) * e = 1 := he.symm
    have hf_dvd_gcd : f ∣ DensePoly.gcd f (w - FpPoly.C c) := by
      refine ⟨e, ?_⟩
      calc DensePoly.gcd f (w - FpPoly.C c)
          = DensePoly.gcd f (w - FpPoly.C c) * 1 :=
            (DensePoly.mul_one_right_poly _).symm
        _ = DensePoly.gcd f (w - FpPoly.C c) *
              ((f / DensePoly.gcd f (w - FpPoly.C c)) * e) := by rw [hke]
        _ = (DensePoly.gcd f (w - FpPoly.C c) *
              (f / DensePoly.gcd f (w - FpPoly.C c))) * e :=
            (FpPoly.mul_assoc _ _ _).symm
        _ = f * e := by rw [← hf_eq]
    exact hnonconst c (fp_dvd_trans hf_dvd_gcd hgcd_dvd_h)
  exact kernelWitnessSplit?_some_of_nontrivial_splitFactorAt f w c
    (by simp [splitFactorAt, hnotZero])
    (by simpa [splitFactorAt] using hdegree)
    (by simpa [splitFactorAt] using hsize_lt)

/-! ### Bezout-coefficient route for square-free monic splits

From any nontrivial product factorization of a square-free monic `f`, the
common-divisor form `gcd a b ∣ 1` supplied by `common_dvd_one_of_squareFree_mul`
scales the xgcd Bezout identity to `s * a + t * b = 1`. This bypasses the
`Monic (DensePoly.gcd a b)` hypothesis required by the corresponding
`_squareFree_split` wrapper, by using explicit Bezout coefficients to feed
`crtZeroOneCandidate` directly. -/

/-- From `gcd a b ∣ 1`, scale the xgcd Bezout identity by the cofactor of `1`
to obtain explicit `s, t` with `s * a + t * b = 1`. -/
private theorem exists_bezout_eq_one_of_gcd_dvd_one
    (a b : FpPoly p) (hgcd_dvd : DensePoly.gcd a b ∣ (1 : FpPoly p)) :
    ∃ s t : FpPoly p, s * a + t * b = 1 := by
  rcases hgcd_dvd with ⟨e, he⟩
  have hbez_raw :
      (DensePoly.xgcd a b).left * a + (DensePoly.xgcd a b).right * b =
        (DensePoly.xgcd a b).gcd := by
    simpa using DensePoly.xgcd_bezout a b
  have hxgcd_eq : (DensePoly.xgcd a b).gcd = DensePoly.gcd a b :=
    DensePoly.xgcd_gcd_eq_gcd a b
  refine ⟨e * (DensePoly.xgcd a b).left, e * (DensePoly.xgcd a b).right, ?_⟩
  calc
    e * (DensePoly.xgcd a b).left * a + e * (DensePoly.xgcd a b).right * b
        = e * ((DensePoly.xgcd a b).left * a) +
            e * ((DensePoly.xgcd a b).right * b) := by
          rw [FpPoly.mul_assoc e (DensePoly.xgcd a b).left a,
              FpPoly.mul_assoc e (DensePoly.xgcd a b).right b]
      _ = e * ((DensePoly.xgcd a b).left * a +
              (DensePoly.xgcd a b).right * b) :=
          (FpPoly.left_distrib e _ _).symm
      _ = e * (DensePoly.xgcd a b).gcd := by rw [hbez_raw]
      _ = e * DensePoly.gcd a b := by rw [hxgcd_eq]
      _ = DensePoly.gcd a b * e := FpPoly.mul_comm _ _
      _ = 1 := he.symm

omit [ZMod64.PrimeModulus p] in
/-- The common-divisor form `∀ d, d ∣ a → d ∣ b → d ∣ 1` is also a consequence
of an explicit `s * a + t * b = 1` Bezout identity, with no monicity required
on the gcd. -/
private theorem common_dvd_one_of_bezout
    {a b s t : FpPoly p}
    (hbez : s * a + t * b = 1) (d : FpPoly p)
    (hda : d ∣ a) (hdb : d ∣ b) : d ∣ (1 : FpPoly p) := by
  rcases hda with ⟨a', ha'⟩
  rcases hdb with ⟨b', hb'⟩
  refine ⟨s * a' + t * b', ?_⟩
  have hs : s * (d * a') = d * (s * a') := by
    calc s * (d * a')
        = (s * d) * a' := (FpPoly.mul_assoc s d a').symm
      _ = (d * s) * a' := by rw [FpPoly.mul_comm s d]
      _ = d * (s * a') := FpPoly.mul_assoc d s a'
  have ht : t * (d * b') = d * (t * b') := by
    calc t * (d * b')
        = (t * d) * b' := (FpPoly.mul_assoc t d b').symm
      _ = (d * t) * b' := by rw [FpPoly.mul_comm t d]
      _ = d * (t * b') := FpPoly.mul_assoc d t b'
  calc 1
      = s * a + t * b := hbez.symm
    _ = s * (d * a') + t * (d * b') := by rw [ha', hb']
    _ = d * (s * a') + d * (t * b') := by rw [hs, ht]
    _ = d * (s * a' + t * b') := (FpPoly.left_distrib d _ _).symm

/-- Reduced zero-one CRT witness from explicit Bezout coefficients. Parallels
`exists_reduced_crtZeroOne_kernelWitness_of_coprime_split` but consumes an
arbitrary Bezout pair `s * a + t * b = 1` instead of `gcd a b = 1`. -/
private theorem exists_reduced_crtZeroOne_kernelWitness_of_bezout
    (a b s t : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hbez : s * a + t * b = 1) :
    ∃ h : FpPoly p,
      h = crtZeroOneCandidate a b s t % (a * b) ∧
      (a * b) ∣ (FpPoly.linearPow h p - h) ∧
      ∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b) := by
  let h0 := crtZeroOneCandidate a b s t
  refine ⟨h0 % (a * b), rfl, ?_, ?_⟩
  · have hleft : a ∣ (FpPoly.linearPow h0 p - h0) :=
      dvd_linearPow_sub_self_of_congr_zero a h0
        (crtZeroOneCandidate_congr_zero_left a b s t hbez)
    have hright : b ∣ (FpPoly.linearPow h0 p - h0) :=
      dvd_linearPow_sub_self_of_congr_one b h0
        (crtZeroOneCandidate_congr_one_right a b s t hbez)
    have hprod : a * b ∣ (FpPoly.linearPow h0 p - h0) :=
      mul_dvd_of_dvd_dvd_common hleft hright (common_dvd_one_of_bezout hbez)
    have hred :=
      (dvd_linearPow_sub_self_mod_iff (a * b) h0 1).mp (by simpa using hprod)
    simpa using hred
  · intro c
    apply not_congr_constant_mod_of_mod (a * b) h0 c
    exact crtZeroOneCandidate_not_congr_constant_mod_product a b s t
      ha hb ha_pos hb_pos hbez c

/-- Reduced zero-one CRT witness for a monic split of a square-free product.
Avoids the `Monic (DensePoly.gcd a b)` hypothesis of
`exists_reduced_crtZeroOne_kernelWitness_of_squareFree_split` by routing
through `common_dvd_one_of_squareFree_mul` and the Bezout-coefficient route.
-/
private theorem exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split
    (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hsf : ∀ d, d ∣ (a * b) → d ∣ DensePoly.derivative (a * b) →
      isUnitPolynomial d = true) :
    ∃ h : FpPoly p,
      (a * b) ∣ (FpPoly.linearPow h p - h) ∧
      (∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b)) ∧
      h.size ≤ (a * b).degree?.getD 0 := by
  have hgcd_dvd_one : DensePoly.gcd a b ∣ (1 : FpPoly p) :=
    common_dvd_one_of_squareFree_mul hsf
      (DensePoly.gcd_dvd_left a b) (DensePoly.gcd_dvd_right a b)
  obtain ⟨s, t, hbez⟩ := exists_bezout_eq_one_of_gcd_dvd_one a b hgcd_dvd_one
  obtain ⟨h, hheq, hdvd, hnonconst⟩ :=
    exists_reduced_crtZeroOne_kernelWitness_of_bezout
      a b s t ha hb ha_pos hb_pos hbez
  refine ⟨h, hdvd, hnonconst, ?_⟩
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hab_pos : 0 < (a * b).degree?.getD 0 := by
    have ha_ne : a ≠ 0 := ne_zero_of_pos_degree ha_pos
    have hb_ne : b ≠ 0 := ne_zero_of_pos_degree hb_pos
    rw [FpPoly.degree?_mul_eq_add_degree? a b ha_ne hb_ne]
    omega
  rw [hheq]
  have hlt :=
    DensePoly.mod_degree_lt_of_pos_degree
      (crtZeroOneCandidate a b s t) (a * b) hab_pos
  by_cases hsize :
      (crtZeroOneCandidate a b s t % (a * b)).size = 0
  · omega
  · have hpos :
        0 < (crtZeroOneCandidate a b s t % (a * b)).size :=
      Nat.pos_of_ne_zero hsize
    have hdeg_eq :
        (crtZeroOneCandidate a b s t % (a * b)).degree?.getD 0 =
          (crtZeroOneCandidate a b s t % (a * b)).size - 1 := by
      unfold DensePoly.degree?
      simp [Nat.ne_of_gt hpos]
    omega


end Berlekamp
end Hex
