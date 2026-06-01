import Init.Grind.Ring.Field
import HexGFqField.Basic

/-!
Executable finite-field operations for `F_p[x] / (f)`.

This module keeps `GFqField.FiniteField` on the quotient-ring arithmetic path:
all operations, exponentiation, and Frobenius are implemented by delegating to
`Hex.GFqRing.PolyQuotient` and then rewrapping the reduced representative.
-/
namespace Hex

namespace GFqField

set_option linter.unusedSectionVars false

variable {p : Nat} [ZMod64.Bounds p] {hp : Hex.Nat.Prime p}

/-- Natural-number literals reuse the quotient-ring cast and then rewrap the
resulting reduced residue. -/
def natCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (n : Nat) : FiniteField f hf hp hirr :=
  ofQuotient (n : GFqRing.PolyQuotient f hf)

/-- The additive identity in the finite-field wrapper. -/
def zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) :
    FiniteField f hf hp hirr :=
  ofQuotient 0

/-- The multiplicative identity in the finite-field wrapper. -/
def one (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) :
    FiniteField f hf hp hirr :=
  ofQuotient 1

/-- Field addition reuses the quotient-ring sum. -/
def add {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient + y.toQuotient)

/-- Field multiplication reuses the quotient-ring product. -/
def mul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient * y.toQuotient)

/-- Field negation reuses the quotient-ring additive inverse. -/
def neg {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (-x.toQuotient)

/-- Field subtraction reuses the quotient-ring difference. -/
def sub {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient - y.toQuotient)

/-- Exponentiation reuses the quotient-ring repeated-multiplication path. -/
def pow {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient ^ n)

/-- Natural scalar multiplication reuses the quotient-ring scalar action. -/
def nsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (n • x.toQuotient)

/-- Integer literals reuse the quotient-ring cast and then rewrap the reduced
residue. -/
def intCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (i : Int) : FiniteField f hf hp hirr :=
  ofQuotient (i : GFqRing.PolyQuotient f hf)

/-- Integer scalar multiplication reuses the quotient-ring scalar action. -/
def zsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (i • x.toQuotient)

section InverseInternals

variable [ZMod64.PrimeModulus p]

/-- The inverse polynomial representative for a quotient element.

This normalizes the extended-GCD left coefficient by the gcd's constant-unit
factor, producing a polynomial whose residue is the multiplicative inverse
whenever the quotient element is nonzero. -/
private def invPoly {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) : FpPoly p :=
  let r := DensePoly.xgcd (GFqRing.repr x) f
  let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
  DensePoly.scale unitInv r.left

/-- The inverse candidate is the normalized left Bezout coefficient from the
extended gcd between the representative and the modulus. -/
private theorem invPoly_eq_scale_xgcd_left
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    invPoly x =
      let r := DensePoly.xgcd (GFqRing.repr x) f
      let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
      DensePoly.scale unitInv r.left := by
  rfl

/-- The extended-gcd output gives the unscaled Bezout identity for the reduced
representative and the modulus. -/
private theorem xgcd_repr_bezout
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    r.left * GFqRing.repr x + r.right * f = r.gcd := by
  simpa using DensePoly.xgcd_bezout (GFqRing.repr x) f

/-- After scaling the Bezout coefficients by the inverse of the gcd's constant
term, the left coefficient is still a quotient-level inverse candidate. -/
private theorem scaled_xgcd_repr_bezout
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
    DensePoly.scale unitInv r.left * GFqRing.repr x +
        DensePoly.scale unitInv r.right * f =
      DensePoly.scale unitInv r.gcd := by
  dsimp
  calc
    DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
          (DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x +
        DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
          (DensePoly.xgcd (GFqRing.repr x) f).right * f
        =
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            ((DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x) +
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            ((DensePoly.xgcd (GFqRing.repr x) f).right * f) := by
            rw [FpPoly.scale_mul_left, FpPoly.scale_mul_left]
    _ =
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            ((DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x +
              (DensePoly.xgcd (GFqRing.repr x) f).right * f) := by
            rw [FpPoly.scale_add]
    _ =
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).gcd := by
            rw [xgcd_repr_bezout x]

/-- Modulo `f`, multiplying a representative by the normalized inverse
candidate reduces to the normalized gcd witness from the same xgcd run. -/
private theorem reduceMod_repr_mul_invPoly_eq_scaled_gcd
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
    GFqRing.reduceMod f (GFqRing.repr x * invPoly x) =
      GFqRing.reduceMod f (DensePoly.scale unitInv r.gcd) := by
  dsimp [invPoly]
  calc
    GFqRing.reduceMod f
        (GFqRing.repr x *
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).left)
        =
      GFqRing.reduceMod f
        (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).left *
          GFqRing.repr x) := by
          rw [FpPoly.mul_comm]
    _ =
      GFqRing.reduceMod f
        (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x +
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).right * f) := by
          exact (GFqRing.reduceMod_add_mul_self_right f hf
            (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
              (DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x)
            (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
              (DensePoly.xgcd (GFqRing.repr x) f).right)).symm
    _ =
      GFqRing.reduceMod f
        (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
          (DensePoly.xgcd (GFqRing.repr x) f).gcd) := by
          rw [scaled_xgcd_repr_bezout x]

/-- Nonzero field elements have nonzero quotient representatives. This connects
field-level hypotheses to the quotient-level helper lemmas. -/
private theorem toQuotient_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    x.toQuotient ≠ (0 : GFqRing.PolyQuotient f hf) := by
  intro hq
  apply hx
  exact GFqField.ext hq

/-- The xgcd gcd witness divides the nonzero field representative. -/
private theorem xgcd_repr_gcd_dvd_repr
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    (DensePoly.xgcd (GFqRing.repr x) f).gcd ∣ GFqRing.repr x := by
  simpa [DensePoly.gcd]
    using DensePoly.gcd_dvd_left (GFqRing.repr x) f

/-- The xgcd gcd witness divides the irreducible modulus. -/
private theorem xgcd_repr_gcd_dvd_modulus
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    (DensePoly.xgcd (GFqRing.repr x) f).gcd ∣ f := by
  simpa [DensePoly.gcd]
    using DensePoly.gcd_dvd_right (GFqRing.repr x) f

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

private theorem scale_one_poly (c : ZMod64 p) :
    DensePoly.scale c (1 : FpPoly p) = DensePoly.C c := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  change c * (DensePoly.C (1 : ZMod64 p)).coeff n = (DensePoly.C c).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n => exact hzero

private theorem C_mul_eq_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.C c * f = DensePoly.scale c f := by
  have hscale := FpPoly.scale_mul_left c (1 : FpPoly p) f
  rw [FpPoly.one_mul, scale_one_poly] at hscale
  exact hscale.symm

private theorem scale_C (c d : ZMod64 p) :
    DensePoly.scale c (DensePoly.C d : FpPoly p) = DensePoly.C (c * d) := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => rfl
  | succ n => exact hzero

private theorem C_mul_C_inv_of_ne_zero
    (hp : Hex.Nat.Prime p) {c : ZMod64 p} (hc : c ≠ 0) :
    (DensePoly.C c : FpPoly p) * DensePoly.C c⁻¹ = 1 := by
  rw [C_mul_eq_scale, scale_C, zmod64_mul_inv_eq_one_of_prime_ne_zero hp hc]
  rfl

private theorem scale_inv_C_eq_one_of_ne_zero
    (hp : Hex.Nat.Prime p) {c : ZMod64 p} (hc : c ≠ 0) :
    DensePoly.scale c⁻¹ (DensePoly.C c : FpPoly p) = 1 := by
  rw [scale_C]
  have hmul : c⁻¹ * c = 1 := by
    have hright := zmod64_mul_inv_eq_one_of_prime_ne_zero hp hc
    have hcomm : c⁻¹ * c = c * c⁻¹ := by grind
    rw [hcomm]
    exact hright
  rw [hmul]
  rfl

private theorem eq_C_of_degree_eq_zero
    (g : FpPoly p) (hdeg : g.degree? = some 0) :
    g = DensePoly.C (g.coeff 0) := by
  have hsize : g.size = 1 := by
    unfold DensePoly.degree? at hdeg
    by_cases hzero : g.size = 0
    · simp [hzero] at hdeg
    · have hpred : g.size - 1 = 0 := by
        simpa [hzero] using hdeg
      omega
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · have hle : g.size ≤ n := by omega
    rw [DensePoly.coeff_eq_zero_of_size_le g hle]
    simp [hn]

private theorem coeff_zero_ne_zero_of_degree_eq_zero
    (g : FpPoly p) (hdeg : g.degree? = some 0) :
    g.coeff 0 ≠ 0 := by
  have hsize : g.size = 1 := by
    unfold DensePoly.degree? at hdeg
    by_cases hzero : g.size = 0
    · simp [hzero] at hdeg
    · have hpred : g.size - 1 = 0 := by
        simpa [hzero] using hdeg
      omega
  simpa [hsize] using DensePoly.coeff_last_ne_zero_of_pos_size g (by omega)

private theorem dvd_trans_poly {a b c : FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨u, hu⟩
  rcases hbc with ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  rw [hv, hu]
  exact DensePoly.mul_assoc_poly a u v

private theorem dvd_left_of_mul_const_right_eq
    (hp : Hex.Nat.Prime p) {g r f : FpPoly p}
    (hfg : g * r = f) (hrdeg : r.degree? = some 0) :
    f ∣ g := by
  let c := r.coeff 0
  have hrC : r = DensePoly.C c := eq_C_of_degree_eq_zero r hrdeg
  have hc : c ≠ 0 := coeff_zero_ne_zero_of_degree_eq_zero r hrdeg
  refine ⟨DensePoly.C c⁻¹, ?_⟩
  have hfgC : g * DensePoly.C c = f := by
    rw [← hfg]
    rw [hrC]
  calc
    g = g * (1 : FpPoly p) := by rw [FpPoly.mul_one]
    _ = g * (DensePoly.C c * DensePoly.C c⁻¹) := by
      rw [C_mul_C_inv_of_ne_zero hp hc]
    _ = (g * DensePoly.C c) * DensePoly.C c⁻¹ := by
      exact (DensePoly.mul_assoc_poly g (DensePoly.C c) (DensePoly.C c⁻¹)).symm
    _ = f * DensePoly.C c⁻¹ := by
      rw [hfgC]

/-- For a nonzero residue class modulo irreducible `f`, the xgcd gcd witness
is a constant polynomial. -/
private theorem xgcd_repr_gcd_degree_eq_zero_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd.degree? = some 0 := by
  let g := (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd
  have hg_dvd_repr : g ∣ GFqRing.repr x.toQuotient := by
    simpa [g] using xgcd_repr_gcd_dvd_repr x.toQuotient
  have hg_dvd_f : g ∣ f := by
    simpa [g] using xgcd_repr_gcd_dvd_modulus x.toQuotient
  rcases hg_dvd_f with ⟨r, hfr⟩
  have hirr_split := hirr.2 g r hfr.symm
  rcases hirr_split with hg_const | hr_const
  · exact hg_const
  · have hf_dvd_g : f ∣ g :=
      dvd_left_of_mul_const_right_eq hp hfr.symm hr_const
    have hf_dvd_repr : f ∣ GFqRing.repr x.toQuotient :=
      dvd_trans_poly hf_dvd_g hg_dvd_repr
    have hmod_zero : GFqRing.reduceMod f (GFqRing.repr x.toQuotient) = 0 := by
      simpa [GFqRing.reduceMod, DensePoly.mod_eq_divMod]
        using DensePoly.mod_eq_zero_of_dvd (GFqRing.repr x.toQuotient) f hf_dvd_repr
    have hrepr_self :
        GFqRing.reduceMod f (GFqRing.repr x.toQuotient) = GFqRing.repr x.toQuotient :=
      GFqRing.reduceMod_eq_self_of_degree_lt f (GFqRing.repr x.toQuotient)
        (GFqRing.degree_repr_lt_degree x.toQuotient)
    have hrepr_zero : GFqRing.repr x.toQuotient = 0 := by
      rw [hrepr_self] at hmod_zero
      exact hmod_zero
    have hquot_ne : x.toQuotient ≠ (0 : GFqRing.PolyQuotient f hf) :=
      toQuotient_ne_zero hx
    have hrepr_ne_reduce :
        GFqRing.repr x.toQuotient ≠ GFqRing.reduceMod f 0 := by
      exact (GFqRing.ne_zero_iff_repr_ne_zero x.toQuotient).1 (by
        simpa [GFqRing.zero] using hquot_ne)
    have hrepr_ne : GFqRing.repr x.toQuotient ≠ 0 := by
      simpa [GFqRing.reduceMod_zero f hf] using hrepr_ne_reduce
    exact False.elim (hrepr_ne hrepr_zero)

/-- For a nonzero residue class modulo irreducible `f`, the constant xgcd gcd
witness has nonzero constant coefficient. -/
private theorem xgcd_repr_gcd_coeff_zero_ne_zero_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd.coeff 0 ≠ 0 := by
  let g := (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd
  have hdeg : g.degree? = some 0 :=
    xgcd_repr_gcd_degree_eq_zero_of_ne_zero (x := x) hx
  have hsize : g.size = 1 := by
    unfold DensePoly.degree? at hdeg
    by_cases hzero : g.size = 0
    · simp [hzero] at hdeg
    · have hpred : g.size - 1 = 0 := by
        simpa [hzero] using hdeg
      omega
  have hpos : 0 < g.size := by omega
  simpa [g, hsize] using DensePoly.coeff_last_ne_zero_of_pos_size g hpos

/-- For a nonzero residue class modulo an irreducible polynomial, the
normalized xgcd witness reduces to the multiplicative identity. -/
private theorem reduceMod_repr_mul_invPoly_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) =
      GFqRing.reduceMod f 1 := by
  let r := DensePoly.xgcd (GFqRing.repr x.toQuotient) f
  let c : ZMod64 p := r.gcd.coeff 0
  have hscaled :=
    reduceMod_repr_mul_invPoly_eq_scaled_gcd (f := f) (hf := hf) x.toQuotient
  have hdeg : r.gcd.degree? = some 0 := by
    simpa [r] using xgcd_repr_gcd_degree_eq_zero_of_ne_zero (x := x) hx
  have hgcd_C : r.gcd = DensePoly.C c := by
    simpa [c] using eq_C_of_degree_eq_zero r.gcd hdeg
  have hc : c ≠ 0 := by
    simpa [r, c] using xgcd_repr_gcd_coeff_zero_ne_zero_of_ne_zero (x := x) hx
  have hnormalized :
      GFqRing.reduceMod f (DensePoly.scale c⁻¹ r.gcd) =
        GFqRing.reduceMod f 1 := by
    rw [hgcd_C]
    rw [scale_inv_C_eq_one_of_ne_zero hp hc]
  exact hscaled.trans (by simpa [r, c] using hnormalized)

end InverseInternals

/-- Field inversion stays on the quotient-reduction path by reusing the
polynomial extended-GCD witness, normalized by the gcd's constant unit factor.
The `0` case follows the usual junk-value convention required by
`Lean.Grind.Field`. -/
def inv {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  if _hx : x = zero f hf hp hirr then
    zero f hf hp hirr
  else
    ofPoly f hf hp hirr (invPoly x.toQuotient)

private theorem toQuotient_inv_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    (inv x).toQuotient = GFqRing.ofPoly f hf (invPoly x.toQuotient) := by
  simp [GFqField.inv, hx]

/-- Division is multiplication by the inverse candidate. -/
def div {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  mul x (inv y)

/-- Integer exponentiation uses the existing natural-power path together with
the inverse candidate for negative exponents. -/
def zpow {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : Int → FiniteField f hf hp hirr
  | .ofNat n => pow x n
  | .negSucc n => inv (pow x (n + 1))

/-- The Frobenius map is the `p`-th power map on the existing quotient
representation. -/
def frob {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  pow x p

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Zero (FiniteField f hf hp hirr) where
  zero := zero f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    One (FiniteField f hf hp hirr) where
  one := one f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Add (FiniteField f hf hp hirr) where
  add := add

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Mul (FiniteField f hf hp hirr) where
  mul := mul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Neg (FiniteField f hf hp hirr) where
  neg := neg

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Sub (FiniteField f hf hp hirr) where
  sub := sub

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Pow (FiniteField f hf hp hirr) Nat where
  pow := pow

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    NatCast (FiniteField f hf hp hirr) where
  natCast := natCast f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) : OfNat (FiniteField f hf hp hirr) n where
  ofNat := natCast f hf hp hirr n

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    SMul Nat (FiniteField f hf hp hirr) where
  smul := nsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    IntCast (FiniteField f hf hp hirr) where
  intCast := intCast f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    SMul Int (FiniteField f hf hp hirr) where
  smul := zsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Inv (FiniteField f hf hp hirr) where
  inv := inv

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Div (FiniteField f hf hp hirr) where
  div := div

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    HPow (FiniteField f hf hp hirr) Int (FiniteField f hf hp hirr) where
  hPow := zpow

/-- Zero projects to the quotient-ring zero. -/
@[simp, grind =] theorem toQuotient_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hp hirr).toQuotient = 0 :=
  rfl

/-- One projects to the quotient-ring one. -/
@[simp, grind =] theorem toQuotient_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    (1 : FiniteField f hf hp hirr).toQuotient = 1 :=
  rfl

theorem zero_ne_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hp hirr) ≠ 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro h
  have hq := congrArg FiniteField.toQuotient h
  exact GFqRing.zero_ne_one f hf (by simpa using hq)

/-- Natural literals project to quotient-ring natural literals. -/
@[simp, grind =] theorem toQuotient_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (n : Nat) :
    ((n : FiniteField f hf hp hirr).toQuotient) = (n : GFqRing.PolyQuotient f hf) :=
  rfl

@[simp] theorem repr_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (n : Nat) :
    repr (n : FiniteField f hf hp hirr) =
      GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl

theorem natCast_eq_of_zmod64_natCast_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    {m n : Nat} (h : (m : ZMod64 p) = (n : ZMod64 p)) :
    (m : FiniteField f hf hp hirr) = n := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  apply GFqField.ext
  exact GFqRing.natCast_eq_of_zmod64_natCast_eq f hf h

theorem natCast_eq_of_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    {m n : Nat} (h : m % p = n % p) :
    (m : FiniteField f hf hp hirr) = n := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  apply GFqField.ext
  exact GFqRing.natCast_eq_of_mod_eq f hf h

theorem natCast_eq_natCast_iff_reduceMod_const_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    (m n : Nat) :
    ((m : FiniteField f hf hp hirr) = n) ↔
      GFqRing.reduceMod f (FpPoly.C (m : ZMod64 p)) =
        GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  constructor
  · intro h
    simpa [repr_natCast] using congrArg repr h
  · intro h
    apply GFqField.ext
    apply GFqRing.ext
    simpa [repr_natCast] using h

theorem natCast_eq_natCast_iff_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    (m n : Nat) :
    ((m : FiniteField f hf hp hirr) = n) ↔ m % p = n % p := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  constructor
  · intro h
    have hq :
        ((m : GFqRing.PolyQuotient f hf) = n) := by
      simpa using congrArg FiniteField.toQuotient h
    exact (GFqRing.natCast_eq_natCast_iff_mod_eq f hf m n).1 hq
  · intro h
    exact natCast_eq_of_mod_eq f hf hp hirr h

/-- Addition projects to quotient-ring addition. -/
@[simp, grind =] theorem toQuotient_add
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    (x + y : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient + y.toQuotient :=
  rfl

/-- Multiplication projects to quotient-ring multiplication. -/
@[simp, grind =] theorem toQuotient_mul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    (x * y : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient * y.toQuotient :=
  rfl

/-- Negation projects to the quotient-ring additive inverse. -/
@[simp, grind =] theorem toQuotient_neg
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    (-x : FiniteField f hf hp hirr).toQuotient = -x.toQuotient :=
  rfl

/-- Subtraction projects to the quotient-ring difference. -/
@[simp, grind =] theorem toQuotient_sub
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    (x - y : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient - y.toQuotient :=
  rfl

/-- Natural scalar multiplication projects to the quotient-ring scalar action. -/
@[simp, grind =] theorem toQuotient_nsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hp hirr) :
    (n • x : FiniteField f hf hp hirr).toQuotient = n • x.toQuotient :=
  rfl

/-- Integer literals project to quotient-ring integer literals. -/
@[simp, grind =] theorem toQuotient_intCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (i : Int) :
    ((i : FiniteField f hf hp hirr).toQuotient) = (i : GFqRing.PolyQuotient f hf) :=
  rfl

/-- Integer scalar multiplication projects to the quotient-ring scalar action. -/
@[simp, grind =] theorem toQuotient_zsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hp hirr) :
    (i • x : FiniteField f hf hp hirr).toQuotient = i • x.toQuotient :=
  rfl

/-- Natural powers project to quotient-ring natural powers. -/
@[simp, grind =] theorem toQuotient_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    (x ^ n : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient ^ n :=
  rfl

/-- Division projects to multiplication by the projected inverse. -/
@[simp, grind =] theorem toQuotient_div
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    (x / y : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient * (inv y).toQuotient :=
  rfl

/-- Nonnegative integer powers project to quotient-ring natural powers. -/
@[simp, grind =] theorem toQuotient_zpow_ofNat
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    (x ^ (Int.ofNat n) : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient ^ n :=
  rfl

/-- Negative integer powers project through inversion of the positive power. -/
@[simp, grind =] theorem toQuotient_zpow_negSucc
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    (x ^ (Int.negSucc n) : FiniteField f hf hp hirr).toQuotient =
      (inv (pow x (n + 1))).toQuotient :=
  rfl

/-- The field inverse uses the standard junk value at zero. -/
@[simp] theorem inv_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    ((0 : FiniteField f hf hp hirr) : FiniteField f hf hp hirr)⁻¹ = 0 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  change (if ((0 : FiniteField f hf hp hirr) : FiniteField f hf hp hirr) = 0 then 0 else
    ofPoly f hf hp hirr (invPoly ((0 : FiniteField f hf hp hirr).toQuotient))) = 0
  simp

/-- Division is field multiplication by inverse. -/
theorem div_eq_mul_inv
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    x / y = x * y⁻¹ := by
  rfl

/-- A nonzero field element cancels against its inverse on the right. -/
theorem mul_inv_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hreduced := reduceMod_repr_mul_invPoly_eq_one (x := x) hx
  have hxrepr :
      GFqRing.reduceMod f (GFqRing.repr x.toQuotient) = GFqRing.repr x.toQuotient := by
    rcases x.toQuotient.property with ⟨g, hg⟩
    change GFqRing.reduceMod f x.toQuotient.val = x.toQuotient.val
    rw [hg, GFqRing.reduceMod_idem]
  have hinv := toQuotient_inv_of_ne_zero (x := x) hx
  have honeQuotient :
      (1 : GFqRing.PolyQuotient f hf) = GFqRing.one f hf := by
    change GFqRing.natCast f hf 1 = GFqRing.one f hf
    rfl
  set_option linter.unnecessarySimpa false in
  have hmulReduce :
      GFqRing.reduceMod f
          (GFqRing.repr x.toQuotient * GFqRing.reduceMod f (invPoly x.toQuotient)) =
        GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) := by
    simpa [hxrepr] using
      (GFqRing.reduceMod_mul_reduceMod f (GFqRing.repr x.toQuotient)
        (invPoly x.toQuotient)).symm
  apply GFqField.ext
  apply GFqRing.ext
  calc
    GFqRing.repr ((x * x⁻¹ : FiniteField f hf hp hirr).toQuotient)
        = GFqRing.repr (x.toQuotient * GFqRing.ofPoly f hf (invPoly x.toQuotient)) := by
            rw [toQuotient_mul]
            change GFqRing.repr (x.toQuotient * (inv x).toQuotient) =
              GFqRing.repr (x.toQuotient * GFqRing.ofPoly f hf (invPoly x.toQuotient))
            rw [hinv]
    _ = GFqRing.reduceMod f
            (GFqRing.repr x.toQuotient * GFqRing.reduceMod f (invPoly x.toQuotient)) := by
            rfl
    _ = GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) :=
        hmulReduce
    _ = GFqRing.reduceMod f 1 := hreduced
    _ = GFqRing.repr ((1 : FiniteField f hf hp hirr).toQuotient) := by
        rw [toQuotient_one]
        rw [honeQuotient]
        rfl

/-- A nonzero field element cancels against its inverse on the left. -/
theorem inv_mul_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ 0) :
    x⁻¹ * x = 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hleft := mul_inv_cancel (x := x) hx
  apply GFqField.ext
  calc
    (x⁻¹ * x : FiniteField f hf hp hirr).toQuotient
        = (x⁻¹).toQuotient * x.toQuotient := rfl
    _ = x.toQuotient * (x⁻¹).toQuotient :=
        Lean.Grind.CommSemiring.mul_comm (x⁻¹).toQuotient x.toQuotient
    _ = (x * x⁻¹ : FiniteField f hf hp hirr).toQuotient := rfl
    _ = (1 : FiniteField f hf hp hirr).toQuotient := congrArg FiniteField.toQuotient hleft

@[simp] theorem repr_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    repr (0 : FiniteField f hf hp hirr) = GFqRing.reduceMod f 0 :=
  rfl

/-- The multiplicative-identity representative is the reduced form of `1`. -/
@[simp] theorem repr_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    repr (1 : FiniteField f hf hp hirr) = GFqRing.reduceMod f 1 :=
  rfl

@[simp] theorem repr_add
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    repr (x + y) = GFqRing.reduceMod f (repr x + repr y) :=
  rfl

@[simp] theorem repr_mul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    repr (x * y) = GFqRing.reduceMod f (repr x * repr y) :=
  rfl

/-- The representative of a negation reduces from the negated representative. -/
@[simp] theorem repr_neg
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    repr (-x) = GFqRing.reduceMod f (-(repr x)) :=
  rfl

/-- The representative of a subtraction reduces from the difference of
representatives. -/
@[simp] theorem repr_sub
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    repr (x - y) = GFqRing.reduceMod f (repr x - repr y) :=
  rfl

@[simp] theorem repr_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    repr (x ^ n) = GFqRing.repr (x.toQuotient ^ n) :=
  rfl

@[simp] theorem repr_div
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    repr (x / y : FiniteField f hf hp hirr) =
      GFqRing.repr (x.toQuotient * (inv y).toQuotient) :=
  rfl

@[simp] theorem repr_zpow_ofNat
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    repr (x ^ (Int.ofNat n) : FiniteField f hf hp hirr) =
      GFqRing.repr (x.toQuotient ^ n) :=
  rfl

@[simp] theorem repr_zpow_negSucc
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    repr (x ^ (Int.negSucc n) : FiniteField f hf hp hirr) =
      GFqRing.repr ((inv (pow x (n + 1))).toQuotient) :=
  rfl

/-- The representative of an integer cast lifts the quotient-ring cast. -/
@[simp] theorem repr_intCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (i : Int) :
    repr (i : FiniteField f hf hp hirr) =
      GFqRing.repr ((i : GFqRing.PolyQuotient f hf)) :=
  rfl

/-- The representative of a natural scalar action lifts the quotient-ring action. -/
@[simp] theorem repr_nsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hp hirr) :
    repr (n • x : FiniteField f hf hp hirr) = GFqRing.repr (n • x.toQuotient) :=
  rfl

/-- The representative of an integer scalar action lifts the quotient-ring action. -/
@[simp] theorem repr_zsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hp hirr) :
    repr (i • x : FiniteField f hf hp hirr) = GFqRing.repr (i • x.toQuotient) :=
  rfl

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Semiring (FiniteField f hf hp hirr) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.add_zero a.toQuotient
  · intro a b
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.add_comm a.toQuotient b.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.add_assoc a.toQuotient b.toQuotient c.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.mul_assoc a.toQuotient b.toQuotient c.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.mul_one a.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.one_mul a.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.left_distrib a.toQuotient b.toQuotient c.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.right_distrib a.toQuotient b.toQuotient c.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.zero_mul a.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.mul_zero a.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.pow_zero a.toQuotient
  · intro a n
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.pow_succ a.toQuotient n
  · intro n
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.ofNat_succ (α := GFqRing.PolyQuotient f hf) n
  · intro n
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.ofNat_eq_natCast (α := GFqRing.PolyQuotient f hf) n
  · intro n a
    apply GFqField.ext
    simpa using
      Lean.Grind.Semiring.nsmul_eq_natCast_mul (α := GFqRing.PolyQuotient f hf) n a.toQuotient

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Ring (FiniteField f hf hp hirr) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Ring.neg_add_cancel a.toQuotient
  · intro a b
    apply GFqField.ext
    simpa using Lean.Grind.Ring.sub_eq_add_neg a.toQuotient b.toQuotient
  · intro i a
    apply GFqField.ext
    simpa using Lean.Grind.Ring.neg_zsmul i a.toQuotient
  · intro n a
    apply GFqField.ext
    simpa using Lean.Grind.Ring.zsmul_natCast_eq_nsmul (α := GFqRing.PolyQuotient f hf) n a.toQuotient
  · intro n
    apply GFqField.ext
    simpa using Lean.Grind.Ring.intCast_ofNat (α := GFqRing.PolyQuotient f hf) n
  · intro i
    apply GFqField.ext
    simpa using Lean.Grind.Ring.intCast_neg (α := GFqRing.PolyQuotient f hf) i

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.CommRing (FiniteField f hf hp hirr) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply GFqField.ext
  simpa using Lean.Grind.CommSemiring.mul_comm a.toQuotient b.toQuotient

private theorem eq_inv_of_mul_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {a b : FiniteField f hf hp hirr} (h : a * b = 1) :
    a = b⁻¹ := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  by_cases hb : b = 0
  · subst b
    have hmul_zero : a * (0 : FiniteField f hf hp hirr) = 0 :=
      Lean.Grind.Semiring.mul_zero a
    have hzero_one : (0 : FiniteField f hf hp hirr) = 1 :=
      hmul_zero.symm.trans h
    exfalso
    exact zero_ne_one f hf hp hirr hzero_one
  · replace h := congrArg (fun x => x * b⁻¹) h
    calc
      a = a * 1 := (Lean.Grind.Semiring.mul_one a).symm
      _ = a * (b * b⁻¹) := by rw [mul_inv_cancel hb]
      _ = (a * b) * b⁻¹ := (Lean.Grind.Semiring.mul_assoc a b b⁻¹).symm
      _ = 1 * b⁻¹ := h
      _ = b⁻¹ := Lean.Grind.Semiring.one_mul b⁻¹

private theorem inv_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    (1 : FiniteField f hf hp hirr)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one (Lean.Grind.Semiring.mul_one (1 : FiniteField f hf hp hirr))).symm

private theorem inv_inv
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    x⁻¹⁻¹ = x := by
  by_cases hx : x = 0
  · subst x
    simp [inv_zero]
  · symm
    apply eq_inv_of_mul_eq_one
    exact mul_inv_cancel (x := x) hx

private theorem inv_inv_def
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    (inv x)⁻¹ = x :=
  inv_inv x

private theorem pow_zero_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    pow x 0 = 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  apply GFqField.ext
  simpa using Lean.Grind.Semiring.pow_zero x.toQuotient

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Field (FiniteField f hf hp hirr) := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    simpa using div_eq_mul_inv a b
  · intro h
    exact zero_ne_one f hf hp hirr h
  · exact inv_zero f hf hp hirr
  · intro a ha
    have ha' : a ≠ (0 : FiniteField f hf hp hirr) := ha
    exact mul_inv_cancel (x := a) ha'
  · intro a
    apply GFqField.ext
    simpa [zpow] using Lean.Grind.Semiring.pow_zero a.toQuotient
  · intro a n
    apply GFqField.ext
    simpa [zpow] using Lean.Grind.Semiring.pow_succ a.toQuotient n
  · intro a n
    cases n with
    | ofNat m =>
        cases m with
        | zero =>
            change pow a 0 = (pow a 0)⁻¹
            rw [pow_zero_eq_one, inv_one]
        | succ m =>
            rfl
    | negSucc m =>
        change zpow a (Int.ofNat (m + 1)) = (zpow a (Int.negSucc m))⁻¹
        rw [zpow, zpow]
        exact (inv_inv_def (pow a (m + 1))).symm

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.IsCharP (FiniteField f hf hp hirr) p where
  ofNat_ext_iff {x y} := natCast_eq_natCast_iff_mod_eq f hf hp hirr x y

theorem frob_eq_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    frob x = x ^ p :=
  rfl

/-- Frobenius projects to the quotient-ring `p`-th power. -/
@[simp, grind =] theorem toQuotient_frob
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    (frob x).toQuotient = x.toQuotient ^ p :=
  rfl

@[simp] theorem repr_frob
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    repr (frob x) = GFqRing.repr (x.toQuotient ^ p) :=
  rfl

end GFqField
end Hex
