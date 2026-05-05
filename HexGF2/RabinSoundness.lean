import HexGF2.Irreducibility

/-!
Project-side soundness bridge from `GF2Poly.rabinTest` to
`GF2Poly.Irreducible`.

The executable certificate checker in `HexGF2/Irreducibility.lean` already
proves soundness up to the Boolean `rabinTest` predicate. This module adds the
Rabin-theorem layer from `rabinTest = true` to the project-side packed
polynomial irreducibility predicate. The top-level proof is a contrapositive
Rabin argument; the finite-field algebra leaves are stated explicitly so they
can be discharged independently.
-/
namespace Hex
namespace GF2Poly

/-! ## Foundational Rabin leaves -/

/--
The absolute polynomial `X^(2^k) - X` in characteristic two.

Packed `GF(2)` subtraction is addition, so this is represented as
`X^(2^k) + X`.
-/
def xPowSubX (k : Nat) : GF2Poly :=
  monomial (2 ^ k) + monomial 1

/--
The executable Frobenius remainder vanishes exactly when `f` divides the
absolute Rabin polynomial `X^(2^k) - X`.

This is the GF2 counterpart of the absolute-to-modular bridge used by the
generic Berlekamp Rabin soundness proof.
-/
theorem dvd_xPowSubX_iff_frobeniusDiffMod_isZero
    (f : GF2Poly) (k : Nat) :
    f ∣ xPowSubX k ↔ (frobeniusDiffMod f k).isZero = true := by
  sorry

/--
Every nonconstant factor of a packed GF2 polynomial has an irreducible factor.

The proof is the usual descent on degree, specialized to the project-side
`GF2Poly.Irreducible` predicate and the packed divisibility relation.
-/
theorem exists_irreducible_factor_of_factor
    {f a b : GF2Poly} (hab : a * b = f) (ha_pos : 0 < a.degree) :
    ∃ g : GF2Poly,
      GF2Poly.Irreducible g ∧ g ∣ a ∧
        0 < g.degree ∧ g.degree ≤ a.degree := by
  sorry

/--
Forward Rabin degree theorem for packed GF2 polynomials.

If an irreducible `g` of positive degree divides `X^(2^n) - X`, then
`deg g` divides `n`.
-/
theorem degree_dvd_of_irreducible_dvd_xPowSubX
    {g : GF2Poly} (hg_irr : GF2Poly.Irreducible g)
    (hg_pos : 0 < g.degree) {n : Nat}
    (_hg_dvd : g ∣ xPowSubX n) :
    g.degree ∣ n := by
  sorry

/--
Backward Rabin degree theorem for packed GF2 polynomials.

An irreducible `g` of degree `d > 0` divides `X^(2^d) - X`.
-/
theorem irreducible_dvd_xPowSubX_degree
    {g : GF2Poly} (hg_irr : GF2Poly.Irreducible g)
    (hg_pos : 0 < g.degree) :
    g ∣ xPowSubX g.degree := by
  sorry

/--
Divisibility chain on Rabin polynomials: if `d ∣ m`, then
`X^(2^d) - X` divides `X^(2^m) - X`.
-/
theorem xPowSubX_dvd_of_dvd {d m : Nat} (_hdvd : d ∣ m) :
    xPowSubX d ∣ xPowSubX m := by
  sorry

/--
Every positive proper divisor of `n` is contained in a maximal proper divisor
of `n`.

This routes an irreducible factor degree to one of the gcd legs checked by
`rabinTest`.
-/
theorem exists_maximalProperDivisor_dvd
    {n d : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m := by
  sorry

/--
A common divisor of `f` and the absolute Rabin polynomial also divides the
modular Frobenius remainder used by the executable test.
-/
theorem dvd_frobeniusDiffMod_of_dvd_dvd
    {f g : GF2Poly} (hg_dvd_f : g ∣ f) {k : Nat}
    (hg_dvd_pow : g ∣ xPowSubX k) :
    g ∣ frobeniusDiffMod f k := by
  sorry

/--
A divisor of a unit polynomial is a unit polynomial.

For packed GF2 this is a degree argument over the executable divisibility
relation.
-/
theorem isUnitPolynomial_of_dvd_isUnitPolynomial
    {g h : GF2Poly} (hgh : g ∣ h) (hh : isUnitPolynomial h = true) :
    isUnitPolynomial g = true := by
  sorry

/-! ## Small structural helpers -/

/-- Local divisibility transitivity for `GF2Poly`. -/
private theorem dvd_trans {a b c : GF2Poly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, mul_assoc]

/-- A polynomial of positive degree is nonzero. -/
theorem ne_zero_of_pos_degree {f : GF2Poly} (hpos : 0 < f.degree) : f ≠ 0 := by
  intro hzero
  rw [hzero] at hpos
  simp at hpos

/-- The left factor in a factorization of a nonzero polynomial is nonzero. -/
theorem factor_ne_zero_of_ne_zero
    {f a b : GF2Poly} (hab : a * b = f) (hf_ne_zero : f ≠ 0) :
    a ≠ 0 := by
  intro hzero
  rw [hzero, zero_mul] at hab
  exact hf_ne_zero hab.symm

/-- A nonzero polynomial whose degree is not zero has positive degree. -/
theorem pos_degree_of_ne_zero_of_not_degree_zero
    {a : GF2Poly} (_ha_ne_zero : a ≠ 0) (ha_not_unit : a.degree ≠ 0) :
    0 < a.degree := by
  omega

/-- A nonzero packed `GF2Poly` has a successful `degree?` computation. -/
private theorem degree?_isSome_of_ne_zero
    {p : GF2Poly} (hp : p ≠ 0) :
    ∃ d, p.degree? = some d := by
  apply degree?_isSome_of_isZero_false
  cases h : p.isZero with
  | true => exact (hp (eq_zero_of_isZero h)).elim
  | false => rfl

/--
The degree of a factor `a` is strictly less than the degree of `f` whenever
the cofactor `b` has positive degree.
-/
theorem factor_degree_lt
    {f a b : GF2Poly}
    (hab : a * b = f) (ha_ne_zero : a ≠ 0) (hb_pos : 0 < b.degree) :
    a.degree < f.degree := by
  have hb_ne_zero : b ≠ 0 := ne_zero_of_pos_degree hb_pos
  obtain ⟨da, hda⟩ := degree?_isSome_of_ne_zero ha_ne_zero
  obtain ⟨db, hdb⟩ := degree?_isSome_of_ne_zero hb_ne_zero
  have hab_deg : (a * b).degree? = some (da + db) :=
    degree?_mul_of_degree?_eq_some hda hdb
  have hf_deg : f.degree? = some (da + db) := hab ▸ hab_deg
  have ha_deg : a.degree = da := degree_eq_of_degree?_eq_some hda
  have hb_deg : b.degree = db := degree_eq_of_degree?_eq_some hdb
  have hf_deg_eq : f.degree = da + db := degree_eq_of_degree?_eq_some hf_deg
  rw [hb_deg] at hb_pos
  omega

/-- A positive-degree polynomial is not a unit polynomial. -/
theorem isUnitPolynomial_eq_false_of_pos_degree
    {g : GF2Poly} (hpos : 0 < g.degree) :
    isUnitPolynomial g = false := by
  unfold isUnitPolynomial
  cases hdeg : g.degree? with
  | none =>
      rfl
  | some k =>
      have hk : k = g.degree := by
        exact (degree_eq_of_degree?_eq_some hdeg).symm
      subst hk
      cases hcase : g.degree with
      | zero =>
          simp [hcase] at hpos
      | succ _ =>
          rfl

/--
The `m`-th maximal-proper-divisor witness of `rabinTest`: if the test passes,
the gcd leg holds at every maximal proper divisor.
-/
theorem rabinCoprimeTest_of_mem_maximalProperDivisors
    (f : GF2Poly)
    (hwitnesses : (rabinWitnesses f).all Prod.snd = true)
    {m : Nat} (hm : m ∈ maximalProperDivisors f.degree) :
    rabinCoprimeTest f m = true := by
  unfold rabinWitnesses at hwitnesses
  rw [List.all_eq_true] at hwitnesses
  have hmem :
      (m, rabinCoprimeTest f m) ∈
        (maximalProperDivisors f.degree).map
          (fun d => (d, rabinCoprimeTest f d)) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  exact hwitnesses _ hmem

/--
If `gcd(f, q)` is a unit polynomial and `g` divides both `f` and `q`, then
`g` is itself a unit polynomial.
-/
theorem isUnitPolynomial_of_dvd_gcd_isUnit
    {f q g : GF2Poly}
    (hgf : g ∣ f) (hgq : g ∣ q)
    (hgcd : isUnitPolynomial (gcd f q) = true) :
  isUnitPolynomial g = true :=
  isUnitPolynomial_of_dvd_isUnitPolynomial
    (dvd_gcd g f q hgf hgq) hgcd

/-! ## Bridge theorem -/

/--
Soundness of the executable Rabin test against `GF2Poly.Irreducible`.

The proof decomposes the Boolean test, picks an irreducible factor of any
nontrivial factorization, routes its degree through a maximal proper divisor,
and contradicts the corresponding gcd leg.
-/
theorem rabinTest_imp_irreducible
    (f : GF2Poly) (hrabin : rabinTest f = true) :
    GF2Poly.Irreducible f := by
  simp only [rabinTest, Bool.and_eq_true, decide_eq_true_eq] at hrabin
  obtain ⟨⟨hpos, hdivides⟩, hwitnesses⟩ := hrabin
  have hdiff_isZero :
      (frobeniusDiffMod f f.degree).isZero = true := by
    unfold rabinDividesTest at hdivides
    exact hdivides
  have hf_dvd_xPowSubX_n : f ∣ xPowSubX f.degree :=
    (dvd_xPowSubX_iff_frobeniusDiffMod_isZero f f.degree).mpr hdiff_isZero
  have hf_ne_zero : f ≠ 0 := ne_zero_of_pos_degree hpos
  refine ⟨hf_ne_zero, ?_⟩
  intro a b hab
  by_cases ha_unit : a.degree = 0
  · exact Or.inl ha_unit
  refine Or.inr ?_
  by_cases hb_unit : b.degree = 0
  · exact hb_unit
  exfalso
  have ha_ne_zero : a ≠ 0 := factor_ne_zero_of_ne_zero hab hf_ne_zero
  have hb_ne_zero : b ≠ 0 := by
    have hba : b * a = f := by
      rw [mul_comm]
      exact hab
    exact factor_ne_zero_of_ne_zero hba hf_ne_zero
  have ha_pos : 0 < a.degree :=
    pos_degree_of_ne_zero_of_not_degree_zero ha_ne_zero ha_unit
  have hb_pos : 0 < b.degree :=
    pos_degree_of_ne_zero_of_not_degree_zero hb_ne_zero hb_unit
  have ha_lt : a.degree < f.degree :=
    factor_degree_lt hab ha_ne_zero hb_pos
  obtain ⟨g, hg_irr, hg_dvd_a, hg_deg_pos, hg_deg_le_a⟩ :=
    exists_irreducible_factor_of_factor hab ha_pos
  have hg_dvd_f : g ∣ f := by
    rcases hg_dvd_a with ⟨r, hr⟩
    refine ⟨r * b, ?_⟩
    calc
      f = a * b := hab.symm
      _ = (g * r) * b := by rw [hr]
      _ = g * (r * b) := by rw [mul_assoc]
  have hg_dvd_xPowSubX_n : g ∣ xPowSubX f.degree :=
    dvd_trans hg_dvd_f hf_dvd_xPowSubX_n
  have hdeg_dvd : g.degree ∣ f.degree :=
    degree_dvd_of_irreducible_dvd_xPowSubX hg_irr hg_deg_pos hg_dvd_xPowSubX_n
  have hdeg_lt : g.degree < f.degree :=
    Nat.lt_of_le_of_lt hg_deg_le_a ha_lt
  obtain ⟨m, hm_mem, hdeg_dvd_m⟩ :=
    exists_maximalProperDivisor_dvd hg_deg_pos hdeg_dvd hdeg_lt
  have hg_dvd_xPowSubX_deg : g ∣ xPowSubX g.degree :=
    irreducible_dvd_xPowSubX_degree hg_irr hg_deg_pos
  have hxPow_dvd_xPow : xPowSubX g.degree ∣ xPowSubX m :=
    xPowSubX_dvd_of_dvd hdeg_dvd_m
  have hg_dvd_xPowSubX_m : g ∣ xPowSubX m :=
    dvd_trans hg_dvd_xPowSubX_deg hxPow_dvd_xPow
  have hg_dvd_frob : g ∣ frobeniusDiffMod f m :=
    dvd_frobeniusDiffMod_of_dvd_dvd hg_dvd_f hg_dvd_xPowSubX_m
  have hcoprime : rabinCoprimeTest f m = true :=
    rabinCoprimeTest_of_mem_maximalProperDivisors f hwitnesses hm_mem
  have hgcd_unit : isUnitPolynomial (gcd f (frobeniusDiffMod f m)) = true := by
    unfold rabinCoprimeTest at hcoprime
    exact hcoprime
  have hg_unit : isUnitPolynomial g = true :=
    isUnitPolynomial_of_dvd_gcd_isUnit hg_dvd_f hg_dvd_frob hgcd_unit
  have hg_not_unit : isUnitPolynomial g = false :=
    isUnitPolynomial_eq_false_of_pos_degree hg_deg_pos
  rw [hg_not_unit] at hg_unit
  exact Bool.noConfusion hg_unit

/--
Accepted executable irreducibility certificates imply project-side
`GF2Poly.Irreducible`, composing checker soundness with Rabin soundness.
-/
theorem checkIrreducibilityCertificate_imp_irreducible
    (f : GF2Poly) (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificate f cert = true) :
    GF2Poly.Irreducible f :=
  rabinTest_imp_irreducible f
    (checkIrreducibilityCertificate_rabinTest f cert hcheck)

end GF2Poly
end Hex
