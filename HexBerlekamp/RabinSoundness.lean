import HexBerlekamp.Irreducibility

/-!
Project-side soundness bridge from `Berlekamp.rabinTest` to
`FpPoly.Irreducible`.

The executable irreducibility surface in `HexBerlekamp/Irreducibility.lean`
gives a `Bool` predicate `rabinTest f hmonic` capturing the three legs of
Rabin's criterion phrased through `frobeniusXPowMod`. This module bridges
`rabinTest = true` to the project-side `FpPoly.Irreducible` predicate from
`HexPolyFp/Basic.lean`, without going through Mathlib.

The bridge proof reduces to a small set of foundational lemmas tracked as
their own follow-up issues; `rabinTest_imp_irreducible` only orchestrates
them in a single contrapositive argument.
-/

namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

section

variable [ZMod64.PrimeModulus p]

/--
The polynomial `X^(p^k) - X` viewed inside the executable `FpPoly p` model.

Used to phrase the absolute (not modular) divisibility leg `f ∣ X^(p^n) - X`
underlying Rabin's test.
-/
def xPowSubX (k : Nat) : FpPoly p :=
  DensePoly.monomial (p ^ k) (1 : ZMod64 p) - FpPoly.X

/-! ### Foundational lemmas

The following declarations are stated with proofs deferred to their own
follow-up issues. Every other declaration in this file is a small
orchestration step on top of them. -/

/--
`f` divides `X^(p^k) - X` (in the absolute sense) exactly when the
Berlekamp Frobenius remainder `frobeniusDiffMod f hmonic k` vanishes.

Bridges the absolute polynomial `xPowSubX k` to the modular Frobenius
remainder used by the executable `rabinTest`. The proof goes through
`frobeniusDiffMod = (xPowSubX k) % f`, which itself relies on
`frobeniusXPowMod_eq_powMod` for the absolute Frobenius identity.
-/
theorem dvd_xPowSubX_iff_frobeniusDiffMod_isZero
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    f ∣ xPowSubX (p := p) k ↔ (frobeniusDiffMod f hmonic k).isZero = true := by
  sorry

omit [ZMod64.PrimeModulus p] in
/--
A polynomial of positive degree is nonzero.

Used to discharge the `f ≠ 0` leg of `FpPoly.Irreducible` and to show
that the factors `a, b` of `f` are individually nonzero.
-/
theorem ne_zero_of_pos_degree
    {f : FpPoly p} (hpos : 0 < f.degree?.getD 0) :
    f ≠ 0 := by
  intro hzero
  rw [hzero] at hpos
  unfold DensePoly.degree? at hpos
  simp at hpos

/--
Existence of a monic irreducible factor for any non-unit factor.

For a polynomial `a : FpPoly p` of positive degree appearing as a factor
of a monic polynomial `f`, there is a monic irreducible `g ∣ a` with
`0 < deg g ≤ deg a`. Standard descent on degree, with the monic-associate
rescaling needed when `a` itself is not monic.
-/
theorem exists_monic_irreducible_factor_of_factor
    {f a b : FpPoly p}
    (hmonic_f : DensePoly.Monic f) (hab : a * b = f)
    (ha_pos : 0 < a.degree?.getD 0) :
    ∃ g : FpPoly p,
      FpPoly.Irreducible g ∧ DensePoly.Monic g ∧ g ∣ a ∧
        0 < g.degree?.getD 0 ∧ g.degree?.getD 0 ≤ a.degree?.getD 0 := by
  sorry

/--
Rabin's degree-divisibility theorem in its `FpPoly` form (forward
direction).

If `g` is a monic irreducible polynomial of degree `d > 0` over `F_p` and
`g ∣ X^(p^n) - X`, then `d ∣ n`. The standard proof works in the residue
field `F_p[X]/(g)` and shows that `X` has multiplicative order dividing
`p^d - 1`, forcing `d ∣ n` via the order of the Frobenius automorphism.

This is the deepest finite-field ingredient of Rabin's test soundness.
-/
theorem degree_dvd_of_irreducible_dvd_xPowSubX
    {g : FpPoly p} (hg_irr : FpPoly.Irreducible g)
    (hg_monic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) {n : Nat}
    (_hg_dvd : g ∣ xPowSubX (p := p) n) :
    g.degree?.getD 0 ∣ n := by
  sorry

/--
Rabin's degree-divisibility theorem in its `FpPoly` form (backward
direction).

A monic irreducible polynomial `g` of degree `d > 0` over `F_p` divides
`X^(p^d) - X`. The standard proof builds the residue field
`F_p[X]/(g)` of order `p^d` and applies the Frobenius identity
`α^(p^d) = α` for every element of a finite field of order `p^d`.
-/
theorem irreducible_dvd_xPowSubX_degree
    {g : FpPoly p} (hg_irr : FpPoly.Irreducible g)
    (hg_monic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) :
    g ∣ xPowSubX (p := p) (g.degree?.getD 0) := by
  sorry

/--
Divisibility chain on Rabin polynomials: if `d ∣ m`, then
`X^(p^d) - X` divides `X^(p^m) - X` inside `FpPoly p`.

A standard polynomial-algebra identity. Used to lift divisibility of an
irreducible factor `g` from `X^(p^d) - X` to `X^(p^m) - X` where `m` is a
maximal proper divisor of `n` in which `d` lives.
-/
theorem xPowSubX_dvd_of_dvd
    {d m : Nat} (_hdvd : d ∣ m) :
    xPowSubX (p := p) d ∣ xPowSubX (p := p) m := by
  sorry

private theorem lt_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : d < n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, hk, rfl⟩, _⟩
  omega

private theorem pos_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : 0 < d := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, _, rfl⟩, _⟩
  omega

private theorem dvd_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : d ∣ n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, _, rfl⟩, hmod⟩
  exact Nat.dvd_of_mod_eq_zero hmod

private theorem mem_properDivisors_of_pos_of_dvd_of_lt {n d : Nat}
    (hpos : 0 < d) (hdvd : d ∣ n) (hlt : d < n) :
    d ∈ properDivisors n := by
  unfold properDivisors
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨d - 1, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · exact Nat.mod_eq_zero_of_dvd hdvd

private theorem exists_maximalProperDivisor_dvd_aux (n : Nat) :
    ∀ (k d : Nat), 0 < d → d ∣ n → d < n → n - d ≤ k →
        ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m
  | 0, _d, _hpos, _hdvd, hlt, hbound => by omega
  | k + 1, d, hpos, hdvd, hlt, hbound => by
      by_cases hmax : ∃ e, e ∈ properDivisors n ∧ d < e ∧ d ∣ e
      · obtain ⟨e, he_mem, he_lt, he_dvd⟩ := hmax
        have he_lt_n := lt_of_mem_properDivisors he_mem
        have he_dvd_n := dvd_of_mem_properDivisors he_mem
        have he_pos : 0 < e := Nat.lt_of_lt_of_le hpos (Nat.le_of_lt he_lt)
        have hsmaller : n - e ≤ k := by omega
        obtain ⟨m, hm_mem, hm_dvd⟩ :=
          exists_maximalProperDivisor_dvd_aux n k e he_pos he_dvd_n he_lt_n hsmaller
        exact ⟨m, hm_mem, Nat.dvd_trans he_dvd hm_dvd⟩
      · refine ⟨d, ?_, Nat.dvd_refl d⟩
        have hd_in : d ∈ properDivisors n :=
          mem_properDivisors_of_pos_of_dvd_of_lt hpos hdvd hlt
        unfold maximalProperDivisors
        simp only [List.mem_filter]
        refine ⟨hd_in, ?_⟩
        have hany_false :
            (properDivisors n).any
                (fun e => decide (d < e) && decide (e % d = 0)) = false := by
          apply Bool.eq_false_iff.mpr
          intro hany
          rw [List.any_eq_true] at hany
          obtain ⟨e, he_mem, he_cond⟩ := hany
          simp only [Bool.and_eq_true, decide_eq_true_eq] at he_cond
          exact hmax ⟨e, he_mem, he_cond.1, Nat.dvd_of_mod_eq_zero he_cond.2⟩
        rw [hany_false]
        rfl

/--
Every positive proper divisor `d` of `n` is dominated by some maximal
proper divisor of `n` (with `d` dividing it).

Combinatorial fact about the proper-divisor lattice. Used in the
contrapositive proof to route an irreducible factor's degree `d` to a
divisor at which the gcd leg of `rabinTest` rules out divisibility.
-/
theorem exists_maximalProperDivisor_dvd
    {n d : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m :=
  exists_maximalProperDivisor_dvd_aux n (n - d) d hd_pos hd_dvd hd_lt (Nat.le_refl _)

/--
A `g` that divides both `f` and `xPowSubX k` also divides the modular
Frobenius remainder `frobeniusDiffMod f hmonic k`.

Direct consequence of the absolute–modular Frobenius identity together
with the `divMod_spec` characterization of polynomial remainders.
-/
theorem dvd_frobeniusDiffMod_of_dvd_dvd
    {f g : FpPoly p} (hmonic : DensePoly.Monic f)
    (_hg_dvd_f : g ∣ f) {k : Nat}
    (_hg_dvd_pow : g ∣ xPowSubX (p := p) k) :
    g ∣ frobeniusDiffMod f hmonic k := by
  sorry

/--
A divisor of a unit polynomial is itself a unit polynomial.

Routine consequence of degree arithmetic: if `g ∣ h` and `h` has degree 0
with nonzero constant, then `g` also has degree 0 with nonzero constant.
-/
theorem isUnitPolynomial_of_dvd_isUnitPolynomial
    {g h : FpPoly p} (_hgh : g ∣ h) (_hh : isUnitPolynomial h = true) :
    isUnitPolynomial g = true := by
  sorry

omit [ZMod64.PrimeModulus p] in
/-- The factor `a` of a nontrivial product `a * b = f` is nonzero. -/
theorem factor_ne_zero_of_ne_zero
    {f a b : FpPoly p} (hab : a * b = f) (hf_ne_zero : f ≠ 0) :
    a ≠ 0 := by
  intro hzero
  rw [hzero, FpPoly.zero_mul] at hab
  exact hf_ne_zero hab.symm

omit [ZMod64.PrimeModulus p] in
/--
A nonzero polynomial whose `degree?` is not `some 0` has positive degree.
-/
theorem pos_degree_of_ne_zero_of_not_isUnit
    {a : FpPoly p} (ha_ne_zero : a ≠ 0)
    (ha_not_unit : a.degree? ≠ some 0) :
    0 < a.degree?.getD 0 := by
  -- Show `a.size > 0` from `a ≠ 0`.
  have ha_size_pos : 0 < a.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply ha_ne_zero
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
  have ha_size_ne_zero : a.size ≠ 0 := Nat.pos_iff_ne_zero.mp ha_size_pos
  -- Compute `a.degree? = some (a.size - 1)`.
  have hdeg : a.degree? = some (a.size - 1) := by
    unfold DensePoly.degree?
    simp [ha_size_ne_zero]
  rw [hdeg] at ha_not_unit
  rw [hdeg]
  -- `some (a.size - 1) ≠ some 0 ⟹ a.size - 1 ≠ 0 ⟹ 0 < a.size - 1`.
  have : a.size - 1 ≠ 0 := fun h => ha_not_unit (by rw [h])
  simp
  omega

/--
The degree of a factor `a` is strictly less than the degree of `f` whenever
the cofactor `b` has positive degree. Phrased relative to `basisSize` to
match the Berlekamp / Rabin scaffolding.
-/
theorem factor_degree_lt_basisSize
    {f a b : FpPoly p}
    (_hab : a * b = f) (_hb_pos : 0 < b.degree?.getD 0) :
    a.degree?.getD 0 < basisSize f := by
  sorry

omit [ZMod64.PrimeModulus p] in
/--
The `m`-th maximal-proper-divisor witness of `rabinTest`: when the test
passes, every entry of `rabinWitnesses` is `true`, hence the gcd leg
holds at every maximal proper divisor.
-/
theorem rabinCoprimeTest_of_mem_maximalProperDivisors
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hwitnesses : (rabinWitnesses f hmonic).all Prod.snd = true)
    {m : Nat} (hm : m ∈ maximalProperDivisors (basisSize f)) :
    rabinCoprimeTest f hmonic m = true := by
  unfold rabinWitnesses at hwitnesses
  rw [List.all_eq_true] at hwitnesses
  have hmem :
      (m, rabinCoprimeTest f hmonic m) ∈
        (maximalProperDivisors (basisSize f)).map
          (fun d => (d, rabinCoprimeTest f hmonic d)) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  exact hwitnesses _ hmem

/-! ### Structural lemmas

These small consequences only use the foundational lemmas above plus
existing infrastructure in `HexBerlekamp.Irreducibility`. -/

omit [ZMod64.PrimeModulus p] in
/-- Local divisibility transitivity for `FpPoly p`. -/
private theorem fp_dvd_trans {a b c : FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, FpPoly.mul_assoc]

omit [ZMod64.PrimeModulus p] in
/-- A polynomial of positive degree is not the unit polynomial. -/
theorem isUnitPolynomial_eq_false_of_pos_degree
    {g : FpPoly p} (hpos : 0 < g.degree?.getD 0) :
    isUnitPolynomial g = false := by
  unfold isUnitPolynomial
  cases hdeg : g.degree? with
  | none => rfl
  | some k =>
    have hk : k = g.degree?.getD 0 := by simp [hdeg]
    subst hk
    cases hcase : g.degree?.getD 0 with
    | zero =>
        simp [hcase] at hpos
    | succ _ => rfl

/--
If `gcd(f, q)` is a unit polynomial and `g` divides both `f` and `q`,
then `g` is itself a unit polynomial.
-/
theorem isUnitPolynomial_of_dvd_gcd_isUnit
    {f q g : FpPoly p}
    (hgf : g ∣ f) (hgq : g ∣ q)
    (hgcd : isUnitPolynomial (DensePoly.gcd f q) = true) :
    isUnitPolynomial g = true :=
  isUnitPolynomial_of_dvd_isUnitPolynomial
    (DensePoly.dvd_gcd g f q hgf hgq) hgcd

/-! ### Bridge theorem -/

/--
Soundness of the executable Rabin test against the project-side
`FpPoly.Irreducible` predicate.

The proof orchestrates the foundational lemmas above. The combinatorial
shape (decomposing `rabinTest`, picking a monic irreducible factor of
size strictly between `0` and `n`, routing through a maximal proper
divisor, and contradicting the gcd leg) lives here. The heavy
mathematical content (Rabin's degree theorem in both directions,
finite-field factor existence, the absolute–modular Frobenius bridge,
and the `xPowSubX` divisibility chain) is delegated to the foundational
sorries above.
-/
theorem rabinTest_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hrabin : rabinTest f hmonic = true) :
    FpPoly.Irreducible f := by
  -- Decompose the executable test surface.
  simp only [rabinTest, Bool.and_eq_true, decide_eq_true_eq] at hrabin
  obtain ⟨⟨hpos, hdivides⟩, hwitnesses⟩ := hrabin
  -- Modular and absolute forms of the divisibility leg.
  have hdiff_isZero :
      (frobeniusDiffMod f hmonic (basisSize f)).isZero = true := by
    unfold rabinDividesTest at hdivides
    exact hdivides
  have hf_dvd_xPowSubX_n :
      f ∣ xPowSubX (p := p) (basisSize f) :=
    (dvd_xPowSubX_iff_frobeniusDiffMod_isZero f hmonic (basisSize f)).mpr
      hdiff_isZero
  -- `f ≠ 0` from positive degree.
  have hf_ne_zero : f ≠ 0 := ne_zero_of_pos_degree hpos
  refine ⟨hf_ne_zero, ?_⟩
  intro a b hab
  -- Reduce the disjunction to a contradiction proof using classical case analysis.
  by_cases ha_unit : a.degree? = some 0
  · exact Or.inl ha_unit
  refine Or.inr ?_
  by_cases hb_unit : b.degree? = some 0
  · exact hb_unit
  exfalso
  -- Both factors are nonconstant. Derive a contradiction with `rabinTest`.
  have ha_ne_zero : a ≠ 0 := factor_ne_zero_of_ne_zero hab hf_ne_zero
  have hb_ne_zero : b ≠ 0 := by
    have hba : b * a = f := by rw [FpPoly.mul_comm]; exact hab
    exact factor_ne_zero_of_ne_zero hba hf_ne_zero
  have ha_pos : 0 < a.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit ha_ne_zero ha_unit
  have hb_pos : 0 < b.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit hb_ne_zero hb_unit
  have ha_lt : a.degree?.getD 0 < basisSize f :=
    factor_degree_lt_basisSize hab hb_pos
  -- Pick a monic irreducible factor `g` of `a`.
  obtain ⟨g, hg_irr, hg_monic, hg_dvd_a, hg_deg_pos, hg_deg_le_a⟩ :=
    exists_monic_irreducible_factor_of_factor hmonic hab ha_pos
  -- `g ∣ f` via `g ∣ a ∣ f`.
  have hg_dvd_f : g ∣ f := by
    rcases hg_dvd_a with ⟨r, hr⟩
    refine ⟨r * b, ?_⟩
    calc f = a * b := hab.symm
      _ = (g * r) * b := by rw [hr]
      _ = g * (r * b) := by rw [FpPoly.mul_assoc]
  -- `g ∣ X^(p^n) - X` from transitivity.
  have hg_dvd_xPowSubX_n : g ∣ xPowSubX (p := p) (basisSize f) :=
    fp_dvd_trans hg_dvd_f hf_dvd_xPowSubX_n
  -- Rabin: `deg g ∣ basisSize f`.
  have hdeg_dvd : g.degree?.getD 0 ∣ basisSize f :=
    degree_dvd_of_irreducible_dvd_xPowSubX hg_irr hg_monic hg_deg_pos
      hg_dvd_xPowSubX_n
  -- `deg g < basisSize f` because `deg g ≤ deg a < basisSize f`.
  have hdeg_lt : g.degree?.getD 0 < basisSize f :=
    Nat.lt_of_le_of_lt hg_deg_le_a ha_lt
  -- Route `deg g` through some maximal proper divisor `m` of `basisSize f`.
  obtain ⟨m, hm_mem, hdeg_dvd_m⟩ :=
    exists_maximalProperDivisor_dvd hg_deg_pos hdeg_dvd hdeg_lt
  -- `g ∣ X^(p^(deg g)) - X` (Rabin backward direction).
  have hg_dvd_xPowSubX_deg : g ∣ xPowSubX (p := p) (g.degree?.getD 0) :=
    irreducible_dvd_xPowSubX_degree hg_irr hg_monic hg_deg_pos
  -- `X^(p^(deg g)) - X ∣ X^(p^m) - X` via the divisibility chain.
  have hxPow_dvd_xPow : xPowSubX (p := p) (g.degree?.getD 0) ∣
      xPowSubX (p := p) m :=
    xPowSubX_dvd_of_dvd hdeg_dvd_m
  have hg_dvd_xPowSubX_m : g ∣ xPowSubX (p := p) m :=
    fp_dvd_trans hg_dvd_xPowSubX_deg hxPow_dvd_xPow
  -- Lift to `g ∣ frobeniusDiffMod f hmonic m`.
  have hg_dvd_frob : g ∣ frobeniusDiffMod f hmonic m :=
    dvd_frobeniusDiffMod_of_dvd_dvd hmonic hg_dvd_f hg_dvd_xPowSubX_m
  -- The gcd leg of `rabinTest` at `m` says the gcd is a unit polynomial.
  have hcoprime : rabinCoprimeTest f hmonic m = true :=
    rabinCoprimeTest_of_mem_maximalProperDivisors f hmonic hwitnesses hm_mem
  have hgcd_unit :
      isUnitPolynomial (DensePoly.gcd f (frobeniusDiffMod f hmonic m)) = true := by
    unfold rabinCoprimeTest frobeniusDiffMod at hcoprime
    -- `rabinCoprimeTest` is exactly `isUnitPolynomial (gcd f (frobeniusDiffMod _ _ m))`.
    exact hcoprime
  -- A common divisor of `f` and `frobeniusDiffMod f hmonic m` is a unit.
  have hg_unit : isUnitPolynomial g = true :=
    isUnitPolynomial_of_dvd_gcd_isUnit hg_dvd_f hg_dvd_frob hgcd_unit
  -- But `g` has positive degree, contradiction.
  have hg_not_unit : isUnitPolynomial g = false :=
    isUnitPolynomial_eq_false_of_pos_degree hg_deg_pos
  rw [hg_not_unit] at hg_unit
  exact Bool.noConfusion hg_unit

/-! ### Convenience corollary for the certificate checker -/

/--
Accepted executable irreducibility certificates imply project-side
`FpPoly.Irreducible`, composing
`checkIrreducibilityCertificate_rabinTest` with the Rabin soundness
bridge above.
-/
theorem checkIrreducibilityCertificate_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificate f hmonic cert = true) :
    FpPoly.Irreducible f :=
  rabinTest_imp_irreducible f hmonic
    (checkIrreducibilityCertificate_rabinTest f hmonic cert hcheck)

end

end Berlekamp
end Hex
