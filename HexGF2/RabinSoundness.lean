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

/-! ## Basic divisibility helpers -/

private theorem mulXk_zero' (p : GF2Poly) : p.mulXk 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mulXk, coeff_shiftLeft]
  simp [coeff]

private theorem one_mul' (p : GF2Poly) : (1 : GF2Poly) * p = p := by
  show monomial 0 * p = p
  rw [monomial_mul, mulXk_zero']

private theorem mul_one' (p : GF2Poly) : p * (1 : GF2Poly) = p := by
  rw [mul_comm, one_mul']

private theorem dvd_refl' (p : GF2Poly) : p ∣ p :=
  ⟨1, (mul_one' p).symm⟩

private theorem dvd_zero' (p : GF2Poly) : p ∣ 0 :=
  ⟨0, (mul_zero p).symm⟩

private theorem dvd_add' {d a b : GF2Poly} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a + b := by
  rcases hda with ⟨ra, hra⟩
  rcases hdb with ⟨rb, hrb⟩
  exact ⟨ra + rb, by rw [hra, hrb, right_distrib]⟩

private theorem dvd_sub' {d a b : GF2Poly}
    (hab : d ∣ a + b) (ha : d ∣ a) : d ∣ b := by
  rcases hab with ⟨c, hc⟩
  rcases ha with ⟨e, he⟩
  refine ⟨e + c, ?_⟩
  rw [right_distrib, ← he, ← hc]
  exact (add_add_cancel_left a b).symm

private theorem dvd_mul_left' {d a : GF2Poly} (c : GF2Poly) (hda : d ∣ a) :
    d ∣ c * a := by
  rcases hda with ⟨r, hr⟩
  refine ⟨c * r, ?_⟩
  rw [hr, ← mul_assoc, ← mul_assoc, mul_comm c d]

private theorem mul_dvd_mul_left' (c : GF2Poly) {a b : GF2Poly} (h : a ∣ b) :
    c * a ∣ c * b := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, by rw [hr, mul_assoc]⟩

/-! ## Frobenius bridge helpers -/

/-- Char-2 freshman's dream: `(a + b) * (a + b) = a * a + b * b`. -/
private theorem freshman_dream (a b : GF2Poly) :
    (a + b) * (a + b) = a * a + b * b := by
  rw [right_distrib, left_distrib, left_distrib, mul_comm b a]
  rw [add_assoc, ← add_assoc (a * b) (a * b) (b * b), add_self, zero_add]

/-- The remainder added to its dividend is divisible by the divisor in
characteristic two. -/
private theorem mod_add_self_dvd (p f : GF2Poly) :
    f ∣ ((divMod p f).2 + p) := by
  refine ⟨(divMod p f).1, ?_⟩
  have hspec : (divMod p f).1 * f + (divMod p f).2 = p := divMod_spec p f
  have hexpand :
      (divMod p f).2 + p =
        (divMod p f).2 + ((divMod p f).1 * f + (divMod p f).2) := by rw [hspec]
  rw [hexpand, add_comm ((divMod p f).1 * f) ((divMod p f).2),
      ← add_assoc, add_self, zero_add, mul_comm]

/-- The iterated-squaring chain `xpow2kMod f k` equals the absolute monomial
`X^(2^k)` modulo `f`. Proved as a divisibility statement to avoid
multiplication-mod compatibility lemmas. -/
private theorem dvd_xpow2kMod_add_monomial (f : GF2Poly) :
    ∀ k, f ∣ ((xpow2kMod f k) + monomial (2 ^ k))
  | 0 => by
      show f ∣ ((monomial 1 % f) + monomial 1)
      exact mod_add_self_dvd (monomial 1) f
  | k + 1 => by
      have ih := dvd_xpow2kMod_add_monomial f k
      have hsq :
          f ∣ ((xpow2kMod f k) * (xpow2kMod f k) +
                monomial (2 ^ k) * monomial (2 ^ k)) := by
        rw [← freshman_dream]
        exact dvd_mul_left' _ ih
      have hmm : monomial (2 ^ k) * monomial (2 ^ k) = monomial (2 ^ (k + 1)) := by
        rw [monomial_mul_monomial]
        congr 1
        rw [Nat.pow_succ]
        omega
      rw [hmm] at hsq
      have hmod :
          f ∣ (((xpow2kMod f k) * (xpow2kMod f k)) % f +
                (xpow2kMod f k) * (xpow2kMod f k)) :=
        mod_add_self_dvd _ _
      have hsum := dvd_add' hsq hmod
      show f ∣ ((xpow2kMod f k) * (xpow2kMod f k) % f + monomial (2 ^ (k + 1)))
      have heq :
          ((xpow2kMod f k) * (xpow2kMod f k) + monomial (2 ^ (k + 1))) +
              ((xpow2kMod f k) * (xpow2kMod f k) % f +
                (xpow2kMod f k) * (xpow2kMod f k)) =
            (xpow2kMod f k) * (xpow2kMod f k) % f + monomial (2 ^ (k + 1)) := by
        apply ext_coeff
        intro n
        rw [coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne,
            coeff_add_eq_bne]
        cases ((xpow2kMod f k) * (xpow2kMod f k)).coeff n <;>
          cases (monomial (2 ^ (k + 1))).coeff n <;>
          cases ((xpow2kMod f k) * (xpow2kMod f k) % f).coeff n <;> rfl
      rw [heq] at hsum
      exact hsum

/-- `f` divides the (char-2) sum `xPowSubX k + frobeniusDiffMod f k`, the key
algebraic identity bridging the absolute Rabin polynomial to its modular
form. -/
private theorem dvd_xPowSubX_add_frobeniusDiffMod (f : GF2Poly) (k : Nat) :
    f ∣ (xPowSubX k + frobeniusDiffMod f k) := by
  have h1 : f ∣ ((xpow2kMod f k) + monomial (2 ^ k)) :=
    dvd_xpow2kMod_add_monomial f k
  have h2 : f ∣ ((monomial 1 % f) + monomial 1) :=
    mod_add_self_dvd (monomial 1) f
  have hsum := dvd_add' h1 h2
  show f ∣ ((monomial (2 ^ k) + monomial 1) +
            ((xpow2kMod f k) + monomial 1 % f))
  have heq :
      ((xpow2kMod f k) + monomial (2 ^ k)) +
          ((monomial 1 % f) + monomial 1) =
        (monomial (2 ^ k) + monomial 1) +
          ((xpow2kMod f k) + monomial 1 % f) := by
    apply ext_coeff
    intro n
    rw [coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne,
        coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne]
    cases (xpow2kMod f k).coeff n <;>
      cases (monomial (2 ^ k)).coeff n <;>
      cases ((monomial 1 : GF2Poly) % f).coeff n <;>
      cases (monomial 1 : GF2Poly).coeff n <;> rfl
  rw [heq] at hsum
  exact hsum

/-! ## Reduced-residue helpers -/

private theorem coeff_eq_false_of_reduced_le {p : GF2Poly} {bound n : Nat}
    (hred : p.isZero = true ∨ p.degree < bound) (hbound : bound ≤ n) :
    p.coeff n = false := by
  cases hred with
  | inl hzero =>
      rw [eq_zero_of_isZero hzero, coeff_zero]
  | inr hdegree =>
      by_cases hpzero : p.isZero = true
      · rw [eq_zero_of_isZero hpzero, coeff_zero]
      · have hpzeroFalse : p.isZero = false := by
          cases h : p.isZero <;> simp [h] at hpzero ⊢
        obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hpzeroFalse
        have hdn : d < n := by
          have hdegree' : d < bound := by
            simpa [degree, hd] using hdegree
          omega
        exact coeff_eq_false_of_degree?_lt hd hdn

private theorem add_reduced_of_reduced {p q : GF2Poly} {bound : Nat}
    (hp : p.isZero = true ∨ p.degree < bound)
    (hq : q.isZero = true ∨ q.degree < bound) :
    (p + q).isZero = true ∨ (p + q).degree < bound := by
  by_cases hsumZero : (p + q).isZero = true
  · exact Or.inl hsumZero
  · right
    have hsumZeroFalse : (p + q).isZero = false := by
      cases h : (p + q).isZero <;> simp [h] at hsumZero ⊢
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hsumZeroFalse
    have hdbound : d < bound := by
      by_cases hbound : bound ≤ d
      · have hpfalse := coeff_eq_false_of_reduced_le (p := p) hp hbound
        have hqfalse := coeff_eq_false_of_reduced_le (p := q) hq hbound
        have htrue := coeff_eq_true_of_degree?_eq_some hd
        rw [coeff_add_eq_bne, hpfalse, hqfalse] at htrue
        contradiction
      · omega
    change (p + q).degree < bound
    simpa [degree, hd] using hdbound

private theorem reduced_dvd_eq_zero {f r : GF2Poly}
    (hf : f ≠ 0) (hred : r.isZero = true ∨ r.degree < f.degree)
    (hdvd : f ∣ r) :
    r = 0 := by
  by_cases hr : r = 0
  · exact hr
  · cases hred with
    | inl hzero =>
        exact eq_zero_of_isZero hzero
    | inr hlt =>
        have hle : f.degree ≤ r.degree := degree_le_of_dvd_nonzero hf hr hdvd
        omega

/-- Each `xpow2kMod` value is a `% f` step, so it is reduced modulo `f`. -/
private theorem xpow2kMod_reduced (f : GF2Poly) (hf : f ≠ 0) :
    ∀ k, (xpow2kMod f k).isZero = true ∨
      (xpow2kMod f k).degree < f.degree
  | 0 => by
      show (monomial 1 % f).isZero = true ∨ (monomial 1 % f).degree < f.degree
      exact mod_degree_lt _ f hf
  | k + 1 => by
      show ((xpow2kMod f k) * (xpow2kMod f k) % f).isZero = true ∨
        ((xpow2kMod f k) * (xpow2kMod f k) % f).degree < f.degree
      exact mod_degree_lt _ f hf

/--
The executable Frobenius remainder vanishes exactly when `f` divides the
absolute Rabin polynomial `X^(2^k) - X`.

This is the GF2 counterpart of the absolute-to-modular bridge used by the
generic Berlekamp Rabin soundness proof.
-/
theorem dvd_xPowSubX_iff_frobeniusDiffMod_isZero
    (f : GF2Poly) (k : Nat) :
    f ∣ xPowSubX k ↔ (frobeniusDiffMod f k).isZero = true := by
  have hkey : f ∣ (xPowSubX k + frobeniusDiffMod f k) :=
    dvd_xPowSubX_add_frobeniusDiffMod f k
  refine ⟨fun hxsub => ?_, fun hzero => ?_⟩
  · -- Forward: f ∣ xPowSubX k → frobeniusDiffMod f k = 0.
    have hdiff : f ∣ frobeniusDiffMod f k := dvd_sub' hkey hxsub
    have hdiff_eq_zero : frobeniusDiffMod f k = 0 := by
      by_cases hf : f = 0
      · subst hf
        rcases hdiff with ⟨c, hc⟩
        rw [hc, zero_mul]
      · have hxpow_red := xpow2kMod_reduced f hf k
        have hmod_red := mod_degree_lt (monomial 1) f hf
        have hdiff_red :
            (frobeniusDiffMod f k).isZero = true ∨
              (frobeniusDiffMod f k).degree < f.degree := by
          show ((xpow2kMod f k) + (monomial 1 % f)).isZero = true ∨
            ((xpow2kMod f k) + (monomial 1 % f)).degree < f.degree
          exact add_reduced_of_reduced hxpow_red hmod_red
        exact reduced_dvd_eq_zero hf hdiff_red hdiff
    rw [isZero_iff_eq_zero]
    exact hdiff_eq_zero
  · -- Backward: frobeniusDiffMod = 0 → f ∣ xPowSubX k.
    have hzero_eq : frobeniusDiffMod f k = 0 := (isZero_iff_eq_zero _).mp hzero
    rw [hzero_eq, add_zero] at hkey
    exact hkey

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
Backward Rabin algebraic content packaged at the executable level.

For an irreducible packed polynomial `g` of positive degree `d`, the
iterated-squaring chain `xpow2kMod g d` returns to the residue class of `X`.
Equivalently, the residue field element `X mod g` is fixed by the `d`-fold
Frobenius endomorphism `α ↦ α^(2^d)` — the standard Fermat–Euler statement
for the residue field `F_2[X]/(g)` (which has `2^d` elements when `g` is
irreducible).

This is the deepest finite-field ingredient of Rabin's test: once it is
available, `irreducible_dvd_xPowSubX_degree` follows by char-2 cancellation.
-/
theorem xpow2kMod_eq_modX_at_degree
    {g : GF2Poly} (hg_irr : GF2Poly.Irreducible g)
    (hg_pos : 0 < g.degree) :
    xpow2kMod g g.degree = monomial 1 % g := by
  sorry

/--
Backward Rabin degree theorem for packed GF2 polynomials.

An irreducible `g` of degree `d > 0` divides `X^(2^d) - X`. The proof
combines char-2 cancellation with `xpow2kMod_eq_modX_at_degree`, which
carries the residue-field Fermat–Euler argument.
-/
theorem irreducible_dvd_xPowSubX_degree
    {g : GF2Poly} (hg_irr : GF2Poly.Irreducible g)
    (hg_pos : 0 < g.degree) :
    g ∣ xPowSubX g.degree := by
  rw [(dvd_xPowSubX_iff_frobeniusDiffMod_isZero g g.degree),
      isZero_iff_eq_zero]
  show xpow2kMod g g.degree + monomial 1 % g = 0
  rw [xpow2kMod_eq_modX_at_degree hg_irr hg_pos, add_self]

/--
Geometric-series divisibility in characteristic two: `X^k + 1` divides
`X^(k*n) + 1` for any `k` and `n`.

Iterated XOR-cancellation gives the identity
`X^(k*(n+1)) + 1 = X^k * (X^(k*n) + 1) + (X^k + 1)`,
so the result reduces by induction on `n` to the base cases `n = 0`
(both sides are zero) and `n = 1` (reflexivity).
-/
private theorem monomial_add_one_dvd_geom (k : Nat) :
    ∀ n, (monomial k + 1) ∣ (monomial (k * n) + 1)
  | 0 => by
      rw [Nat.mul_zero, show (monomial 0 : GF2Poly) = 1 from rfl, add_self]
      exact dvd_zero' _
  | n + 1 => by
      have ih := monomial_add_one_dvd_geom k n
      have heq :
          monomial (k * (n + 1)) + 1 =
            monomial k * (monomial (k * n) + 1) + (monomial k + 1) := by
        rw [right_distrib, mul_one', monomial_mul_monomial]
        rw [show k + k * n = k * (n + 1) from by rw [Nat.mul_succ]; omega]
        rw [add_assoc]
        congr 1
        rw [← add_assoc, add_self, zero_add]
      rw [heq]
      exact dvd_add' (dvd_mul_left' (monomial k) ih) (dvd_refl' _)

/--
Number-theoretic companion to `monomial_add_one_dvd_geom`: when `d ∣ m`,
the integer `2 ^ d - 1` divides `2 ^ m - 1`.

Both follow from the same telescoping identity, transposed between the
polynomial and natural-number rings.
-/
private theorem two_pow_sub_one_dvd_two_pow_sub_one_of_dvd
    {d m : Nat} (hdvd : d ∣ m) : (2 ^ d - 1) ∣ (2 ^ m - 1) := by
  obtain ⟨k, rfl⟩ := hdvd
  induction k with
  | zero => simp
  | succ k ih =>
      have h2dk_pos : 0 < 2 ^ (d * k) := Nat.two_pow_pos _
      have h2d_pos : 0 < 2 ^ d := Nat.two_pow_pos _
      have hexp : 2 ^ (d * (k + 1)) = 2 ^ d * 2 ^ (d * k) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      have hge : 2 ^ d ≤ 2 ^ d * 2 ^ (d * k) := by
        calc 2 ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ d * 2 ^ (d * k) := Nat.mul_le_mul_left _ h2dk_pos
      have hkey :
          2 ^ (d * (k + 1)) - 1 = 2 ^ d * (2 ^ (d * k) - 1) + (2 ^ d - 1) := by
        rw [hexp, Nat.mul_sub, Nat.mul_one]
        omega
      rw [hkey]
      exact Nat.dvd_add (Nat.dvd_mul_left_of_dvd ih _) (Nat.dvd_refl _)

/--
Factor `xPowSubX d = monomial 1 * (monomial (2 ^ d - 1) + 1)`.

In characteristic two this collapses `X^(2^d) + X = X * (X^(2^d - 1) + 1)`.
The factor is uniform in `d ≥ 0`: when `d = 0` both sides reduce to `0`.
-/
private theorem xPowSubX_factor (d : Nat) :
    xPowSubX d = monomial 1 * (monomial (2 ^ d - 1) + 1) := by
  unfold xPowSubX
  rw [right_distrib, mul_one', monomial_mul_monomial]
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos _
  rw [show 1 + (2 ^ d - 1) = 2 ^ d from by omega]

/--
Divisibility chain on Rabin polynomials: if `d ∣ m`, then
`X^(2^d) - X` divides `X^(2^m) - X`.
-/
theorem xPowSubX_dvd_of_dvd {d m : Nat} (hdvd : d ∣ m) :
    xPowSubX d ∣ xPowSubX m := by
  obtain ⟨n, hn⟩ :=
    two_pow_sub_one_dvd_two_pow_sub_one_of_dvd hdvd
  have hgeo : (monomial (2 ^ d - 1) + 1) ∣ (monomial (2 ^ m - 1) + 1) := by
    rw [hn]
    exact monomial_add_one_dvd_geom (2 ^ d - 1) n
  rw [xPowSubX_factor d, xPowSubX_factor m]
  exact mul_dvd_mul_left' (monomial 1) hgeo

private theorem lt_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : d < n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, hk, rfl⟩, _⟩
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
Every positive proper divisor of `n` is contained in a maximal proper divisor
of `n`.

This routes an irreducible factor degree to one of the gcd legs checked by
`rabinTest`.
-/
theorem exists_maximalProperDivisor_dvd
    {n d : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m :=
  exists_maximalProperDivisor_dvd_aux n (n - d) d hd_pos hd_dvd hd_lt (Nat.le_refl _)

/--
A common divisor of `f` and the absolute Rabin polynomial also divides the
modular Frobenius remainder used by the executable test.
-/
theorem dvd_frobeniusDiffMod_of_dvd_dvd
    {f g : GF2Poly} (hg_dvd_f : g ∣ f) {k : Nat}
    (hg_dvd_pow : g ∣ xPowSubX k) :
    g ∣ frobeniusDiffMod f k := by
  have hf_dvd_sum : f ∣ (xPowSubX k + frobeniusDiffMod f k) :=
    dvd_xPowSubX_add_frobeniusDiffMod f k
  have hg_dvd_sum : g ∣ (xPowSubX k + frobeniusDiffMod f k) := by
    rcases hg_dvd_f with ⟨c, hc⟩
    rcases hf_dvd_sum with ⟨d, hd⟩
    exact ⟨c * d, by rw [hd, hc, mul_assoc]⟩
  exact dvd_sub' hg_dvd_sum hg_dvd_pow

/--
A divisor of a unit polynomial is a unit polynomial.

For packed GF2 this is a degree argument over the executable divisibility
relation.
-/
theorem isUnitPolynomial_of_dvd_isUnitPolynomial
    {g h : GF2Poly} (hgh : g ∣ h) (hh : isUnitPolynomial h = true) :
    isUnitPolynomial g = true := by
  have hh_deg? : h.degree? = some 0 := by
    unfold isUnitPolynomial at hh
    cases hdeg : h.degree? with
    | none => rw [hdeg] at hh; simp at hh
    | some k =>
        rw [hdeg] at hh
        cases k with
        | zero => rfl
        | succ _ => simp at hh
  have hh_ne_zero : h ≠ 0 := ne_zero_of_degree?_eq_some hh_deg?
  have hg_ne_zero : g ≠ 0 := by
    intro hg
    rcases hgh with ⟨r, hr⟩
    apply hh_ne_zero
    rw [hr, hg, zero_mul]
  have hh_deg : h.degree = 0 := degree_eq_of_degree?_eq_some hh_deg?
  have hgle : g.degree ≤ h.degree :=
    degree_le_of_dvd_nonzero hg_ne_zero hh_ne_zero hgh
  rw [hh_deg] at hgle
  have hg_deg_zero : g.degree = 0 := Nat.eq_zero_of_le_zero hgle
  have hg_isZero_false : g.isZero = false := by
    cases hzero : g.isZero
    · rfl
    · exact False.elim (hg_ne_zero (eq_zero_of_isZero hzero))
  obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hg_isZero_false
  have hd0 : d = 0 := by simpa [degree, hd] using hg_deg_zero
  unfold isUnitPolynomial
  rw [hd, hd0]

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

/--
Strong-induction descent step for `exists_irreducible_factor_of_factor`.
Given any `a` of positive degree `n`, there is an irreducible divisor of
`a` of positive degree at most `n`.
-/
private theorem exists_irreducible_factor_of_pos_degree_aux :
    ∀ (n : Nat) (a : GF2Poly), a.degree = n → 0 < a.degree →
        ∃ g : GF2Poly,
          GF2Poly.Irreducible g ∧ g ∣ a ∧
            0 < g.degree ∧ g.degree ≤ a.degree := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a hn ha_pos
    by_cases hirr : Irreducible a
    · exact ⟨a, hirr, dvd_refl' a, ha_pos, Nat.le_refl _⟩
    · have ha_ne : a ≠ 0 := ne_zero_of_pos_degree ha_pos
      have hnotforall :
          ¬ (∀ x y : GF2Poly, x * y = a → x.degree = 0 ∨ y.degree = 0) :=
        fun h => hirr ⟨ha_ne, h⟩
      have hex : ∃ x y, x * y = a ∧ x.degree ≠ 0 ∧ y.degree ≠ 0 := by
        apply Classical.byContradiction
        intro hno
        apply hnotforall
        intro x y hxy
        by_cases hx0 : x.degree = 0
        · exact Or.inl hx0
        · by_cases hy0 : y.degree = 0
          · exact Or.inr hy0
          · exact (hno ⟨x, y, hxy, hx0, hy0⟩).elim
      obtain ⟨x, y, hxy, hx_deg_ne, hy_deg_ne⟩ := hex
      have hx_pos : 0 < x.degree := Nat.pos_of_ne_zero hx_deg_ne
      have hy_pos : 0 < y.degree := Nat.pos_of_ne_zero hy_deg_ne
      have hx_dvd_a : x ∣ a := ⟨y, hxy.symm⟩
      have hx_ne_zero : x ≠ 0 := ne_zero_of_pos_degree hx_pos
      have hx_lt : x.degree < a.degree :=
        factor_degree_lt hxy hx_ne_zero hy_pos
      have hx_lt_n : x.degree < n := hn ▸ hx_lt
      obtain ⟨g, hg_irr, hg_dvd_x, hg_deg_pos, hg_deg_le_x⟩ :=
        ih x.degree hx_lt_n x rfl hx_pos
      exact ⟨g, hg_irr, dvd_trans hg_dvd_x hx_dvd_a, hg_deg_pos,
        Nat.le_trans hg_deg_le_x (Nat.le_of_lt hx_lt)⟩

/--
Every nonconstant factor of a packed GF2 polynomial has an irreducible factor.

The proof is the usual descent on degree, specialized to the project-side
`GF2Poly.Irreducible` predicate and the packed divisibility relation. The
hypothesis `a * b = f` is irrelevant to the construction; descent operates
purely on `a` via strong induction on `a.degree`.
-/
theorem exists_irreducible_factor_of_factor
    {f a b : GF2Poly} (_hab : a * b = f) (ha_pos : 0 < a.degree) :
    ∃ g : GF2Poly,
      GF2Poly.Irreducible g ∧ g ∣ a ∧
        0 < g.degree ∧ g.degree ≤ a.degree :=
  exists_irreducible_factor_of_pos_degree_aux a.degree a rfl ha_pos

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

/--
The linear-time variant of the certificate checker also implies
project-side `GF2Poly.Irreducible`, composing the linear soundness theorem
with Rabin soundness.
-/
theorem checkIrreducibilityCertificateLinear_imp_irreducible
    (f : GF2Poly) (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificateLinear f cert = true) :
    GF2Poly.Irreducible f :=
  rabinTest_imp_irreducible f
    (checkIrreducibilityCertificateLinear_rabinTest f cert hcheck)

end GF2Poly
end Hex
