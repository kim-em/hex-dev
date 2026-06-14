import HexGF2.Multiply

/-!
Executable Euclidean-algorithm operations for packed `GF2Poly`.

This module adds long division with remainder to the packed `GF(2)` polynomial
representation, then derives gcd and extended-gcd routines from that division
surface. The computational updates exploit characteristic two, so subtraction is
implemented by the same XOR operation as addition.
-/
namespace Hex
namespace GF2Poly

/-- Tail-recursive long division for packed `GF(2)` polynomials. -/
private def divModAux (q : GF2Poly) (fuel : Nat) (quot rem : GF2Poly) :
    GF2Poly × GF2Poly :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      if q.isZero then
        (0, rem)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let term := monomial k
              divModAux q fuel (quot + term) (rem + q.mulXk k)
        | _, _ => (quot, rem)

/-- Polynomial long division over `GF(2)`. Division by `0` returns `(0, p)`. -/
def divMod (p q : GF2Poly) : GF2Poly × GF2Poly :=
  divModAux q (p.degree + 1) 0 p

/-- Quotient from polynomial long division over `GF(2)`. -/
def div (p q : GF2Poly) : GF2Poly :=
  (divMod p q).1

/-- Remainder from polynomial long division over `GF(2)`. -/
def mod (p q : GF2Poly) : GF2Poly :=
  (divMod p q).2

instance : Div GF2Poly where
  div := div

instance : Mod GF2Poly where
  mod := mod

/-- Divisibility in `GF(2)[x]` is witnessed by an explicit quotient. -/
instance : Dvd GF2Poly where
  dvd p q := ∃ r : GF2Poly, q = p * r

/-- Polynomial irreducibility over `GF(2)` phrased in terms of nontrivial
factorizations inside the packed `GF2Poly` execution model. -/
def Irreducible (f : GF2Poly) : Prop :=
  f ≠ 0 ∧ ∀ a b : GF2Poly, a * b = f → a.degree = 0 ∨ b.degree = 0

/-- Bitmask for coefficients of degree `< n` inside one `UInt64` word. -/
def lowerMask (n : Nat) : UInt64 :=
  if n < 64 then
    ((1 : UInt64) <<< n.toUInt64) - 1
  else
    (0 : UInt64) - 1

/-- Build the monic degree-`n` polynomial `x^n + lower`, truncating `lower` to
degrees `< n` as required by the packed `GF(2^n)` modulus convention. -/
def ofUInt64Monic (lower : UInt64) (n : Nat) : GF2Poly :=
  monomial n + ofUInt64 (lower &&& lowerMask n)

/-- Reduce a packed polynomial modulo a single-word extension modulus and read
back the low canonical word. -/
def packedReduceWord (n : Nat) (irr : UInt64) (p : GF2Poly) : UInt64 :=
  (((p % ofUInt64Monic irr n).toWords).getD 0 0) &&& lowerMask n

/-- Repackage a word as a canonical representative below `2^n`. -/
def canonicalWordLT (n : Nat) (hn64 : n < 64) (w : UInt64) : UInt64 :=
  UInt64.ofNatLT (w.toNat % 2 ^ n) <| by
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by
      show 0 < 2 ^ n
      exact Nat.pow_pos (by decide : 0 < 2))) <|
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hn64)

/-- A packed polynomial whose degree is below one machine word is exactly the
single-word polynomial obtained by reading its low stored word. -/
private theorem ofUInt64_lowWord_eq_of_degree_lt_64 (p : GF2Poly)
    (hred : p.isZero = true ∨ p.degree < 64) :
    ofUInt64 (p.toWords.getD 0 0) = p := by
  by_cases hzero : p.isZero = true
  · rw [eq_zero_of_isZero hzero]
    change ofWords #[(0 : UInt64)] = 0
    apply ext_words
    simp
  · have hzeroFalse : p.isZero = false := by
      cases h : p.isZero <;> simp [h] at hzero ⊢
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hzeroFalse
    have hd64 : d < 64 := by
      cases hred with
      | inl h =>
          rw [h] at hzeroFalse
          contradiction
      | inr hdegree =>
          simpa [degree, hd] using hdegree
    apply ext_coeff
    intro i
    unfold ofUInt64
    rw [coeff_ofWords]
    by_cases hi64 : i < 64
    · have hiword : i / 64 = 0 := Nat.div_eq_of_lt hi64
      simp [toWords, coeff, coeffWords, hiword]
    · have hiword_pos : 0 < i / 64 := by
        exact Nat.div_pos (by omega) (by decide : 0 < 64)
      have hpfalse : p.coeff i = false :=
        coeff_eq_false_of_degree?_lt hd (by omega)
      rw [hpfalse]
      cases hidx : i / 64 with
      | zero =>
          omega
      | succ k =>
          simp [coeffWords, hidx]

/-- Specialized low-word representation for a reduced residue modulo a
single-word monic modulus. This is the non-mask part of the
`packedReduceWord` correctness proof. -/
private theorem ofUInt64_mod_lowWord_eq_of_degree_lt {n : Nat} {irr : UInt64}
    (hn64 : n < 64) (p : GF2Poly)
    (hred :
      (p % ofUInt64Monic irr n).isZero = true ∨
        (p % ofUInt64Monic irr n).degree < n) :
    ofUInt64 (((p % ofUInt64Monic irr n).toWords).getD 0 0) =
      p % ofUInt64Monic irr n := by
  apply ofUInt64_lowWord_eq_of_degree_lt_64
  cases hred with
  | inl hzero =>
      exact Or.inl hzero
  | inr hdegree =>
      exact Or.inr (Nat.lt_trans hdegree hn64)

/-- `(a + b) + (c + b)` cancels the shared summand to `a + c` over `GF(2)`. -/
private theorem add_cancel_middle (a b c : GF2Poly) :
    (a + b) + (c + b) = a + c := by
  apply ext_coeff
  intro n
  rw [coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne]
  cases a.coeff n <;> cases b.coeff n <;> cases c.coeff n <;> rfl

/-- `(a + b) + (c + d)` regroups to `(a + c) + (b + d)` by commutativity of `GF(2)` addition. -/
private theorem add_pair_swap (a b c d : GF2Poly) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  apply ext_coeff
  intro n
  rw [coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne,
    coeff_add_eq_bne, coeff_add_eq_bne]
  cases a.coeff n <;> cases b.coeff n <;> cases c.coeff n <;>
    cases d.coeff n <;> rfl

/-- A single long-division update preserves quotient/remainder
reconstruction. -/
theorem quotient_step_reconstruct (quot rem q : GF2Poly) (k : Nat) :
    let term := monomial k
    (quot + term) * q + (rem + q.mulXk k) = quot * q + rem := by
  dsimp
  rw [add_monomial_mul]
  exact add_cancel_middle (quot * q) (q.mulXk k) rem

/-- Each `divModAux` step preserves the reconstruction invariant `quot * q + rem`. -/
private theorem divModAux_reconstruct
    (q : GF2Poly) (fuel : Nat) (quot rem : GF2Poly) :
    let qr := divModAux q fuel quot rem
    qr.1 * q + qr.2 = quot * q + rem := by
  induction fuel generalizing quot rem with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [divModAux]
      by_cases hqzero : q.isZero = true
      · simp [eq_zero_of_isZero hqzero]
      · have hqzeroFalse : q.isZero = false := by
          cases h : q.isZero <;> simp [h] at hqzero ⊢
        simp [hqzeroFalse]
        cases hrem : rem.degree? with
        | none =>
            simp
        | some rd =>
            cases hq : q.degree? with
            | none =>
                simp
            | some qd =>
                simp
                by_cases hlt : rd < qd
                · simp [hlt]
                · simp [hlt]
                  rw [ih]
                  exact quotient_step_reconstruct quot rem q (rd - qd)

/-- A polynomial whose `degree?` is `none` is the zero polynomial. -/
private theorem isZero_eq_true_of_degree?_eq_none {p : GF2Poly}
    (h : p.degree? = none) :
    p.isZero = true := by
  by_cases hzero : p.isZero = true
  · exact hzero
  · have hfalse : p.isZero = false := by
      cases hp : p.isZero <;> simp [hp] at hzero ⊢
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hfalse
    rw [hd] at h
    contradiction

/-- Given enough fuel, the `divModAux` remainder is zero or has degree below the divisor `q`. -/
private theorem divModAux_remainder_degree_lt
    {q : GF2Poly} {qd : Nat} (hq : q.degree? = some qd)
    (fuel : Nat) (quot rem : GF2Poly)
    (hremFuel : rem.isZero = true ∨ rem.degree < fuel) :
    let qr := divModAux q fuel quot rem
    qr.2.isZero = true ∨ qr.2.degree < q.degree := by
  induction fuel generalizing quot rem with
  | zero =>
      simp only [divModAux]
      cases hremFuel with
      | inl hzero =>
          exact Or.inl hzero
      | inr hlt =>
          omega
  | succ fuel ih =>
      simp only [divModAux]
      have hqzeroFalse : q.isZero = false := isZero_false_of_degree?_eq_some hq
      simp [hqzeroFalse]
      cases hrem : rem.degree? with
      | none =>
          simpa using Or.inl (isZero_eq_true_of_degree?_eq_none hrem)
      | some rd =>
          rw [hq]
          by_cases hlt : rd < qd
          · simp [hlt]
            right
            rw [degree_eq_of_degree?_eq_some hrem, degree_eq_of_degree?_eq_some hq]
            exact hlt
          · simp [hlt]
            have hrdFuel : rd < fuel + 1 := by
              cases hremFuel with
              | inl hzero =>
                  have hnone := degree?_eq_none_of_isZero hzero
                  rw [hrem] at hnone
                  contradiction
              | inr hltFuel =>
                  simpa [degree_eq_of_degree?_eq_some hrem] using hltFuel
            have hstep :=
              division_step_degree_lt (rem := rem) (q := q) (rd := rd) (qd := qd)
                hrem hq hlt
            have hnextFuel :
                (rem + q.mulXk (rd - qd)).isZero = true ∨
                  (rem + q.mulXk (rd - qd)).degree < fuel := by
              cases hstep with
              | inl hzero =>
                  exact Or.inl hzero
              | inr hdegree =>
                  exact Or.inr (Nat.lt_of_lt_of_le hdegree (Nat.le_of_lt_succ hrdFuel))
            have hih :=
              ih (quot + monomial (rd - qd)) (rem + q.mulXk (rd - qd)) hnextFuel
            simpa using hih

/-- Result package for the packed extended Euclidean algorithm. -/
structure XGCDResult where
  gcd : GF2Poly
  left : GF2Poly
  right : GF2Poly

/-- Tail-recursive extended Euclidean algorithm over packed `GF(2)`
polynomials. -/
private def xgcdAux
    (r₀ s₀ t₀ r₁ s₁ t₁ : GF2Poly) (fuel : Nat) : XGCDResult :=
  match fuel with
  | 0 => { gcd := r₀, left := s₀, right := t₀ }
  | fuel + 1 =>
      if r₁.isZero then
        { gcd := r₀, left := s₀, right := t₀ }
      else
        let qr := divMod r₀ r₁
        let q := qr.1
        let r := qr.2
        xgcdAux r₁ s₁ t₁ r (s₀ + q * s₁) (t₀ + q * t₁) fuel

/-- Extended gcd for packed `GF(2)` polynomials, returning the gcd together
with Bezout coefficients. -/
def xgcd (p q : GF2Poly) : XGCDResult :=
  xgcdAux p 1 0 q 0 1 (p.degree + q.degree + 2)

/-- The single-word xgcd inverse candidate reduced modulo the packed
irreducible modulus. -/
def packedInvWord (n : Nat) (irr w : UInt64) : UInt64 :=
  packedReduceWord n irr ((xgcd (ofUInt64 w) (ofUInt64Monic irr n)).left)

/-- Polynomial gcd over packed `GF(2)`. -/
def gcd (p q : GF2Poly) : GF2Poly :=
  (xgcd p q).gcd

/-- The division output reconstructs the dividend. -/
theorem divMod_spec (p q : GF2Poly) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  unfold divMod
  simpa using divModAux_reconstruct q (p.degree + 1) 0 p

/-- The first component of `divMod` is the public quotient operation. -/
@[simp] theorem divMod_fst (p q : GF2Poly) :
    (divMod p q).1 = p / q :=
  rfl

/-- The second component of `divMod` is the public remainder operation. -/
@[simp] theorem divMod_snd (p q : GF2Poly) :
    (divMod p q).2 = p % q :=
  rfl

/-- Dividing by zero returns zero quotient and leaves the dividend as the
remainder. -/
@[simp] theorem divMod_zero_right (p : GF2Poly) :
    divMod p 0 = (0, p) := by
  unfold divMod
  cases hfuel : p.degree + 1 with
  | zero => omega
  | succ fuel =>
      simp [divModAux]

/-- Zero has zero quotient and zero remainder against any divisor. -/
@[simp] theorem divMod_zero_left (q : GF2Poly) :
    divMod 0 q = (0, 0) := by
  unfold divMod
  simp [divModAux]

/-- Division by zero has quotient zero for packed `GF(2)` polynomials. -/
@[simp] theorem div_zero_right (p : GF2Poly) :
    p / 0 = 0 := by
  rw [← divMod_fst, divMod_zero_right]

/-- Remainder modulo zero is the dividend for packed `GF(2)` polynomials. -/
@[simp] theorem mod_zero_right (p : GF2Poly) :
    p % 0 = p := by
  rw [← divMod_snd, divMod_zero_right]

/-- Zero divided by any packed `GF(2)` polynomial has quotient zero. -/
@[simp] theorem zero_div (q : GF2Poly) :
    (0 : GF2Poly) / q = 0 := by
  rw [← divMod_fst, divMod_zero_left]

/-- Zero has zero remainder modulo any packed `GF(2)` polynomial. -/
@[simp] theorem zero_mod (q : GF2Poly) :
    (0 : GF2Poly) % q = 0 := by
  rw [← divMod_snd, divMod_zero_left]

/-- Quotient/remainder reconstruction through the public `/` and `%`
operations. -/
@[grind =]
theorem div_mul_add_mod (p q : GF2Poly) :
    (p / q) * q + p % q = p := by
  simpa using divMod_spec p q

/-- Every packed `GF(2)` polynomial divides itself. -/
private theorem dvd_refl (p : GF2Poly) :
    p ∣ p := by
  exact ⟨1, by rw [mul_one]⟩

/-- Every packed `GF(2)` polynomial divides zero. -/
private theorem dvd_zero (p : GF2Poly) :
    p ∣ 0 := by
  exact ⟨0, by rw [mul_zero]⟩

/-- A divisor of both `a` and `b` divides their sum `a + b`. -/
private theorem dvd_add {d a b : GF2Poly} :
    d ∣ a → d ∣ b → d ∣ a + b := by
  intro hda hdb
  rcases hda with ⟨ra, hra⟩
  rcases hdb with ⟨rb, hrb⟩
  exact ⟨ra + rb, by rw [hra, hrb, right_distrib]⟩

/-- A divisor of `a` divides any left multiple `c * a`. -/
private theorem dvd_mul_left {d a : GF2Poly} (c : GF2Poly) :
    d ∣ a → d ∣ c * a := by
  intro hda
  rcases hda with ⟨r, hr⟩
  refine ⟨c * r, ?_⟩
  calc
    c * a = c * (d * r) := by rw [hr]
    _ = (c * d) * r := by rw [mul_assoc]
    _ = (d * c) * r := by rw [mul_comm c d]
    _ = d * (c * r) := by rw [mul_assoc]

/-- A common divisor of `r₁` and the remainder divides the dividend `r₀` rebuilt by one division step. -/
private theorem dvd_of_division_step {d r₀ r₁ div rem : GF2Poly}
    (hr₁ : d ∣ r₁) (hrem : d ∣ rem)
    (hdiv : div * r₁ + rem = r₀) :
    d ∣ r₀ := by
  rw [← hdiv]
  exact dvd_add (dvd_mul_left div hr₁) hrem

/-- One extended-Euclid step carries the Bezout identity from `r₀` to the updated coefficients for the remainder. -/
private theorem xgcd_step_bezout
    (p q r₀ s₀ t₀ r₁ s₁ t₁ div rem : GF2Poly)
    (h₀ : s₀ * p + t₀ * q = r₀)
    (h₁ : s₁ * p + t₁ * q = r₁)
    (hdiv : div * r₁ + rem = r₀) :
    (s₀ + div * s₁) * p + (t₀ + div * t₁) * q = rem := by
  calc
    (s₀ + div * s₁) * p + (t₀ + div * t₁) * q
        = (s₀ * p + (div * s₁) * p) + (t₀ * q + (div * t₁) * q) := by
          rw [left_distrib, left_distrib]
    _ = (s₀ * p + div * (s₁ * p)) + (t₀ * q + div * (t₁ * q)) := by
          rw [mul_assoc, mul_assoc]
    _ = (s₀ * p + t₀ * q) + (div * (s₁ * p) + div * (t₁ * q)) := by
          exact add_pair_swap (s₀ * p) (div * (s₁ * p)) (t₀ * q) (div * (t₁ * q))
    _ = (s₀ * p + t₀ * q) + div * (s₁ * p + t₁ * q) := by
          rw [right_distrib]
    _ = r₀ + div * r₁ := by
          rw [h₀, h₁]
    _ = rem := by
          rw [← hdiv, add_comm (div * r₁) rem]
          simp

/-- `xgcdAux` preserves the Bezout identity `left * p + right * q = gcd` across the fuel recursion. -/
private theorem xgcdAux_bezout
    (p q r₀ s₀ t₀ r₁ s₁ t₁ : GF2Poly) (fuel : Nat)
    (h₀ : s₀ * p + t₀ * q = r₀)
    (h₁ : s₁ * p + t₁ * q = r₁) :
    let result := xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel
    result.left * p + result.right * q = result.gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      simp [xgcdAux, h₀]
  | succ fuel ih =>
      simp only [xgcdAux]
      by_cases hzero : r₁.isZero = true
      · simp [hzero, h₀]
      · have hzeroFalse : r₁.isZero = false := by
          cases h : r₁.isZero <;> simp [h] at hzero ⊢
        simp [hzeroFalse]
        let qr := divMod r₀ r₁
        let div := qr.1
        let rem := qr.2
        have hdiv : div * r₁ + rem = r₀ := by
          simpa [qr, div, rem] using divMod_spec r₀ r₁
        exact ih r₁ s₁ t₁ rem (s₀ + div * s₁) (t₀ + div * t₁)
          h₁ (xgcd_step_bezout p q r₀ s₀ t₀ r₁ s₁ t₁ div rem h₀ h₁ hdiv)

/-- The computed remainder has smaller degree than a nonzero divisor. -/
theorem mod_degree_lt (p q : GF2Poly) :
    q ≠ 0 → (p % q).isZero = true ∨ (p % q).degree < q.degree := by
  intro hqne
  have hqzeroFalse : q.isZero = false := by
    cases hqzero : q.isZero
    · rfl
    · exfalso
      exact hqne (eq_zero_of_isZero hqzero)
  obtain ⟨qd, hqdeg⟩ := degree?_isSome_of_isZero_false hqzeroFalse
  change ((divMod p q).2).isZero = true ∨ (divMod p q).2.degree < q.degree
  unfold divMod
  apply divModAux_remainder_degree_lt (q := q) (qd := qd) hqdeg
  by_cases hpzero : p.isZero = true
  · exact Or.inl hpzero
  · exact Or.inr (Nat.lt_succ_self p.degree)

set_option maxHeartbeats 800000 in
/-- Given enough fuel, the `xgcdAux` result divides both current remainders `r₀` and `r₁`. -/
private theorem xgcdAux_dvd_current_of_fuel
    (r₀ s₀ t₀ r₁ s₁ t₁ : GF2Poly) (fuel : Nat)
    (hfuel : r₁.isZero = true ∨ r₁.degree < fuel) :
    (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd ∣ r₀ ∧
      (xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel).gcd ∣ r₁ := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      cases hfuel with
      | inl hzero =>
          simp only [xgcdAux]
          constructor
          · exact dvd_refl r₀
          · rw [eq_zero_of_isZero hzero]
            exact dvd_zero r₀
      | inr hlt =>
          omega
  | succ fuel ih =>
      simp only [xgcdAux]
      by_cases hzero : r₁.isZero = true
      · simp only [hzero]
        constructor
        · exact dvd_refl r₀
        · rw [eq_zero_of_isZero hzero]
          exact dvd_zero r₀
      · have hzeroFalse : r₁.isZero = false := by
          cases h : r₁.isZero <;> simp [h] at hzero ⊢
        simp [hzeroFalse]
        have hdiv : (divMod r₀ r₁).1 * r₁ + (divMod r₀ r₁).2 = r₀ := by
          exact divMod_spec r₀ r₁
        have hr₁ne : r₁ ≠ 0 := by
          intro hr₁
          have : r₁.isZero = true := by simp [hr₁]
          exact hzero this
        have hremDegree :
            (divMod r₀ r₁).2.isZero = true ∨ (divMod r₀ r₁).2.degree < r₁.degree := by
          simpa [mod] using mod_degree_lt r₀ r₁ hr₁ne
        have hr₁Degree : r₁.degree < fuel + 1 := by
          cases hfuel with
          | inl hzero' =>
              contradiction
          | inr hlt =>
              exact hlt
        have hnextFuel :
            (divMod r₀ r₁).2.isZero = true ∨ (divMod r₀ r₁).2.degree < fuel := by
          cases hremDegree with
          | inl hremZero =>
              exact Or.inl hremZero
          | inr hremLt =>
              exact Or.inr (Nat.lt_of_lt_of_le hremLt (Nat.le_of_lt_succ hr₁Degree))
        have hih :=
          ih r₁ s₁ t₁ (divMod r₀ r₁).2 (s₀ + (divMod r₀ r₁).1 * s₁)
            (t₀ + (divMod r₀ r₁).1 * t₁) hnextFuel
        constructor
        · exact dvd_of_division_step hih.1 hih.2 hdiv
        · exact hih.1

/-- The extended-gcd output satisfies the Bezout identity. -/
theorem xgcd_bezout (p q : GF2Poly) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  unfold xgcd
  apply xgcdAux_bezout
  · rw [one_mul, zero_mul, add_zero]
  · rw [zero_mul, one_mul, zero_add]

/-- Let-free Bezout form for automation over the computed extended-gcd record. -/
@[grind =]
theorem xgcd_left_mul_add_right_mul (p q : GF2Poly) :
    (xgcd p q).left * p + (xgcd p q).right * q = (xgcd p q).gcd := by
  simpa using xgcd_bezout p q

example (p q : GF2Poly) :
    (xgcd p q).left * p + (xgcd p q).right * q = (xgcd p q).gcd := by
  grind

/-- The gcd divides the left input. -/
theorem gcd_dvd_left (p q : GF2Poly) :
    gcd p q ∣ p := by
  unfold gcd xgcd
  have hfuel : q.isZero = true ∨ q.degree < p.degree + q.degree + 2 := by
    by_cases hqzero : q.isZero = true
    · exact Or.inl hqzero
    · exact Or.inr (by omega)
  exact (xgcdAux_dvd_current_of_fuel p 1 0 q 0 1 (p.degree + q.degree + 2) hfuel).1

/-- The gcd divides the right input. -/
theorem gcd_dvd_right (p q : GF2Poly) :
    gcd p q ∣ q := by
  unfold gcd xgcd
  have hfuel : q.isZero = true ∨ q.degree < p.degree + q.degree + 2 := by
    by_cases hqzero : q.isZero = true
    · exact Or.inl hqzero
    · exact Or.inr (by omega)
  exact (xgcdAux_dvd_current_of_fuel p 1 0 q 0 1 (p.degree + q.degree + 2) hfuel).2

/-- Any common divisor divides the computed gcd. -/
theorem dvd_gcd (d p q : GF2Poly) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  intro hdp hdq
  unfold gcd
  have hbezout := xgcd_bezout p q
  let r := xgcd p q
  have hsum : d ∣ r.left * p + r.right * q :=
    dvd_add (dvd_mul_left r.left hdp) (dvd_mul_left r.right hdq)
  rw [hbezout] at hsum
  simpa [r] using hsum

/-- A nonzero packed polynomial of degree `0` equals `1`, the only degree-`0`
GF(2) polynomial. -/
private theorem nonzero_degree_zero_eq_one {p : GF2Poly}
    (hp : p ≠ 0) (hdegree : p.degree = 0) :
    p = 1 := by
  have hpzeroFalse : p.isZero = false := by
    cases hzero : p.isZero
    · rfl
    · exfalso
      exact hp (eq_zero_of_isZero hzero)
  obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hpzeroFalse
  have hd0 : d = 0 := by
    simpa [degree, hd] using hdegree
  subst d
  rw [one_eq_monomial_zero]
  apply ext_coeff
  intro n
  cases n with
  | zero =>
      rw [coeff_eq_true_of_degree?_eq_some hd, coeff_monomial_self]
  | succ n =>
      rw [coeff_eq_false_of_degree?_lt hd (by omega)]
      rw [coeff_monomial_ne (by omega)]

/-- A nonzero divisor of a nonzero packed polynomial has degree no larger than
the dividend. -/
theorem degree_le_of_dvd_nonzero {p q : GF2Poly}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    p ∣ q → p.degree ≤ q.degree := by
  intro hdvd
  rcases hdvd with ⟨r, hr⟩
  have hpzeroFalse : p.isZero = false := by
    cases hpzero : p.isZero
    · rfl
    · exfalso
      exact hp (eq_zero_of_isZero hpzero)
  have hrne : r ≠ 0 := by
    intro hrzero
    apply hq
    rw [hr, hrzero, mul_zero]
  have hrzeroFalse : r.isZero = false := by
    cases hrzero : r.isZero
    · rfl
    · exfalso
      exact hrne (eq_zero_of_isZero hrzero)
  obtain ⟨dp, hdp⟩ := degree?_isSome_of_isZero_false hpzeroFalse
  obtain ⟨dr, hdr⟩ := degree?_isSome_of_isZero_false hrzeroFalse
  have hq_degree? : q.degree? = some (dp + dr) := by
    rw [hr]
    exact degree?_mul_of_degree?_eq_some hdp hdr
  rw [degree_eq_of_degree?_eq_some hdp,
    degree_eq_of_degree?_eq_some hq_degree?]
  omega

/-- A polynomial reduced below `bound` (either zero, or of degree `< bound`)
has `coeff n = false` at every index `n ≥ bound`. -/
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

/-- The `n`-bit low mask has numeric value `2 ^ n - 1` when `n < 64`. -/
private theorem lowerMask_toNat_of_lt_64 {n : Nat} (hn64 : n < 64) :
    (lowerMask n).toNat = 2 ^ n - 1 := by
  unfold lowerMask
  have hshift :
      (((1 : UInt64) <<< n.toUInt64).toNat) = 2 ^ n := by
    have hpow : 2 ^ n < 2 ^ 64 :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hn64
    simp [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hn64,
      Nat.one_shiftLeft, Nat.mod_eq_of_lt hpow]
  have hle : (1 : UInt64) ≤ ((1 : UInt64) <<< n.toUInt64) := by
    rw [UInt64.le_iff_toNat_le, hshift]
    exact Nat.one_le_two_pow
  rw [if_pos hn64]
  rw [UInt64.toNat_sub_of_le _ _ hle, hshift]
  simp

/-- Masking a word whose value is already `< 2 ^ n` with `lowerMask n` returns
it unchanged. -/
private theorem UInt64.and_lowerMask_eq_self_of_lt {n : Nat} (hn64 : n < 64)
    {w : UInt64} (hw : w.toNat < 2 ^ n) :
    w &&& lowerMask n = w := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, lowerMask_toNat_of_lt_64 hn64]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow hw

/-- Masking any word with `lowerMask n` bounds the result below `2 ^ n`
(for `n < 64`), giving the canonical reduced representative. -/
private theorem UInt64.and_lowerMask_toNat_lt {n : Nat} (hn64 : n < 64)
    (w : UInt64) :
    (w &&& lowerMask n).toNat < 2 ^ n := by
  rw [UInt64.toNat_and, lowerMask_toNat_of_lt_64 hn64]
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by decide : 0 < 2)
  have hand :
      w.toNat &&& (2 ^ n - 1) = w.toNat % 2 ^ n := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases hi : i < n <;> simp [hi]
  rw [hand]
  exact Nat.mod_lt _ hpow

/-- `canonicalWordLT` fixes a word that is already reduced below `2 ^ n`. -/
private theorem canonicalWordLT_eq_self_of_lt {n : Nat} (hn64 : n < 64)
    {w : UInt64} (hw : w.toNat < 2 ^ n) :
    canonicalWordLT n hn64 w = w := by
  apply UInt64.toNat_inj.mp
  simp [canonicalWordLT, Nat.mod_eq_of_lt hw]

/-- A natural number `< 2 ^ k` has `testBit i = false` at every index
`i ≥ k`. -/
private theorem nat_testBit_eq_false_of_lt_two_pow {x k i : Nat}
    (hx : x < 2 ^ k) (hki : k ≤ i) :
    x.testBit i = false := by
  have hbit : (x % 2 ^ k).testBit i = x.testBit i := by
    rw [Nat.mod_eq_of_lt hx]
  rw [Nat.testBit_mod_two_pow] at hbit
  have hnot : ¬ i < k := Nat.not_lt_of_ge hki
  simp [hnot] at hbit
  exact hbit

/-- Coefficient `i` of the polynomial packed from `w &&& lowerMask n`: the
original bit when `i < n`, and `false` otherwise. -/
private theorem coeff_ofUInt64_and_lowerMask (w : UInt64) {n i : Nat} (hn64 : n < 64) :
    (ofUInt64 (w &&& lowerMask n)).coeff i =
      if i < n then (ofUInt64 w).coeff i else false := by
  by_cases hi64 : i < 64
  · rw [coeff_ofUInt64_eq_testBit _ hi64, coeff_ofUInt64_eq_testBit _ hi64,
      UInt64.toNat_and, lowerMask_toNat_of_lt_64 hn64, Nat.testBit_and,
      Nat.testBit_two_pow_sub_one]
    by_cases hin : i < n <;> simp [hin]
  · have hi64le : 64 ≤ i := Nat.le_of_not_gt hi64
    have hinFalse : ¬ i < n := by omega
    rw [coeff_ofUInt64_eq_false_of_ge_64 _ hi64le, if_neg hinFalse]

/-- The packed single-word monic modulus has the advertised degree when
`n < 64`. -/
@[simp] theorem degree?_ofUInt64Monic_of_lt_64 (lower : UInt64) {n : Nat}
    (hn64 : n < 64) :
    (ofUInt64Monic lower n).degree? = some n := by
  apply degree?_eq_some_of_coeff_eq_true_of_forall_gt_false
  · unfold ofUInt64Monic
    rw [coeff_add_eq_bne, coeff_monomial_self,
      coeff_ofUInt64_and_lowerMask lower hn64]
    simp
  · intro m hm
    unfold ofUInt64Monic
    rw [coeff_add_eq_bne, coeff_monomial_ne (by omega),
      coeff_ofUInt64_and_lowerMask lower hn64]
    simp [Nat.not_lt_of_ge (by omega : n ≤ m)]

/-- The degree of `ofUInt64Monic lower n` is exactly `n` when `n < 64`. -/
@[simp] theorem degree_ofUInt64Monic_of_lt_64 (lower : UInt64) {n : Nat}
    (hn64 : n < 64) :
    (ofUInt64Monic lower n).degree = n := by
  exact degree_eq_of_degree?_eq_some (degree?_ofUInt64Monic_of_lt_64 lower hn64)

/-- A nonzero `UInt64` word unpacks to a nonzero packed polynomial. -/
private theorem ofUInt64_ne_zero_of_ne_zero {w : UInt64} (hw : w ≠ 0) :
    ofUInt64 w ≠ 0 := by
  intro h
  apply hw
  apply ofUInt64_injective
  simpa [ofUInt64] using h

/-- A word with value `< 2 ^ n` unpacks to a polynomial that is either zero or
of degree `< n`, i.e. reduced below `n`. -/
private theorem ofUInt64_reduced_of_toNat_lt {n : Nat} {w : UInt64}
    (hwlt : w.toNat < 2 ^ n) :
    (ofUInt64 w).IsZero ∨ (ofUInt64 w).degree < n := by
  by_cases hzero : (ofUInt64 w).isZero = true
  · exact Or.inl hzero
  · right
    have hzeroFalse : (ofUInt64 w).isZero = false := by
      cases h : (ofUInt64 w).isZero <;> simp [h] at hzero ⊢
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hzeroFalse
    have hdlt : d < n := by
      by_cases hdn : d < n
      · exact hdn
      · have hnle : n ≤ d := Nat.le_of_not_gt hdn
        have hdtrue := coeff_eq_true_of_degree?_eq_some hd
        by_cases hd64 : d < 64
        · have hbitfalse : w.toNat.testBit d = false := by
            exact nat_testBit_eq_false_of_lt_two_pow
              (k := n) hwlt hnle
          rw [coeff_ofUInt64_eq_testBit w hd64, hbitfalse] at hdtrue
          contradiction
        · have hd64le : 64 ≤ d := Nat.le_of_not_gt hd64
          rw [coeff_ofUInt64_eq_false_of_ge_64 w hd64le] at hdtrue
          contradiction
    simpa [degree, hd] using hdlt

/-- `packedReduceWord` always returns a canonical word below `2^n` for
single-word extension degrees. -/
theorem packedReduceWord_toNat_lt {n : Nat} {irr : UInt64}
    (hn64 : n < 64) (p : GF2Poly) :
    (packedReduceWord n irr p).toNat < 2 ^ n := by
  unfold packedReduceWord
  exact UInt64.and_lowerMask_toNat_lt hn64 _

/-- Masking the low word of a degree-`< n` residue preserves the represented
polynomial. -/
theorem ofUInt64_packedReduceWord_eq_of_degree_lt
    {n : Nat} {irr : UInt64} (hn64 : n < 64) (p : GF2Poly)
    (hred :
      (p % ofUInt64Monic irr n).isZero = true ∨
        (p % ofUInt64Monic irr n).degree < n) :
    ofUInt64 (packedReduceWord n irr p) = p % ofUInt64Monic irr n := by
  unfold packedReduceWord
  let r := p % ofUInt64Monic irr n
  change ofUInt64 (r.toWords.getD 0 0 &&& lowerMask n) = r
  let low := r.toWords.getD 0 0
  have hred' : r.isZero = true ∨ r.degree < n := by
    simpa [r] using hred
  have hlow : ofUInt64 low = r := by
    simpa [r, low] using ofUInt64_mod_lowWord_eq_of_degree_lt (n := n) (irr := irr) hn64 p hred
  apply ext_coeff
  intro i
  rw [coeff_ofUInt64_and_lowerMask low hn64]
  by_cases hin : i < n
  · rw [if_pos hin]
    exact congrArg (fun q : GF2Poly => q.coeff i) hlow
  · rw [if_neg hin]
    exact (coeff_eq_false_of_reduced_le (p := r) hred' (Nat.le_of_not_gt hin)).symm

/-- Reducedness below `bound` (zero, or degree `< bound`) is preserved by
addition of two reduced polynomials. -/
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

/-- A residue reduced below `f.degree` that is divisible by nonzero `f` must
be `0` (a proper-degree multiple of `f` cannot exist). -/
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

/-- Any common divisor of an irreducible `f` and a nonzero residue `a` reduced
below `f.degree` is `1`; the backbone of the gcd-coprimality result. -/
private theorem irreducible_common_divisor_eq_one_of_reduced
    {a f d : GF2Poly} (hf : Irreducible f) (ha : a ≠ 0)
    (hred : a.IsZero ∨ a.degree < f.degree)
    (hda : d ∣ a) (hdf : d ∣ f) :
    d = 1 := by
  rcases hdf with ⟨r, hr⟩
  have hdne : d ≠ 0 := by
    intro hd
    rcases hda with ⟨s, hs⟩
    apply ha
    rw [hs, hd, zero_mul]
  rcases hf.2 d r hr.symm with hd_degree | hr_degree
  · exact nonzero_degree_zero_eq_one hdne hd_degree
  · have hrne : r ≠ 0 := by
      intro hzero
      apply hf.1
      rw [hr, hzero, mul_zero]
    have hr_one : r = 1 := nonzero_degree_zero_eq_one hrne hr_degree
    have hdf : d = f := by
      calc
        d = d * 1 := by rw [mul_one]
        _ = d * r := by rw [hr_one]
        _ = f := hr.symm
    have hf_dvd_a : f ∣ a := by
      simpa [hdf] using hda
    cases hred with
    | inl hzero =>
        exact False.elim (ha (eq_zero_of_isZero hzero))
    | inr hlt =>
        have hle : f.degree ≤ a.degree := degree_le_of_dvd_nonzero hf.1 ha hf_dvd_a
        omega

/-- Adding a right multiple `c * f` leaves the remainder modulo `f` unchanged;
the engine behind the quotient-congruence `simp` lemmas below. -/
private theorem mod_eq_of_add_right_multiple (a c f : GF2Poly) :
    (a + c * f) % f = a % f := by
  by_cases hf : f = 0
  · subst hf
    simp [mul_zero, add_zero]
  · let q₁ := (divMod (a + c * f) f).1
    let r₁ := (divMod (a + c * f) f).2
    let q₂ := (divMod a f).1
    let r₂ := (divMod a f).2
    have hspec₁ : q₁ * f + r₁ = a + c * f := by
      simpa [q₁, r₁] using divMod_spec (a + c * f) f
    have hspec₂ : q₂ * f + r₂ = a := by
      simpa [q₂, r₂] using divMod_spec a f
    have hsum :
        (q₁ * f + q₂ * f) + (r₁ + r₂) = c * f := by
      calc
        (q₁ * f + q₂ * f) + (r₁ + r₂)
            = (q₁ * f + r₁) + (q₂ * f + r₂) := by
                rw [add_pair_swap]
        _ = (a + c * f) + a := by rw [hspec₁, hspec₂]
        _ = c * f := by
          have haa : a + a = 0 := by
            simp
          rw [add_comm a (c * f), add_assoc, haa, add_zero]
    have hdvd_sum : f ∣ r₁ + r₂ := by
      refine ⟨q₁ + q₂ + c, ?_⟩
      have hprod : q₁ * f + q₂ * f = (q₁ + q₂) * f := by
        rw [left_distrib]
      calc
        r₁ + r₂ = (q₁ * f + q₂ * f) + ((q₁ * f + q₂ * f) + (r₁ + r₂)) := by
          simp
        _ = (q₁ * f + q₂ * f) + c * f := by rw [hsum]
        _ = (q₁ + q₂ + c) * f := by
          calc
            (q₁ * f + q₂ * f) + c * f = (q₁ + q₂) * f + c * f := by
              exact congrArg (fun x => x + c * f) hprod
            _ = (q₁ + q₂ + c) * f := by
              exact (left_distrib (q₁ + q₂) c f).symm
        _ = f * (q₁ + q₂ + c) := by rw [mul_comm]
    have hred₁ : r₁.isZero = true ∨ r₁.degree < f.degree := by
      simpa [mod, r₁] using mod_degree_lt (a + c * f) f hf
    have hred₂ : r₂.isZero = true ∨ r₂.degree < f.degree := by
      simpa [mod, r₂] using mod_degree_lt a f hf
    have hsumZero : r₁ + r₂ = 0 :=
      reduced_dvd_eq_zero hf (add_reduced_of_reduced hred₁ hred₂) hdvd_sum
    have hr₁eq : r₁ = r₂ := by
      calc
        r₁ = r₁ + 0 := by rw [add_zero]
        _ = r₁ + (r₁ + r₂) := by rw [hsumZero, add_zero]
        _ = r₂ := by rw [add_add_cancel_left]
    simpa [mod, r₁, r₂] using hr₁eq

/-- Any nonzero reduced residue modulo an irreducible packed polynomial is
coprime to the modulus, as computed by the packed Euclidean algorithm. -/
theorem gcd_eq_one_of_irreducible_of_nonzero_reduced {a f : GF2Poly}
    (hf : Irreducible f) (ha : a ≠ 0)
    (hred : a.IsZero ∨ a.degree < f.degree) :
    gcd a f = 1 := by
  exact irreducible_common_divisor_eq_one_of_reduced hf ha hred
    (gcd_dvd_left a f) (gcd_dvd_right a f)

/-- Adding a right multiple of the modulus does not change the computed
remainder. This is the quotient-congruence form used with Bezout witnesses. -/
@[simp]
theorem mod_add_mul_right_eq_mod (a c f : GF2Poly) :
    (a + c * f) % f = a % f := by
  exact mod_eq_of_add_right_multiple a c f

example (a c f : GF2Poly) : (a + c * f) % f = a % f := by
  simp

/-- A reduced packed polynomial is its own remainder modulo `f`. -/
@[simp]
theorem mod_eq_self_of_reduced (p f : GF2Poly)
    (hred : p.isZero = true ∨ p.degree < f.degree) :
    p % f = p := by
  by_cases hf : f = 0
  · subst hf
    change (divModAux 0 (p.degree + 1) 0 p).2 = p
    have hsucc : p.degree + 1 = Nat.succ p.degree := by omega
    rw [hsucc]
    simp [divModAux]
  · have hmod_red : (p % f).isZero = true ∨ (p % f).degree < f.degree :=
      mod_degree_lt p f hf
    have hdvd : f ∣ p % f + p := by
      let q := (divMod p f).1
      have hspec : q * f + p % f = p := by
        simpa [q, mod] using divMod_spec p f
      refine ⟨q, ?_⟩
      calc
        p % f + p = p % f + (q * f + p % f) := by rw [hspec]
        _ = q * f := by
          rw [add_comm (q * f) (p % f), ← add_assoc, add_self, zero_add]
        _ = f * q := by rw [mul_comm]
    have hsum_zero : p % f + p = 0 :=
      reduced_dvd_eq_zero hf (add_reduced_of_reduced hmod_red hred) hdvd
    calc
      p % f = p % f + 0 := by rw [add_zero]
      _ = p % f + (p % f + p) := by rw [hsum_zero, add_zero]
      _ = p := by rw [add_add_cancel_left]

/-- Validate a remainder using an explicit quotient witness. -/
theorem mod_eq_of_eq_add_mul_right {a r c f : GF2Poly}
    (h : a = r + c * f)
    (hred : r.isZero = true ∨ r.degree < f.degree) :
    a % f = r := by
  rw [h, mod_add_mul_right_eq_mod]
  exact mod_eq_self_of_reduced r f hred

/-- `1 % f = 1` whenever `f` has positive degree, since `1` is already reduced
modulo `f`. -/
private theorem one_mod_eq_one_of_degree_pos {f : GF2Poly} (hfdegree : 0 < f.degree) :
    (1 : GF2Poly) % f = 1 := by
  have hfzeroFalse : f.isZero = false := by
    by_cases hzero : f.isZero = true
    · have hfzero : f = 0 := eq_zero_of_isZero hzero
      subst hfzero
      simp at hfdegree
    · cases h : f.isZero <;> simp [h] at hzero ⊢
  obtain ⟨fd, hfd⟩ := degree?_isSome_of_isZero_false hfzeroFalse
  have hfdpos : 0 < fd := by
    simpa [degree, hfd] using hfdegree
  change (divMod 1 f).2 = 1
  unfold divMod
  change (divModAux f 1 0 1).2 = 1
  simp only [divModAux]
  have hone_degree : (1 : GF2Poly).degree? = some 0 := by
    rfl
  rw [hone_degree, hfd]
  simp [hfzeroFalse, hfdpos]

/-- The Bezout identity for `xgcd` gives a congruence between the left inverse
candidate and the computed gcd modulo the right input. -/
theorem xgcd_left_mul_mod_eq_gcd_mod (a f : GF2Poly) :
    (a * (xgcd a f).left) % f = (gcd a f) % f := by
  let r := xgcd a f
  have hbezout : r.left * a + r.right * f = r.gcd := by
    simpa [r] using xgcd_bezout a f
  have hcongr : a * r.left = r.gcd + r.right * f := by
    calc
      a * r.left = r.left * a := by rw [mul_comm]
      _ = (r.left * a + r.right * f) + r.right * f := by
            rw [add_add_cancel_right]
      _ = r.gcd + r.right * f := by rw [hbezout]
  calc
    (a * (xgcd a f).left) % f = (a * r.left) % f := by rfl
    _ = (r.gcd + r.right * f) % f := by rw [hcongr]
    _ = r.gcd % f := mod_add_mul_right_eq_mod r.gcd r.right f
    _ = (gcd a f) % f := by rfl

/-- For a nonzero reduced residue modulo an irreducible packed polynomial, the
left Bezout coefficient computed by `xgcd` is a multiplicative inverse modulo
the modulus. -/
theorem xgcd_left_mul_mod_eq_one_of_irreducible_of_nonzero_reduced {a f : GF2Poly}
    (hf : Irreducible f) (ha : a ≠ 0)
    (hred : a.IsZero ∨ a.degree < f.degree) :
    (a * (xgcd a f).left) % f = 1 := by
  have hfdegree : 0 < f.degree := by
    cases hred with
    | inl hzero =>
        exact False.elim (ha (eq_zero_of_isZero hzero))
    | inr hlt =>
        omega
  rw [xgcd_left_mul_mod_eq_gcd_mod]
  rw [gcd_eq_one_of_irreducible_of_nonzero_reduced hf ha hred]
  exact one_mod_eq_one_of_degree_pos hfdegree

/-- Reducing the xgcd left coefficient before multiplying preserves the
left-inverse congruence for nonzero reduced residues modulo an irreducible. -/
theorem mul_mod_xgcd_left_mod_eq_one_of_irreducible_of_nonzero_reduced {a f : GF2Poly}
    (hf : Irreducible f) (ha : a ≠ 0)
    (hred : a.IsZero ∨ a.degree < f.degree) :
    (a * ((xgcd a f).left % f)) % f = 1 % f := by
  have hfdegree : 0 < f.degree := by
    cases hred with
    | inl hzero =>
        exact False.elim (ha (eq_zero_of_isZero hzero))
    | inr hlt =>
        omega
  let r := xgcd a f
  let q := (divMod r.left f).1
  let rem := (divMod r.left f).2
  have hspec : q * f + rem = r.left := by
    simpa [q, rem] using divMod_spec r.left f
  have hrem_eq : rem = r.left + q * f := by
    calc
      rem = rem + 0 := by rw [add_zero]
      _ = rem + (q * f + q * f) := by simp
      _ = (rem + q * f) + q * f := by rw [add_assoc]
      _ = (q * f + rem) + q * f := by rw [add_comm rem (q * f)]
      _ = r.left + q * f := by rw [hspec]
  have hmul_congr : a * rem = a * r.left + (a * q) * f := by
    rw [hrem_eq, right_distrib, mul_assoc]
  calc
    (a * ((xgcd a f).left % f)) % f = (a * rem) % f := by rfl
    _ = (a * r.left + (a * q) * f) % f := by rw [hmul_congr]
    _ = (a * r.left) % f := mod_add_mul_right_eq_mod (a * r.left) (a * q) f
    _ = 1 % f := by
      rw [xgcd_left_mul_mod_eq_one_of_irreducible_of_nonzero_reduced hf ha hred]
      exact (one_mod_eq_one_of_degree_pos hfdegree).symm

/-- The packed single-word CLMUL/reduction path agrees with the polynomial
xgcd inverse for nonzero canonical representatives. -/
theorem packedReduceWord_clmul_packedInvWord_eq_one {n : Nat} {irr w : UInt64}
    (hn64 : n < 64) (hf : Irreducible (ofUInt64Monic irr n)) (hw : w ≠ 0)
    (hwlt : w.toNat < 2 ^ n) :
    packedReduceWord n irr
        (ofWords #[(clmul w (canonicalWordLT n hn64 (packedInvWord n irr w))).2,
          (clmul w (canonicalWordLT n hn64 (packedInvWord n irr w))).1]) =
      packedReduceWord n irr 1 := by
  let f := ofUInt64Monic irr n
  let a := ofUInt64 w
  let invWord := packedInvWord n irr w
  let invCanonical := canonicalWordLT n hn64 invWord
  let product :=
    ofWords #[(clmul w invCanonical).2, (clmul w invCanonical).1]
  have hfdegree : f.degree = n := by
    simpa [f] using degree_ofUInt64Monic_of_lt_64 irr hn64
  have ha_ne : a ≠ 0 := by
    simpa [a] using ofUInt64_ne_zero_of_ne_zero hw
  have ha_reduced : a.IsZero ∨ a.degree < f.degree := by
    rw [hfdegree]
    simpa [a] using ofUInt64_reduced_of_toNat_lt hwlt
  have hcanonical : invCanonical = invWord := by
    simpa [invCanonical, invWord] using
      canonicalWordLT_eq_self_of_lt hn64 (packedReduceWord_toNat_lt hn64
        ((xgcd (ofUInt64 w) (ofUInt64Monic irr n)).left))
  have hinvWord :
      ofUInt64 invWord = (xgcd a f).left % f := by
    have hred :
        ((xgcd a f).left % f).isZero = true ∨
          ((xgcd a f).left % f).degree < n := by
      have hmod := mod_degree_lt (xgcd a f).left f hf.1
      cases hmod with
      | inl hzero =>
          exact Or.inl hzero
      | inr hdegree =>
          exact Or.inr (by simpa [hfdegree] using hdegree)
    simpa [packedInvWord, invWord, a, f] using
      ofUInt64_packedReduceWord_eq_of_degree_lt (n := n) (irr := irr) hn64
        ((xgcd a f).left) hred
  have hinvCanonical : ofUInt64 invCanonical = (xgcd a f).left % f := by
    rw [hcanonical]
    exact hinvWord
  have hproductPoly : product = a * ((xgcd a f).left % f) := by
    calc
      product = ofUInt64 w * ofUInt64 invCanonical := by
          rw [ofUInt64_mul_ofUInt64 w invCanonical]
      _ = a * ((xgcd a f).left % f) := by rw [hinvCanonical]
  have hleftRed :
      (product % f).isZero = true ∨ (product % f).degree < n := by
    have hmod := mod_degree_lt product f hf.1
    cases hmod with
    | inl hzero =>
        exact Or.inl hzero
    | inr hdegree =>
        exact Or.inr (by simpa [hfdegree] using hdegree)
  have honeRed :
      ((1 : GF2Poly) % f).isZero = true ∨ ((1 : GF2Poly) % f).degree < n := by
    have hmod := mod_degree_lt (1 : GF2Poly) f hf.1
    cases hmod with
    | inl hzero =>
        exact Or.inl hzero
    | inr hdegree =>
        exact Or.inr (by simpa [hfdegree] using hdegree)
  apply ofUInt64_injective
  calc
    ofUInt64 (packedReduceWord n irr product)
        = product % f := by
            simpa [f, product] using
              ofUInt64_packedReduceWord_eq_of_degree_lt (n := n) (irr := irr)
                hn64 product hleftRed
    _ = (a * ((xgcd a f).left % f)) % f := by rw [hproductPoly]
    _ = 1 % f :=
        mul_mod_xgcd_left_mod_eq_one_of_irreducible_of_nonzero_reduced
          (a := a) (f := f) (by simpa [f] using hf) ha_ne ha_reduced
    _ = ofUInt64 (packedReduceWord n irr (1 : GF2Poly)) := by
        symm
        simpa [f] using
          ofUInt64_packedReduceWord_eq_of_degree_lt (n := n) (irr := irr)
            hn64 (1 : GF2Poly) honeRed

end GF2Poly
end Hex
