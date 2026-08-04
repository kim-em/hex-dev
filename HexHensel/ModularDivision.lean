/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel.ModularPolynomial
public import HexPoly.Euclid.MonicUnique

public section

/-!
The modular coefficient kernel of the quadratic Hensel step.

This module holds the data the doubling step carries
(`Hex.QuadraticLiftResult`), the coefficientwise arithmetic it runs
modulo `m²`, and the monic long division that its factor and Bezout
corrections both call. `HexHensel/Quadratic.lean` builds the step and its
correctness surface on top.

The division is the step's dominant cost, so it appears twice: once as the
fuel-driven specification `divModMonicModSquareAux`, whose recursion the
correctness proofs read, and once as the windowed
`divModMonicModSquareAuxImpl` that a `@[csimp]` theorem installs as the
compiled shape.
-/

namespace Hex

/-- Output of one quadratic Hensel doubling step. The four fields package the
updated leading factor `g` (monic, the input `g` corrected modulo `m^2`), the
updated complementary factor `h`, and the updated Bezout witnesses `s`, `t`
satisfying `s * g + t * h ≡ 1 (mod m^2)`. -/
structure QuadraticLiftResult where
  /-- The updated monic factor. -/
  g : ZPoly
  /-- The updated complementary factor. -/
  h : ZPoly
  /-- The updated Bezout coefficient multiplying `g`. -/
  s : ZPoly
  /-- The updated Bezout coefficient multiplying `h`. -/
  t : ZPoly

namespace QuadraticLiftResult

/-- Canonical coefficient reduction modulo `m^2`. -/
@[expose]
def reduceModSquare (f : ZPoly) (m : Nat) : ZPoly :=
  ZPoly.reduceModPow f m 2

/-- Residue `f - g * h` corrected by the factor update of the quadratic Hensel
step: starting from `g * h ≡ f (mod m)`, this quantity is divisible by `m` and
its lift drives the first-order correction that achieves `g' * h' ≡ f (mod
m^2)`. -/
@[expose]
def factorError (f g h : ZPoly) : ZPoly :=
  f - g * h

/-- Runtime implementation of {name}`factorError`: the same residual with the
product taken by Kronecker substitution (`Hex.ZPoly.mulKronecker`, value-equal
to the schoolbook product by `Hex.ZPoly.mulKronecker_eq`). The bignum Hensel
step is the only caller, and its `g * h` is the widest product in the lift. -/
def factorErrorImpl (f g h : ZPoly) : ZPoly :=
  f - ZPoly.mulKronecker g h

/-- Register the Kronecker product as the compiled implementation of
{name}`factorError`. -/
@[csimp]
theorem factorError_eq_impl : @factorError = @factorErrorImpl := by
  funext f g h
  unfold factorError factorErrorImpl
  rw [ZPoly.mulKronecker_eq]

end QuadraticLiftResult

namespace ZPoly

/-- The working modulus `m * m = m²` of one quadratic Hensel doubling step. -/
@[expose]
def quadraticModulus (m : Nat) : Nat :=
  m * m

/-- Canonical nonnegative residue of `z` in the range `[0, modulus)`. -/
@[expose]
def canonicalMod (z : Int) (modulus : Nat) : Int :=
  Int.ofNat <| Int.toNat (z % Int.ofNat modulus)

/-- Reduce a single coefficient to its canonical residue modulo `m²`. -/
@[expose]
def reduceCoeffModSquare (z : Int) (m : Nat) : Int :=
  canonicalMod z (quadraticModulus m)

/-- Polynomial sum `f + g` with every coefficient reduced modulo `m²`. -/
@[expose]
def addModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f + g) m

/-- Polynomial difference `f - g` with every coefficient reduced modulo `m²`. -/
@[expose]
def subModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f - g) m

/-- Polynomial product `f * g` with every coefficient reduced modulo `m²`.

Public, unlike its sibling reductions, because its compiled implementation is
swapped by a `@[csimp]` theorem, and `csimp` lemmas must be public. -/
@[expose]
def mulModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f * g) m

/-- Runtime implementation of {name}`mulModSquare`: the same reduced product
with the multiplication taken by Kronecker substitution. Eight of the nine
polynomial products in the bignum quadratic step go through this definition. -/
def mulModSquareImpl (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (ZPoly.mulKronecker f g) m

/-- Register the Kronecker product as the compiled implementation of
{name}`mulModSquare`. -/
@[csimp]
theorem mulModSquare_eq_impl : @mulModSquare = @mulModSquareImpl := by
  funext f g m
  unfold mulModSquare mulModSquareImpl
  rw [ZPoly.mulKronecker_eq]

/-- Modular multiplication by a single monomial. Kept as a separate
specification so compiled division can avoid sending the monomial's leading
zero coefficients through the generic schoolbook multiplier. -/
@[expose]
def mulMonomialModSquare
    (k : Nat) (coeff : Int) (q : ZPoly) (m : Nat) : ZPoly :=
  mulModSquare (DensePoly.monomial k coeff) q m

/-- Multiplication by `coeff * X^k` is a scaled coefficient shift. -/
private theorem monomial_mul_eq_shift_scale
    (k : Nat) (coeff : Int) (q : ZPoly) :
    DensePoly.monomial k coeff * q =
      DensePoly.shift k (DensePoly.scale coeff q) := by
  have hmono : DensePoly.monomial k coeff =
      DensePoly.scale coeff (DensePoly.monomial k 1) := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_monomial, DensePoly.coeff_scale_semiring,
      DensePoly.coeff_monomial]
    by_cases hnk : n = k
    · simp [hnk]
    · simp only [hnk, ↓reduceIte]
      exact (Lean.Grind.Semiring.mul_zero coeff).symm
  rw [hmono, ← DensePoly.scale_mul,
    DensePoly.monomial_one_mul_poly_eq_shift]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale_semiring,
    DensePoly.coeff_shift_scale_semiring, DensePoly.coeff_shift]
  by_cases hnk : n < k
  · simp only [hnk, ↓reduceIte]
    exact Lean.Grind.Semiring.mul_zero coeff
  · simp [hnk]

/-- Linear-time implementation of modular monomial multiplication. -/
def mulMonomialModSquareImpl
    (k : Nat) (coeff : Int) (q : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare
    (DensePoly.shift k (DensePoly.scale coeff q)) m

/-- The shift-and-scale monomial kernel is exactly the generic modular
product. -/
theorem mulMonomialModSquare_eq
    (k : Nat) (coeff : Int) (q : ZPoly) (m : Nat) :
    mulMonomialModSquare k coeff q m =
      mulMonomialModSquareImpl k coeff q m := by
  unfold mulMonomialModSquare mulMonomialModSquareImpl mulModSquare
  rw [monomial_mul_eq_shift_scale]

/-- Proof-backed compiled implementation of modular monomial multiplication. -/
@[csimp]
theorem mulMonomialModSquare_eq_impl :
    @mulMonomialModSquare = @mulMonomialModSquareImpl := by
  funext k coeff q m
  exact mulMonomialModSquare_eq k coeff q m

/-- Fuel-driven long-division kernel returning the quotient/remainder of the
running `rem` by the monic divisor `q`, with all arithmetic reduced modulo `m²`.
The Hensel theorem surface supplies monic divisors, so this exploits that
invariant to avoid coefficient division in the modular hot path. -/
@[expose]
def divModMonicModSquareAux
    (m : Nat) (q : ZPoly) : Nat → ZPoly → ZPoly → ZPoly × ZPoly
  | 0, quot, rem => (quot, rem)
  | fuel + 1, quot, rem =>
      if q.isZero then
        (0, QuadraticLiftResult.reduceModSquare rem m)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := reduceCoeffModSquare rem.leadingCoeff m
              let term := DensePoly.monomial k coeff
              let quot := addModSquare quot term m
              let rem := subModSquare rem (mulMonomialModSquare k coeff q m) m
              divModMonicModSquareAux m q fuel quot rem
        | _, _ => (quot, rem)

/-- Quotient and remainder of `p` divided by the monic divisor `q`, working
modulo `m²`, with the dividend size supplying the recursion fuel.

Public, unlike its `Aux` worker, because its compiled implementation is swapped
by a `@[csimp]` theorem, and `csimp` lemmas must be public. -/
@[expose]
def divModMonicModSquare (p q : ZPoly) (m : Nat) : ZPoly × ZPoly :=
  let p := QuadraticLiftResult.reduceModSquare p m
  divModMonicModSquareAux m q p.size 0 p

/-! Windowed monic modular division.

`divModMonicModSquareAux` rebuilds *and re-canonicalises* the whole running
remainder and the whole running quotient at every elimination step, though a
step changes only the `q.size` remainder slots inside the elimination window
and one quotient slot. On a bignum quadratic step that is `Θ(deg p · deg p)`
coefficient reductions where `Θ(deg p · deg q)` is the arithmetic actually
being done, and the two divisions of one bignum step measured as just over half
its total cost.

`elimStep` and `quotStep` below perform the same two
updates in one pass each, touching only the slots that change. Two facts
license that. A slot outside the window already holds a canonical residue, so
reducing it again is the identity; and a slot inside the window may subtract
the *raw* product where the specification subtracts its reduction, because
reducing a summand first does not move the difference's canonical
representative (`Hex.ZPoly.intEmod_sub_intEmod`). -/

/-- Subtract `coeff · X^k · q` from `rem` modulo `m²`, in one pass that reads
and reduces only the `q.size` slots the subtraction reaches. The remainder's
coefficient array is threaded linearly through the division loop, so each write
lands in place. -/
def elimStep (m : Nat) (rem q : ZPoly) (k : Nat) (coeff : Int) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range q.size).foldl
      (fun acc j =>
        acc.setIfInBounds (k + j)
          (intEmod (acc.getD (k + j) (0 : Int) - coeff * q.coeff j) (m * m)))
      rem.toArray

/-- Write `coeff` into slot `k` of the running quotient. The division loop fills
the quotient from its top slot downwards, so only the first write of a division
grows the array; every later one lands in place. -/
def quotStep (quot : ZPoly) (k : Nat) (coeff : Int) : ZPoly :=
  DensePoly.ofCoeffs <|
    if k < quot.size then quot.toArray.setIfInBounds k coeff
    else Array.ofFn (n := k + 1) fun i => if i.val = k then coeff else quot.coeff i.val

private theorem getD_setIfInBounds (a : Array Int) (i j : Nat) (v : Int) :
    (a.setIfInBounds i v).getD j (Zero.zero : Int)
      = if j = i ∧ i < a.size then v else a.getD j (Zero.zero : Int) := by
  by_cases hji : j = i
  · subst hji
    by_cases hi : j < a.size
    · rw [if_pos ⟨rfl, hi⟩, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by simpa using hi)]
      simp
    · rw [if_neg (by omega : ¬ (j = j ∧ j < a.size)),
        Array.setIfInBounds, dif_neg hi]
  · rw [if_neg (by omega : ¬ (j = i ∧ i < a.size)),
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds]
    rw [if_neg (by omega : ¬ (i = j))]

private theorem elimFold_size (M : Nat) (q : ZPoly) (k : Nat) (c : Int) :
    ∀ (len : Nat) (a : Array Int),
      ((List.range len).foldl
        (fun acc j => acc.setIfInBounds (k + j)
          (intEmod (acc.getD (k + j) (Zero.zero : Int) - c * q.coeff j) M)) a).size
        = a.size := by
  intro len
  induction len with
  | zero => intro a; simp
  | succ len ih =>
      intro a
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Array.size_setIfInBounds]
      exact ih a

/-- Every slot of the elimination fold's window carries the reduced difference;
every other slot is untouched. -/
private theorem elimFold_getD (M : Nat) (q : ZPoly) (k : Nat) (c : Int) :
    ∀ (len : Nat) (a : Array Int) (n : Nat), k + len ≤ a.size →
      ((List.range len).foldl
        (fun acc j => acc.setIfInBounds (k + j)
          (intEmod (acc.getD (k + j) (Zero.zero : Int) - c * q.coeff j) M)) a).getD n
          (Zero.zero : Int)
      = if k ≤ n ∧ n - k < len then
          intEmod (a.getD n (Zero.zero : Int) - c * q.coeff (n - k)) M
        else a.getD n (Zero.zero : Int) := by
  intro len
  induction len with
  | zero =>
      intro a n _
      simp
  | succ len ih =>
      intro a n hbound
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [getD_setIfInBounds, elimFold_size M q k c len a,
        ih a (k + len) (by omega), ih a n (by omega),
        if_neg (by omega : ¬ (k ≤ k + len ∧ k + len - k < len))]
      by_cases hn : n = k + len
      · subst hn
        rw [if_pos ⟨rfl, by omega⟩, if_pos ⟨by omega, by omega⟩,
          show k + len - k = len by omega]
      · rw [if_neg (by omega : ¬ (n = k + len ∧ k + len < a.size))]
        by_cases hk : k ≤ n
        · by_cases hlt : n - k < len
          · rw [if_pos ⟨hk, hlt⟩, if_pos ⟨hk, by omega⟩]
          · rw [if_neg (by omega : ¬ (k ≤ n ∧ n - k < len)),
              if_neg (by omega : ¬ (k ≤ n ∧ n - k < len + 1))]
        · rw [if_neg (by omega : ¬ (k ≤ n ∧ n - k < len)),
            if_neg (by omega : ¬ (k ≤ n ∧ n - k < len + 1))]

theorem coeff_elimStep (m : Nat) (rem q : ZPoly) (k : Nat) (coeff : Int)
    (hwindow : k + q.size ≤ rem.size) (i : Nat) :
    (elimStep m rem q k coeff).coeff i =
      if k ≤ i ∧ i - k < q.size then
        intEmod (rem.coeff i - coeff * q.coeff (i - k)) (m * m)
      else rem.coeff i := by
  unfold elimStep
  rw [DensePoly.coeff_ofCoeffs]
  show ((List.range q.size).foldl
      (fun acc j => acc.setIfInBounds (k + j)
        (intEmod (acc.getD (k + j) (Zero.zero : Int) - coeff * q.coeff j) (m * m)))
      rem.toArray).getD i (Zero.zero : Int) = _
  rw [elimFold_getD (m * m) q k coeff q.size rem.toArray i (by simpa using hwindow)]
  rfl

private theorem elimStep_size_le (m : Nat) (rem q : ZPoly) (k : Nat) (coeff : Int) :
    (elimStep m rem q k coeff).size ≤ rem.size := by
  unfold elimStep
  have h := DensePoly.size_ofCoeffs_le
    ((List.range q.size).foldl
      (fun acc j => acc.setIfInBounds (k + j)
        (intEmod (acc.getD (k + j) (0 : Int) - coeff * q.coeff j) (m * m)))
      rem.toArray)
  rw [show ((List.range q.size).foldl
      (fun acc j => acc.setIfInBounds (k + j)
        (intEmod (acc.getD (k + j) (0 : Int) - coeff * q.coeff j) (m * m)))
      rem.toArray).size
      = ((List.range q.size).foldl
        (fun acc j => acc.setIfInBounds (k + j)
          (intEmod (acc.getD (k + j) (Zero.zero : Int) - coeff * q.coeff j) (m * m)))
        rem.toArray).size from rfl,
    elimFold_size (m * m) q k coeff q.size rem.toArray] at h
  simpa using h

/-- Default-indexed read of an `Array.ofFn` of integers. -/
private theorem intArray_ofFn_getD {n : Nat} (f : Fin n → Int) (i : Nat) :
    (Array.ofFn f).getD i (Zero.zero : Int) =
      if h : i < n then f ⟨i, h⟩ else (Zero.zero : Int) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : i < n
  · rw [dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

theorem coeff_quotStep (quot : ZPoly) (k : Nat) (coeff : Int) (i : Nat) :
    (quotStep quot k coeff).coeff i = if i = k then coeff else quot.coeff i := by
  unfold quotStep
  rw [DensePoly.coeff_ofCoeffs]
  by_cases hk : k < quot.size
  · rw [if_pos hk, getD_setIfInBounds]
    by_cases hik : i = k
    · rw [if_pos ⟨hik, by simpa using hk⟩, if_pos hik]
    · rw [if_neg (by omega : ¬ (i = k ∧ k < quot.toArray.size)), if_neg hik,
        DensePoly.toArray_getD]
  · rw [if_neg hk, intArray_ofFn_getD]
    by_cases hik : i = k
    · rw [dif_pos (by omega : i < k + 1), if_pos hik]
    · by_cases hi : i < k + 1
      · rw [dif_pos hi, if_neg hik]
      · rw [dif_neg hi, if_neg hik,
          DensePoly.coeff_eq_zero_of_size_le quot (by omega)]

private theorem pow_two_eq_mul (m : Nat) : m ^ 2 = m * m := by
  rw [Nat.pow_succ, Nat.pow_one]

/-- Coefficients of the modular monomial product, before the surrounding
subtraction sees them. -/
private theorem coeff_mulMonomialModSquare (m : Nat) (q : ZPoly) (k : Nat)
    (coeff : Int) (i : Nat) :
    (mulMonomialModSquare k coeff q m).coeff i =
      if k ≤ i then intEmod (coeff * q.coeff (i - k)) (m * m) else 0 := by
  unfold mulMonomialModSquare mulModSquare QuadraticLiftResult.reduceModSquare
  rw [monomial_mul_eq_shift_scale, coeff_reduceModPow, pow_two_eq_mul,
    DensePoly.coeff_shift]
  by_cases hk : i < k
  · rw [if_pos hk, if_neg (by omega : ¬ k ≤ i)]
    show intEmod 0 (m * m) = 0
    unfold intEmod intModNat
    simp
  · rw [if_neg hk, if_pos (by omega : k ≤ i), DensePoly.coeff_scale_semiring]
    rfl

/-- The windowed elimination is the specification's elimination, given a
canonical remainder whose stored range is exactly the elimination window. -/
private theorem elimStep_eq (m : Nat) (hm : 0 < m) (rem q : ZPoly) (k : Nat) (coeff : Int)
    (hrem : Canonical rem (m * m)) (hsize : rem.size = k + q.size) :
    elimStep m rem q k coeff
      = subModSquare rem (mulMonomialModSquare k coeff q m) m := by
  have hmm : 0 < m * m := Nat.mul_pos hm hm
  have hzero : intEmod (0 : Int) (m * m) = 0 := by
    unfold intEmod intModNat
    simp
  apply DensePoly.ext_coeff
  intro i
  have hrhs : (subModSquare rem (mulMonomialModSquare k coeff q m) m).coeff i
      = intEmod (rem.coeff i
          - (if k ≤ i then intEmod (coeff * q.coeff (i - k)) (m * m) else 0)) (m * m) := by
    unfold subModSquare QuadraticLiftResult.reduceModSquare
    rw [coeff_reduceModPow, pow_two_eq_mul, DensePoly.coeff_sub_ring,
      coeff_mulMonomialModSquare]
    rfl
  rw [coeff_elimStep m rem q k coeff (by omega) i, hrhs]
  by_cases hk : k ≤ i
  · simp only [if_pos hk]
    rw [intEmod_sub_intEmod _ _ hmm]
    by_cases hi : i - k < q.size
    · rw [if_pos ⟨hk, hi⟩]
    · rw [if_neg (by omega : ¬ (k ≤ i ∧ i - k < q.size))]
      have hr : rem.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le rem (by omega)
      have hq : q.coeff (i - k) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le q (by omega)
      rw [hr, hq, Int.mul_zero, Int.sub_zero, hzero]
  · simp only [if_neg hk]
    rw [Int.sub_zero, if_neg (by omega : ¬ (k ≤ i ∧ i - k < q.size))]
    exact (intEmod_eq_self (hrem i).1 (hrem i).2).symm

/-- The windowed quotient write is the specification's quotient update, given a
canonical quotient whose slot `k` is still empty. -/
private theorem quotStep_eq (m : Nat) (_hm : 0 < m) (quot : ZPoly) (k : Nat) (coeff : Int)
    (hquot : Canonical quot (m * m)) (hslot : quot.coeff k = 0)
    (hc0 : 0 ≤ coeff) (hc1 : coeff < ((m * m : Nat) : Int)) :
    quotStep quot k coeff = addModSquare quot (DensePoly.monomial k coeff) m := by
  have hzero : intEmod (0 : Int) (m * m) = 0 := by
    unfold intEmod intModNat
    simp
  apply DensePoly.ext_coeff
  intro i
  have hrhs : (addModSquare quot (DensePoly.monomial k coeff) m).coeff i
      = intEmod (quot.coeff i + (if i = k then coeff else 0)) (m * m) := by
    unfold addModSquare QuadraticLiftResult.reduceModSquare
    rw [coeff_reduceModPow, pow_two_eq_mul, DensePoly.coeff_add_semiring,
      DensePoly.coeff_monomial]
    rfl
  rw [coeff_quotStep, hrhs]
  by_cases hik : i = k
  · simp only [if_pos hik]
    rw [hik, hslot, Int.zero_add]
    exact (intEmod_eq_self hc0 hc1).symm
  · simp only [if_neg hik]
    rw [Int.add_zero]
    exact (intEmod_eq_self (hquot i).1 (hquot i).2).symm

private theorem reduceCoeffModSquare_eq_intEmod (z : Int) (m : Nat) :
    reduceCoeffModSquare z m = intEmod z (m * m) := rfl

private theorem size_of_degree?_eq_some {p : ZPoly} {d : Nat} (h : p.degree? = some d) :
    p.size = d + 1 := by
  unfold DensePoly.degree? at h
  by_cases hz : p.size = 0
  · rw [dif_pos hz] at h
    exact absurd h (by simp)
  · rw [dif_neg hz] at h
    have hd : p.size - 1 = d := by
      injection h
    omega

/-- The elimination cancels the remainder's leading term, so the remainder's
stored range strictly shrinks and the loop makes progress. -/
private theorem elimStep_size_lt (m : Nat) (hm : 0 < m) (rem q : ZPoly) (rd qd : Nat)
    (hrd : rem.degree? = some rd) (hqd : q.degree? = some qd)
    (hq : DensePoly.leadingCoeff q = 1) (hle : qd ≤ rd) :
    (elimStep m rem q (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)).size
      < rem.size := by
  have hmm : 0 < m * m := Nat.mul_pos hm hm
  have hrsize : rem.size = rd + 1 := size_of_degree?_eq_some hrd
  have hqsize : q.size = qd + 1 := size_of_degree?_eq_some hqd
  have hqlead : q.coeff qd = 1 := by
    rw [← hq, DensePoly.leadingCoeff_eq_coeff_last q (by omega), hqsize]
    simp
  have hrlead : rem.leadingCoeff = rem.coeff rd := by
    rw [DensePoly.leadingCoeff_eq_coeff_last rem (by omega), hrsize]
    simp
  have htop : (elimStep m rem q (rd - qd)
      (reduceCoeffModSquare rem.leadingCoeff m)).coeff rd = 0 := by
    rw [coeff_elimStep m rem q (rd - qd) _ (by omega) rd,
      if_pos ⟨by omega, by omega⟩,
      show rd - (rd - qd) = qd by omega, hqlead, Int.mul_one,
      reduceCoeffModSquare_eq_intEmod, hrlead, intEmod_sub_intEmod _ _ hmm,
      Int.sub_self]
    unfold intEmod intModNat
    simp
  have hle' := elimStep_size_le m rem q (rd - qd)
    (reduceCoeffModSquare rem.leadingCoeff m)
  by_cases heq : (elimStep m rem q (rd - qd)
      (reduceCoeffModSquare rem.leadingCoeff m)).size = rem.size
  · exfalso
    have hpos : 0 < (elimStep m rem q (rd - qd)
        (reduceCoeffModSquare rem.leadingCoeff m)).size := by omega
    have := DensePoly.coeff_last_ne_zero_of_pos_size _ hpos
    rw [heq, hrsize] at this
    simp only [Nat.add_sub_cancel] at this
    exact this htop
  · omega

/-- Windowed shape of `divModMonicModSquareAux`: the same long division, with
each elimination step confined to the slots it changes. Proved equal to the
specification loop, on monic divisors at a positive modulus, in
`divModMonicModSquareAux_eq_impl`. -/
private def divModMonicModSquareAuxImpl
    (m : Nat) (q : ZPoly) : Nat → ZPoly → ZPoly → ZPoly × ZPoly
  | 0, quot, rem => (quot, rem)
  | fuel + 1, quot, rem =>
      if q.isZero then
        (0, QuadraticLiftResult.reduceModSquare rem m)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := reduceCoeffModSquare rem.leadingCoeff m
              divModMonicModSquareAuxImpl m q fuel (quotStep quot k coeff)
                (elimStep m rem q k coeff)
        | _, _ => (quot, rem)

private theorem divModMonicModSquareAux_eq_impl
    (m : Nat) (hm : 0 < m) (q : ZPoly) (hq : DensePoly.leadingCoeff q = 1) :
    ∀ (fuel : Nat) (quot rem : ZPoly),
      Canonical quot (m * m) → Canonical rem (m * m) →
      (∀ i, i + q.size ≤ rem.size → quot.coeff i = 0) →
      divModMonicModSquareAux m q fuel quot rem
        = divModMonicModSquareAuxImpl m q fuel quot rem := by
  have hmm : 0 < m * m := Nat.mul_pos hm hm
  have hpow : 0 < m ^ 2 := by
    rw [pow_two_eq_mul]
    exact hmm
  intro fuel
  induction fuel with
  | zero =>
      intro quot rem _ _ _
      rfl
  | succ fuel ih =>
      intro quot rem hquot hrem hsupp
      rw [divModMonicModSquareAux, divModMonicModSquareAuxImpl]
      by_cases hz : q.isZero = true
      · simp only [hz, if_true]
      · simp only [hz, if_false, Bool.false_eq_true]
        cases hrd : rem.degree? with
        | none => simp only
        | some rd =>
            cases hqd : q.degree? with
            | none => simp only
            | some qd =>
                simp only
                by_cases hlt : rd < qd
                · simp only [if_pos hlt]
                · simp only [if_neg hlt]
                  have hle : qd ≤ rd := by omega
                  have hrsize : rem.size = rd + 1 := size_of_degree?_eq_some hrd
                  have hqsize : q.size = qd + 1 := size_of_degree?_eq_some hqd
                  have hwindow : rem.size = (rd - qd) + q.size := by omega
                  have hcmem := intEmod_mem rem.leadingCoeff hmm
                  have hstepQ :
                      quotStep quot (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)
                        = addModSquare quot
                          (DensePoly.monomial (rd - qd)
                            (reduceCoeffModSquare rem.leadingCoeff m)) m := by
                    refine quotStep_eq m hm quot _ _ hquot ?_ ?_ ?_
                    · exact hsupp _ (by omega)
                    · rw [reduceCoeffModSquare_eq_intEmod]
                      exact hcmem.1
                    · rw [reduceCoeffModSquare_eq_intEmod]
                      exact hcmem.2
                  have hstepR :
                      elimStep m rem q (rd - qd) (reduceCoeffModSquare rem.leadingCoeff m)
                        = subModSquare rem
                          (mulMonomialModSquare (rd - qd)
                            (reduceCoeffModSquare rem.leadingCoeff m) q m) m :=
                    elimStep_eq m hm rem q _ _ hrem hwindow
                  have hcanonQ : Canonical
                      (quotStep quot (rd - qd)
                        (reduceCoeffModSquare rem.leadingCoeff m)) (m * m) := by
                    rw [hstepQ]
                    show Canonical (ZPoly.reduceModPow _ m 2) (m * m)
                    rw [← pow_two_eq_mul]
                    exact canonical_reduceModPow _ m 2 hpow
                  have hcanonR : Canonical
                      (elimStep m rem q (rd - qd)
                        (reduceCoeffModSquare rem.leadingCoeff m)) (m * m) := by
                    rw [hstepR]
                    show Canonical (ZPoly.reduceModPow _ m 2) (m * m)
                    rw [← pow_two_eq_mul]
                    exact canonical_reduceModPow _ m 2 hpow
                  have hshrink := elimStep_size_lt m hm rem q rd qd hrd hqd hq hle
                  have hsupp' : ∀ i,
                      i + q.size ≤ (elimStep m rem q (rd - qd)
                        (reduceCoeffModSquare rem.leadingCoeff m)).size →
                      (quotStep quot (rd - qd)
                        (reduceCoeffModSquare rem.leadingCoeff m)).coeff i = 0 := by
                    intro i hi
                    have hik : i < rd - qd := by omega
                    rw [coeff_quotStep, if_neg (by omega : ¬ i = rd - qd)]
                    exact hsupp i (by omega)
                  rw [← hstepQ, ← hstepR]
                  exact ih _ _ hcanonQ hcanonR hsupp'

/-- Windowed implementation of the modular monic division.

The windowed loop needs a monic divisor at a positive modulus -- the only shape
the Hensel step ever divides by; every other input falls back to the
specification loop, so the two agree on every input. -/
def divModMonicModSquareImpl (p q : ZPoly) (m : Nat) : ZPoly × ZPoly :=
  let reduced := QuadraticLiftResult.reduceModSquare p m
  if 0 < m ∧ DensePoly.leadingCoeff q = 1 then
    divModMonicModSquareAuxImpl m q reduced.size 0 reduced
  else
    divModMonicModSquareAux m q reduced.size 0 reduced

/-- Proof-backed compiled implementation of the modular monic division. -/
@[csimp] theorem divModMonicModSquare_eq_impl :
    @divModMonicModSquare = @divModMonicModSquareImpl := by
  funext p q m
  unfold divModMonicModSquare divModMonicModSquareImpl
  by_cases hguard : 0 < m ∧ DensePoly.leadingCoeff q = 1
  · rw [if_pos hguard]
    have hm := hguard.1
    have hpow : 0 < m ^ 2 := Nat.pow_pos hm
    have hcanon : Canonical (QuadraticLiftResult.reduceModSquare p m) (m * m) := by
      show Canonical (ZPoly.reduceModPow p m 2) (m * m)
      rw [← pow_two_eq_mul]
      exact canonical_reduceModPow p m 2 hpow
    refine divModMonicModSquareAux_eq_impl m hm q hguard.2 _ 0 _ ?_ hcanon ?_
    · intro i
      have hc : (0 : ZPoly).coeff i = 0 := by simp
      have hmm : (0 : Int) < ((m * m : Nat) : Int) := by
        exact_mod_cast Nat.mul_pos hm hm
      rw [hc]
      omega
    · intro i _
      simp
  · rw [if_neg hguard]

end ZPoly

end Hex
