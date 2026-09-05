/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePoly.Dense

@[expose] public section
set_option backward.proofsInPublic true

/-!
Evaluation, the derivative, and substitution on canonical sparse
polynomials. Evaluation runs Horner over the exponent gaps, so its cost
is the term count times the logarithm of the mean gap, not the degree.
`substPow` is the operation that stays sparse and is the reason the
library exists; `compose` is general substitution and promises nothing
about the size of its output.
-/

namespace Hex

open scoped Hex

universe u

namespace SparsePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- `x^g` for `g ≥ 1` by binary powering, using only multiplication:
gap powers never need an identity element (`pow1 x 0` is `x`, unused). -/
def pow1 [Mul R] (x : R) : Nat → R
  | 0 => x
  | 1 => x
  | g + 2 =>
      if (g + 2) % 2 = 1 then pow1 (x * x) ((g + 2) / 2) * x
      else pow1 (x * x) ((g + 2) / 2)
termination_by g => g
decreasing_by all_goals omega

/-- `a * x^g`, using only multiplication: `g = 0` is the identity
application and multiplies nothing. -/
def mulPow [Mul R] (a x : R) : Nat → R
  | 0 => a
  | g + 1 => a * pow1 x (g + 1)

/-- Gap-Horner worker: the value of an ascending term list at `x`,
relative to a base exponent, with each bracket closed by one gap power.
`evalShifted x l b` is `Σ cᵢ · x^(eᵢ − b)` bracketed as
`(c₀ + (c₁ + …) · x^(e₁−e₀)) · x^(e₀−b)`. -/
def evalShifted [Add R] [Mul R] (x : R) : List (Nat × R) → Nat → R
  | [], _ => 0
  | (e, c) :: rest, base => mulPow (c + evalShifted x rest e) x (e - base)

/-- Evaluate at `x` by Horner over the exponent gaps: writing `m` for
the term count and `n` for the degree, `m` additions and
`O(m · log(n/m + 1))` multiplications, against `DensePoly`'s `O(n)`. -/
def eval [Add R] [Mul R] (s : SparsePoly R) (x : R) : R :=
  evalShifted x s.terms.toList 0

section EvalLaws

variable {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]

omit [DecidableEq S] in
/-- Powers of the square are even powers. -/
theorem sq_pow (x : S) (n : Nat) : (x * x) ^ n = x ^ (2 * n) := by
  induction n with
  | zero => grind
  | succ n ih =>
      have hexp : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [hexp]
      have h1 : (x * x) ^ (n + 1) = (x * x) ^ n * (x * x) := by grind
      have h2 : x ^ (2 * n + 1 + 1) = x ^ (2 * n) * x * x := by grind
      rw [h1, ih, h2]
      grind

/-- The positive binary powering computes the semiring power. -/
theorem pow1_eq (x : S) (g : Nat) (hg : 1 ≤ g) : pow1 x g = x ^ g := by
  induction x, g using pow1.induct with
  | case1 x => omega
  | case2 x =>
      rw [pow1]
      grind
  | case3 x g hodd ih =>
      rw [pow1, ite_eq_left hodd, ih (by omega), sq_pow]
      have hexp : g + 2 = 2 * ((g + 2) / 2) + 1 := by omega
      rw [hexp]
      grind
  | case4 x g hodd ih =>
      rw [pow1, ite_eq_right hodd, ih (by omega), sq_pow]
      have hexp : 2 * ((g + 2) / 2) = g + 2 := by omega
      rw [hexp]

omit [DecidableEq S] in
/-- Powers at added exponents multiply. -/
theorem pow_add' (x : S) (a b : Nat) : x ^ a * x ^ b = x ^ (a + b) := by
  grind

/-- The gap multiplier computes multiplication by the power. -/
theorem mulPow_eq (a x : S) (g : Nat) : mulPow a x g = a * x ^ g := by
  cases g with
  | zero =>
      rw [mulPow]
      grind
  | succ g =>
      rw [mulPow, pow1_eq x (g + 1) (by omega)]

/-- The gap-Horner worker computes the exponent-shifted term sum. -/
theorem evalShifted_eq {l : List (Nat × S)}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) (x : S) (base : Nat)
    (hbase : ∀ t ∈ l, base ≤ t.1) :
    evalShifted x l base =
      l.foldr (fun t acc => t.2 * x ^ (t.1 - base) + acc) 0 := by
  induction l generalizing base with
  | nil => rfl
  | cons t rest ih =>
      rw [List.pairwise_cons] at hs
      rw [show evalShifted x ((t.1, t.2) :: rest) base =
          mulPow (t.2 + evalShifted x rest t.1) x (t.1 - base) from rfl,
        mulPow_eq, ih hs.2 t.1 (fun u hu => Nat.le_of_lt (hs.1 u hu)),
        List.foldr_cons]
      have hshift : ∀ (l' : List (Nat × S)), (∀ u ∈ l', t.1 ≤ u.1) →
          (l'.foldr (fun u acc => u.2 * x ^ (u.1 - t.1) + acc) 0) *
              x ^ (t.1 - base) =
            l'.foldr (fun u acc => u.2 * x ^ (u.1 - base) + acc) 0 := by
        intro l' hl'
        induction l' with
        | nil => grind
        | cons u us ihu =>
            rw [List.foldr_cons, List.foldr_cons,
              ← ihu fun v hv => hl' v (List.mem_cons_of_mem _ hv)]
            have hu := hl' u (List.mem_cons_self ..)
            have hexp : u.1 - t.1 + (t.1 - base) = u.1 - base := by
              have := hbase t (List.mem_cons_self ..)
              omega
            have hpow : x ^ (u.1 - t.1) * x ^ (t.1 - base) =
                x ^ (u.1 - base) := by
              rw [← hexp]
              exact pow_add' x _ _
            rw [Lean.Grind.Semiring.right_distrib,
              Lean.Grind.Semiring.mul_assoc, hpow]
      rw [← hshift rest (fun u hu => Nat.le_of_lt (hs.1 u hu))]
      grind

omit [DecidableEq S] in
/-- Every term sum over the stored terms evaluates the polynomial: the
bridge between the gap form and the dense fold-of-monomials form. -/
private theorem foldl_add_eval_monomials {l : List (Nat × S)} (x : S) :
    ∀ init : S,
    l.foldl (fun acc t => acc + t.2 * x ^ t.1) init =
      init + l.foldr (fun t acc => t.2 * x ^ t.1 + acc) 0 := by
  induction l with
  | nil =>
      intro init
      rw [List.foldl_nil, List.foldr_nil]
      grind
  | cons t rest ih =>
      intro init
      rw [List.foldl_cons, List.foldr_cons, ih]
      grind

/-- Gap Horner agrees with dense Horner. `Lean.Grind.Semiring` and not
`CommRing`: both run in the same orientation and the gap form only
skips the zero coefficients, so no coefficient is commuted past a power
of `x`. -/
theorem eval_toDense (s : SparsePoly S) (x : S) :
    s.eval x = s.toDense.eval x := by
  rw [show s.toDense = _ from toDense_foldl_monomial s]
  have hfold : ∀ (l : List (Nat × S)) (init : DensePoly S),
      DensePoly.eval (l.foldl
        (fun acc a => acc + DensePoly.monomial a.1 a.2) init) x =
      l.foldl (fun acc a => acc + a.2 * x ^ a.1) (DensePoly.eval init x) := by
    intro l
    induction l with
    | nil => intro init; rfl
    | cons a rest ih =>
        intro init
        rw [List.foldl_cons, List.foldl_cons, ih,
          DensePoly.eval_add_semiring, DensePoly.eval_monomial_semiring]
  rw [hfold, foldl_add_eval_monomials, DensePoly.eval_zero]
  unfold eval
  rw [evalShifted_eq s.pairwise_toList x 0 (fun t _ => Nat.zero_le _)]
  have : ∀ l : List (Nat × S),
      l.foldr (fun t acc => t.2 * x ^ (t.1 - 0) + acc) 0 =
        l.foldr (fun t acc => t.2 * x ^ t.1 + acc) 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons t rest ih =>
        rw [List.foldr_cons, List.foldr_cons, ih, Nat.sub_zero]
  rw [this]
  grind

end EvalLaws

/-- The formal derivative: `c · x^e` maps to `(e : R) · c · x^(e−1)`,
the `e = 0` term is dropped, and — the invariant hazard — a coefficient
`(e : R) * c` that vanishes (every exponent divisible by `p` over
`ZMod64 p`) drops its term rather than storing a zero. -/
def derivative [NatCast R] [Mul R] (s : SparsePoly R) : SparsePoly R :=
  ofCanonicalList
    (mapTerms (fun e => e - 1) (fun e c => (e : R) * c)
      (s.terms.toList.filter (fun t => t.1 ≠ 0)))
    (mapTerms_canonical
      (List.Pairwise.filter _ s.pairwise_toList)
      (fun a ha b hb hab => by
        have ha' := (List.mem_filter.mp ha).2
        have hb' := (List.mem_filter.mp hb).2
        simp only [decide_eq_true_eq] at ha' hb'
        omega)).1
    (mapTerms_canonical
      (List.Pairwise.filter _ s.pairwise_toList)
      (fun a ha b hb hab => by
        have ha' := (List.mem_filter.mp ha).2
        have hb' := (List.mem_filter.mp hb).2
        simp only [decide_eq_true_eq] at ha' hb'
        omega)).2

omit [DecidableEq R] in
/-- Removing the constant term changes no other coefficient. -/
theorem coeffList_filter_ne_zero {l : List (Nat × R)} {e : Nat}
    (he : e ≠ 0) :
    coeffList (l.filter (fun t => t.1 ≠ 0)) e = coeffList l e := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : a.1 = 0
      · rw [List.filter_cons_of_neg (by simpa using ha)]
        rw [ih]
        simp only [coeffList]
        rw [ite_eq_right (fun h : a.1 = e => he (by omega))]
      · rw [List.filter_cons_of_pos (by simpa using ha)]
        simp only [coeffList]
        by_cases hae : a.1 = e
        · rw [ite_eq_left hae, ite_eq_left hae]
        · rw [ite_eq_right hae, ite_eq_right hae, ih]

attribute [local instance 1100] Lean.Grind.Semiring.natCast

/-- Coefficient law for the derivative. -/
theorem coeff_derivative {S : Type u} [Lean.Grind.Semiring S]
    [DecidableEq S] (s : SparsePoly S) (f : Nat) :
    s.derivative.coeff f = ((f + 1 : Nat) : S) * s.coeff (f + 1) := by
  unfold derivative
  rw [coeff_ofCanonicalList]
  have happly := coeffList_mapTerms_apply (g := fun e => e - 1)
    (f := fun e c => ((e : Nat) : S) * c)
    (l := s.terms.toList.filter (fun t => t.1 ≠ 0)) (e := f + 1)
    (List.Pairwise.filter _ s.pairwise_toList)
    (fun u hu h => by
      have hu' := (List.mem_filter.mp hu).2
      simp only [decide_eq_true_eq] at hu'
      omega)
    (by grind)
  rw [show f + 1 - 1 = f from by omega] at happly
  rw [happly, coeffList_filter_ne_zero (by omega)]
  rfl

/-- Substitute `x^k` for `x`: multiply every exponent by `k`. For
`k ≥ 1` the map is strictly monotone, so the terms, their order, and
their coefficients are unchanged and the cost is `O(t)`. For `k = 0`
every term lands on exponent `0`, so the result is the combined
constant, which can vanish; that case is a canonicalisation to perform,
not an input to reject. -/
def substPow [Add R] (s : SparsePoly R) (k : Nat) : SparsePoly R :=
  if hk : k = 0 then ofTerms (s.terms.map fun t => (0, t.2))
  else
    ofCanonicalList
      (mapTerms (fun e => k * e) (fun _ c => c) s.terms.toList)
      (mapTerms_canonical s.pairwise_toList
        (fun _ _ _ _ hab =>
          (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hk)).mpr hab)).1
      (mapTerms_canonical s.pairwise_toList
        (fun _ _ _ _ hab =>
          (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hk)).mpr hab)).2

/-- Coefficient law for the sparse substitution, positive case: the
coefficient moves from `e` to `k · e` untouched. -/
theorem coeff_substPow_mul [Add R] (s : SparsePoly R) {k : Nat}
    (hk : k ≠ 0) (e : Nat) : (s.substPow k).coeff (k * e) = s.coeff e := by
  unfold substPow
  rw [dite_eq_right hk, coeff_ofCanonicalList]
  exact coeffList_mapTerms_apply (g := fun e => k * e)
    s.pairwise_toList
    (fun u _ h => by
      have : 1 ≤ k := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) h)
    rfl

/-- Off the multiples of `k`, the substituted polynomial vanishes. -/
theorem coeff_substPow_of_ne [Add R] (s : SparsePoly R) {k : Nat}
    (hk : k ≠ 0) {f : Nat} (hf : ∀ e, f ≠ k * e) :
    (s.substPow k).coeff f = 0 := by
  unfold substPow
  rw [dite_eq_right hk, coeff_ofCanonicalList]
  exact coeffList_mapTerms_of_ne fun u _ h => hf u.1 h.symm

/-- One step of the `substScale` walk: the power of `a` for the next
exponent, from the power at the previous one (`none` encodes `a^0`, so
no identity element is needed). -/
def substScaleStep [Mul R] (a : R) (prev : Nat) (pw : Option R)
    (e : Nat) : Option R :=
  if e - prev = 0 then pw
  else
    match pw with
    | none => some (pow1 a (e - prev))
    | some p => some (p * pow1 a (e - prev))

/-- Walk the ascending terms scaling each coefficient by the
accumulated power of `a`, dropping the products that vanish: the worker
for `substScale`. -/
def substScaleGo [Mul R] (a : R) : Nat → Option R →
    List (Nat × R) → List (Nat × R)
  | _, _, [] => []
  | prev, pw, t :: rest =>
      match substScaleStep a prev pw t.1 with
      | none =>
          if t.2 = 0 then substScaleGo a t.1 none rest
          else t :: substScaleGo a t.1 none rest
      | some p =>
          if t.2 * p = 0 then substScaleGo a t.1 (some p) rest
          else (t.1, t.2 * p) :: substScaleGo a t.1 (some p) rest

/-- Every exponent the walk emits is a stored one. -/
theorem exp_mem_substScaleGo [Mul R] {a : R} {l : List (Nat × R)}
    {prev : Nat} {pw : Option R} {u : Nat × R}
    (hu : u ∈ substScaleGo a prev pw l) : ∃ v ∈ l, u.1 = v.1 := by
  induction l generalizing prev pw with
  | nil => cases hu
  | cons t rest ih =>
      rw [substScaleGo] at hu
      split at hu <;> split at hu
      · obtain ⟨v, hv, huv⟩ := ih hu
        exact ⟨v, List.mem_cons_of_mem _ hv, huv⟩
      · rcases List.mem_cons.mp hu with heq | hu'
        · exact ⟨t, List.mem_cons_self .., by rw [heq]⟩
        · obtain ⟨v, hv, huv⟩ := ih hu'
          exact ⟨v, List.mem_cons_of_mem _ hv, huv⟩
      · obtain ⟨v, hv, huv⟩ := ih hu
        exact ⟨v, List.mem_cons_of_mem _ hv, huv⟩
      · rcases List.mem_cons.mp hu with heq | hu'
        · exact ⟨t, List.mem_cons_self .., by rw [heq]⟩
        · obtain ⟨v, hv, huv⟩ := ih hu'
          exact ⟨v, List.mem_cons_of_mem _ hv, huv⟩

/-- The walk emits a canonical list. -/
theorem substScaleGo_canonical [Mul R] {a : R} {l : List (Nat × R)}
    (hs : l.Pairwise (fun x y => x.1 < y.1)) (prev : Nat)
    (pw : Option R) :
    (substScaleGo a prev pw l).Pairwise (fun x y => x.1 < y.1) ∧
      ∀ t ∈ substScaleGo a prev pw l, t.2 ≠ 0 := by
  induction l generalizing prev pw with
  | nil =>
      rw [substScaleGo]
      exact ⟨List.Pairwise.nil, by intro t ht; cases ht⟩
  | cons t rest ih =>
      rw [List.pairwise_cons] at hs
      rw [substScaleGo]
      have hhead : ∀ pw' : Option R,
          ∀ u ∈ substScaleGo a t.1 pw' rest, t.1 < u.1 := by
        intro pw' u hu
        obtain ⟨v, hv, huv⟩ := exp_mem_substScaleGo hu
        rw [huv]
        exact hs.1 v hv
      split <;> split
      · exact ih hs.2 _ _
      · rename_i hc
        obtain ⟨hpw, hnz⟩ := ih hs.2 t.1 _
        refine ⟨List.pairwise_cons.mpr ⟨hhead _, hpw⟩, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hc
        · exact hnz u hu'
      · exact ih hs.2 _ _
      · rename_i hc
        obtain ⟨hpw, hnz⟩ := ih hs.2 t.1 _
        refine ⟨List.pairwise_cons.mpr ⟨hhead _, hpw⟩, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hc
        · exact hnz u hu'

/-- Scale the argument: `c · x^e` maps to `(c · a^e) · x^e`, with the
powers of `a` computed from the exponent gaps as `eval` computes its
powers of `x`. Exponents are unchanged; coefficients can vanish when
`a` is a zero divisor or zero, so the zero filter applies. -/
def substScale [Mul R] (s : SparsePoly R) (a : R) : SparsePoly R :=
  ofCanonicalList (substScaleGo a 0 none s.terms.toList)
    (substScaleGo_canonical s.pairwise_toList 0 none).1
    (substScaleGo_canonical s.pairwise_toList 0 none).2

/-- `p^g` for `g ≥ 1` by binary powering over `mul`, with no identity
needed: the gap powers of `compose` are always positive. -/
def polyPow1 [Add R] [Mul R] (p : SparsePoly R) : Nat → SparsePoly R
  | 0 => p
  | 1 => p
  | g + 2 =>
      if (g + 2) % 2 = 1 then polyPow1 (p * p) ((g + 2) / 2) * p
      else polyPow1 (p * p) ((g + 2) / 2)
termination_by g => g
decreasing_by all_goals omega

/-- Substitute `t` for `x` in `s`: `Σ cₑ · t^e` in increasing exponent,
with the powers of `t` obtained by binary powering from the exponent
gaps. The cost is the sum of the multiplication costs over this
schedule, not a function of the output size. A caller wanting `f(x^k)`
must use {name}`substPow`, never this. -/
def composeStep [Add R] [Mul R] (t : SparsePoly R)
    (st : SparsePoly R × Nat × Option (SparsePoly R)) (term : Nat × R) :
    SparsePoly R × Nat × Option (SparsePoly R) :=
  match term.1 - st.2.1 with
  | 0 =>
      (st.1 + (match st.2.2 with
        | none => C term.2
        | some p => scale term.2 p), term.1, st.2.2)
  | g + 1 =>
      match st.2.2 with
      | none =>
          (st.1 + scale term.2 (polyPow1 t (g + 1)), term.1,
            some (polyPow1 t (g + 1)))
      | some p =>
          (st.1 + scale term.2 (p * polyPow1 t (g + 1)), term.1,
            some (p * polyPow1 t (g + 1)))

/-- Substitute `t` for the variable of `s`: one fold of `composeStep` over the terms, carrying the running power of `t` across each exponent gap. -/
def compose [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R :=
  (s.terms.foldl (composeStep t)
    ((0 : SparsePoly R), (0, (none : Option (SparsePoly R))))).1

section Agreements

variable {S : Type u} [Lean.Grind.Semiring S] [DecidableEq S]

/-- The derivative transports through the dense conversion. -/
theorem derivative_toDense (s : SparsePoly S) :
    s.derivative.toDense = s.toDense.derivative := by
  apply DensePoly.ext_coeff
  intro f
  rw [coeff_toDense, coeff_derivative,
    DensePoly.coeff_derivative_semiring, coeff_toDense]

/-- The derivative is additive. -/
theorem derivative_add (s t : SparsePoly S) :
    (s + t).derivative = s.derivative + t.derivative := by
  apply ext_coeff
  intro f
  rw [coeff_derivative, coeff_add, coeff_add, coeff_derivative,
    coeff_derivative]
  grind

/-- The product rule, by transport through the dense derivative. -/
theorem derivative_mul {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s t : SparsePoly C) :
    (s * t).derivative = s.derivative * t + s * t.derivative := by
  apply toDense_inj
  rw [derivative_toDense, toDense_mul, toDense_add, toDense_mul,
    toDense_mul, derivative_toDense, derivative_toDense]
  exact DensePoly.derivative_mul _ _

section ComposeAlgebra

variable {K : Type u} [Lean.Grind.CommRing K] [DecidableEq K]

/-- Powers at added exponents multiply, on the polynomials themselves. -/
theorem poly_pow_add (p : SparsePoly K) (a b : Nat) :
    p ^ (a + b) = p ^ a * p ^ b := by
  induction b with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 from by omega, pow_succ, ih,
        pow_succ, ← mul_assoc, mul_comm p (p ^ a), mul_assoc]

/-- Powers of the square are even powers, on the polynomials
themselves. -/
theorem poly_sq_pow (p : SparsePoly K) (n : Nat) :
    (p * p) ^ n = p ^ (2 * n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]
  | succ n ih =>
      rw [pow_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 from by omega,
        pow_succ, pow_succ, mul_assoc]

/-- The positive binary powering over `mul` computes the power. -/
theorem polyPow1_eq (p : SparsePoly K) (g : Nat) (hg : 1 ≤ g) :
    polyPow1 p g = p ^ g := by
  induction p, g using polyPow1.induct with
  | case1 p => omega
  | case2 p =>
      rw [polyPow1, pow_succ, pow_zero, mul_one]
  | case3 p g hodd ih =>
      rw [polyPow1, ite_eq_left hodd, ih (by omega), poly_sq_pow]
      show p ^ (2 * ((g + 2) / 2)) * p = p ^ (g + 2)
      rw [mul_comm, ← pow_succ,
        show 2 * ((g + 2) / 2) + 1 = g + 2 from by omega]
  | case4 p g hodd ih =>
      rw [polyPow1, ite_eq_right hodd, ih (by omega), poly_sq_pow,
        show 2 * ((g + 2) / 2) = g + 2 from by omega]

/-- Evaluation is additive, by transport. -/
theorem eval_add (s t : SparsePoly K) (x : K) :
    (s + t).eval x = s.eval x + t.eval x := by
  rw [eval_toDense, toDense_add, DensePoly.eval_add_semiring,
    ← eval_toDense, ← eval_toDense]

/-- Evaluation is multiplicative, by transport. -/
theorem eval_mul (s t : SparsePoly K) (x : K) :
    (s * t).eval x = s.eval x * t.eval x := by
  rw [eval_toDense, toDense_mul, DensePoly.eval_mul_commring,
    ← eval_toDense, ← eval_toDense]

/-- Evaluating a monomial multiplies its coefficient by the power. -/
@[simp, grind =] theorem eval_monomial (e : Nat) (c : K) (x : K) :
    (monomial e c).eval x = c * x ^ e := by
  rw [eval_toDense, toDense_monomial, DensePoly.eval_monomial_semiring]

/-- Constants evaluate to their value. -/
@[simp, grind =] theorem eval_C (c : K) (x : K) : (C c).eval x = c := by
  show (monomial 0 c).eval x = c
  rw [eval_monomial]
  grind

/-- One evaluates to `1`. -/
@[simp, grind =] theorem eval_one (x : K) : (1 : SparsePoly K).eval x = 1 := by
  show (SparsePoly.C 1).eval x = 1
  rw [eval_C]

/-- Zero evaluates to `0`. -/
@[simp, grind =] theorem eval_zero (x : K) :
    (0 : SparsePoly K).eval x = 0 :=
  rfl

/-- Evaluation respects powers. -/
theorem eval_pow (s : SparsePoly K) (n : Nat) (x : K) :
    (s ^ n).eval x = s.eval x ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, eval_one]
      grind
  | succ n ih =>
      rw [pow_succ, eval_mul, ih]
      grind

/-- The value the `compose` walk carries for `t^prev` (`none` encodes
`t^0` so that no identity element is needed at the `[Add R] [Mul R]`
signature). -/
def tpVal : Option (SparsePoly K) → SparsePoly K
  | none => 1
  | some p => p

/-- The stateful gap-powered walk of {name}`compose` computes the plain
power-sum fold. -/
private theorem compose_go (t : SparsePoly K) (l : List (Nat × K)) :
    ∀ (acc : SparsePoly K) (prev : Nat) (tp : Option (SparsePoly K)),
    l.Pairwise (fun a b => a.1 < b.1) → (∀ u ∈ l, prev ≤ u.1) →
    (tp = none → prev = 0) → tpVal tp = t ^ prev →
    (l.foldl (composeStep t) (acc, (prev, tp))).1 =
      l.foldl (fun a u => a + SparsePoly.C u.2 * t ^ u.1) acc := by
  induction l with
  | nil =>
      intro acc prev tp _ _ _ _
      rfl
  | cons u rest ih =>
      intro acc prev tp hs hge hnone htpv
      rw [List.pairwise_cons] at hs
      rw [List.foldl_cons, List.foldl_cons]
      have hple : prev ≤ u.1 := hge u (List.mem_cons_self ..)
      have hnext : ∃ tp', composeStep t (acc, (prev, tp)) u =
          (acc + SparsePoly.C u.2 * t ^ u.1, u.1, tp') ∧
          (tp' = none → u.1 = 0) ∧ tpVal tp' = t ^ u.1 := by
        unfold composeStep
        cases hgap : u.1 - prev with
        | zero =>
            have hpe : prev = u.1 := by omega
            refine ⟨tp, ?_, ?_, ?_⟩
            · cases tp with
              | none =>
                  have h0 : u.1 = 0 := by
                    have := hnone rfl
                    omega
                  show (acc + SparsePoly.C u.2, u.1, none) = _
                  rw [h0, pow_zero, mul_one]
              | some p =>
                  show (acc + scale u.2 p, u.1, some p) = _
                  have hp : p = t ^ prev := htpv
                  rw [scale_eq_C_mul, hp, hpe]
            · intro h
              subst h
              have := hnone rfl
              omega
            · rw [htpv, hpe]
        | succ g =>
            have hg1 : g + 1 = u.1 - prev := hgap.symm
            cases tp with
            | none =>
                have h0 : prev = 0 := hnone rfl
                refine ⟨some (polyPow1 t (g + 1)), ?_, by simp, ?_⟩
                · show (acc + scale u.2 (polyPow1 t (g + 1)), u.1, _) = _
                  rw [scale_eq_C_mul, polyPow1_eq t _ (by omega),
                    show g + 1 = u.1 from by omega]
                · show polyPow1 t (g + 1) = t ^ u.1
                  rw [polyPow1_eq t _ (by omega),
                    show g + 1 = u.1 from by omega]
            | some p =>
                have hp : p = t ^ prev := htpv
                refine ⟨some (p * polyPow1 t (g + 1)), ?_, by simp, ?_⟩
                · show (acc + scale u.2 (p * polyPow1 t (g + 1)), u.1, _)
                      = _
                  rw [scale_eq_C_mul, polyPow1_eq t _ (by omega), hp,
                    ← poly_pow_add,
                    show prev + (g + 1) = u.1 from by omega]
                · show p * polyPow1 t (g + 1) = t ^ u.1
                  rw [polyPow1_eq t _ (by omega), hp, ← poly_pow_add,
                    show prev + (g + 1) = u.1 from by omega]
      obtain ⟨tp', hstep, hn', hv'⟩ := hnext
      rw [hstep]
      exact ih _ _ _ hs.2
        (fun v hv => Nat.le_of_lt (hs.1 v hv)) hn' hv'

end ComposeAlgebra

section Agreements

variable {K : Type u} [Lean.Grind.CommRing K] [DecidableEq K]

/-- {name}`compose` as the plain power-sum fold over the stored terms:
the characterisation everything below transports through. -/
theorem compose_eq_foldl (s t : SparsePoly K) :
    s.compose t =
      s.terms.toList.foldl
        (fun a u => a + SparsePoly.C u.2 * t ^ u.1) 0 := by
  show (s.terms.foldl (composeStep t) (0, 0, none)).1 = _
  rw [← Array.foldl_toList]
  exact compose_go t s.terms.toList 0 0 none s.pairwise_toList
    (fun u _ => Nat.zero_le _) (fun _ => rfl)
    (by show (1 : SparsePoly K) = t ^ 0; rw [pow_zero])

private theorem dense_C_zero : (DensePoly.C (0 : K)) = 0 := by
  apply DensePoly.ext_coeff
  intro f
  rw [DensePoly.coeff_C]
  rw [show (0 : DensePoly K).coeff f = 0 from
    DensePoly.coeff_eq_zero_of_size_le 0 (by simp)]
  split <;> rfl

private theorem q_mul_psf (q : DensePoly K) (cs : List K) :
    ∀ base, q * DensePoly.composeCoeffPowerSumFrom cs base q =
      DensePoly.composeCoeffPowerSumFrom cs (base + 1) q := by
  induction cs with
  | nil =>
      intro base
      show q * 0 = 0
      rw [DensePoly.mul_comm_poly]
      exact DensePoly.zero_mul q
  | cons c cs ih =>
      intro base
      show q * (DensePoly.C c * DensePoly.composePower q base + _) =
        DensePoly.C c * DensePoly.composePower q (base + 1) + _
      rw [DensePoly.mul_add_right_poly, ih,
        show DensePoly.composePower q (base + 1) =
          q * DensePoly.composePower q base from rfl,
        ← DensePoly.mul_assoc_poly, DensePoly.mul_comm_poly q (DensePoly.C c),
        DensePoly.mul_assoc_poly]

private theorem scl_eq_psf (q : DensePoly K) (cs : List K) :
    DensePoly.composeScalarCoeffList cs q =
      DensePoly.composeCoeffPowerSumFrom cs 0 q := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show DensePoly.C c + q * DensePoly.composeScalarCoeffList cs q = _
      rw [ih, q_mul_psf]
      show _ = DensePoly.C c * DensePoly.composePower q 0 + _
      rw [show DensePoly.composePower q 0 = DensePoly.C 1 from rfl,
        show DensePoly.C (1 : K) = (1 : DensePoly K) from rfl,
        DensePoly.mul_one_right_poly]

private theorem dense_foldl_add_init {α : Type _} (l : List α)
    (g : α → DensePoly K) :
    ∀ init, l.foldl (fun a u => a + g u) init =
      init + l.foldl (fun a u => a + g u) 0 := by
  induction l with
  | nil =>
      intro init
      rw [List.foldl_nil, List.foldl_nil, DensePoly.add_zero_poly]
  | cons u us ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih, ih ((0 : DensePoly K) + g u),
        DensePoly.zero_add, DensePoly.add_assoc_poly]

private theorem psf_eq_terms_sum (q : DensePoly K) (cs : List K) :
    ∀ base, DensePoly.composeCoeffPowerSumFrom cs base q =
      (termsOfCoeffsList base cs).foldl
        (fun a u => a + DensePoly.C u.2 * DensePoly.composePower q u.1)
        0 := by
  induction cs with
  | nil => intro base; rfl
  | cons c cs ih =>
      intro base
      show DensePoly.C c * DensePoly.composePower q base + _ = _
      rw [ih (base + 1)]
      by_cases hc : c = 0
      · rw [show termsOfCoeffsList base (c :: cs) =
            termsOfCoeffsList (base + 1) cs from by
          rw [termsOfCoeffsList, ite_eq_left hc]]
        rw [hc, dense_C_zero, DensePoly.zero_mul, DensePoly.zero_add]
      · rw [show termsOfCoeffsList base (c :: cs) =
            (base, c) :: termsOfCoeffsList (base + 1) cs from by
          rw [termsOfCoeffsList, ite_eq_right hc]]
        rw [List.foldl_cons]
        conv => rhs; rw [dense_foldl_add_init, DensePoly.zero_add]

/-- The dense image's stored coefficients walk back to exactly the
sparse terms. -/
private theorem termsOfCoeffsList_toDense (s : SparsePoly K) :
    termsOfCoeffsList 0 s.toDense.toList = s.terms.toList := by
  refine coeffList_ext (termsOfCoeffsList_canonical _ 0).1
    s.pairwise_toList (termsOfCoeffsList_canonical _ 0).2
    s.nonzero_toList ?_
  intro e
  have h := coeffList_termsOfCoeffsList s.toDense.toList 0 e
  rw [Nat.zero_add] at h
  rw [h]
  have h2 : s.toDense.toList.getD e (Zero.zero : K) = s.toDense.coeff e :=
    DensePoly.toList_getD_eq_coeff s.toDense e
  rw [show s.toDense.toList.getD e (0 : K) =
      s.toDense.toList.getD e (Zero.zero : K) from rfl, h2, coeff_toDense]
  rfl

/-- Powers transport to the dense iterated product. -/
theorem toDense_composePower (t : SparsePoly K) (n : Nat) :
    (t ^ n).toDense = DensePoly.composePower t.toDense n := by
  induction n with
  | zero =>
      rw [pow_zero, toDense_one]
      rfl
  | succ n ih =>
      rw [pow_succ, toDense_mul, ih]
      rfl

/-- The substitution transports: composing then converting is
converting then composing. -/
theorem compose_toDense (s t : SparsePoly K) :
    (s.compose t).toDense = s.toDense.compose t.toDense := by
  have hstep : ∀ (acc : DensePoly K) (c : K),
      acc * t.toDense + DensePoly.C c = DensePoly.C c + t.toDense * acc := by
    intro acc c
    rw [DensePoly.mul_comm_poly acc t.toDense, DensePoly.add_comm_poly]
  rw [DensePoly.compose_eq_composeScalarCoeffList_of_step _ _ hstep,
    scl_eq_psf, psf_eq_terms_sum, termsOfCoeffsList_toDense,
    compose_eq_foldl, toDense_foldl_add]
  rw [show (0 : SparsePoly K).toDense = 0 from toDense_zero]
  refine foldl_congr' rfl fun b u _ => ?_
  rw [toDense_mul, toDense_C, toDense_composePower]

/-- Powers of a monomial are monomials. -/
theorem monomial_pow (k : Nat) (c : K) (e : Nat) :
    (monomial k c) ^ e = monomial (k * e) (c ^ e) := by
  induction e with
  | zero =>
      rw [pow_zero, Nat.mul_zero, Lean.Grind.Semiring.pow_zero]
      rfl
  | succ e ih =>
      rw [pow_succ, ih, monomial_mul_monomial,
        show k + k * e = k * (e + 1) from by
          rw [Nat.mul_succ, Nat.add_comm],
        show c * c ^ e = c ^ (e + 1) from by grind]

/-- Constants scale monomials by scaling their coefficient. -/
theorem C_mul_monomial (c : K) (m : Nat) (d : K) :
    SparsePoly.C c * monomial m d = monomial m (c * d) := by
  show monomial 0 c * monomial m d = monomial m (c * d)
  rw [monomial_mul_monomial, Nat.zero_add]

private theorem coeff_monomial_foldl (l : List (Nat × K))
    (ex : Nat × K → Nat) (co : Nat × K → K) (f : Nat) :
    ∀ init : SparsePoly K,
    (l.foldl (fun a u => a + monomial (ex u) (co u)) init).coeff f =
      l.foldl
        (fun a u => a + (if f = ex u then co u else 0))
        (init.coeff f) := by
  induction l with
  | nil => intro init; rfl
  | cons u us ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih, coeff_add, coeff_monomial]

omit [DecidableEq K] in
private theorem foldl_add_ifs_zero {l : List (Nat × K)}
    {g : Nat × K → K} (h : ∀ u ∈ l, g u = 0) :
    ∀ x : K, l.foldl (fun a u => a + g u) x = x := by
  induction l with
  | nil => intro x; rfl
  | cons u us ih =>
      intro x
      rw [List.foldl_cons, h u (List.mem_cons_self ..),
        show x + (0 : K) = x from by grind]
      exact ih (fun v hv => h v (List.mem_cons_of_mem _ hv)) x

omit [DecidableEq K] in
private theorem foldl_single_match {l : List (Nat × K)}
    (hs : l.Pairwise (fun a b => a.1 < b.1)) {k : Nat} (hk : ¬ k = 0)
    (e : Nat) :
    l.foldl (fun a u => a + (if k * e = k * u.1 then u.2 else 0)) 0 =
      coeffList l e := by
  induction l with
  | nil => rfl
  | cons u us ih =>
      rw [List.pairwise_cons] at hs
      rw [List.foldl_cons]
      by_cases hue : u.1 = e
      · rw [ite_eq_left (by rw [hue]),
          show (0 : K) + u.2 = u.2 from by grind,
          foldl_add_ifs_zero (fun v hv => by
            rw [ite_eq_right (fun h => by
              have hev : e = v.1 := Nat.eq_of_mul_eq_mul_left
                (by omega) h
              have := hs.1 v hv
              omega)])]
        simp only [coeffList, ite_eq_left hue]
      · rw [ite_eq_right (fun h => hue (Nat.eq_of_mul_eq_mul_left
            (by omega) h).symm),
          show (0 : K) + 0 = 0 from by grind, ih hs.2]
        simp only [coeffList, ite_eq_right (fun h : u.1 = e => hue h)]

/-- The fast path and the general path agree: what lets the cyclotomic
adapter use {name}`substPow` and reason with {name}`compose`. -/
theorem substPow_eq_compose (s : SparsePoly K) (k : Nat) :
    s.substPow k = s.compose (monomial k 1) := by
  rw [compose_eq_foldl]
  have hfold : s.terms.toList.foldl
      (fun a u => a + SparsePoly.C u.2 * monomial k 1 ^ u.1) 0 =
      s.terms.toList.foldl
        (fun a u => a + monomial (k * u.1) u.2) 0 := by
    refine foldl_congr' rfl fun b u _ => ?_
    rw [monomial_pow, C_mul_monomial, Lean.Grind.Semiring.one_pow,
      Lean.Grind.Semiring.mul_one]
  rw [hfold]
  apply ext_coeff
  intro f
  rw [coeff_monomial_foldl, coeff_zero]
  by_cases hk : k = 0
  · subst hk
    show (s.substPow 0).coeff f = _
    unfold substPow
    rw [dite_eq_left rfl, coeff_ofTerms_addCoeff]
    have hz : ∀ c : K, (0 : K) + c = c := by grind
    simp only [addCoeff_eq_add hz, Array.toList_map]
    by_cases hf : f = 0
    · subst hf
      rw [show ((s.terms.toList.map fun t => ((0 : Nat), t.2)).filter
          (fun t => t.1 = 0)) = s.terms.toList.map fun t => ((0 : Nat), t.2)
        from List.filter_eq_self.mpr (fun a ha => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
          simp)]
      rw [List.foldl_map]
      refine foldl_congr' rfl fun b u _ => ?_
      rw [ite_eq_left (by omega)]
    · rw [show ((s.terms.toList.map fun t => ((0 : Nat), t.2)).filter
          (fun t => t.1 = f)) = [] from List.filter_eq_nil_iff.mpr (fun a ha => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
          simpa using fun h : (0 : Nat) = f => hf h.symm)]
      rw [List.foldl_nil]
      exact ((foldl_add_ifs_zero (fun u _ => by
        rw [ite_eq_right (by omega)])) 0).symm
  · by_cases hmul : ∃ e, f = k * e
    · obtain ⟨e, rfl⟩ := hmul
      rw [coeff_substPow_mul s hk]
      exact (foldl_single_match s.pairwise_toList hk e).symm
    · rw [coeff_substPow_of_ne s hk (fun e h => hmul ⟨e, h⟩)]
      exact ((foldl_add_ifs_zero (fun u _ => by
        rw [ite_eq_right (fun h => hmul ⟨u.1, h⟩)])) 0).symm

private theorem eval_foldl_add {α : Type _} (l : List α)
    (g : α → SparsePoly K) (x : K) :
    ∀ init : SparsePoly K,
    (l.foldl (fun a u => a + g u) init).eval x =
      l.foldl (fun a u => a + (g u).eval x) (init.eval x) := by
  induction l with
  | nil => intro init; rfl
  | cons u us ih =>
      intro init
      rw [List.foldl_cons, List.foldl_cons, ih, eval_add]

/-- Substitution then evaluation is evaluation at the evaluation. -/
theorem eval_compose (s t : SparsePoly K) (x : K) :
    (s.compose t).eval x = s.eval (t.eval x) := by
  rw [compose_eq_foldl, eval_foldl_add, eval_zero]
  have hterm : ∀ (b : K) (u : Nat × K),
      b + (SparsePoly.C u.2 * t ^ u.1).eval x =
        b + u.2 * (t.eval x) ^ u.1 := by
    intro b u
    rw [eval_mul, eval_C, eval_pow]
  rw [foldl_congr' rfl (fun b u _ => hterm b u)]
  have hsub : ∀ (y : K) (l : List (Nat × K)),
      l.foldr (fun u acc => u.2 * y ^ (u.1 - 0) + acc) 0 =
        l.foldr (fun u acc => u.2 * y ^ u.1 + acc) 0 := by
    intro y l
    induction l with
    | nil => rfl
    | cons u us ih =>
        rw [List.foldr_cons, List.foldr_cons, ih, Nat.sub_zero]
  rw [show s.eval (t.eval x) =
      evalShifted (t.eval x) s.terms.toList 0 from rfl,
    evalShifted_eq s.pairwise_toList _ 0 (fun u _ => Nat.zero_le _),
    hsub (t.eval x) s.terms.toList, foldl_add_eval_monomials]
  grind

/-- Evaluating the exponent substitution is evaluating at the power. -/
theorem eval_substPow (s : SparsePoly K) (k : Nat) (x : K) :
    (s.substPow k).eval x = s.eval (x ^ k) := by
  rw [substPow_eq_compose, eval_compose, eval_monomial,
    show (1 : K) * x ^ k = x ^ k from by grind]

/-- The exponent substitution transports to dense composition with the
unit monomial. -/
theorem substPow_toDense (s : SparsePoly K) (k : Nat) :
    (s.substPow k).toDense = s.toDense.compose (DensePoly.monomial k 1) := by
  rw [substPow_eq_compose, compose_toDense, toDense_monomial]

/-- The power of `a` the `substScale` walk carries (`none` encodes
`a^0`). -/
private def pwVal : Option K → K
  | none => 1
  | some p => p

private theorem coeffList_substScaleGo (a : K) (l : List (Nat × K)) :
    ∀ (prev : Nat) (pw : Option K),
    l.Pairwise (fun x y => x.1 < y.1) → (∀ u ∈ l, prev ≤ u.1) →
    (pw = none → prev = 0) → pwVal pw = a ^ prev →
    ∀ f, coeffList (substScaleGo a prev pw l) f =
      coeffList l f * a ^ f := by
  induction l with
  | nil =>
      intro prev pw _ _ _ _ f
      show (0 : K) = 0 * a ^ f
      grind
  | cons u rest ih =>
      intro prev pw hs hge hnone hval f
      rw [List.pairwise_cons] at hs
      have hple : prev ≤ u.1 := hge u (List.mem_cons_self ..)
      have hnext : ∃ pw', substScaleGo a prev pw (u :: rest) =
          (if u.2 * pwVal pw' = 0 then substScaleGo a u.1 pw' rest
           else (u.1, u.2 * pwVal pw') :: substScaleGo a u.1 pw' rest) ∧
          (pw' = none → u.1 = 0) ∧ pwVal pw' = a ^ u.1 := by
        rw [substScaleGo]
        unfold substScaleStep
        by_cases hgap : u.1 - prev = 0
        · rw [ite_eq_left hgap]
          have hpe : prev = u.1 := by omega
          refine ⟨pw, ?_, ?_, ?_⟩
          · cases pw with
            | none =>
                show (if u.2 = 0 then _ else u :: _) = _
                rw [show pwVal (none : Option K) = 1 from rfl]
                by_cases hu2 : u.2 = 0
                · rw [ite_eq_left hu2, ite_eq_left (by rw [hu2]; grind)]
                · rw [ite_eq_right hu2, ite_eq_right (by
                    intro h
                    exact hu2 (by grind))]
                  rw [show (u.1, u.2 * (1 : K)) =
                    u from by rw [show u.2 * (1 : K) = u.2 from by grind]]
            | some p =>
                rfl
          · intro h
            rw [h] at hnone
            have := hnone rfl
            omega
          · rw [hval, hpe]
        · rw [ite_eq_right hgap]
          cases pw with
          | none =>
              have h0 : prev = 0 := hnone rfl
              refine ⟨some (pow1 a (u.1 - prev)), rfl, by simp, ?_⟩
              show pow1 a (u.1 - prev) = a ^ u.1
              rw [pow1_eq a _ (by omega),
                show u.1 - prev = u.1 from by omega]
          | some p =>
              have hp : p = a ^ prev := hval
              refine ⟨some (p * pow1 a (u.1 - prev)), rfl, by simp, ?_⟩
              show p * pow1 a (u.1 - prev) = a ^ u.1
              rw [pow1_eq a _ (by omega), hp]
              have : prev + (u.1 - prev) = u.1 := by omega
              rw [← this]
              grind
      obtain ⟨pw', hstep, hn', hv'⟩ := hnext
      rw [hstep]
      have hrest := ih u.1 pw' hs.2
        (fun v hv => Nat.le_of_lt (hs.1 v hv)) hn' hv'
      have htail_zero : coeffList (substScaleGo a u.1 pw' rest) u.1 = 0 := by
        rw [hrest u.1]
        rw [coeffList_eq_zero (l := rest) (fun v hv hveq => by
          have := hs.1 v hv
          omega)]
        grind
      by_cases hzero : u.2 * pwVal pw' = 0
      · rw [ite_eq_left hzero]
        by_cases hf : u.1 = f
        · rw [← hf, htail_zero]
          simp only [coeffList, ite_true]
          rw [← hv', ← hzero]
        · rw [hrest f]
          simp only [coeffList, ite_eq_right hf]
      · rw [ite_eq_right hzero]
        by_cases hf : u.1 = f
        · simp only [coeffList, ite_eq_left hf]
          rw [← hf, hv']
        · simp only [coeffList, ite_eq_right hf]
          exact hrest f

/-- Coefficient law for {name}`substScale`: each coefficient is scaled
by the power of the argument at its exponent. -/
theorem coeff_substScale (s : SparsePoly K) (a : K) (e : Nat) :
    (s.substScale a).coeff e = s.coeff e * a ^ e := by
  unfold substScale
  rw [coeff_ofCanonicalList]
  exact coeffList_substScaleGo a s.terms.toList 0 none
    s.pairwise_toList (fun u _ => Nat.zero_le _) (fun _ => rfl)
    (by show (1 : K) = a ^ 0; grind) e

omit [DecidableEq K] in
private theorem foldl_scale_match {l : List (Nat × K)}
    (hs : l.Pairwise (fun x y => x.1 < y.1)) (a : K) (f : Nat) :
    l.foldl (fun acc u => acc + (if f = u.1 then u.2 * a ^ u.1 else 0)) 0 =
      coeffList l f * a ^ f := by
  induction l with
  | nil =>
      show (0 : K) = 0 * a ^ f
      grind
  | cons u us ih =>
      rw [List.pairwise_cons] at hs
      rw [List.foldl_cons]
      by_cases huf : f = u.1
      · rw [ite_eq_left huf,
          show (0 : K) + u.2 * a ^ u.1 = u.2 * a ^ u.1 from by grind,
          foldl_add_ifs_zero (fun v hv => by
            rw [ite_eq_right (fun h => by
              have := hs.1 v hv
              omega)])]
        simp only [coeffList, ite_eq_left huf.symm]
        rw [huf]
      · rw [ite_eq_right huf, show (0 : K) + 0 = 0 from by grind, ih hs.2]
        simp only [coeffList, ite_eq_right (fun h : u.1 = f => huf h.symm)]

/-- Argument scaling is composition with the degree-one monomial
`a · x`: the sparse fast path and the general path agree. -/
theorem substScale_eq_compose (s : SparsePoly K) (a : K) :
    s.substScale a = s.compose (monomial 1 a) := by
  rw [compose_eq_foldl]
  have hfold : s.terms.toList.foldl
      (fun b u => b + SparsePoly.C u.2 * monomial 1 a ^ u.1) 0 =
      s.terms.toList.foldl
        (fun b u => b + monomial u.1 (u.2 * a ^ u.1)) 0 := by
    refine foldl_congr' rfl fun b u _ => ?_
    rw [monomial_pow, C_mul_monomial, Nat.one_mul]
  rw [hfold]
  apply ext_coeff
  intro f
  rw [coeff_substScale, coeff_monomial_foldl, coeff_zero]
  exact (foldl_scale_match s.pairwise_toList a f).symm

/-- The scaling substitution transports to dense composition with the
degree-one monomial. -/
theorem substScale_toDense (s : SparsePoly K) (a : K) :
    (s.substScale a).toDense = s.toDense.compose (DensePoly.monomial 1 a) := by
  rw [substScale_eq_compose, compose_toDense, toDense_monomial]

end Agreements

end Agreements

end SparsePoly

end Hex
