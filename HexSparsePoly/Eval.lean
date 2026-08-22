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
      rw [pow1, if_pos hodd, ih (by omega), sq_pow]
      have hexp : g + 2 = 2 * ((g + 2) / 2) + 1 := by omega
      rw [hexp]
      grind
  | case4 x g hodd ih =>
      rw [pow1, if_neg hodd, ih (by omega), sq_pow]
      have hexp : 2 * ((g + 2) / 2) = g + 2 := by omega
      rw [hexp]

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
        rw [if_neg (fun h : a.1 = e => he (by omega))]
      · rw [List.filter_cons_of_pos (by simpa using ha)]
        simp only [coeffList]
        by_cases hae : a.1 = e
        · rw [if_pos hae, if_pos hae]
        · rw [if_neg hae, if_neg hae, ih]

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
        (fun a _ b _ hab =>
          (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hk)).mpr hab)).1
      (mapTerms_canonical s.pairwise_toList
        (fun a _ b _ hab =>
          (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hk)).mpr hab)).2

/-- Coefficient law for the sparse substitution, positive case: the
coefficient moves from `e` to `k · e` untouched. -/
theorem coeff_substPow_mul [Add R] (s : SparsePoly R) {k : Nat}
    (hk : k ≠ 0) (e : Nat) : (s.substPow k).coeff (k * e) = s.coeff e := by
  unfold substPow
  rw [dif_neg hk, coeff_ofCanonicalList]
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
  rw [dif_neg hk, coeff_ofCanonicalList]
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
def compose [Add R] [Mul R] (s t : SparsePoly R) : SparsePoly R :=
  (s.terms.foldl
    (fun st term =>
      let tp : Option (SparsePoly R) :=
        if term.1 - st.2.1 = 0 then st.2.2
        else
          match st.2.2 with
          | none => some (polyPow1 t (term.1 - st.2.1))
          | some p => some (p * polyPow1 t (term.1 - st.2.1))
      let contrib : SparsePoly R :=
        match tp with
        | none => C term.2
        | some p => scale term.2 p
      (st.1 + contrib, (term.1, tp)))
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

/-- The fast path and the general path agree: what lets the cyclotomic
adapter use {name}`substPow` and reason with {name}`compose`. Proved in
the implementation work loop together with the `compose`
characterisations. -/
theorem substPow_eq_compose {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s : SparsePoly C) (k : Nat) :
    s.substPow k = s.compose (monomial k 1) := by
  sorry

theorem eval_substPow {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s : SparsePoly C) (k : Nat) (x : C) :
    (s.substPow k).eval x = s.eval (x ^ k) := by
  sorry

theorem eval_compose {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s t : SparsePoly C) (x : C) :
    (s.compose t).eval x = s.eval (t.eval x) := by
  sorry

theorem compose_toDense {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s t : SparsePoly C) :
    (s.compose t).toDense = s.toDense.compose t.toDense := by
  sorry

theorem substPow_toDense {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s : SparsePoly C) (k : Nat) :
    (s.substPow k).toDense = s.toDense.compose (DensePoly.monomial k 1) := by
  sorry

/-- Coefficient law for {name}`substScale`: proved in the implementation
work loop together with the `compose` characterisations. -/
theorem coeff_substScale {C : Type u} [Lean.Grind.CommRing C]
    [DecidableEq C] (s : SparsePoly C) (a : C) (e : Nat) :
    (s.substScale a).coeff e = s.coeff e * a ^ e := by
  sorry

end Agreements

end SparsePoly

end Hex
