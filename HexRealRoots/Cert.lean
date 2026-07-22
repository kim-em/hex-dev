/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Var

public section

/-!
Executable chain-validity certificate for kernel replay.

The `isolate_roots` term elaborator (companion `HexRealRootsMathlib`) reifies
the Sturm chain of `p` once as a literal `Array ZPoly`, then discharges every
per-interval `count_one` and the `complete` field as cheap sign-variation
`decide`s against that literal chain, rather than rebuilding `sturmChain p`
inside each field. `SturmChainCert p chain` is the single decidable predicate
that validates the reified chain: it verifies, by coefficient-level checks that
kernel-reduce, that `chain` *is* the Sturm chain of `p`. Its soundness bridge
`cert_imp_eq` proves `chain = sturmChain p` as a proposition (the ban is only on
*deciding* an `Array ZPoly` equality in the kernel — the core
`Array.instDecidableEqImpl` module issue — not on proving one), whence the two
transport lemmas `sturmCount_eq_of_cert` / `rootCount_eq_of_cert` rewrite the
certified counts onto the literal chain.

`orderedAdjacent` and `ordered_of_adjacent` are the companion upgrade for the
`RealRootIsolations.ordered` field: an engine emits its isolations sorted, so
the elaborator checks only the `size − 1` adjacent-pair inequalities (an `O(n)`
`decide`) and this lemma walks them up to the all-pairs `ordered` shape by
transitivity.

Everything here is Mathlib-free: coefficient extensionality, structural
induction over the chain, and the core `Dyadic` order lemmas.
-/
namespace Hex

namespace ZPoly

/-- Coefficient-level Boolean equality for `ZPoly`: the generic
`DensePoly.beqCoeffs` at `R = Int`. Kept as an `abbrev` so the Sturm-chain
checkers below read at the `ZPoly` level; see `DensePoly.beqCoeffs` for why
this is used instead of the structural `DecidableEq`. -/
@[expose]
abbrev beqCoeffs (a b : ZPoly) : Bool :=
  DensePoly.beqCoeffs a b

/-- `beqCoeffs` is sound: a `true` result forces genuine polynomial equality. -/
theorem eq_of_beqCoeffs {a b : ZPoly} (h : beqCoeffs a b = true) : a = b :=
  DensePoly.eq_of_beqCoeffs h

/-- The tail validator for `SturmChainCert`: given the two most recent chain
elements `prev`, `cur`, check that `rest` continues the Sturm chain exactly as
`sturmChainAux` builds it. An empty tail requires the next pseudo-remainder to
vanish (`sturmChainAux`'s stopping condition); a nonempty tail requires the
pseudo-remainder nonzero, its next element `= −primitivePart (spem prev cur)`,
and the rest to continue from `cur`, `next`. Mirrors `sturmChainAux`'s branch
structure so `certTail_sound` is a direct induction. -/
@[expose]
def certTail : ZPoly → ZPoly → List ZPoly → Bool
  | prev, cur, [] => (spem prev cur).isZero
  | prev, cur, next :: rest =>
      !(spem prev cur).isZero &&
        beqCoeffs next (-(primitivePart (spem prev cur))) &&
          certTail cur next rest

/-- The tail validator reconstructs `sturmChainAux` exactly: if `certTail prev
cur rest` holds and there is enough fuel, then running `sturmChainAux` from
`prev`, `cur` with accumulator `acc` yields `acc` followed by `rest`. Induction
on `rest`. -/
theorem certTail_sound :
    ∀ (fuel : Nat) (prev cur : ZPoly) (rest : List ZPoly) (acc : Array ZPoly),
      certTail prev cur rest = true → rest.length < fuel →
      (sturmChainAux fuel prev cur acc).toList = acc.toList ++ rest := by
  intro fuel prev cur rest
  induction rest generalizing fuel prev cur with
  | nil =>
    intro acc h hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [certTail] at h
    simp only [sturmChainAux, h, if_true, List.append_nil]
  | cons next rest ih =>
    intro acc h hfuel
    rw [List.length_cons] at hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [certTail, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hnz, hbeq⟩, htail⟩ := h
    have hnext : next = -(primitivePart (spem prev cur)) := eq_of_beqCoeffs hbeq
    have hnz2 : ¬ ((spem prev cur).isZero = true) := by rw [hnz]; exact Bool.false_ne_true
    have hstep := ih f cur next (acc.push next) htail (by omega)
    simp only [sturmChainAux]
    rw [if_neg hnz2, ← hnext, hstep]
    simp [Array.toList_push]

/-- A decidable executable certificate that `chain` is the Sturm chain of `p`,
by coefficient-level checks that kernel-reduce.

`chain` must have at least two elements, `p` must have positive degree
(`2 ≤ p.size`) and `chain` must be no longer than `p.size` (a fuel bound that
every genuine chain satisfies, since chain degrees strictly decrease). The head
must be `primitivePart p`, the second `primitivePart p'`, each further element
`−primitivePart (spem …)` of its two predecessors, and the chain must terminate
with a vanishing pseudo-remainder — exactly `sturmChain`'s construction. All
element comparisons go through `beqCoeffs`, never structural `Array` equality. -/
@[expose]
def sturmChainCertB (p : ZPoly) (chain : Array ZPoly) : Bool :=
  match chain.toList with
  | s₀ :: s₁ :: rest =>
      decide (2 ≤ p.size) && decide (chain.size ≤ p.size) &&
        beqCoeffs s₀ (primitivePart p) &&
          beqCoeffs s₁ (primitivePart (DensePoly.derivative p)) &&
            certTail s₀ s₁ rest
  | _ => false

end ZPoly

/-- Chain-validity certificate: `chain` is the Sturm chain of `p`. A decidable
`Prop` (the `Bool`-check `= true` pattern) verified by coefficient-level checks
that kernel-reduce. -/
@[expose]
def SturmChainCert (p : ZPoly) (chain : Array ZPoly) : Prop :=
  ZPoly.sturmChainCertB p chain = true

instance (p : ZPoly) (chain : Array ZPoly) : Decidable (SturmChainCert p chain) :=
  inferInstanceAs (Decidable (_ = true))

namespace ZPoly

/-- **Certificate soundness.** A valid `SturmChainCert p chain` identifies
`chain` with `sturmChain p` as a proposition. Proving (not deciding) this
equality sidesteps the kernel `Array.instDecidableEqImpl` block. -/
theorem cert_imp_eq {p : ZPoly} {chain : Array ZPoly}
    (h : SturmChainCert p chain) : chain = sturmChain p := by
  unfold SturmChainCert sturmChainCertB at h
  -- `chain` has at least two elements, else the match returns `false`.
  obtain ⟨s₀, s₁, rest, hl⟩ :
      ∃ s₀ s₁ rest, chain.toList = s₀ :: s₁ :: rest := by
    match hm : chain.toList with
    | [] => rw [hm] at h; simp at h
    | [_] => rw [hm] at h; simp at h
    | a :: b :: r => exact ⟨a, b, r, rfl⟩
  rw [hl] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsize2, hsizele⟩, hb0⟩, hb1⟩, htail⟩ := h
  have hs0 : s₀ = primitivePart p := eq_of_beqCoeffs hb0
  have hs1 : s₁ = primitivePart (DensePoly.derivative p) := eq_of_beqCoeffs hb1
  -- `chain.size = rest.length + 2`, and the fuel bound gives `rest.length < p.size`.
  have hlen : chain.size = rest.length + 2 := by
    have := congrArg List.length hl
    rw [Array.length_toList] at this
    simp at this
    omega
  have hfuel : rest.length < p.size := by omega
  -- Positive degree makes `sturmChain p` unfold to the `sturmChainAux` form.
  have hne : p.size ≠ 0 := by omega
  have hdeg : p.degree? = some (p.size - 1) := by
    unfold DensePoly.degree?
    rw [dif_neg hne]
  obtain ⟨m, hm2⟩ : ∃ m, p.size - 1 = m + 1 := ⟨p.size - 2, by omega⟩
  have hchain_eq : sturmChain p =
      sturmChainAux p.size (primitivePart p) (primitivePart (DensePoly.derivative p))
        #[primitivePart p, primitivePart (DensePoly.derivative p)] := by
    unfold sturmChain
    rw [hdeg, hm2]
    rfl
  rw [hchain_eq]
  -- Compare via `toList`.
  apply Array.ext'
  rw [certTail_sound p.size (primitivePart p) (primitivePart (DensePoly.derivative p)) rest
        #[primitivePart p, primitivePart (DensePoly.derivative p)]
        (by rw [← hs0, ← hs1]; exact htail) hfuel]
  rw [hl, hs0, hs1]
  simp

/-- **Count transport.** Under a valid certificate, the Sturm count of `p` on
any interval is the sign-variation gap of the *literal* certified chain at the
two endpoints — the shape the elaborator `decide`s per emitted root. -/
theorem sturmCount_eq_of_cert {p : ZPoly} {chain : Array ZPoly}
    (h : SturmChainCert p chain) (I : DyadicInterval) :
    sturmCount p I = (sturmVarAt chain I.lower : Int) - sturmVarAt chain I.upper := by
  unfold sturmCount
  rw [← cert_imp_eq h]

/-- **Root-count transport.** Under a valid certificate, the total root count of
`p` is the `−∞/+∞` sign-variation gap of the literal certified chain — the shape
the elaborator `decide`s for the `complete` field. -/
theorem rootCount_eq_of_cert {p : ZPoly} {chain : Array ZPoly}
    (h : SturmChainCert p chain) :
    rootCount p = sturmVarNegInf chain - sturmVarPosInf chain := by
  unfold rootCount
  rw [← cert_imp_eq h]

end ZPoly

/-- `Dyadic` version of `le_of_lt`, from `le_total` and the core `not_le`. -/
private theorem dyadic_le_of_lt {a b : Dyadic} (h : a < b) : a ≤ b := by
  rcases Dyadic.le_total a b with h1 | h1
  · exact h1
  · exact absurd h (Dyadic.not_le.mpr h1)

/-- An `O(n)` adjacent-pair order check on an emitted isolation array: every
consecutive pair has `upperᵢ ≤ lowerᵢ₊₁`. The elaborator `decide`s this in place
of the quadratic `RealRootIsolations.ordered`, which `ordered_of_adjacent`
recovers by transitivity. -/
@[expose]
def orderedAdjacent {p : ZPoly} (arr : Array (RealRootIsolation p)) : Bool :=
  (List.range (arr.size - 1)).all (fun i =>
    if h : i + 1 < arr.size then
      decide ((arr[i]'(by omega)).interval.upper ≤ (arr[i + 1]'h).interval.lower)
    else true)

/-- Each adjacent inequality certified by `orderedAdjacent`. -/
theorem adjacent_step {p : ZPoly} {arr : Array (RealRootIsolation p)}
    (h : orderedAdjacent arr = true) (i : Nat) (hi : i + 1 < arr.size) :
    (arr[i]'(by omega)).interval.upper ≤ (arr[i + 1]'hi).interval.lower := by
  have hmem : i ∈ List.range (arr.size - 1) := List.mem_range.mpr (by omega)
  have hstep := (List.all_eq_true.mp h) i hmem
  simp only [hi, dif_pos] at hstep
  exact of_decide_eq_true hstep

/-- The transitivity walk: `orderedAdjacent` (adjacent pairs) upgrades to the
all-pairs `RealRootIsolations.ordered` shape, using each interval's own
`lower < upper` to bridge consecutive gaps. -/
theorem ordered_of_adjacent {p : ZPoly} {arr : Array (RealRootIsolation p)}
    (h : orderedAdjacent arr = true) :
    ∀ i j : Fin arr.size, i < j →
      arr[i].interval.upper ≤ arr[j].interval.lower := by
  have aux : ∀ (j : Nat) (hj : j < arr.size) (i : Nat) (_hij : i < j),
      (arr[i]'(by omega)).interval.upper ≤ (arr[j]'hj).interval.lower := by
    intro j
    induction j with
    | zero => intro _ i hij; omega
    | succ j ih =>
      intro hj i hij
      rcases Nat.lt_or_ge i j with hlt | hge
      · have hjlt : j < arr.size := by omega
        have step1 := ih hjlt i hlt
        have step2 : (arr[j]'hjlt).interval.lower ≤ (arr[j]'hjlt).interval.upper :=
          dyadic_le_of_lt (arr[j]'hjlt).interval.lt
        have step3 := adjacent_step h j (by omega)
        exact Dyadic.le_trans step1 (Dyadic.le_trans step2 step3)
      · have hij' : i = j := by omega
        subst hij'
        exact adjacent_step h i (by omega)
  intro i j hij
  exact aux j.val j.isLt i.val hij

end Hex
