/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
public import HexMvPoly.Ring
public import HexMvPoly.Structural

@[expose] public section
set_option backward.proofsInPublic true

/-!
Canonical list arithmetic for kernel certificate replay.

Unlike the reference `MvPoly` representation, certificate arithmetic never
traverses an `Array`, `Vector`, or `Fin`. Exponents are ordinary lists and
terms are kept in descending lexicographic order. The coefficient operations
are deliberately the ordinary operations on the representation type: at
`Int` they reduce to `Int.add`, `Int.mul`, and `Int.neg`; `Rat` is already a
reduced numerator--denominator representation. Positive-characteristic replay
uses the modulus-parametrised natural-residue operations in `KernelResidue`.
-/

namespace Hex.MvPoly.Kernel

open Hex
open scoped Hex

universe u

/-- A list-form term: an exponent list and a coefficient. -/
abbrev Term (κ : Type u) := List Nat × κ

/-- A sparse polynomial represented by a canonical list of terms. -/
abbrev PolyList (κ : Type u) := List (Term κ)

/-! # Kernel primitives -/

/-- Equality of exponent lists, using only `Nat.beq` and structural recursion. -/
def expBeq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a b && expBeq as bs
  | _, _ => false

/-- Lexicographic comparison of exponent lists, using only `Nat.blt`. -/
def expCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      if Nat.blt a b then .lt
      else if Nat.blt b a then .gt
      else expCmp as bs

/-- Pointwise addition of exponent lists. Canonical inputs have equal length;
the trailing clauses make the operation total on untrusted data. -/
def addExp : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => Nat.add a b :: addExp as bs

/-- Insert one term into descending lexicographic order, adding coefficients
on a collision and dropping a zero coefficient. -/
def insert [Zero κ] [Add κ] [DecidableEq κ] (t : Term κ) :
    PolyList κ → PolyList κ
  | [] => if t.2 = 0 then [] else [t]
  | u :: us =>
      match expCmp t.1 u.1 with
      | .gt => if t.2 = 0 then u :: us else t :: u :: us
      | .eq =>
          let c := t.2 + u.2
          if c = 0 then us else (u.1, c) :: us
      | .lt => u :: insert t us

/-- Canonicalize an arbitrary term stream by insertion. -/
def normalize [Zero κ] [Add κ] [DecidableEq κ] :
    PolyList κ → PolyList κ
  | [] => []
  | t :: ts => insert t (normalize ts)

/-- Insertion sum, also the total fallback for an undersupplied merge budget. -/
def insertSum [Zero κ] [Add κ] [DecidableEq κ] :
    PolyList κ → PolyList κ → PolyList κ
  | [], q => q
  | t :: ts, q => insert t (insertSum ts q)

/-- Linear merge of descending term lists. Recursion is structural on fuel.
The public caller supplies the sum of the lengths, so its fallback is never
needed; the fallback keeps the denotation law unconditional. -/
def merge [Zero κ] [Add κ] [DecidableEq κ] :
    Nat → PolyList κ → PolyList κ → PolyList κ
  | _, [], q => q
  | _, p, [] => p
  | 0, p, q => insertSum p q
  | fuel + 1, t :: ts, u :: us =>
      match expCmp t.1 u.1 with
      | .gt => t :: merge fuel ts (u :: us)
      | .lt => u :: merge fuel (t :: ts) us
      | .eq =>
          let c := t.2 + u.2
          if c = 0 then merge fuel ts us
          else (t.1, c) :: merge fuel ts us

/-- Add canonical term lists in one merge pass. -/
def add [Zero κ] [Add κ] [DecidableEq κ] (p q : PolyList κ) : PolyList κ :=
  merge (Nat.add p.length q.length) p q

/-- Map coefficients, filtering zero results without changing exponents. -/
def mapCoeffs [Zero κ] [DecidableEq κ] (f : κ → κ) :
    PolyList κ → PolyList κ
  | [] => []
  | t :: ts =>
      let c := f t.2
      if c = 0 then mapCoeffs f ts else (t.1, c) :: mapCoeffs f ts

/-- Negate a canonical term list, defensively filtering zero results. -/
def neg [Zero κ] [Neg κ] [DecidableEq κ]
    (p : PolyList κ) : PolyList κ :=
  mapCoeffs Neg.neg p

/-- Subtraction through canonical addition and negation. -/
def sub [Zero κ] [Add κ] [Neg κ] [DecidableEq κ]
    (p q : PolyList κ) : PolyList κ := add p (neg q)

/-- Multiply every coefficient by a scalar, filtering zero products. -/
def smul [Zero κ] [Mul κ] [DecidableEq κ] (a : κ)
    (p : PolyList κ) : PolyList κ :=
  mapCoeffs (fun c => a * c) p

/-- Multiply one term by every term of a polynomial, canonicalizing the row. -/
def mulTerm [Zero κ] [Add κ] [Mul κ] [DecidableEq κ]
    (t : Term κ) : PolyList κ → PolyList κ
  | [] => []
  | u :: us =>
      insert (addExp t.1 u.1, t.2 * u.2) (mulTerm t us)

/-- Sum rows, used for the total fallback of balanced merging. -/
def sumRows [Zero κ] [Add κ] [DecidableEq κ] : List (PolyList κ) → PolyList κ
  | [] => []
  | p :: ps => add p (sumRows ps)

/-- Merge each adjacent pair of rows. -/
def mergeRound [Zero κ] [Add κ] [DecidableEq κ] :
    List (PolyList κ) → List (PolyList κ)
  | [] => []
  | [p] => [p]
  | p :: q :: ps => add p q :: mergeRound ps

/-- Balanced merge rounds, structurally recursive on a row-count budget. -/
def mergeRows [Zero κ] [Add κ] [DecidableEq κ] :
    Nat → List (PolyList κ) → PolyList κ
  | _, [] => []
  | _, [p] => p
  | 0, ps => sumRows ps
  | fuel + 1, ps => mergeRows fuel (mergeRound ps)

/-- Multiply via translated rows and balanced linear merges. -/
def mul [Zero κ] [Add κ] [Mul κ] [DecidableEq κ]
    (p q : PolyList κ) : PolyList κ :=
  mergeRows p.length (p.map fun t => mulTerm t q)

/-- The zero test for a canonical list. -/
def isZero : PolyList κ → Bool
  | [] => true
  | _ :: _ => false

/-- Structural equality of term lists, with explicit exponent comparison. -/
def beq [DecidableEq κ] : PolyList κ → PolyList κ → Bool
  | [], [] => true
  | t :: ts, u :: us =>
      expBeq t.1 u.1 && decide (t.2 = u.2) && beq ts us
  | _, _ => false

/-- Linear-time exponentiation used by `evalAt`; unlike the reference
repeated-squaring helper this is visibly structural recursion on `Nat`. -/
def pow [One κ] [Mul κ] (a : κ) : Nat → κ
  | 0 => 1
  | n + 1 => pow a n * a

/-- Evaluate a monomial at a list point, stopping at the shorter list. -/
def evalMono [One κ] [Mul κ] : List κ → List Nat → κ
  | x :: xs, e :: es => (pow x e) * evalMono xs es
  | _, _ => 1

/-- Evaluate a term list at a point. -/
def evalAt [Zero κ] [One κ] [Add κ] [Mul κ]
    (x : List κ) : PolyList κ → κ
  | [] => 0
  | t :: ts => t.2 * evalMono x t.1 + evalAt x ts

/-- The zero exponent list of length `n`. -/
def zeroExp : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: zeroExp n

/-- The list-form multiplicative identity in `n` variables. -/
def one [Zero κ] [One κ] [DecidableEq κ] (n : Nat) : PolyList κ :=
  if (1 : κ) = 0 then [] else [(zeroExp n, 1)]

/-! # Canonical form -/

/-- Canonical lists have the declared arity, strictly descending
lexicographic exponents, and no zero coefficient. The arity conjunct is
essential: without it distinct exponent lists can denote the same fixed-arity
monomial. -/
def Canonical [Zero κ] (n : Nat) (p : PolyList κ) : Prop :=
  (∀ t ∈ p, t.1.length = n) ∧
  p.Pairwise (fun a b => b.1 < a.1) ∧
  ∀ t ∈ p, t.2 ≠ 0

/-- The structurally generated zero exponent has its declared length. -/
theorem length_zeroExp (n : Nat) : (zeroExp n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeroExp, ih]

/-- The list-form multiplicative identity is canonical. -/
theorem one_canonical [Zero κ] [One κ] [DecidableEq κ] (n : Nat) :
    Canonical n (one (κ := κ) n) := by
  unfold one
  split
  · exact ⟨fun _ h => by contradiction, List.Pairwise.nil,
      fun _ h => by contradiction⟩
  · exact ⟨by simp [length_zeroExp], by simp, by simp_all⟩

/-- The explicit equality test agrees with equality of exponent lists. -/
theorem expBeq_iff {a b : List Nat} : expBeq a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [expBeq]
  | cons x xs ih =>
      cases b with
      | nil => simp [expBeq]
      | cons y ys => simp [expBeq, ih]

/-- The explicit kernel comparator is the standard lexicographic list
comparison. -/
theorem expCmp_eq_compare (a b : List Nat) : expCmp a b = compare a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
          by_cases hxy : x < y
          · simp [expCmp, Nat.blt_eq.mpr hxy, Nat.compare_eq_lt.mpr hxy]
          · by_cases hyx : y < x
            · simp [expCmp, Nat.blt_eq, hxy, hyx, Nat.compare_eq_gt.mpr hyx]
            · have h : x = y := Nat.le_antisymm (Nat.le_of_not_gt hyx)
                (Nat.le_of_not_gt hxy)
              subst y
              simp [expCmp, ih]

/-- The result `.lt` of the explicit comparator is lexicographic `<`. -/
theorem expCmp_eq_lt_iff {a b : List Nat} : expCmp a b = .lt ↔ a < b := by
  induction a generalizing b with
  | nil => cases b <;> simp [expCmp]
  | cons x xs ih =>
      cases b with
      | nil => simp [expCmp]
      | cons y ys =>
          by_cases hxy : x < y
          · simp [expCmp, Nat.blt_eq.mpr hxy, List.cons_lt_cons_iff, hxy]
          · by_cases hyx : y < x
            · have hne : x ≠ y := Nat.ne_of_gt hyx
              simp [expCmp, Nat.blt_eq, hxy, hyx, hne, List.cons_lt_cons_iff]
            · have heq : x = y := Nat.le_antisymm (Nat.le_of_not_gt hyx)
                (Nat.le_of_not_gt hxy)
              subst y
              simp [expCmp, ih]

/-- Pointwise exponent addition preserves a common arity. -/
theorem length_addExp {a b : List Nat} {n : Nat}
    (ha : a.length = n) (hb : b.length = n) :
    (addExp a b).length = n := by
  induction a generalizing b n with
  | nil => simpa [addExp] using hb
  | cons x xs ih =>
      cases b with
      | nil => simp_all [addExp]
      | cons y ys =>
          simp only [List.length_cons] at ha hb
          have hxs : xs.length = ys.length := by omega
          have hi := ih (b := ys) (n := xs.length) rfl hxs.symm
          simp only [addExp, List.length_cons]
          rw [hi]
          omega

/-- Every exponent emitted by insertion is either the inserted exponent or
an exponent already present. -/
theorem exp_mem_insert [Zero κ] [Add κ] [DecidableEq κ]
    {t u : Term κ} {us : PolyList κ}
    (h : u ∈ insert t us) : u.1 = t.1 ∨ ∃ v ∈ us, u.1 = v.1 := by
  induction us with
  | nil =>
      by_cases hz : t.2 = 0
      · simp [insert, hz] at h
      · simp [insert, hz] at h
        exact Or.inl (congrArg Prod.fst h)
  | cons v vs ih =>
      cases hc : expCmp t.1 v.1 with
      | gt =>
          by_cases hz : t.2 = 0
          · simp [insert, hc, hz] at h
            exact Or.inr ⟨u, List.mem_cons.mpr h, rfl⟩
          · simp only [insert, hc, hz, ite_false, List.mem_cons] at h
            rcases h with rfl | h
            · exact Or.inl rfl
            · exact Or.inr ⟨u, List.mem_cons.mpr h, rfl⟩
      | eq =>
          have heq : t.1 = v.1 := by
            rw [expCmp_eq_compare] at hc
            exact Std.LawfulEqCmp.eq_of_compare hc
          by_cases hz : t.2 + v.2 = 0
          · simp [insert, hc, hz] at h
            exact Or.inr ⟨u, List.mem_cons_of_mem _ h, rfl⟩
          · simp only [insert, hc, hz, ite_false, List.mem_cons] at h
            rcases h with h | h
            · left
              simpa [heq] using congrArg Prod.fst h
            · exact Or.inr ⟨u, List.mem_cons_of_mem _ h, rfl⟩
      | lt =>
          simp only [insert, hc, List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inr ⟨u, List.mem_cons_self .., rfl⟩
          · rcases ih h with h | ⟨w, hw, he⟩
            · exact Or.inl h
            · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, he⟩

/-- Insertion preserves canonical form. The inserted coefficient may be
zero; in that case no term is added. -/
theorem insert_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} {t : Term κ} {p : PolyList κ}
    (ht : t.1.length = n) (hp : Canonical n p) :
    Canonical n (insert t p) := by
  induction p with
  | nil =>
      simp only [insert]
      split
      · exact ⟨by simp, by simp, by simp⟩
      · exact ⟨by simpa, by simp, by simp_all⟩
  | cons u us ih =>
      rcases hp with ⟨hlen, hpair, hnz⟩
      have huLen := hlen u (List.mem_cons_self ..)
      have husLen : ∀ v ∈ us, v.1.length = n :=
        fun v hv => hlen v (List.mem_cons_of_mem _ hv)
      have husPair := (List.pairwise_cons.mp hpair).2
      have husNz : ∀ v ∈ us, v.2 ≠ 0 :=
        fun v hv => hnz v (List.mem_cons_of_mem _ hv)
      have hi := ih ⟨husLen, husPair, husNz⟩
      simp only [insert]
      split
      next hcmp =>
        have htu : u.1 < t.1 := by
          have hcomp : compare t.1 u.1 = .gt := by
            simpa [expCmp_eq_compare] using hcmp
          have hrev : compare u.1 t.1 = .lt :=
            Std.OrientedCmp.gt_iff_lt.mp hcomp
          have hcmp' : expCmp u.1 t.1 = .lt := by
            rw [expCmp_eq_compare]
            exact hrev
          exact expCmp_eq_lt_iff.mp hcmp'
        split
        · exact ⟨hlen, hpair, hnz⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact ht
            · exact hlen v hv
          · rw [List.pairwise_cons]
            refine ⟨?_, hpair⟩
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact htu
            · exact List.lt_trans ((List.pairwise_cons.mp hpair).1 v hv) htu
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · assumption
            · exact hnz v hv
      next hcmp =>
        have htu : t.1 = u.1 := by
          rw [expCmp_eq_compare] at hcmp
          exact Std.LawfulEqCmp.eq_of_compare hcmp
        split
        · exact ⟨husLen, husPair, husNz⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact huLen
            · exact husLen v hv
          · simpa using hpair
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · assumption
            · exact husNz v hv
      next hcmp =>
        have htu : t.1 < u.1 := by
          exact expCmp_eq_lt_iff.mp hcmp
        refine ⟨?_, ?_, ?_⟩
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact huLen
          · exact hi.1 v hv
        · rw [List.pairwise_cons]
          refine ⟨?_, hi.2.1⟩
          intro v hv
          rcases exp_mem_insert hv with h | ⟨w, hw, he⟩
          · simpa [h] using htu
          · have huw := (List.pairwise_cons.mp hpair).1 w hw
            simpa [he] using huw
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hnz v (List.mem_cons_self ..)
          · exact hi.2.2 v hv

/-- Normalization emits a canonical list when every input exponent has the
declared arity. -/
theorem normalize_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} {p : PolyList κ} (h : ∀ t ∈ p, t.1.length = n) :
    Canonical n (normalize p) := by
  induction p with
  | nil =>
      exact ⟨fun t ht => by contradiction, List.Pairwise.nil,
        fun t ht => by contradiction⟩
  | cons t ts ih =>
      rw [normalize]
      apply insert_canonical (h t (List.mem_cons_self ..))
      exact ih fun u hu => h u (List.mem_cons_of_mem _ hu)

/-- Addition preserves canonical form. -/
theorem insertSum_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} {p q : PolyList κ}
    (hp : Canonical n p) (hq : Canonical n q) : Canonical n (insertSum p q) := by
  induction p with
  | nil => exact hq
  | cons t ts ih =>
      rw [insertSum]
      apply insert_canonical (hp.1 t (List.mem_cons_self ..))
      exact ih ⟨fun u hu => hp.1 u (List.mem_cons_of_mem _ hu),
        (List.pairwise_cons.mp hp.2.1).2,
        fun u hu => hp.2.2 u (List.mem_cons_of_mem _ hu)⟩

private theorem insertSum_exps [Zero κ] [Add κ] [DecidableEq κ]
    (P : List Nat → Prop) (p q : PolyList κ)
    (hp : ∀ t ∈ p, P t.1) (hq : ∀ t ∈ q, P t.1) :
    ∀ t ∈ insertSum p q, P t.1 := by
  induction p with
  | nil => exact hq
  | cons u us ih =>
      intro t ht
      rcases exp_mem_insert ht with he | ⟨v, hv, he⟩
      · rw [he]; exact hp u (by simp)
      · rw [he]; exact ih (fun v hv => hp v (by simp [hv])) v hv

private theorem merge_exps [Zero κ] [Add κ] [DecidableEq κ]
    (P : List Nat → Prop) (fuel : Nat) (p q : PolyList κ)
    (hp : ∀ t ∈ p, P t.1) (hq : ∀ t ∈ q, P t.1) :
    ∀ t ∈ merge fuel p q, P t.1 := by
  induction fuel generalizing p q with
  | zero =>
      cases p <;> cases q
      · exact hq
      · exact hq
      · exact hp
      · exact insertSum_exps P _ _ hp hq
  | succ fuel ih =>
      cases p with
      | nil => exact hq
      | cons t ts =>
        cases q with
        | nil => exact hp
        | cons u us =>
          have hts : ∀ v ∈ ts, P v.1 := fun v hv => hp v (by simp [hv])
          have hus : ∀ v ∈ us, P v.1 := fun v hv => hq v (by simp [hv])
          simp only [merge]
          split
          · simpa using And.intro (hp t (by simp)) (ih ts (u :: us) hts hq)
          · simpa using And.intro (hq u (by simp)) (ih (t :: ts) us hp hus)
          · split
            · exact ih ts us hts hus
            · simpa using And.intro (hp t (by simp)) (ih ts us hts hus)

private theorem canonical_tail [Zero κ] {n : Nat} {t : Term κ}
    {ts : PolyList κ} (h : Canonical n (t :: ts)) : Canonical n ts :=
  ⟨fun u hu => h.1 u (by simp [hu]), (List.pairwise_cons.mp h.2.1).2,
    fun u hu => h.2.2 u (by simp [hu])⟩

private theorem canonical_cons [Zero κ] {n : Nat} {t : Term κ}
    {ts : PolyList κ} (ht : t.1.length = n) (hz : t.2 ≠ 0)
    (hs : Canonical n ts) (hb : ∀ u ∈ ts, u.1 < t.1) :
    Canonical n (t :: ts) :=
  ⟨by simpa using And.intro ht hs.1,
    List.pairwise_cons.mpr ⟨hb, hs.2.1⟩,
    by simpa using And.intro hz hs.2.2⟩

/-- Merging preserves canonical form, including for an undersupplied budget. -/
theorem merge_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} (fuel : Nat) {p q : PolyList κ}
    (hp : Canonical n p) (hq : Canonical n q) :
    Canonical n (merge fuel p q) := by
  induction fuel generalizing p q with
  | zero =>
      cases p <;> cases q
      · exact hq
      · exact hq
      · exact hp
      · exact insertSum_canonical hp hq
  | succ fuel ih =>
      cases p with
      | nil => exact hq
      | cons t ts =>
        cases q with
        | nil => exact hp
        | cons u us =>
          have hts := canonical_tail hp
          have hus := canonical_tail hq
          have htb := (List.pairwise_cons.mp hp.2.1).1
          have hub := (List.pairwise_cons.mp hq.2.1).1
          simp only [merge]
          split
          next hc =>
            have htu : u.1 < t.1 := by
              apply expCmp_eq_lt_iff.mp
              rw [expCmp_eq_compare]
              exact Std.OrientedCmp.gt_iff_lt.mp (by simpa [expCmp_eq_compare] using hc)
            apply canonical_cons (hp.1 t (by simp)) (hp.2.2 t (by simp)) (ih hts hq)
            refine merge_exps (fun e => e < t.1) fuel ts (u :: us) htb ?_
            intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact htu
            · exact List.lt_trans (hub v hv) htu
          next hc =>
            have htu := expCmp_eq_lt_iff.mp hc
            apply canonical_cons (hq.1 u (by simp)) (hq.2.2 u (by simp)) (ih hp hus)
            apply merge_exps (fun e => e < u.1) fuel (t :: ts) us
            · intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact htu
              · exact List.lt_trans (htb v hv) htu
            · exact hub
          next hc =>
            have he : t.1 = u.1 := by
              simpa [expCmp_eq_compare] using hc
            split
            · exact ih hts hus
            next hz =>
              apply canonical_cons (t := (t.1, t.2 + u.2))
                (hp.1 t (by simp)) hz (ih hts hus)
              refine merge_exps (fun e => e < t.1) fuel ts us htb ?_
              simpa [he] using hub

/-- Addition preserves canonical form. -/
theorem add_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} {p q : PolyList κ}
    (hp : Canonical n p) (hq : Canonical n q) : Canonical n (add p q) :=
  merge_canonical _ hp hq

/-- Once the combined input length is covered, extra fuel cannot change a
merge. In particular the insertion fallback is irrelevant to public addition. -/
theorem merge_stable [Zero κ] [Add κ] [DecidableEq κ]
    (fuel extra : Nat) (p q : PolyList κ) (h : p.length + q.length ≤ fuel) :
    merge (fuel + extra) p q = merge fuel p q := by
  induction fuel generalizing p q with
  | zero =>
      have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst p
      simp [merge]
  | succ fuel ih =>
      cases p with
      | nil => simp [merge]
      | cons t ts =>
        cases q with
        | nil => simp [merge]
        | cons u us =>
          have hts : ts.length + (u :: us).length ≤ fuel := by simp_all; omega
          have hus : (t :: ts).length + us.length ≤ fuel := by simp_all; omega
          have hboth : ts.length + us.length ≤ fuel := by simp_all; omega
          simp only [Nat.succ_add, merge]
          split
          · rw [ih ts (u :: us) hts]
          · rw [ih (t :: ts) us hus]
          · split <;> rw [ih ts us hboth]

/-- The public addition budget agrees with any larger merge budget. -/
theorem add_eq_merge [Zero κ] [Add κ] [DecidableEq κ]
    (p q : PolyList κ) (fuel : Nat) (h : p.length + q.length ≤ fuel) :
    add p q = merge fuel p q := by
  have hs := merge_stable (p.length + q.length) (fuel - (p.length + q.length)) p q
    (Nat.le_refl _)
  have he : p.length + q.length + (fuel - (p.length + q.length)) = fuel := by omega
  rw [he] at hs
  exact hs.symm

/-- A coefficient map preserves the exponent of every surviving term. -/
theorem exp_mem_mapCoeffs [Zero κ] [DecidableEq κ] (f : κ → κ)
    {u : Term κ} {p : PolyList κ} (hu : u ∈ mapCoeffs f p) :
    ∃ v ∈ p, u.1 = v.1 := by
  induction p with
  | nil => contradiction
  | cons v vs ih =>
      rw [mapCoeffs] at hu
      split at hu
      · rcases ih hu with ⟨w, hw, he⟩
        exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
      · rcases List.mem_cons.mp hu with h | hu
        · have he := congrArg (fun z : Term κ => z.1) h
          exact ⟨v, List.mem_cons_self .., by simpa using he⟩
        · rcases ih hu with ⟨w, hw, he⟩
          exact ⟨w, List.mem_cons_of_mem _ hw, he⟩

/-- Mapping and filtering coefficients preserves canonical form. -/
theorem mapCoeffs_canonical [Zero κ] [DecidableEq κ] (f : κ → κ)
    {n : Nat} {p : PolyList κ} (hp : Canonical n p) :
    Canonical n (mapCoeffs f p) := by
  induction p with
  | nil => exact ⟨fun _ h => by contradiction, List.Pairwise.nil,
      fun _ h => by contradiction⟩
  | cons t ts ih =>
      have htail : Canonical n ts :=
        ⟨fun u hu => hp.1 u (List.mem_cons_of_mem _ hu),
          (List.pairwise_cons.mp hp.2.1).2,
          fun u hu => hp.2.2 u (List.mem_cons_of_mem _ hu)⟩
      have hi := ih htail
      rw [mapCoeffs]
      split
      · exact hi
      · refine ⟨?_, ?_, ?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hp.1 t (List.mem_cons_self ..)
          · exact hi.1 u hu
        · rw [List.pairwise_cons]
          refine ⟨?_, hi.2.1⟩
          intro u hu
          have hu' := exp_mem_mapCoeffs f hu
          rcases hu' with ⟨v, hv, he⟩
          simpa [he] using (List.pairwise_cons.mp hp.2.1).1 v hv
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · assumption
          · exact hi.2.2 u hu

/-- Negation preserves canonical form. -/
theorem neg_canonical [Zero κ] [Neg κ] [DecidableEq κ]
    {n : Nat} {p : PolyList κ} (hp : Canonical n p) :
    Canonical n (neg p) := by
  exact mapCoeffs_canonical Neg.neg hp

/-- Subtraction preserves canonical form. -/
theorem sub_canonical [Zero κ] [Add κ] [Neg κ] [DecidableEq κ]
    {n : Nat} {p q : PolyList κ} (hp : Canonical n p) (hq : Canonical n q) :
    Canonical n (sub p q) := add_canonical hp (neg_canonical hq)

/-- Scalar multiplication preserves canonical form. -/
theorem smul_canonical [Zero κ] [Mul κ] [DecidableEq κ]
    (a : κ) {n : Nat} {p : PolyList κ} (hp : Canonical n p) :
    Canonical n (smul a p) := by
  exact mapCoeffs_canonical (fun c => a * c) hp

/-- A translated product row is canonical. -/
theorem mulTerm_canonical [Zero κ] [Add κ] [Mul κ] [DecidableEq κ]
    {n : Nat} {t : Term κ} {p : PolyList κ}
    (ht : t.1.length = n) (hp : Canonical n p) :
    Canonical n (mulTerm t p) := by
  induction p with
  | nil => exact ⟨fun _ h => by contradiction, List.Pairwise.nil,
      fun _ h => by contradiction⟩
  | cons u us ih =>
      rw [mulTerm]
      apply insert_canonical
      · exact length_addExp ht (hp.1 u (List.mem_cons_self ..))
      · exact ih ⟨fun v hv => hp.1 v (List.mem_cons_of_mem _ hv),
          (List.pairwise_cons.mp hp.2.1).2,
          fun v hv => hp.2.2 v (List.mem_cons_of_mem _ hv)⟩

private theorem sumRows_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} {ps : List (PolyList κ)} (h : ∀ p ∈ ps, Canonical n p) :
    Canonical n (sumRows ps) := by
  induction ps with
  | nil => simp [sumRows, Canonical]
  | cons p ps ih =>
      exact add_canonical (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

private theorem mergeRound_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} (ps : List (PolyList κ)) (h : ∀ p ∈ ps, Canonical n p) :
    ∀ p ∈ mergeRound ps, Canonical n p := by
  induction ps using mergeRound.induct with
  | case1 => simp [mergeRound]
  | case2 p => simpa [mergeRound] using h
  | case3 p q ps ih =>
      simp only [mergeRound, List.mem_cons, forall_eq_or_imp]
      exact ⟨add_canonical (h p (by simp)) (h q (by simp)),
        ih (fun r hr => h r (by simp [hr]))⟩

/-- Balanced merging preserves canonical form. -/
theorem mergeRows_canonical [Zero κ] [Add κ] [DecidableEq κ]
    {n : Nat} (fuel : Nat) (ps : List (PolyList κ))
    (h : ∀ p ∈ ps, Canonical n p) : Canonical n (mergeRows fuel ps) := by
  induction fuel generalizing ps with
  | zero =>
      cases ps with
      | nil => simp [mergeRows, Canonical]
      | cons p ps =>
        cases ps with
        | nil => exact h p (by simp)
        | cons q ps => exact sumRows_canonical h
  | succ fuel ih =>
      cases ps with
      | nil => simp [mergeRows, Canonical]
      | cons p ps =>
        cases ps with
        | nil => exact h p (by simp)
        | cons q ps => exact ih _ (mergeRound_canonical _ h)

/-- Multiplication preserves canonical form. -/
theorem mul_canonical [Zero κ] [Add κ] [Mul κ] [DecidableEq κ]
    {n : Nat} {p q : PolyList κ}
    (hp : Canonical n p) (hq : Canonical n q) : Canonical n (mul p q) := by
  apply mergeRows_canonical
  intro r hr
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
  exact mulTerm_canonical (hp.1 t ht) hq

/-- Boolean check for the canonical invariant. -/
def isCanonical [Zero κ] [DecidableEq κ] (n : Nat) :
    PolyList κ → Bool
  | [] => true
  | [t] => Nat.beq t.1.length n && decide (t.2 ≠ 0)
  | t :: u :: ts =>
      Nat.beq t.1.length n && decide (t.2 ≠ 0) &&
        (expCmp t.1 u.1 == .gt) && isCanonical n (u :: ts)

/-- The Boolean canonicality check decides the proposition. -/
theorem isCanonical_iff [Zero κ] [DecidableEq κ]
    {n : Nat} {p : PolyList κ} :
    isCanonical n p = true ↔ Canonical n p := by
  induction p with
  | nil => simp [isCanonical, Canonical]
  | cons t ts ih =>
      cases ts with
      | nil => simp [isCanonical, Canonical]
      | cons u us =>
          simp only [isCanonical, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq, Nat.beq_eq, ih]
          rw [expCmp_eq_compare]
          constructor
          · rintro ⟨⟨⟨htlen, htnz⟩, hcmp⟩, htail⟩
            have hut : u.1 < t.1 := by
              have hrev : compare u.1 t.1 = .lt :=
                Std.OrientedCmp.gt_iff_lt.mp hcmp
              rw [← expCmp_eq_compare] at hrev
              exact expCmp_eq_lt_iff.mp hrev
            refine ⟨?_, ?_, ?_⟩
            · intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact htlen
              · exact htail.1 v hv
            · rw [List.pairwise_cons]
              refine ⟨?_, htail.2.1⟩
              intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact hut
              · exact List.lt_trans ((List.pairwise_cons.mp htail.2.1).1 v hv) hut
            · intro v hv
              rcases List.mem_cons.mp hv with rfl | hv
              · exact htnz
              · exact htail.2.2 v hv
          · rintro ⟨hlen, hpair, hnz⟩
            have hut := (List.pairwise_cons.mp hpair).1 u (List.mem_cons_self ..)
            have hcmp : compare t.1 u.1 = .gt := by
              apply Std.OrientedCmp.gt_iff_lt.mpr
              rw [← expCmp_eq_compare]
              exact expCmp_eq_lt_iff.mpr hut
            refine ⟨⟨⟨hlen t (List.mem_cons_self ..),
              hnz t (List.mem_cons_self ..)⟩, hcmp⟩, ?_⟩
            exact ⟨fun v hv => hlen v (List.mem_cons_of_mem _ hv),
              (List.pairwise_cons.mp hpair).2,
              fun v hv => hnz v (List.mem_cons_of_mem _ hv)⟩

/-! # Denotation and conversion -/

/-- Read an exponent list as an `n`-variable monomial. Canonical inputs have
exactly length `n`; `getD` merely makes denotation total on malformed input. -/
def mono (n : Nat) (e : List Nat) : Mono n :=
  Hex.Vector.ofFn' fun i => e.getD i 0

/-- Denote a term list in the reference polynomial type. -/
def denote {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ] [BEq κ]
    [LawfulBEq κ] {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    PolyList κ → MvPoly n κ cmp
  | [] => 0
  | t :: ts => MvPoly.monomial (mono n t.1) t.2 + denote ts

/-- Convert a reference polynomial to the fixed canonical list order. This is
a producer-side conversion; certificate replay sees only its quoted result. -/
def toList {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ] [BEq κ]
    [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n κ cmp) : PolyList κ :=
  let ts := p.termsList.map fun t => (t.1.toList, t.2)
  let reversed := ts.reverse
  if isCanonical n reversed then reversed else normalize ts

/-! # Denotation laws -/

/-- A zero coefficient denotes the zero reference polynomial. -/
private theorem monomial_zero {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (m : Mono n) :
    (MvPoly.monomial m 0 : MvPoly n κ cmp) = 0 := by
  apply MvPoly.ext
  intro k
  by_cases h : k = m <;>
    simp [MvPoly.coeff_monomial, MvPoly.coeff_zero, h]

/-- Adding coefficients of one monomial agrees with reference addition. -/
private theorem monomial_add {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (m : Mono n) (a b : κ) :
    (MvPoly.monomial m (a + b) : MvPoly n κ cmp) =
      MvPoly.monomial m a + MvPoly.monomial m b := by
  apply MvPoly.ext
  intro k
  by_cases h : k = m <;>
    simp [MvPoly.coeff_monomial, MvPoly.coeff_add, h,
      Lean.Grind.AddCommMonoid.zero_add]

/-- Inserting a term has the denotation of adding its monomial. -/
theorem denote_insert {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (t : Term κ) (p : PolyList κ) :
    denote (cmp := cmp) (insert t p) =
      MvPoly.monomial (mono n t.1) t.2 + denote (cmp := cmp) p := by
  induction p with
  | nil =>
      by_cases hz : t.2 = 0
      · simp [insert, hz, denote, monomial_zero, MvPoly.zero_add]
      · simp [insert, hz, denote, MvPoly.add_zero]
  | cons u us ih =>
      cases hc : expCmp t.1 u.1 with
      | gt =>
          by_cases hz : t.2 = 0
          · simp [insert, hc, hz, denote, monomial_zero, MvPoly.zero_add]
          · simp [insert, hc, hz, denote]
      | eq =>
          have he : t.1 = u.1 := by
            rw [expCmp_eq_compare] at hc
            exact Std.LawfulEqCmp.eq_of_compare hc
          have hm : mono n t.1 = mono n u.1 := congrArg (mono n) he
          by_cases hz : t.2 + u.2 = 0
          · simp only [insert, hc]
            rw [ite_eq_left hz]
            simp only [denote]
            rw [← MvPoly.add_assoc,
              hm, ← monomial_add, hz, monomial_zero, MvPoly.zero_add]
          · simp only [insert, hc]
            rw [ite_eq_right hz]
            simp only [denote]
            rw [← MvPoly.add_assoc,
              hm, ← monomial_add]
      | lt =>
          rw [insert, hc, denote, ih, denote, ← MvPoly.add_assoc,
            MvPoly.add_comm (MvPoly.monomial (mono n u.1) u.2)
              (MvPoly.monomial (mono n t.1) t.2),
            MvPoly.add_assoc]

/-- Normalization does not change denotation. -/
theorem denote_normalize {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (p : PolyList κ) :
    denote (cmp := cmp) (normalize p) = denote (cmp := cmp) p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
      rw [normalize, denote_insert, ih]
      rfl

/-- List addition denotes reference addition. -/
theorem denote_insertSum {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (p q : PolyList κ) :
    denote (cmp := cmp) (insertSum p q) =
      denote (cmp := cmp) p + denote (cmp := cmp) q := by
  induction p with
  | nil => exact (MvPoly.zero_add (denote q)).symm
  | cons t ts ih =>
      rw [insertSum, denote_insert, ih, denote]
      exact (MvPoly.add_assoc _ _ _).symm

/-- A merge has the denotation of the sum, for any fuel and any input. -/
theorem denote_merge {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (fuel : Nat) (p q : PolyList κ) :
    denote (cmp := cmp) (merge fuel p q) =
      denote (cmp := cmp) p + denote (cmp := cmp) q := by
  induction fuel generalizing p q with
  | zero =>
      cases p <;> cases q
      · exact (MvPoly.zero_add _).symm
      · exact (MvPoly.zero_add _).symm
      · exact (MvPoly.add_zero _).symm
      · exact denote_insertSum _ _
  | succ fuel ih =>
      cases p with
      | nil => exact (MvPoly.zero_add _).symm
      | cons t ts =>
        cases q with
        | nil => exact (MvPoly.add_zero _).symm
        | cons u us =>
          simp only [merge]
          split
          · simp only [denote, ih, MvPoly.add_assoc]
          · simp only [denote, ih]
            grind only [MvPoly.add_comm, MvPoly.add_assoc]
          next hc =>
            have he : t.1 = u.1 := by simpa [expCmp_eq_compare] using hc
            split
            next hz =>
              simp only [ih, denote]
              have hm := monomial_add (cmp := cmp) (mono n t.1) t.2 u.2
              rw [hz, monomial_zero] at hm
              simp only [← he]
              grind only [MvPoly.add_comm, MvPoly.add_assoc, MvPoly.zero_add]
            · simp only [denote, ih, monomial_add]
              simp only [← he]
              grind only [MvPoly.add_comm, MvPoly.add_assoc]

/-- List addition denotes reference addition. -/
theorem denote_add {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (p q : PolyList κ) :
    denote (cmp := cmp) (add p q) =
      denote (cmp := cmp) p + denote (cmp := cmp) q :=
  denote_merge _ p q

/-- List negation denotes reference negation. -/
theorem denote_neg {n : Nat} {κ : Type u} [Lean.Grind.CommRing κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (p : PolyList κ) :
    denote (cmp := cmp) (neg p) = -denote (cmp := cmp) p := by
  unfold neg
  induction p with
  | nil =>
      simp only [mapCoeffs, denote]
      exact MvPoly.neg_zero
  | cons t ts ih =>
      rw [mapCoeffs]
      split <;> apply MvPoly.ext <;> intro m
      all_goals have ihc := congrArg (MvPoly.coeff m) ih
      all_goals simp only [denote, MvPoly.coeff_add, MvPoly.coeff_monomial,
        MvPoly.coeff_neg] at ihc ⊢
      all_goals by_cases hm : m = mono n t.1 <;>
        simp [hm, Lean.Grind.AddCommMonoid.zero_add] at * <;>
        grind

/-- List subtraction denotes reference subtraction. -/
theorem denote_sub {n : Nat} {κ : Type u} [Lean.Grind.CommRing κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (p q : PolyList κ) :
    denote (cmp := cmp) (sub p q) = denote (cmp := cmp) p - denote (cmp := cmp) q := by
  rw [sub, denote_add, denote_neg, MvPoly.sub_eq_add_neg]

/-- List scalar multiplication denotes multiplication by a constant. -/
theorem denote_smul {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (a : κ) (p : PolyList κ) :
    denote (cmp := cmp) (smul a p) =
      MvPoly.C a * denote (cmp := cmp) p := by
  unfold smul
  induction p with
  | nil =>
      simp only [mapCoeffs, denote]
      exact (MvPoly.mul_zero (MvPoly.C a)).symm
  | cons t ts ih =>
      rw [mapCoeffs]
      split
      next hz =>
        apply MvPoly.ext
        intro m
        have ihc := congrArg (MvPoly.coeff m) ih
        simp only [denote, MvPoly.coeff_add, MvPoly.coeff_monomial,
          MvPoly.coeff_C_mul] at ihc ⊢
        by_cases hm : m = mono n t.1
        · simp [hm, Lean.Grind.Semiring.left_distrib, hz,
            Lean.Grind.AddCommMonoid.zero_add]
          simpa [hm] using ihc
        · simp [hm, Lean.Grind.AddCommMonoid.zero_add, ihc]
      next hnz =>
        apply MvPoly.ext
        intro m
        have ihc := congrArg (MvPoly.coeff m) ih
        simp only [denote, MvPoly.coeff_add, MvPoly.coeff_monomial,
          MvPoly.coeff_C_mul] at ihc ⊢
        by_cases hm : m = mono n t.1
        · simp [hm, Lean.Grind.Semiring.left_distrib]
          congr 1
          simpa [hm] using ihc
        · simp [hm, Lean.Grind.AddCommMonoid.zero_add, ihc]

/-- Reading a list exponent through its denotation uses `getD`. -/
theorem get_mono (n : Nat) (e : List Nat) (i : Fin n) :
    (mono n e)[i] = e.getD i.val 0 := by
  change (Hex.Vector.ofFn' fun j : Fin n => e.getD j.val 0)[i.val] = _
  rw [Hex.Vector.getElem_ofFn' _ i.val i.isLt]

/-- The zero exponent denotes the reference constant monomial. -/
theorem mono_zeroExp (n : Nat) : mono n (zeroExp n) = Mono.zero := by
  have hzero (n i : Nat) : (zeroExp n).getD i 0 = 0 := by
    induction n generalizing i with
    | zero => simp [zeroExp]
    | succ n ih =>
        cases i with
        | zero => rfl
        | succ i => exact ih i
  apply Vector.ext
  intro i hi
  change (mono n (zeroExp n))[(⟨i, hi⟩ : Fin n)] = _
  rw [get_mono, hzero]
  simp [Mono.zero]

/-- The list multiplicative identity denotes the reference identity. -/
theorem denote_one {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    denote (cmp := cmp) (one (κ := κ) n) = 1 := by
  unfold one
  split <;> apply MvPoly.ext <;> intro m
  all_goals simp_all [denote, MvPoly.coeff_add, MvPoly.coeff_monomial,
    MvPoly.coeff_one, mono_zeroExp, Lean.Grind.AddCommMonoid.add_zero]

/-- A pointwise sum has the pointwise sum of `getD` values when both lists
have the declared arity. -/
theorem getD_addExp {a b : List Nat} {n i : Nat}
    (ha : a.length = n) (hb : b.length = n) (hi : i < n) :
    (addExp a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  induction a generalizing b n i with
  | nil => simp_all; omega
  | cons x xs ih =>
      cases b with
      | nil => simp_all; omega
      | cons y ys =>
          cases i with
          | zero => simp [addExp]
          | succ i =>
              simp only [List.length_cons] at ha hb
              simp only [addExp, List.getD_cons_succ]
              exact ih (n := xs.length) (i := i) rfl (by omega) (by omega)

/-- List exponent addition denotes monomial multiplication. -/
theorem mono_addExp {a b : List Nat} {n : Nat}
    (ha : a.length = n) (hb : b.length = n) :
    mono n (addExp a b) = Mono.mul (mono n a) (mono n b) := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  change (mono n (addExp a b))[j] = (Mono.mul (mono n a) (mono n b))[j]
  rw [get_mono, Mono.getElem_mul, get_mono, get_mono,
    getD_addExp ha hb j.isLt]

/-- Multiplying one term through a list denotes multiplication by its
reference monomial. -/
theorem denote_mulTerm {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (t : Term κ) (p : PolyList κ)
    (ht : t.1.length = n) (hp : ∀ u ∈ p, u.1.length = n) :
    denote (cmp := cmp) (mulTerm t p) =
      MvPoly.monomial (mono n t.1) t.2 * denote (cmp := cmp) p := by
  induction p with
  | nil =>
      simp only [mulTerm, denote]
      exact (MvPoly.mul_zero _).symm
  | cons u us ih =>
      rw [mulTerm, denote_insert, ih
        (fun v hv => hp v (List.mem_cons_of_mem _ hv)), denote,
        MvPoly.mul_add, MvPoly.monomial_mul_monomial,
        mono_addExp ht (hp u (List.mem_cons_self ..))]

private theorem denote_mergeRound {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (ps : List (PolyList κ)) :
    denote (cmp := cmp) (sumRows (mergeRound ps)) = denote (cmp := cmp) (sumRows ps) := by
  induction ps using mergeRound.induct with
  | case1 => rfl
  | case2 p => rfl
  | case3 p q ps ih =>
      simp only [mergeRound, sumRows, denote_add] at ih ⊢
      rw [ih, MvPoly.add_assoc]

/-- Balanced merging denotes the sum of its rows, independently of fuel. -/
theorem denote_mergeRows {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (fuel : Nat) (ps : List (PolyList κ)) :
    denote (cmp := cmp) (mergeRows fuel ps) = denote (cmp := cmp) (sumRows ps) := by
  induction fuel generalizing ps with
  | zero =>
      cases ps with
      | nil => rfl
      | cons p ps =>
        cases ps with
        | nil => simp [mergeRows, sumRows, denote_add, denote, MvPoly.add_zero]
        | cons q ps => rfl
  | succ fuel ih =>
      cases ps with
      | nil => rfl
      | cons p ps =>
        cases ps with
        | nil => simp [mergeRows, sumRows, denote_add, denote, MvPoly.add_zero]
        | cons q ps =>
            change denote (mergeRows fuel (mergeRound (p :: q :: ps))) = _
            rw [ih, denote_mergeRound]

/-- List multiplication denotes reference multiplication. -/
theorem denote_mul {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p q : PolyList κ)
    (hp : ∀ t ∈ p, t.1.length = n) (hq : ∀ t ∈ q, t.1.length = n) :
    denote (cmp := cmp) (mul p q) =
      denote (cmp := cmp) p * denote (cmp := cmp) q := by
  unfold mul
  rw [denote_mergeRows]
  induction p with
  | nil =>
      simp only [List.map_nil, sumRows, denote]
      exact (MvPoly.zero_mul _).symm
  | cons t ts ih =>
      rw [List.map_cons, sumRows, denote_add, denote_mulTerm t q
        (hp t (List.mem_cons_self ..)) hq,
        ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)), denote,
        MvPoly.add_mul]

/-- The recursive sum denotation agrees with the reference bulk
constructor. -/
theorem denote_eq_ofTerms {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : PolyList κ) :
    denote (cmp := cmp) p =
      MvPoly.ofTerms (p.map fun t => (mono n t.1, t.2)) := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
      rw [denote, ih]
      apply MvPoly.ext
      intro m
      rw [MvPoly.coeff_add, MvPoly.coeff_monomial,
        MvPoly.coeff_ofTerms, MvPoly.coeff_ofTerms]
      by_cases ht : mono n t.1 = m
      · have hmt : m = mono n t.1 := ht.symm
        simp only [List.map_cons, List.filter_cons, ht, decide_true]
        simp only [hmt, ite_eq_left]
        rw [List.foldl_cons]
        rw [Lean.Grind.AddCommMonoid.zero_add]
        exact (List.foldl_add_eq_add_foldl (R := κ) _
          (fun x : Mono n × κ => x.2) t.2).symm
      · have hmt : m ≠ mono n t.1 := fun h => ht h.symm
        simp [ht, hmt, Lean.Grind.AddCommMonoid.zero_add]

/-- Converting a vector monomial to a list and reading it back is exact. -/
theorem mono_toList {n : Nat} (m : Mono n) : mono n m.toList = m := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i, hi⟩
  change (mono n m.toList)[j] = m[j]
  rw [get_mono, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp), Option.getD_some]
  exact Vector.getElem_toList (xs := m) (i := i) (by simpa using hi)

/-- Producer conversion always emits a canonical list. -/
theorem toList_canonical {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : MvPoly n κ cmp) : Canonical n (toList p) := by
  simp only [toList]
  split
  next h => exact isCanonical_iff.mp h
  next h =>
    apply normalize_canonical
    intro t ht
    rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
    simp

private theorem denote_append {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p q : PolyList κ) :
    denote (cmp := cmp) (p ++ q) = denote (cmp := cmp) p + denote (cmp := cmp) q := by
  induction p with
  | nil => simp [denote, MvPoly.zero_add]
  | cons t ts ih => simp [denote, ih, MvPoly.add_assoc]

private theorem denote_reverse {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : PolyList κ) :
    denote (cmp := cmp) p.reverse = denote (cmp := cmp) p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
      simp [List.reverse_cons, denote_append, ih, denote, MvPoly.zero_add, MvPoly.add_comm]

/-- Producer conversion round-trips through denotation. -/
theorem denote_toList {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : MvPoly n κ cmp) :
    denote (cmp := cmp) (toList p) = p := by
  have hden : denote (cmp := cmp) (toList p) =
      denote (p.termsList.map fun t => (t.1.toList, t.2)) := by
    simp only [toList]
    split
    · exact denote_reverse _
    · exact denote_normalize _
  rw [hden, denote_eq_ofTerms]
  have hmap :
      (p.termsList.map fun t => (mono n t.1.toList, t.2)) = p.termsList := by
    simp [mono_toList]
  rw [List.map_map]
  change MvPoly.ofTerms
    (p.termsList.map fun t => (mono n t.1.toList, t.2)) = p
  rw [hmap]
  apply MvPoly.ext
  intro m
  rw [MvPoly.coeff_ofTerms, MvPoly.coeff_terms]

/-- Producer conversion for nested polynomial lists. A matrix consumer
passes `rowLists P`; no matrix dependency is needed in this library. -/
def toRows {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (rows : List (List (MvPoly n κ cmp))) :
    List (List (PolyList κ)) := rows.map (List.map toList)

/-- Entrywise denotation identifies quoted rows with the original rows.
In particular, instantiate `rows` with `rowLists P` for a reference matrix. -/
theorem denote_toRows {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (rows : List (List (MvPoly n κ cmp))) :
    (toRows rows).map (List.map (denote (cmp := cmp))) = rows := by
  simp [toRows, List.map_map, Function.comp_def, denote_toList]

/-! # Evaluation -/

/-- The linear structural power used by certificate replay has the standard
semiring value. -/
theorem pow_eq_pow [Lean.Grind.Semiring κ] (a : κ) (k : Nat) :
    pow a k = a ^ k := by
  induction k with
  | zero => rw [pow, Lean.Grind.Semiring.pow_zero]
  | succ k ih => rw [pow, ih, Lean.Grind.Semiring.pow_succ]

/-- List monomial evaluation agrees with reference monomial evaluation when
the point and exponent list have the declared arity. -/
theorem evalMono_eq_prod [Lean.Grind.Semiring κ] {n : Nat}
    {x : List κ} {e : List Nat} (hx : x.length = n) (he : e.length = n) :
    evalMono x e = Mono.prod (fun i => x.getD i.val 0) (mono n e) := by
  letI : Std.Associative (· * · : κ → κ → κ) :=
    ⟨Lean.Grind.Semiring.mul_assoc⟩
  letI : Std.LawfulIdentity (· * · : κ → κ → κ) 1 :=
    { left_id := Lean.Grind.Semiring.one_mul
      right_id := Lean.Grind.Semiring.mul_one }
  induction n generalizing x e with
  | zero =>
      have hxnil : x = [] := List.eq_nil_of_length_eq_zero hx
      have henil : e = [] := List.eq_nil_of_length_eq_zero he
      subst x
      subst e
      rfl
  | succ n ih =>
      cases x with
      | nil => simp at hx
      | cons a xs =>
          cases e with
          | nil => simp at he
          | cons k es =>
              have hx' : xs.length = n := by
                simp only [List.length_cons] at hx
                omega
              have he' : es.length = n := by
                simp only [List.length_cons] at he
                omega
              rw [evalMono, Mono.prod, List.finRange_succ, List.foldl_cons,
                List.foldl_map]
              rw [List.foldl_mul_eq_mul_foldl]
              simp only [get_mono,
                Mono.powBySq_eq_pow, pow_eq_pow, Lean.Grind.Semiring.one_mul]
              rw [ih hx' he']
              unfold Mono.prod
              apply congrArg (fun z => a ^ k * z)
              apply List.foldl_mul_congr
              intro i _
              rw [Mono.powBySq_eq_pow, get_mono]
              change xs.getD i.val 0 ^ es.getD i.val 0 =
                (a :: xs).getD (i.val + 1) 0 ^ (k :: es).getD (i.val + 1) 0
              rw [List.getD_cons_succ, List.getD_cons_succ]

/-- List evaluation commutes with evaluation of the reference denotation. -/
theorem evalAt_denote {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (x : List κ) (p : PolyList κ)
    (hx : x.length = n) (hp : ∀ t ∈ p, t.1.length = n) :
    evalAt x p = MvPoly.eval (fun i => x.getD i.val 0) (denote (cmp := cmp) p) := by
  rw [denote_eq_ofTerms]
  unfold MvPoly.eval
  rw [MvPoly.eval₂_ofTerms (f := id) (x := fun i => x.getD i.val 0)
    (by rfl) (by intros; rfl)]
  induction p with
  | nil => rfl
  | cons t ts ih =>
      simp only [evalAt, List.map_cons, List.foldl_cons, id_eq]
      rw [Lean.Grind.AddCommMonoid.zero_add, List.foldl_add_eq_add_foldl,
        evalMono_eq_prod hx (hp t (List.mem_cons_self ..)),
        ih (fun u hu => hp u (List.mem_cons_of_mem _ hu))]
      simp only [id_eq]

/-! # Canonical uniqueness -/

/-- An exact-length exponent list is recovered from its monomial. -/
theorem toList_mono {e : List Nat} {n : Nat} (h : e.length = n) :
    (mono n e).toList = e := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    change (mono n e)[i] = e[i]
    let k : Fin n := ⟨i, by simpa [h] using hi⟩
    change (mono n e)[k] = e[i]
    rw [get_mono, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]

/-- Denotation of exponent lists is injective at a fixed arity. -/
theorem mono_inj {a b : List Nat} {n : Nat}
    (ha : a.length = n) (hb : b.length = n) :
    mono n a = mono n b ↔ a = b := by
  constructor
  · intro h
    rw [← toList_mono ha, ← toList_mono hb, h]
  · exact fun h => congrArg (mono n) h

/-- Coefficient lookup on a canonical list. -/
def coeffAt [Zero κ] (e : List Nat) : PolyList κ → κ
  | [] => 0
  | t :: ts => if e = t.1 then t.2 else coeffAt e ts

/-- A monomial absent from a well-formed list has zero coefficient in its
denotation. -/
theorem coeff_denote_eq_zero {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (e : List Nat) (p : PolyList κ)
    (he : e.length = n) (hp : ∀ t ∈ p, t.1.length = n)
    (hnot : ∀ t ∈ p, e ≠ t.1) :
    MvPoly.coeff (mono n e) (denote (cmp := cmp) p) = 0 := by
  induction p with
  | nil => exact MvPoly.coeff_zero _
  | cons t ts ih =>
      rw [denote, MvPoly.coeff_add, MvPoly.coeff_monomial,
        ih (fun u hu => hp u (List.mem_cons_of_mem _ hu))
          (fun u hu => hnot u (List.mem_cons_of_mem _ hu))]
      have hne : mono n e ≠ mono n t.1 := by
        intro h
        exact hnot t (List.mem_cons_self ..)
          ((mono_inj he (hp t (List.mem_cons_self ..))).mp h)
      rw [ite_eq_right hne, Lean.Grind.AddCommMonoid.zero_add]

/-- Reference coefficients read back the stored coefficient of a canonical
list. -/
theorem coeff_denote {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (e : List Nat) (p : PolyList κ)
    (he : e.length = n) (hp : Canonical n p) :
    MvPoly.coeff (mono n e) (denote (cmp := cmp) p) = coeffAt e p := by
  induction p with
  | nil => rw [denote, coeffAt, MvPoly.coeff_zero]
  | cons t ts ih =>
      have htlen := hp.1 t (List.mem_cons_self ..)
      have htail : Canonical n ts :=
        ⟨fun u hu => hp.1 u (List.mem_cons_of_mem _ hu),
          (List.pairwise_cons.mp hp.2.1).2,
          fun u hu => hp.2.2 u (List.mem_cons_of_mem _ hu)⟩
      by_cases het : e = t.1
      · have hzero : MvPoly.coeff (mono n e) (denote (cmp := cmp) ts) = 0 := by
          apply coeff_denote_eq_zero e ts he htail.1
          intro u hu heu
          have hut := (List.pairwise_cons.mp hp.2.1).1 u hu
          rw [← het, ← heu] at hut
          exact List.lt_irrefl e hut
        rw [denote, MvPoly.coeff_add, MvPoly.coeff_monomial,
          ite_eq_left ((mono_inj he htlen).mpr het), hzero, coeffAt,
          ite_eq_left het, Lean.Grind.Semiring.add_zero]
      · have hm : mono n e ≠ mono n t.1 := fun h =>
          het ((mono_inj he htlen).mp h)
        rw [denote, MvPoly.coeff_add, MvPoly.coeff_monomial, ite_eq_right hm,
          Lean.Grind.AddCommMonoid.zero_add, coeffAt, ite_eq_right het, ih htail]

/-- Lookup is zero above the head of a descending canonical list. -/
theorem coeffAt_eq_zero_of_gt_head [Zero κ] {e : List Nat}
    {t : Term κ} {ts : PolyList κ}
    (hp : (t :: ts).Pairwise (fun a b => b.1 < a.1)) (he : t.1 < e) :
    coeffAt e (t :: ts) = 0 := by
  have het : e ≠ t.1 := by
    intro h
    rw [h] at he
    exact List.lt_irrefl t.1 he
  rw [coeffAt, ite_eq_right het]
  induction ts with
  | nil => rfl
  | cons u us ih =>
      rw [coeffAt]
      have hut := (List.pairwise_cons.mp hp).1 u (List.mem_cons_self ..)
      have heu : e ≠ u.1 := by
        intro h
        have hue : u.1 < e := List.lt_trans hut he
        rw [h] at hue
        exact List.lt_irrefl u.1 hue
      rw [ite_eq_right heu]
      exact ih (List.pairwise_cons.mpr ⟨fun v hv =>
        (List.pairwise_cons.mp hp).1 v (List.mem_cons_of_mem _ hv),
        (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).2⟩)

/-- The tail has zero coefficient at the head exponent. -/
theorem coeffAt_tail_eq_zero [Zero κ] {t : Term κ} {ts : PolyList κ}
    (hp : (t :: ts).Pairwise (fun a b => b.1 < a.1)) :
    coeffAt t.1 ts = 0 := by
  induction ts with
  | nil => rfl
  | cons u us ih =>
      rw [coeffAt]
      have hut := (List.pairwise_cons.mp hp).1 u (List.mem_cons_self ..)
      have htu : t.1 ≠ u.1 := by
        intro h
        rw [← h] at hut
        exact List.lt_irrefl t.1 hut
      rw [ite_eq_right htu]
      exact ih (List.pairwise_cons.mpr ⟨fun v hv =>
        (List.pairwise_cons.mp hp).1 v (List.mem_cons_of_mem _ hv),
        (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).2⟩)

/-- Canonical lists with the same coefficient function are equal. -/
theorem coeffAt_ext [Zero κ] {p q : PolyList κ}
    (hp : p.Pairwise (fun a b => b.1 < a.1))
    (hq : q.Pairwise (fun a b => b.1 < a.1))
    (hp0 : ∀ t ∈ p, t.2 ≠ 0) (hq0 : ∀ t ∈ q, t.2 ≠ 0)
    (h : ∀ e, coeffAt e p = coeffAt e q) : p = q := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | cons u us =>
          have hu := h u.1
          simp only [coeffAt] at hu
          exact absurd hu.symm (hq0 u (List.mem_cons_self ..))
  | cons t ts ih =>
      cases q with
      | nil =>
          have ht := h t.1
          simp only [coeffAt] at ht
          exact absurd ht (hp0 t (List.mem_cons_self ..))
      | cons u us =>
          have hexp : t.1 = u.1 := by
            cases hc : expCmp t.1 u.1 with
            | eq =>
                rw [expCmp_eq_compare] at hc
                exact Std.LawfulEqCmp.eq_of_compare hc
            | lt =>
                have htu := expCmp_eq_lt_iff.mp hc
                have hu := h u.1
                rw [coeffAt_eq_zero_of_gt_head hp htu] at hu
                rw [coeffAt, ite_eq_left rfl] at hu
                exact absurd hu.symm (hq0 u (List.mem_cons_self ..))
            | gt =>
                have hut : u.1 < t.1 := by
                  have hc' : expCmp u.1 t.1 = .lt := by
                    rw [expCmp_eq_compare]
                    apply Std.OrientedCmp.gt_iff_lt.mp
                    simpa [expCmp_eq_compare] using hc
                  exact expCmp_eq_lt_iff.mp hc'
                have ht := h t.1
                rw [coeffAt, ite_eq_left rfl] at ht
                rw [coeffAt_eq_zero_of_gt_head hq hut] at ht
                exact absurd ht (hp0 t (List.mem_cons_self ..))
          have hcoeff : t.2 = u.2 := by
            have ht := h t.1
            rw [coeffAt, ite_eq_left rfl, coeffAt, ite_eq_left hexp] at ht
            exact ht
          have htail : ts = us := by
            apply ih (List.pairwise_cons.mp hp).2 (List.pairwise_cons.mp hq).2
              (fun v hv => hp0 v (List.mem_cons_of_mem _ hv))
              (fun v hv => hq0 v (List.mem_cons_of_mem _ hv))
            intro e
            by_cases het : e = t.1
            · subst e
              rw [coeffAt_tail_eq_zero hp, hexp, coeffAt_tail_eq_zero hq]
            · have heu : e ≠ u.1 := fun he => het (he.trans hexp.symm)
              have he := h e
              simp only [coeffAt, ite_eq_right het, ite_eq_right heu] at he
              exact he
          rw [Prod.ext hexp hcoeff, htail]

/-- A lookup with the wrong arity is zero in a well-formed list. -/
theorem coeffAt_eq_zero_of_length_ne [Zero κ] {e : List Nat}
    {n : Nat} {p : PolyList κ} (hp : ∀ t ∈ p, t.1.length = n)
    (he : e.length ≠ n) : coeffAt e p = 0 := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
      have het : e ≠ t.1 := by
        intro h
        apply he
        rw [h]
        exact hp t (List.mem_cons_self ..)
      rw [coeffAt, ite_eq_right het]
      exact ih (fun u hu => hp u (List.mem_cons_of_mem _ hu))

/-- Canonical list denotation is injective. -/
theorem denote_injective {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {p q : PolyList κ}
    (hp : Canonical n p) (hq : Canonical n q)
    (h : denote (cmp := cmp) p = denote (cmp := cmp) q) : p = q := by
  apply coeffAt_ext hp.2.1 hq.2.1 hp.2.2 hq.2.2
  intro e
  by_cases he : e.length = n
  · rw [← coeff_denote (cmp := cmp) e p he hp,
      ← coeff_denote (cmp := cmp) e q he hq, h]
  · rw [coeffAt_eq_zero_of_length_ne hp.1 he,
      coeffAt_eq_zero_of_length_ne hq.1 he]

/-- A canonical list is recovered by converting its denotation back to list
form. -/
theorem toList_denote {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {p : PolyList κ} (hp : Canonical n p) :
    toList (denote (cmp := cmp) p) = p := by
  apply denote_injective (cmp := cmp)
    (toList_canonical (cmp := cmp) (denote (cmp := cmp) p)) hp
  exact denote_toList (cmp := cmp) (denote (cmp := cmp) p)

/-! # Decidable certificate checks -/

/-- Structural equality returns true exactly for equal term lists. -/
theorem beq_eq_true_iff [DecidableEq κ] {p q : PolyList κ} :
    beq p q = true ↔ p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp [beq]
  | cons t ts ih =>
      cases q with
      | nil => simp [beq]
      | cons u us =>
          simp only [beq, Bool.and_eq_true, decide_eq_true_eq, ih, expBeq_iff]
          constructor
          · rintro ⟨⟨he, hc⟩, htail⟩
            have htu : t = u := Prod.ext he hc
            subst u
            subst us
            rfl
          · intro h
            cases h
            exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The empty-list test agrees with zero denotation on canonical inputs. -/
theorem isZero_iff {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {p : PolyList κ} (hp : Canonical n p) :
    isZero p = true ↔ denote (cmp := cmp) p = 0 := by
  constructor
  · cases p with
    | nil => intro; rfl
    | cons t ts => simp [isZero]
  · intro h
    have hempty : Canonical n ([] : PolyList κ) :=
      ⟨fun _ hmem => by contradiction, List.Pairwise.nil,
        fun _ hmem => by contradiction⟩
    have hd : denote (cmp := cmp) p = denote (cmp := cmp) [] := h
    rw [denote_injective hp hempty hd]
    rfl

/-- Structural equality agrees with denotational equality on canonical
inputs. -/
theorem beq_iff {n : Nat} {κ : Type u} [Lean.Grind.Semiring κ]
    [BEq κ] [LawfulBEq κ] [DecidableEq κ]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {p q : PolyList κ}
    (hp : Canonical n p) (hq : Canonical n q) :
    beq p q = true ↔ denote (cmp := cmp) p = denote (cmp := cmp) q := by
  rw [beq_eq_true_iff]
  constructor
  · exact fun h => congrArg denote h
  · exact denote_injective hp hq

/-- Reflexivity of list equality, stated at the kernel Boolean interface. -/
theorem beq_refl [DecidableEq κ] (p : PolyList κ) : beq p p = true :=
  beq_eq_true_iff.mpr rfl

/-- Symmetry of list equality, stated at the kernel Boolean interface. -/
theorem beq_symm [DecidableEq κ] {p q : PolyList κ} (h : beq p q = true) :
    beq q p = true :=
  beq_eq_true_iff.mpr (beq_eq_true_iff.mp h).symm

/-- Transitivity of list equality, stated at the kernel Boolean interface. -/
theorem beq_trans [DecidableEq κ] {p q r : PolyList κ}
    (hpq : beq p q = true) (hqr : beq q r = true) : beq p r = true :=
  beq_eq_true_iff.mpr ((beq_eq_true_iff.mp hpq).trans (beq_eq_true_iff.mp hqr))

end Hex.MvPoly.Kernel
