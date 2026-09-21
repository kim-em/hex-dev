/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Kernel
public import HexKroneckerMathlib.MulModSound

public section
namespace Hex.Kronecker.Kernel

/-- Unsaturated structural bounds, used only to prove the kernel checkers. -/
structure Exact {k : Nat} (b : Bounds) (p : MvPolynomial (Fin k) Int) : Prop where
  length : b.degrees.length = k
  degree : ∀ i, p.degreeOf i ≤ b.degrees.getD i.val 0
  norm : norm₁ p ≤ b.height

namespace Exact
variable {k : Nat} {a b : Bounds} {p q : MvPolynomial (Fin k) Int}

theorem inBox (h : Exact a p) : InBox a.degrees p := by
  intro e he
  apply box_ofFn _ h.length
  intro i
  exact (MvPolynomial.monomial_le_degreeOf i he).trans (h.degree i)

theorem zero (k : Nat) : Exact (Bounds.zero k) (0 : MvPolynomial (Fin k) Int) := by
  constructor <;> simp [Bounds.zero]

theorem int (k : Nat) (z : Int) :
    Exact ⟨zeroDegrees k, z.natAbs⟩ (MvPolynomial.C z : MvPolynomial (Fin k) Int) := by
  constructor
  · simp
  · intro i
    change (MvPolynomial.C z : MvPolynomial (Fin k) Int).degreeOf i ≤ (zeroDegrees k).getD i.val 0
    rw [MvPolynomial.degreeOf_C, getD_zeroDegrees]
  · exact le_of_eq (norm₁_monomial 0 z)

theorem add (ha : Exact a p) (hb : Exact b q) : Exact (Kernel.add a b) (p + q) := by
  constructor
  · simp [Kernel.add, ha.length, hb.length]
  · intro i
    exact (MvPolynomial.degreeOf_add_le i p q).trans
      (by simpa only [Kernel.add, getD_maxDegrees] using max_le_max (ha.degree i) (hb.degree i))
  · exact (norm₁_add p q).trans (Nat.add_le_add ha.norm hb.norm)

theorem neg (ha : Exact a p) : Exact a (-p) := by
  constructor
  · exact ha.length
  · simpa only [MvPolynomial.degreeOf_neg] using ha.degree
  · simpa only [norm₁_neg] using ha.norm

theorem sub (ha : Exact a p) (hb : Exact b q) : Exact (Kernel.add a b) (p - q) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

theorem mul (ha : Exact a p) (hb : Exact b q) : Exact (Kernel.mul a b) (p * q) := by
  constructor
  · simp [Kernel.mul, ha.length, hb.length]
  · intro i
    exact (MvPolynomial.degreeOf_mul_le i p q).trans
      (by simpa only [Kernel.mul, getD_addDegrees] using Nat.add_le_add (ha.degree i) (hb.degree i))
  · exact (norm₁_mul p q).trans (Nat.mul_le_mul ha.norm hb.norm)

end Exact

theorem terms_bound (k : Nat) (ts : Hex.MvPoly.Kernel.PolyList Int)
    (h : termShape k ts = true) : Exact (terms k ts) (termsPolynomial k ts) := by
  have hd : (terms k ts).degrees = (termBounds 0 k ts).degrees := by
    clear h
    induction ts with
    | nil => rfl
    | cons t ts ih => cases t; simpa only [terms_cons, termBounds, add, Bounds.add] using congrArg (maxDegrees _) ih
  have hh : (terms k ts).height = termHeight ts := by
    clear h hd
    induction ts with
    | nil => rfl
    | cons t ts ih => cases t; simp only [terms_cons, add, termHeight, ih]
  exact ⟨(congrArg List.length hd).trans (termBounds_length 0 k ts h),
    fun i => hd ▸ terms_degreeOf_le 0 k ts h i, hh ▸ terms_norm₁_le k ts⟩

theorem expr_bound {k : Nat} (e : Expr) (h : e.WellFormed k) :
    Exact ⟨e.degrees k, e.height⟩ (e.toMvPolynomial h) :=
  ⟨e.length_degrees k, e.degreeOf_le h, e.norm₁_le h⟩

theorem pair {k : Nat} {a b : Bounds} {p q : MvPolynomial (Fin k) Int}
    (ha : Exact a p) (hb : Exact b q)
    (he : let s := plan (add a b)
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2^s.digitBits : Nat) : Int)^s.strides.getD i.val 0) p =
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i : Fin k => ((2^s.digitBits : Nat) : Int)^s.strides.getD i.val 0) q) : p = q := by
  have hl : (add a b).degrees.length = k := by simp [add, ha.length, hb.length]
  apply balanced_injective (add a b).degrees hl p q
    (ha.inBox.mono hl (fun i => by simp only [add, getD_maxDegrees]; exact Nat.le_max_left _ _))
    (hb.inBox.mono hl (fun i => by simp only [add, getD_maxDegrees]; exact Nat.le_max_right _ _))
    (a.height + b.height) ((a.height + b.height).log2 + 2)
    (ha.norm.trans (Nat.le_add_right _ _)) (hb.norm.trans (Nat.le_add_left _ _)) (width_bound _)
  simpa only [plan, add, Nat.cast_pow, Nat.cast_ofNat] using he

theorem dot_bound {k : Nat} {a b : List Bounds} {p q : List (MvPolynomial (Fin k) Int)}
    (ha : List.Forall₂ Exact a p) (hb : List.Forall₂ Exact b q) :
    Exact (dot k a b) (polyDot p q) := by
  induction ha generalizing b q with
  | nil => cases hb <;> exact Exact.zero k
  | cons h ht ih =>
      cases hb with
      | nil => exact Exact.zero k
      | cons g gt => exact (h.mul g).add (ih gt)

theorem map_bound (k : Nat) (ts : List (Hex.MvPoly.Kernel.PolyList Int))
    (h : ∀ t ∈ ts, termShape k t = true) :
    List.Forall₂ Exact (ts.map (terms k)) (ts.map (termsPolynomial k)) := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons (terms_bound k t (h t (by simp))) (ih fun t ht => h t (by simp [ht]))

theorem matrix_bound (k n m : Nat) (a : TermMatrix) (h : matrixShape k n m a = true) :
    List.Forall₂ (List.Forall₂ Exact) (matrix k a) (matrixPolynomial k a) := by
  have hrows := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2
  clear h
  unfold matrix matrixPolynomial
  induction a with
  | nil => exact .nil
  | cons row rows ih =>
      apply List.Forall₂.cons
      · apply map_bound
        exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hrows row (by simp))).2
      · exact ih (fun row hr => hrows row (by simp [hr]))

theorem product_bound {k : Nat} {cols rows : List (List Bounds)}
    {pc pr : List (List (MvPolynomial (Fin k) Int))}
    (hc : List.Forall₂ (List.Forall₂ Exact) cols pc)
    (hr : List.Forall₂ (List.Forall₂ Exact) rows pr) :
    List.Forall₂ (List.Forall₂ Exact) (product k cols rows) (polyProduct pc pr) := by
  apply List.rel_map _ hr
  intro a p ha
  exact List.rel_map (fun b q hb => dot_bound ha hb) hc

theorem columns_bound (k n m : Nat) (a : TermMatrix) (h : matrixShape k n m a = true) :
    List.Forall₂ (List.Forall₂ Exact) (boundColumns k m (matrix k a))
      (columnsWith 0 m (matrixPolynomial k a)) := by
  rw [boundColumns_eq]
  exact columnsWith_rel _ _ (Exact.zero k) m (matrix_bound k n m a h)

theorem difference_bound {k : Nat} {as bs : List Bounds} {ps qs : List (MvPolynomial (Fin k) Int)}
    (ha : List.Forall₂ Exact as ps) (hb : List.Forall₂ Exact bs qs) :
    List.Forall₂ Exact (difference as bs) (List.zipWith (·-·) ps qs) := by
  induction ha generalizing bs qs with
  | nil => cases hb <;> exact .nil
  | cons h ht ih =>
      cases hb with
      | nil => exact .nil
      | cons g gt => exact .cons (h.sub g) (ih gt)

theorem scaled_bound {k : Nat} (p : Nat) {bs : List Bounds} {ps : List (MvPolynomial (Fin k) Int)}
    (h : List.Forall₂ Exact bs ps) :
    List.Forall₂ Exact (bs.map (mul ⟨zeroDegrees k, p⟩)) (ps.map (MvPolynomial.C (p:Int)*·)) := by
  apply List.rel_map _ h
  intro b q hq
  simpa only [Int.natAbs_natCast] using (Exact.int k (p:Int)).mul hq

theorem add_left (a b : Bounds) : (add a b).Covers a := by
  constructor
  · intro i; simp only [add, getD_maxDegrees]; exact Nat.le_max_left _ _
  · exact Nat.le_add_right _ _

theorem add_right (a b : Bounds) : (add a b).Covers b := by
  constructor
  · intro i; simp only [add, getD_maxDegrees]; exact Nat.le_max_right _ _
  · exact Nat.le_add_left _ _

theorem common_spec (k : Nat) (as bs : List Bounds) (hl : as.length = bs.length)
    (ha : ∀ a ∈ as, a.degrees.length = k) (hb : ∀ b ∈ bs, b.degrees.length = k) :
    (common k as bs).degrees.length = k ∧ ∀ b ∈ as ++ bs, (common k as bs).Covers b := by
  induction as generalizing bs with
  | nil =>
      have : bs = [] := List.length_eq_zero_iff.mp hl.symm
      subst bs
      simp [common, Bounds.zero]
  | cons a as ih =>
      cases bs with
      | nil => simp at hl
      | cons b bs =>
          have ht := ih bs (by simpa using hl) (fun a h => ha a (by simp [h]))
            (fun b h => hb b (by simp [h]))
          constructor
          · simp [common_cons, Bounds.sup, add, ha a (by simp), hb b (by simp), ht.1]
          · intro c hc
            have hleft := Bounds.sup_left (add a b) (common k as bs)
            have hright := Bounds.sup_right (add a b) (common k as bs)
            rcases List.mem_append.mp hc with hc | hc
            · rcases List.mem_cons.mp hc with rfl | hc
              · exact hleft.trans (add_left c b)
              · exact hright.trans (ht.2 c (List.mem_append_left _ hc))
            · rcases List.mem_cons.mp hc with rfl | hc
              · exact hleft.trans (add_right a c)
              · exact hright.trans (ht.2 c (List.mem_append_right _ hc))

theorem common_length (k : Nat) (as bs : List Bounds)
    (ha : ∀ a ∈ as, a.degrees.length = k) (hb : ∀ b ∈ bs, b.degrees.length = k) :
    (common k as bs).degrees.length = k := by
  induction as generalizing bs with
  | nil => simp [common, Bounds.zero]
  | cons a as ih =>
      cases bs with
      | nil => simp [common, Bounds.zero]
      | cons b bs =>
          simp only [common_cons, Bounds.sup, add, length_maxDegrees,
            ha a (by simp), hb b (by simp),
            ih bs (fun a h => ha a (by simp [h])) (fun b h => hb b (by simp [h])), Nat.max_self]

theorem lengths {k : Nat} {bs : List Bounds} {ps : List (MvPolynomial (Fin k) Int)}
    (h : List.Forall₂ Exact bs ps) : ∀ b ∈ bs, b.degrees.length = k := by
  induction h with
  | nil => simp
  | cons h ht ih =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h.length
      · exact ih b hb

theorem lists {k : Nat} {as bs : List Bounds} {ps qs : List (MvPolynomial (Fin k) Int)}
    (ha : List.Forall₂ Exact as ps) (hb : List.Forall₂ Exact bs qs)
    (he : let s := plan (common k as bs)
      List.Forall₂ (fun p q =>
        MvPolynomial.eval₂Hom (RingHom.id Int)
          (fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0) p =
        MvPolynomial.eval₂Hom (RingHom.id Int)
          (fun i : Fin k => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0) q) ps qs) : ps = qs := by
  have hl : as.length = bs.length := ha.length_eq.trans (he.length_eq.trans hb.length_eq.symm)
  have hc := common_spec k as bs hl (lengths ha) (lengths hb)
  apply List.ext_getElem he.length_eq
  intro i hip hiq
  have hia : i < as.length := by simpa only [ha.length_eq] using hip
  have hib : i < bs.length := by simpa only [hb.length_eq] using hiq
  have hap := ha.get hia hip
  have hbq := hb.get hib hiq
  have hac := hc.2 as[i] (List.mem_append_left _ (List.getElem_mem hia))
  have hbc := hc.2 bs[i] (List.mem_append_right _ (List.getElem_mem hib))
  apply balanced_injective (common k as bs).degrees hc.1 _ _
    (hap.inBox.mono hc.1 (fun i => hac.1 i.val))
    (hbq.inBox.mono hc.1 (fun i => hbc.1 i.val))
    (common k as bs).height ((common k as bs).height.log2 + 2)
    (hap.norm.trans hac.2) (hbq.norm.trans hbc.2) (width_bound _)
  simpa only [plan, Nat.cast_pow, Nat.cast_ofNat] using he.get hip hiq

end Hex.Kronecker.Kernel
