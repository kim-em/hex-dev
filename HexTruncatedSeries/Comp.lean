/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.ExpLog

public section

/-!
Horner and Brent--Kung composition of fixed-precision truncated series.

The public operation uses Brent--Kung: powers of the inner series are built
once in a reusable vector, coefficient blocks are evaluated by scalar matrix
products, and the blocks are combined by Horner in the giant step.  The
bounded form restricts both the coefficient blocks and every multiplication
to the requested precision.  Horner remains public as the independent simple
route used by conformance and benchmarking.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

private theorem foldMap [Lean.Grind.CommRing R] {α β : Type}
    (xs : List α) (row : α → List β) (term : α → β → R) :
    (xs.flatMap fun x => (row x).map (term x)).foldl (fun acc y => acc + y) 0 =
      xs.foldl
        (fun acc x => acc + (row x).foldl (fun acc y => acc + term x y) 0) 0 := by
  rw [List.foldl_add_flatMap]
  congr 1
  funext acc x
  rw [List.foldl_map, List.foldl_add_eq_add_foldl]

private def blockSize (n : Nat) : Nat :=
  if n = 0 then 1 else Nat.sqrt (n - 1) + 1

private theorem blockSize_pos (p : Nat) : 0 < blockSize p := by
  unfold blockSize
  split <;> omega

private theorem le_blockSize_sq (p : Nat) : p ≤ blockSize p * blockSize p := by
  unfold blockSize
  split
  · omega
  · have hs := Nat.lt_succ_sqrt (p - 1)
    simp only [Nat.succ_eq_add_one] at hs
    omega

private def compHornerUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a b : TSeries R n) : TSeries R n :=
  let p := min m n
  let raw := (List.range p).foldr
    (fun k acc => mulUpTo m acc b + C (a.coeff k))
    (0 : TSeries R n)
  ofFn fun i => if i < m then raw.coeff i else 0

/-- The reference Horner composition. -/
def compHorner [Lean.Grind.CommRing R]
    (a b : TSeries R n) : TSeries R n :=
  compHornerUpTo n a b

private def powerTable [Lean.Grind.CommRing R] (m : Nat) (b : TSeries R n) :
    (s : Nat) → Vector (TSeries R n) (s + 1)
  | 0 => Hex.Vector.ofFn' fun _ => 1
  | s + 1 =>
      let powers := powerTable m b s
      powers.push (mulUpTo m (powers.get ⟨s, Nat.lt_succ_self s⟩) b)

private theorem powerTable_agree [Lean.Grind.CommRing R]
    (m : Nat) (b : TSeries R n) (s j : Nat) (hj : j ≤ s) :
    Agree m ((powerTable m b s).get ⟨j, by omega⟩) (b ^ j) := by
  induction s generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      change Agree m 1 (b ^ 0)
      rw [pow_zero]
      exact Agree.refl m 1
  | succ s ih =>
      by_cases hjs : j ≤ s
      · unfold powerTable
        have hget :
            ((powerTable m b s).push
              (mulUpTo m ((powerTable m b s).get ⟨s, by omega⟩) b)).get
                ⟨j, by omega⟩ =
              (powerTable m b s).get ⟨j, by omega⟩ :=
          Vector.getElem_push_lt (xs := powerTable m b s)
            (x := mulUpTo m ((powerTable m b s).get ⟨s, by omega⟩) b)
            (i := j) (by omega)
        rw [hget]
        exact ih j hjs
      · have hjeq : j = s + 1 := by omega
        subst j
        unfold powerTable
        have hget :
            ((powerTable m b s).push
              (mulUpTo m ((powerTable m b s).get ⟨s, by omega⟩) b)).get
                ⟨s + 1, by omega⟩ =
              mulUpTo m ((powerTable m b s).get ⟨s, by omega⟩) b :=
          Vector.getElem_push_eq
        rw [hget, pow_succ]
        exact Agree.trans (Agree.mulUpTo m _ _)
          (Agree.mul (ih s (by omega)) (Agree.refl m b))

private def evalBlock [Lean.Grind.CommRing R] (m p s : Nat) (a : TSeries R n)
    (powers : Vector (TSeries R n) (s + 1)) (q : Nat) : TSeries R n :=
  let js := List.range s
  ofFn fun i =>
    if i < m then
      js.foldl (fun acc j =>
        let k := q * s + j
        acc + if k < p then
          a.coeff k *
            (powers.get ⟨min j s, Nat.lt_succ_of_le (Nat.min_le_right j s)⟩).coeff i
        else 0) 0
    else
      0

private def blockSum [Lean.Grind.CommRing R] (p s : Nat)
    (a b : TSeries R n) (q : Nat) : TSeries R n :=
  (List.range s).foldl (fun acc j =>
    let k := q * s + j
    acc + if k < p then C (a.coeff k) * b ^ j else 0) 0

/-- Brent--Kung composition computed only below precision `m`. -/
def compBrentKungUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a b : TSeries R n) : TSeries R n :=
  let p := min m n
  let s := blockSize p
  let powers := powerTable m b s
  let giant := powers[s]'(Nat.lt_succ_self s)
  let raw := (List.range s).foldr
    (fun q acc => mulUpTo m acc giant + evalBlock m p s a powers q)
    (0 : TSeries R n)
  ofFn fun i => if i < m then raw.coeff i else 0

/-- Full-precision Brent--Kung composition. -/
def compBrentKung [Lean.Grind.CommRing R]
    (a b : TSeries R n) : TSeries R n :=
  compBrentKungUpTo n a b

/-- Bounded composition used by Newton reversion. -/
def compUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a b : TSeries R n) : TSeries R n :=
  compBrentKungUpTo m a b

/-- Substitute `b` into `a`, using Brent--Kung composition. -/
def comp [Lean.Grind.CommRing R] (a b : TSeries R n) : TSeries R n :=
  compUpTo n a b

/-- Check the zero-constant sufficient condition before composing. -/
def comp? [Lean.Grind.CommRing R] [DecidableEq R]
    (a b : TSeries R n) : Option (TSeries R n) :=
  if b.coeff 0 = 0 then some (comp a b) else none

private theorem compHorner_eq_raw [Lean.Grind.CommRing R]
    (a b : TSeries R n) :
    compHorner a b = (List.range n).foldr
      (fun k acc => acc * b + C (a.coeff k)) 0 := by
  unfold compHorner compHornerUpTo
  simp only [Nat.min_self, Agree.mulUpTo_full]
  apply ext
  intro i hi
  rw [coeff_ofFn _ i hi, ite_eq_left hi]

private theorem hornerFold [Lean.Grind.CommRing R]
    (a b : TSeries R n) (k : Nat) (z : TSeries R n) :
    (List.range k).foldr (fun i acc => acc * b + C (a.coeff i)) z =
      z * b ^ k + (List.range k).foldl
        (fun acc i => acc + C (a.coeff i) * b ^ i) 0 := by
  induction k generalizing z with
  | zero =>
      rw [List.range_zero, List.foldr_nil, List.foldl_nil, pow_zero,
        mul_one, add_zero]
  | succ k ih =>
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
        ih, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ]
      grind

private theorem hornerFoldFn [Lean.Grind.CommRing R]
    (f : Nat → TSeries R n) (g : TSeries R n) (k : Nat) (z : TSeries R n) :
    (List.range k).foldr (fun i acc => acc * g + f i) z =
      z * g ^ k + (List.range k).foldl
        (fun acc i => acc + f i * g ^ i) 0 := by
  induction k generalizing z with
  | zero =>
      rw [List.range_zero, List.foldr_nil, List.foldl_nil, pow_zero,
        mul_one, add_zero]
  | succ k ih =>
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
        ih, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ]
      grind

private theorem evalBlock_agree [Lean.Grind.CommRing R]
    (m p s : Nat) (a b : TSeries R n) (q : Nat) :
    Agree m (evalBlock m p s a (powerTable m b s) q)
      (blockSum p s a b q) := by
  intro i hi him
  unfold evalBlock blockSum
  rw [coeff_ofFn _ i hi, ite_eq_left him,
    coeff_foldl_add (List.range s)
      (fun j => if q * s + j < p then C (a.coeff (q * s + j)) * b ^ j else 0)
      0 i hi, coeff_zero]
  apply List.foldl_add_congr
  intro j hj
  have hjs : j < s := List.mem_range.mp hj
  have hmin : min j s = j := Nat.min_eq_left (Nat.le_of_lt hjs)
  simp only [hmin]
  split
  · rw [coeff_C_mul _ _ i hi]
    exact congrArg (a.coeff (q * s + j) * ·)
      (powerTable_agree m b s j (by omega) i hi him)
  · rw [coeff_zero]

private theorem brentFold_agree [Lean.Grind.CommRing R]
    (m p s : Nat) (a b : TSeries R n) (qs : List Nat) :
    Agree m
      (qs.foldr
        (fun q acc =>
          mulUpTo m acc ((powerTable m b s).get ⟨s, Nat.lt_succ_self s⟩) +
            evalBlock m p s a (powerTable m b s) q)
        0)
      (qs.foldr
        (fun q acc => acc * b ^ s + blockSum p s a b q)
        0) := by
  induction qs with
  | nil => exact Agree.refl m 0
  | cons q qs ih =>
      simp only [List.foldr_cons]
      apply Agree.add
      · exact Agree.trans (Agree.mulUpTo m _ _)
          (Agree.mul ih (powerTable_agree m b s s (by omega)))
      · exact evalBlock_agree m p s a b q

private theorem blockIndices_eq (s q : Nat) :
    (List.range q).flatMap
      (fun r => (List.range s).map (fun j => r * s + j)) =
      List.range (q * s) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Nat.succ_mul, List.range_add]

private def squarePairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun j =>
    (List.range n).map fun k => (j, k)

private def validPairs (n : Nat) : List (Nat × Nat) :=
  (squarePairs n).filter fun jk => decide (jk.1 + jk.2 < n)

private def trianglePairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun t =>
    (List.range (t + 1)).map fun j => (j, t - j)

private theorem squarePairs_nodup (n : Nat) : (squarePairs n).Nodup := by
  unfold squarePairs
  apply List.nodup_flatMap_of_disjoint List.nodup_range
  · intro j hj
    apply List.nodup_map_on List.nodup_range
    intro a ha b hb hab
    exact Prod.ext_iff.mp hab |>.2
  · intro j hj k hk hjk z hzj hzk
    rcases List.mem_map.mp hzj with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨c, hc, heq⟩
    exact hjk (Prod.ext_iff.mp heq).1.symm

private theorem trianglePairs_nodup (n : Nat) : (trianglePairs n).Nodup := by
  unfold trianglePairs
  apply List.nodup_flatMap_of_disjoint List.nodup_range
  · intro t ht
    apply List.nodup_map_on List.nodup_range
    intro a ha b hb hab
    exact Prod.ext_iff.mp hab |>.1
  · intro t ht u hu htu z hzt hzu
    rcases List.mem_map.mp hzt with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzu with ⟨c, hc, heq⟩
    injection heq with hac hlast
    subst c
    have ha' := List.mem_range.mp ha
    have hc' := List.mem_range.mp hc
    apply htu
    omega

private theorem validPairs_perm (n : Nat) :
    (validPairs n).Perm (trianglePairs n) := by
  apply (List.perm_ext_iff_of_nodup
    ((squarePairs_nodup n).filter _) (trianglePairs_nodup n)).2
  rintro ⟨j, k⟩
  simp only [squarePairs, trianglePairs, List.mem_filter,
    List.mem_flatMap, List.mem_map, List.mem_range, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨u, hu, v, hv, huv⟩, hjk⟩
    rcases huv with ⟨rfl, rfl⟩
    exact ⟨u + v, hjk, u, by omega, rfl, by omega⟩
  · rintro ⟨t, ht, hjt, hlast⟩
    refine ⟨⟨j, ?_, k, ?_, rfl, rfl⟩, ?_⟩ <;> omega

private theorem blockSum_mul_pow [Lean.Grind.CommRing R]
    (p s : Nat) (a b : TSeries R n) (q : Nat) :
    blockSum p s a b q * (b ^ s) ^ q =
      (List.range s).foldl (fun acc j =>
        let k := q * s + j
        acc + if k < p then C (a.coeff k) * b ^ k else 0) 0 := by
  unfold blockSum
  rw [← List.foldl_add_mul_right_zero]
  apply List.foldl_add_congr
  intro j hj
  split
  · rw [Lean.Grind.Semiring.mul_assoc, pow_mul, ← pow_add]
    congr 2
    rw [Nat.mul_comm s q, Nat.add_comm]
  · rw [zero_mul]

private theorem foldIndicatorRange [Lean.Grind.CommRing R]
    (f : Nat → TSeries R n) (p N : Nat) (hp : p ≤ N) :
    (List.range N).foldl
        (fun acc k => acc + if k < p then f k else 0) 0 =
      (List.range p).foldl (fun acc k => acc + f k) 0 := by
  rw [show N = p + (N - p) by omega, List.range_add, List.foldl_append]
  have hfirst :
      (List.range p).foldl
          (fun acc k => acc + if k < p then f k else 0) 0 =
        (List.range p).foldl (fun acc k => acc + f k) 0 := by
    apply List.foldl_add_congr
    intro k hk
    rw [ite_eq_left (List.mem_range.mp hk)]
  rw [hfirst, List.foldl_map]
  apply List.foldl_add_eq_self
  intro k hk
  rw [ite_eq_right]
  have hk' := List.mem_range.mp hk
  omega

private theorem brentFold_eq_sum [Lean.Grind.CommRing R]
    (p s : Nat) (a b : TSeries R n) (hp : p ≤ s * s) :
    (List.range s).foldr
        (fun q acc => acc * b ^ s + blockSum p s a b q) 0 =
      (List.range p).foldl
        (fun acc k => acc + C (a.coeff k) * b ^ k) 0 := by
  rw [hornerFoldFn (fun q => blockSum p s a b q) (b ^ s) s 0,
    zero_mul]
  have hterms :
      (List.range s).foldl
          (fun acc q => acc + blockSum p s a b q * (b ^ s) ^ q) 0 =
        (List.range s).foldl
          (fun acc q => acc +
            (List.range s).foldl (fun acc j =>
              acc + if q * s + j < p then
                C (a.coeff (q * s + j)) * b ^ (q * s + j) else 0) 0) 0 := by
    apply List.foldl_add_congr
    intro q hq
    exact blockSum_mul_pow p s a b q
  rw [hterms]
  rw [show (0 : TSeries R n) +
      (List.range s).foldl
        (fun acc q => acc +
          (List.range s).foldl (fun acc j =>
            acc + if q * s + j < p then
              C (a.coeff (q * s + j)) * b ^ (q * s + j) else 0) 0) 0 =
      (List.range s).foldl
        (fun acc q => acc +
          (List.range s).foldl (fun acc j =>
            acc + if q * s + j < p then
              C (a.coeff (q * s + j)) * b ^ (q * s + j) else 0) 0) 0 by grind]
  calc
    (List.range s).foldl
        (fun acc q => acc +
          (List.range s).foldl (fun acc j =>
            acc + if q * s + j < p then
              C (a.coeff (q * s + j)) * b ^ (q * s + j) else 0) 0) 0 =
      (List.range s).foldl
        (fun acc q =>
          (List.range s).foldl (fun acc j =>
            acc + if q * s + j < p then
              C (a.coeff (q * s + j)) * b ^ (q * s + j) else 0) acc) 0 := by
        apply List.foldl_congr
        intro acc q hq
        exact (List.foldl_add_eq_add_foldl (List.range s)
          (fun j => if q * s + j < p then
            C (a.coeff (q * s + j)) * b ^ (q * s + j) else 0) acc).symm
    _ = (List.range s).foldl
        (fun acc q =>
          ((List.range s).map (fun j => q * s + j)).foldl
            (fun acc k => acc + if k < p then C (a.coeff k) * b ^ k else 0)
            acc) 0 := by
          apply List.foldl_congr
          intro acc q hq
          rw [List.foldl_map]
    _ = ((List.range s).flatMap
          (fun q => (List.range s).map (fun j => q * s + j))).foldl
        (fun acc k => acc + if k < p then C (a.coeff k) * b ^ k else 0) 0 :=
      (List.foldl_add_flatMap (List.range s)
        (fun q => (List.range s).map (fun j => q * s + j))
        (fun k => if k < p then C (a.coeff k) * b ^ k else 0) 0).symm
    _ = (List.range (s * s)).foldl
        (fun acc k => acc + if k < p then C (a.coeff k) * b ^ k else 0) 0 := by
      rw [blockIndices_eq]
    _ = (List.range p).foldl
        (fun acc k => acc + C (a.coeff k) * b ^ k) 0 :=
      foldIndicatorRange (fun k => C (a.coeff k) * b ^ k) p (s * s) hp

/-- A power of a series with zero constant coefficient vanishes below its
exponent. -/
theorem pow_vanish [Lean.Grind.CommRing R] (b : TSeries R n)
    (h : b.coeff 0 = 0) (k : Nat) : Agree k (b ^ k) 0 := by
  have hb : Agree 1 b 0 := by
    intro i hi hi1
    have hi0 : i = 0 := by omega
    subst i
    rw [h, coeff_zero]
  induction k with
  | zero =>
      intro i hi hi0
      omega
  | succ k ih =>
      rw [pow_succ]
      exact Agree.zeroMul ih hb

private theorem sumPrefix_agree [Lean.Grind.CommRing R]
    (a b : TSeries R n) (h : b.coeff 0 = 0) (p : Nat) (hp : p ≤ n) :
    Agree p
      ((List.range p).foldl
        (fun acc k => acc + C (a.coeff k) * b ^ k) 0)
      ((List.range n).foldl
        (fun acc k => acc + C (a.coeff k) * b ^ k) 0) := by
  have hrange : List.range n =
      List.range p ++ (List.range (n - p)).map (p + ·) := by
    calc
      List.range n = List.range (p + (n - p)) := by congr 1 <;> omega
      _ = List.range p ++ (List.range (n - p)).map (p + ·) := List.range_add
  rw [hrange, List.foldl_append, List.foldl_map]
  let headSum : TSeries R n := (List.range p).foldl
    (fun acc k => acc + C (a.coeff k) * b ^ k) 0
  have hterm (k : Nat) (hpk : p ≤ k) :
      Agree p (C (a.coeff k) * b ^ k) 0 := by
    have hbpow := Agree.mono (pow_vanish b h k) hpk
    have hmul := Agree.mul (Agree.refl p (C (a.coeff k))) hbpow
    simpa only [mul_zero] using hmul
  have go (xs : List Nat) (acc : TSeries R n) :
      Agree p acc
        (xs.foldl
          (fun acc j => acc + C (a.coeff (p + j)) * b ^ (p + j)) acc) := by
    induction xs generalizing acc with
    | nil => exact Agree.refl p acc
    | cons j js ih =>
        rw [List.foldl_cons]
        apply Agree.trans (b := acc + 0)
        · simpa only [add_zero] using Agree.refl p acc
        · exact Agree.trans
            (Agree.symm (Agree.add (Agree.refl p acc)
              (hterm (p + j) (by omega))))
            (ih (acc + C (a.coeff (p + j)) * b ^ (p + j)))
  exact go (List.range (n - p)) headSum

private theorem foldSum_mul [Lean.Grind.CommRing R] {α β : Type}
    (xs : List α) (ys : List β) (f : α → TSeries R n)
    (g : β → TSeries R n) :
    xs.foldl (fun acc x => acc + f x) 0 *
        ys.foldl (fun acc y => acc + g y) 0 =
      xs.foldl (fun acc x => acc +
        ys.foldl (fun acc y => acc + f x * g y) 0) 0 := by
  rw [← List.foldl_add_mul_right_zero]
  apply List.foldl_add_congr
  intro x hx
  exact (List.foldl_add_mul_left_zero ys (f x) g).symm

private theorem compTerm_mul [Lean.Grind.CommRing R]
    (a a' b : TSeries R n) (j k : Nat) :
    (C (a.coeff j) * b ^ j) * (C (a'.coeff k) * b ^ k) =
      C (a.coeff j * a'.coeff k) * b ^ (j + k) := by
  calc
    (C (a.coeff j) * b ^ j) * (C (a'.coeff k) * b ^ k) =
        (C (a.coeff j) * C (a'.coeff k)) * (b ^ j * b ^ k) := by grind
    _ = C (a.coeff j * a'.coeff k) * b ^ (j + k) := by
      rw [C_mul, ← pow_add]

private theorem C_fold [Lean.Grind.CommRing R] {α : Type}
    (xs : List α) (f : α → R) (z : R) :
    (C (xs.foldl (fun acc x => acc + f x) z) : TSeries R n) =
      xs.foldl (fun acc x => acc + C (f x)) (C z : TSeries R n) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, C_add]

private theorem C_conv_mul_pow [Lean.Grind.CommRing R]
    (a a' b : TSeries R n) (t : Nat) :
    C (convCoeff a.coeff a'.coeff t) * b ^ t =
      (List.range (t + 1)).foldl
        (fun acc j => acc + C (a.coeff j * a'.coeff (t - j)) * b ^ t) 0 := by
  unfold convCoeff
  rw [C_fold, C_zero, ← List.foldl_add_mul_right_zero]

private def pairTerm [Lean.Grind.CommRing R]
    (a a' b : TSeries R n) (jk : Nat × Nat) : TSeries R n :=
  C (a.coeff jk.1 * a'.coeff jk.2) * b ^ (jk.1 + jk.2)

/-- Horner composition is the finite coefficient-scaled power sum. -/
theorem compHorner_spec [Lean.Grind.CommRing R] (a b : TSeries R n) :
    compHorner a b = (List.range n).foldl
      (fun acc k => acc + C (a.coeff k) * b.pow k) 0 := by
  change compHorner a b = (List.range n).foldl
    (fun acc k => acc + C (a.coeff k) * b ^ k) 0
  rw [compHorner_eq_raw, hornerFold]
  rw [zero_mul]
  exact (add_comm 0 _).trans (add_zero _)

private theorem coeff_compUpTo_horner [Lean.Grind.CommRing R] (m : Nat)
    (a b : TSeries R n) (h : b.coeff 0 = 0) (i : Nat) (hi : i < n) :
    (compUpTo m a b).coeff i =
      if i < m then (compHorner a b).coeff i else 0 := by
  unfold compUpTo compBrentKungUpTo
  rw [coeff_ofFn _ i hi]
  split
  · rename_i him
    let p := min m n
    let s := blockSize p
    have hraw := brentFold_agree m p s a b (List.range s)
    have heval := brentFold_eq_sum p s a b (by
      exact le_blockSize_sq p)
    have hprefix := sumPrefix_agree a b h p (Nat.min_le_right m n)
    calc
      ((List.range s).foldr
          (fun q acc =>
            mulUpTo m acc ((powerTable m b s).get ⟨s, Nat.lt_succ_self s⟩) +
              evalBlock m p s a (powerTable m b s) q) 0).coeff i =
        ((List.range s).foldr
          (fun q acc => acc * b ^ s + blockSum p s a b q) 0).coeff i :=
            hraw i hi him
      _ = ((List.range p).foldl
          (fun acc k => acc + C (a.coeff k) * b ^ k) 0).coeff i :=
            congrArg (fun z : TSeries R n => z.coeff i) heval
      _ = ((List.range n).foldl
          (fun acc k => acc + C (a.coeff k) * b ^ k) 0).coeff i :=
            hprefix i hi (by simp only [p]; omega)
      _ = (compHorner a b).coeff i :=
            congrArg (fun z : TSeries R n => z.coeff i) (compHorner_spec a b).symm
  · rfl

/-- Brent--Kung and Horner agree under the zero-constant substitution
condition. -/
theorem comp_eq_horner [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : b.coeff 0 = 0) : comp a b = compHorner a b := by
  apply ext
  intro i hi
  unfold comp
  rw [coeff_compUpTo_horner n a b h i hi, ite_eq_left hi]

/-- Bounded composition agrees with full composition below its bound. -/
theorem coeff_compUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a b : TSeries R n) (h : b.coeff 0 = 0) (i : Nat) (hi : i < n) :
    (compUpTo m a b).coeff i = if i < m then (comp a b).coeff i else 0 := by
  rw [coeff_compUpTo_horner m a b h i hi]
  split
  · rw [comp_eq_horner a b h]
  · rfl

/-- Composition is the finite truncated sum of coefficient-scaled powers. -/
theorem comp_spec [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : b.coeff 0 = 0) :
    comp a b = (List.range n).foldl
      (fun acc k => acc + C (a.coeff k) * b.pow k) 0 := by
  rw [comp_eq_horner a b h, compHorner_spec]

/-- Substituting `x` leaves a series unchanged. -/
@[simp]
theorem comp_X_right [Lean.Grind.CommRing R] (a : TSeries R n) :
    comp a X = a := by
  rw [comp_spec a X X_coeff_zero]
  apply ext
  intro i hi
  change ((List.range n).foldl
    (fun acc k => acc + C (a.coeff k) * (X : TSeries R n) ^ k) 0).coeff i =
      a.coeff i
  rw [coeff_foldl_add (List.range n)
    (fun k => C (a.coeff k) * (X : TSeries R n) ^ k) 0 i hi]
  rw [coeff_zero]
  calc
    (List.range n).foldl
        (fun acc k => acc + (C (a.coeff k) * (X : TSeries R n) ^ k).coeff i) 0 =
      (List.range n).foldl
        (fun acc k => acc + if k = i then a.coeff k else 0) 0 := by
          apply List.foldl_add_congr
          intro k hk
          rw [coeff_C_mul_X_pow (a.coeff k) k i hi]
          by_cases hki : k = i
          · subst k
            simp
          · have hik : i ≠ k := fun h => hki h.symm
            simp [hki, hik]
    _ = 0 + a.coeff i :=
      List.foldl_add_single _ _ _ _ (List.mem_range.mpr hi) List.nodup_range
    _ = a.coeff i := by grind

/-- Substituting a zero-constant series into `x` returns that series. -/
@[simp]
theorem comp_X_left [Lean.Grind.CommRing R] (b : TSeries R n)
    (h : b.coeff 0 = 0) : comp X b = b := by
  by_cases hn : 1 < n
  · rw [comp_spec X b h]
    have hpow : (b : TSeries R n) ^ 1 = b := by
      rw [pow_succ, pow_zero, one_mul]
    calc
      (List.range n).foldl
          (fun acc k => acc + C ((X : TSeries R n).coeff k) * b ^ k) 0 =
        (List.range n).foldl
          (fun acc k => acc + if k = 1 then b else 0) 0 := by
            apply List.foldl_add_congr
            intro k hk
            rw [coeff_X k (List.mem_range.mp hk)]
            by_cases hk1 : k = 1
            · subst k
              rw [ite_eq_left rfl, C_one, hpow, one_mul, ite_eq_left rfl]
            · rw [ite_eq_right hk1, C_zero, zero_mul, ite_eq_right hk1]
      _ = 0 + b :=
        List.foldl_add_single _ _ _ _ (List.mem_range.mpr hn) List.nodup_range
      _ = b := by grind
  · apply ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    rw [h]
    by_cases hn0 : n = 0
    · omega
    · rw [comp_spec X b h]
      change ((List.range n).foldl
        (fun acc k => acc + C ((X : TSeries R n).coeff k) * b ^ k) 0).coeff 0 = 0
      rw [
        coeff_foldl_add (List.range n)
          (fun k => C ((X : TSeries R n).coeff k) * b ^ k) 0 0 hi,
        coeff_zero]
      apply List.foldl_add_eq_self
      intro k hk
      have hk0 : k = 0 := by
        have := List.mem_range.mp hk
        omega
      subst k
      rw [coeff_C_mul _ _ 0 hi, X_coeff_zero]
      grind

/-- Composition preserves multiplication under the zero-constant condition. -/
theorem comp_mul [Lean.Grind.CommRing R] (a a' b : TSeries R n)
    (h : b.coeff 0 = 0) : comp (a * a') b = comp a b * comp a' b := by
  rw [comp_spec (a * a') b h, comp_spec a b h, comp_spec a' b h]
  have hleft :
      (List.range n).foldl
          (fun acc t => acc + C ((a * a').coeff t) * b ^ t) 0 =
        (trianglePairs n).foldl
          (fun acc jk => acc + pairTerm a a' b jk) 0 := by
    calc
      (List.range n).foldl
          (fun acc t => acc + C ((a * a').coeff t) * b ^ t) 0 =
        (List.range n).foldl
          (fun acc t => acc +
            (List.range (t + 1)).foldl
              (fun acc j => acc +
                C (a.coeff j * a'.coeff (t - j)) * b ^ t) 0) 0 := by
            apply List.foldl_add_congr
            intro t ht
            rw [coeff_mul a a' t (List.mem_range.mp ht), C_conv_mul_pow]
      _ = (List.range n).foldl
          (fun acc t => acc +
            (List.range (t + 1)).foldl
              (fun acc j => acc + pairTerm a a' b (j, t - j)) 0) 0 := by
            apply List.foldl_add_congr
            intro t ht
            apply List.foldl_add_congr
            intro j hj
            unfold pairTerm
            congr 3
            have hj' := List.mem_range.mp hj
            omega
      _ = (trianglePairs n).foldl
          (fun acc jk => acc + pairTerm a a' b jk) 0 := by
            simpa only [trianglePairs, List.foldl_flatMap, List.foldl_map] using
              (foldMap (R := TSeries R n) (List.range n)
                (fun t => List.range (t + 1))
                (fun t j => pairTerm a a' b (j, t - j))).symm
  change
    (List.range n).foldl
        (fun acc t => acc + C ((a * a').coeff t) * b ^ t) 0 =
      (List.range n).foldl
          (fun acc j => acc + C (a.coeff j) * b ^ j) 0 *
        (List.range n).foldl
          (fun acc k => acc + C (a'.coeff k) * b ^ k) 0
  rw [hleft]
  rw [foldSum_mul]
  have hterms :
      (List.range n).foldl
          (fun acc j => acc +
            (List.range n).foldl
              (fun acc k => acc +
                (C (a.coeff j) * b ^ j) * (C (a'.coeff k) * b ^ k)) 0) 0 =
        (List.range n).foldl
          (fun acc j => acc +
            (List.range n).foldl
              (fun acc k => acc + pairTerm a a' b (j, k)) 0) 0 := by
    apply List.foldl_add_congr
    intro j hj
    apply List.foldl_add_congr
    intro k hk
    exact compTerm_mul a a' b j k
  rw [hterms]
  have hsquare :
      (List.range n).foldl
          (fun acc j => acc +
            (List.range n).foldl
              (fun acc k => acc + pairTerm a a' b (j, k)) 0) 0 =
        (squarePairs n).foldl
          (fun acc jk => acc + pairTerm a a' b jk) 0 := by
    simpa only [squarePairs, List.foldl_flatMap, List.foldl_map] using
      (foldMap (R := TSeries R n) (List.range n)
        (fun _ => List.range n) (fun j k => pairTerm a a' b (j, k))).symm
  rw [hsquare]
  have hvalid :
      (squarePairs n).foldl
          (fun acc jk => acc + pairTerm a a' b jk) 0 =
        (validPairs n).foldl
          (fun acc jk => acc + pairTerm a a' b jk) 0 := by
    unfold validPairs
    rw [List.foldl_filter]
    apply List.foldl_congr
    intro acc jk hjk
    by_cases hv : jk.1 + jk.2 < n
    · simp [hv]
    · have hbzero : b ^ (jk.1 + jk.2) = 0 :=
        Agree.full (pow_vanish b h (jk.1 + jk.2)) (by omega)
      simp [hv, pairTerm, hbzero, mul_zero, add_zero]
  rw [hvalid]
  exact (List.foldl_add_perm (pairTerm a a' b) (validPairs_perm n) 0).symm

/-- Substitution preserves addition when the inner series has zero constant
coefficient. -/
theorem comp_add [Lean.Grind.CommRing R] (a a' b : TSeries R n)
    (h : b.coeff 0 = 0) : comp (a + a') b = comp a b + comp a' b := by
  rw [comp_spec (a + a') b h, comp_spec a b h, comp_spec a' b h]
  calc
    (List.range n).foldl
        (fun acc k => acc + C ((a + a').coeff k) * b ^ k) 0 =
      (List.range n).foldl
        (fun acc k => acc +
          (C (a.coeff k) * b ^ k + C (a'.coeff k) * b ^ k)) 0 := by
            apply List.foldl_add_congr
            intro k hk
            rw [coeff_add a a' k (List.mem_range.mp hk), C_add, right_distrib]
    _ = (List.range n).foldl
          (fun acc k => acc + C (a.coeff k) * b ^ k) 0 +
        (List.range n).foldl
          (fun acc k => acc + C (a'.coeff k) * b ^ k) 0 :=
      List.foldl_add_add _ _ _

/-- Substituting into the zero series gives zero. -/
@[simp]
theorem comp_zero [Lean.Grind.CommRing R] (b : TSeries R n)
    (h : b.coeff 0 = 0) : comp 0 b = 0 := by
  rw [comp_spec 0 b h]
  apply List.foldl_add_eq_self
  intro k hk
  rw [coeff_zero, C_zero, zero_mul]

/-- Substitution leaves a constant series unchanged. -/
@[simp]
theorem comp_C [Lean.Grind.CommRing R] (c : R) (b : TSeries R n)
    (h : b.coeff 0 = 0) : comp (C c) b = C c := by
  rw [comp_spec (C c) b h]
  by_cases hn : n = 0
  · apply ext
    intro i hi
    omega
  · calc
      (List.range n).foldl
          (fun acc k => acc + C ((C c : TSeries R n).coeff k) * b ^ k) 0 =
        (List.range n).foldl
          (fun acc k => acc + if k = 0 then C c else 0) 0 := by
            apply List.foldl_add_congr
            intro k hk
            rw [coeff_C c k (List.mem_range.mp hk)]
            split
            · subst k
              rw [pow_zero, mul_one]
            · rw [C_zero, zero_mul]
      _ = 0 + C c :=
        List.foldl_add_single _ _ _ _ (List.mem_range.mpr (by omega)) List.nodup_range
      _ = C c := by grind

/-- Substitution of zero extracts the outer constant coefficient. -/
@[simp]
theorem comp_zero_right [Lean.Grind.CommRing R] (a : TSeries R n) :
    comp a 0 = C (a.coeff 0) := by
  rw [comp_spec a 0 (coeff_zero 0)]
  by_cases hn : 0 < n
  · calc
      (List.range n).foldl
          (fun acc k => acc + C (a.coeff k) * (0 : TSeries R n) ^ k) 0 =
        (List.range n).foldl
          (fun acc k => acc + if k = 0 then C (a.coeff 0) else 0) 0 := by
            apply List.foldl_add_congr
            intro k hk
            by_cases hk0 : k = 0
            · subst k
              rw [ite_eq_left rfl, pow_zero, mul_one]
            · cases k with
              | zero => contradiction
              | succ k =>
                  rw [ite_eq_right (by omega), pow_succ, mul_zero, mul_zero]
      _ = 0 + C (a.coeff 0) :=
        List.foldl_add_single _ _ _ _ (List.mem_range.mpr hn) List.nodup_range
      _ = C (a.coeff 0) := by grind
  · apply ext
    intro i hi
    omega

/-- Substituting into the one series gives one. -/
@[simp]
theorem comp_one [Lean.Grind.CommRing R] (b : TSeries R n)
    (h : b.coeff 0 = 0) : comp 1 b = 1 := by
  rw [← C_one, comp_C 1 b h, C_one]

/-- Substitution preserves natural powers. -/
theorem comp_pow [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : b.coeff 0 = 0) (k : Nat) : comp (a ^ k) b = (comp a b) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, comp_one b h]
  | succ k ih => rw [pow_succ, pow_succ, comp_mul _ _ b h, ih]

/-- Substitution by a zero-constant series preserves the outer constant
coefficient. -/
theorem coeff_comp_zero [Lean.Grind.CommRing R] (a b : TSeries R n)
    (h : b.coeff 0 = 0) : (comp a b).coeff 0 = a.coeff 0 := by
  by_cases hn : 0 < n
  · rw [comp_spec a b h]
    change ((List.range n).foldl
      (fun acc k => acc + C (a.coeff k) * b ^ k) 0).coeff 0 = a.coeff 0
    rw [coeff_foldl_add (List.range n)
      (fun k => C (a.coeff k) * b ^ k) 0 0 hn, coeff_zero]
    calc
      (List.range n).foldl
          (fun acc k => acc + (C (a.coeff k) * b ^ k).coeff 0) 0 =
        (List.range n).foldl
          (fun acc k => acc + if k = 0 then a.coeff 0 else 0) 0 := by
            apply List.foldl_add_congr
            intro k hk
            rw [coeff_C_mul _ _ 0 hn]
            by_cases hk0 : k = 0
            · subst k
              rw [pow_zero, coeff_one 0 hn, ite_eq_left rfl]
              grind
            · have hbzero := pow_vanish b h k 0 hn (by omega)
              rw [hbzero, ite_eq_right hk0]
              grind
      _ = 0 + a.coeff 0 :=
        List.foldl_add_single _ _ _ _ (List.mem_range.mpr hn) List.nodup_range
      _ = a.coeff 0 := by grind
  · unfold coeff
    rw [dite_eq_right hn, dite_eq_right hn]

/-- Substitution is associative when both inner series have zero constant
coefficient. -/
theorem comp_assoc [Lean.Grind.CommRing R] (a b c : TSeries R n)
    (hb : b.coeff 0 = 0) (hc : c.coeff 0 = 0) :
    comp (comp a b) c = comp a (comp b c) := by
  have hbc : (comp b c).coeff 0 = 0 := by rw [coeff_comp_zero b c hc, hb]
  rw [comp_spec a b hb, comp_spec a (comp b c) hbc]
  have hfold (xs : List Nat) (z z' : TSeries R n)
      (hz : comp z c = z') :
      comp (xs.foldl (fun acc k => acc + C (a.coeff k) * b ^ k) z) c =
        xs.foldl
          (fun acc k => acc + C (a.coeff k) * (comp b c) ^ k) z' := by
    induction xs generalizing z z' with
    | nil => exact hz
    | cons k ks ih =>
        simp only [List.foldl_cons]
        apply ih
        rw [comp_add z _ c hc, hz, comp_mul _ _ c hc,
          comp_C _ c hc, comp_pow b c hc k]
  exact hfold (List.range n) 0 0 (comp_zero c hc)

namespace Agree

/-- Substitution by prefix-agreeing zero-constant inner series produces
prefix-agreeing results. -/
theorem comp_inner [Lean.Grind.CommRing R] {p : Nat}
    (a b b' : TSeries R n) (hb : Agree p b b')
    (h0 : b.coeff 0 = 0) (h0' : b'.coeff 0 = 0) :
    Agree p (comp a b) (comp a b') := by
  rw [comp_spec a b h0, comp_spec a b' h0']
  have go (xs : List Nat) (z z' : TSeries R n) (hz : Agree p z z') :
      Agree p
        (xs.foldl (fun acc k => acc + C (a.coeff k) * b ^ k) z)
        (xs.foldl (fun acc k => acc + C (a.coeff k) * b' ^ k) z') := by
    induction xs generalizing z z' with
    | nil => exact hz
    | cons k ks ih =>
        simp only [List.foldl_cons]
        exact ih _ _ (add hz
          (mul (refl p (C (a.coeff k))) (pow hb k)))
  exact go (List.range n) 0 0 (refl p 0)

/-- Bounded substitution agrees with full substitution throughout its work
prefix. -/
theorem compUpTo [Lean.Grind.CommRing R] (p : Nat)
    (a b : TSeries R n) (h : b.coeff 0 = 0) :
    Agree p (Hex.TSeries.compUpTo p a b) (comp a b) := by
  intro i hi hip
  rw [coeff_compUpTo p a b h i hi, ite_eq_left hip]

end Agree

end Hex.TSeries
