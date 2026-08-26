/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Smith

public section

/-! The fixed gcd/lcm network for diagonal Smith input. -/

namespace Hex.Matrix
namespace Smith.Diagonal

/-- First nonzero diagonal position at or after `start`. -/
@[expose]
def findNonzero? (M : Matrix Int r r) (start : Nat) : Option (Fin r) :=
  (List.finRange r).find? fun i =>
    decide (start ≤ i.val) && decide (M[(i, i)] ≠ 0)

/-- Swap the same pair of rows and columns, preserving diagonality. -/
@[expose]
def swap (ops : Smith.Accumulator α r r) (s : Smith.Result α r r)
    (i j : Fin r) : Smith.Result α r r :=
  Smith.swapCols ops (Smith.swapRows ops s i j) i j

/-- Move nonzero diagonal entries stably before zeros and make them positive. -/
@[expose]
def normalizeFuel (ops : Smith.Accumulator α r r) :
    Nat → Nat → Smith.Result α r r → Smith.Result α r r
  | 0, _, s => s
  | fuel + 1, target, s =>
      if ht : target < r then
        match findNonzero? s.matrix target with
        | none => s
        | some found =>
            let pivot : Fin r := ⟨target, ht⟩
            let moved := swap ops s pivot found
            let p := moved.matrix[(pivot, pivot)]
            let normalized :=
              if p < 0 then
                { moved with
                  matrix := Matrix.rowScale moved.matrix pivot (-1)
                  accumulator := ops.rowNegate moved.accumulator pivot }
              else moved
            normalizeFuel ops fuel (target + 1) normalized
      else s

/-- Normalization phase for diagonal input. -/
@[expose]
def normalize (ops : Smith.Accumulator α r r) (s : Smith.Result α r r) :
    Smith.Result α r r :=
  normalizeFuel ops r 0 s

/-- Replace one positive adjacent pair `(a,b)` by `(gcd a b, lcm a b)`
using the determinant-one three-operation factorization from the SPEC. -/
@[expose]
def pairStep (ops : Smith.Accumulator α r r) (s : Smith.Result α r r)
    (i j : Fin r) : Smith.Result α r r :=
  let a := s.matrix[(i, i)]
  let b := s.matrix[(j, j)]
  if a = 0 then
    if b = 0 then s else swap ops s i j
  else if b = 0 then s
  else if a = b then s
  else
    let rowAdded : Smith.Result α r r :=
      { s with
        matrix := Matrix.rowAdd s.matrix j i 1
        accumulator := ops.rowAdd s.accumulator j i 1 }
    let (g, u, v) := HexArith.Int.extGcd a b
    let g' := Int.ofNat g
    let qa := HexArith.Int.exactDiv a g'
    let qb := HexArith.Int.exactDiv b g'
    let columns : Smith.Result α r r :=
      { rowAdded with
        matrix := Hermite.combineCols rowAdded.matrix i j u v (-qb) qa
        accumulator := ops.colCombine rowAdded.accumulator i j u v (-qb) qa }
    let c := -(HexArith.Int.exactDiv (b * v) g')
    { columns with
      matrix := Matrix.rowAdd columns.matrix i j c
      accumulator := ops.rowAdd columns.accumulator i j c }

/-- Execute consecutive adjacent pair steps beginning at `index`. -/
@[expose]
def passFuel (ops : Smith.Accumulator α r r) :
    Nat → Nat → Smith.Result α r r → Smith.Result α r r
  | 0, _, s => s
  | fuel + 1, index, s =>
      if h : index + 1 < r then
        passFuel ops fuel (index + 1)
          (pairStep ops s ⟨index, by omega⟩ ⟨index + 1, h⟩)
      else s

/-- One complete adjacent pass. -/
@[expose]
def pass (ops : Smith.Accumulator α r r) (s : Smith.Result α r r) :
    Smith.Result α r r :=
  passFuel ops (r - 1) 0 s

/-- A fixed `r`-pass bubble network simultaneously sorts every prime
valuation and therefore produces a divisibility chain. -/
@[expose]
def networkFuel (ops : Smith.Accumulator α r r) :
    Nat → Smith.Result α r r → Smith.Result α r r
  | 0, s => s
  | fuel + 1, s => networkFuel ops fuel (pass ops s)

/-- Extract the nonzero prefix after normalization and the network. -/
@[expose]
def collect (M : Matrix Int r r) : List Int :=
  (List.finRange r).filterMap fun i =>
    let d := M[(i, i)]
    if d = 0 then none else some d

/-- Run the diagonal-specific schedule with the requested companion. -/
@[expose]
def run (ops : Smith.Accumulator α r r) (d : Vector Int r) :
    Smith.Result α r r :=
  let initial : Smith.Result α r r :=
    { matrix := diagMatrix d r r, diag := [], accumulator := ops.init }
  let result := networkFuel ops r (normalize ops initial)
  { result with diag := collect result.matrix }

end Smith.Diagonal

namespace Smith.Diagonal

/-- The decidable shape predicate that the compact diagonal run is proved to
satisfy. It contains only the working matrix and diagonal list, so reasoning
about the form-only path does not introduce transform matrices. -/
@[expose]
def Valid (s : Smith.Result α r r) : Prop :=
  s.diag.length ≤ r ∧
  s.matrix = diagMatrix s.diagVector r r ∧
  (∀ i : Fin s.diag.length, 0 < s.diagVector[i]) ∧
  (∀ i : Fin (s.diag.length - 1),
    s.diagVector[(⟨i.val, by omega⟩ : Fin s.diag.length)] ∣
      s.diagVector[(⟨i.val + 1, by omega⟩ : Fin s.diag.length)])

instance (s : Smith.Result α r r) : Decidable (Valid s) := by
  unfold Valid
  infer_instance

/-- Agreement of diagonal runs after erasing their companion accumulators. -/
structure Same (s : Smith.Result α r r) (t : Smith.Result β r r) : Prop where
  matrix : s.matrix = t.matrix
  diag : s.diag = t.diag

/-- Shape validation depends only on the erased matrix and diagonal list. -/
theorem Valid.congr {s : Smith.Result α r r} {t : Smith.Result β r r}
    (h : Same s t) : Valid s ↔ Valid t := by
  rcases s with ⟨matrix, diag, acc⟩
  rcases t with ⟨matrix', diag', acc'⟩
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem swap_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) {s : Smith.Result α r r}
    {t : Smith.Result β r r} (h : Same s t) (i j : Fin r) :
    Same (swap ops s i j) (swap ops' t i j) := by
  rcases s with ⟨matrix, diag, acc⟩
  rcases t with ⟨matrix', diag', acc'⟩
  rcases h with ⟨rfl, rfl⟩
  by_cases hij : i = j
  · simp only [swap, Smith.swapRows, Smith.swapCols, if_pos hij]
    exact ⟨rfl, rfl⟩
  · simp only [swap, Smith.swapRows, Smith.swapCols, if_neg hij]
    exact ⟨rfl, rfl⟩

private theorem normalizeFuel_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (fuel target : Nat)
    {s : Smith.Result α r r} {t : Smith.Result β r r} (h : Same s t) :
    Same (normalizeFuel ops fuel target s)
      (normalizeFuel ops' fuel target t) := by
  induction fuel generalizing target s t with
  | zero => exact h
  | succ fuel ih =>
      rcases s with ⟨matrix, diag, acc⟩
      rcases t with ⟨matrix', diag', acc'⟩
      rcases h with ⟨rfl, rfl⟩
      rw [normalizeFuel, normalizeFuel]
      by_cases ht : target < r
      · rw [dif_pos ht, dif_pos ht]
        cases hf : findNonzero? matrix target with
        | none => simp only [hf]; exact ⟨rfl, rfl⟩
        | some found =>
            simp only [hf]
            let pivot : Fin r := ⟨target, ht⟩
            have hmoved := swap_same ops ops'
              (⟨rfl, rfl⟩ : Same
                ({ matrix := matrix, diag := diag, accumulator := acc } : Smith.Result α r r)
                ({ matrix := matrix, diag := diag, accumulator := acc' } : Smith.Result β r r))
              pivot found
            rcases hmoved with ⟨hmatrix, hdiag⟩
            by_cases hp : (swap ops
                ({ matrix := matrix, diag := diag, accumulator := acc } : Smith.Result α r r)
                pivot found).matrix[(pivot, pivot)] < 0
            · simp only [pivot] at hp hmatrix hdiag ⊢
              rw [if_pos hp]
              have hp' : (swap ops'
                  ({ matrix := matrix, diag := diag, accumulator := acc' } : Smith.Result β r r)
                  ⟨target, ht⟩ found).matrix[
                    ((⟨target, ht⟩ : Fin r), (⟨target, ht⟩ : Fin r))] < 0 := by
                rw [← hmatrix]
                exact hp
              rw [if_pos hp']
              apply ih
              exact ⟨congrArg (fun M => Matrix.rowScale M ⟨target, ht⟩ (-1)) hmatrix,
                hdiag⟩
            · simp only [pivot] at hp hmatrix hdiag ⊢
              rw [if_neg hp]
              have hp' : ¬ (swap ops'
                  ({ matrix := matrix, diag := diag, accumulator := acc' } : Smith.Result β r r)
                  ⟨target, ht⟩ found).matrix[
                    ((⟨target, ht⟩ : Fin r), (⟨target, ht⟩ : Fin r))] < 0 := by
                rw [← hmatrix]
                exact hp
              rw [if_neg hp']
              exact ih (target + 1) ⟨hmatrix, hdiag⟩
      · rw [dif_neg ht, dif_neg ht]
        exact ⟨rfl, rfl⟩

private theorem pairStep_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) {s : Smith.Result α r r}
    {t : Smith.Result β r r} (h : Same s t) (i j : Fin r) :
    Same (pairStep ops s i j) (pairStep ops' t i j) := by
  rcases s with ⟨matrix, diag, acc⟩
  rcases t with ⟨matrix', diag', acc'⟩
  rcases h with ⟨rfl, rfl⟩
  simp only [pairStep, Matrix.getElem_pair_eq_nested]
  by_cases ha : matrix[i][i] = 0
  · rw [if_pos ha, if_pos ha]
    by_cases hb : matrix[j][j] = 0
    · rw [if_pos hb, if_pos hb]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb, if_neg hb]
      exact swap_same ops ops' ⟨rfl, rfl⟩ i j
  · rw [if_neg ha, if_neg ha]
    by_cases hb : matrix[j][j] = 0
    · rw [if_pos hb, if_pos hb]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hb, if_neg hb]
      by_cases hab : matrix[i][i] = matrix[j][j]
      · rw [if_pos hab, if_pos hab]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hab, if_neg hab]
        exact ⟨rfl, rfl⟩

private theorem passFuel_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (fuel index : Nat)
    {s : Smith.Result α r r} {t : Smith.Result β r r} (h : Same s t) :
    Same (passFuel ops fuel index s) (passFuel ops' fuel index t) := by
  induction fuel generalizing index s t with
  | zero => exact h
  | succ fuel ih =>
      rw [passFuel, passFuel]
      by_cases hi : index + 1 < r
      · rw [dif_pos hi, dif_pos hi]
        exact ih (index + 1) (pairStep_same ops ops' h
          ⟨index, by omega⟩ ⟨index + 1, hi⟩)
      · rw [dif_neg hi, dif_neg hi]
        exact h

private theorem pass_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) {s : Smith.Result α r r}
    {t : Smith.Result β r r} (h : Same s t) :
    Same (pass ops s) (pass ops' t) := by
  unfold pass
  exact passFuel_same ops ops' (r - 1) 0 h

private theorem networkFuel_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (fuel : Nat)
    {s : Smith.Result α r r} {t : Smith.Result β r r} (h : Same s t) :
    Same (networkFuel ops fuel s) (networkFuel ops' fuel t) := by
  induction fuel generalizing s t with
  | zero => exact h
  | succ fuel ih =>
      rw [networkFuel.eq_def, networkFuel.eq_def]
      exact ih (pass_same ops ops' h)

/-- Every companion follows the same fixed diagonal schedule. -/
theorem run_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (d : Vector Int r) :
    Same (run ops d) (run ops' d) := by
  unfold run normalize
  have hnorm := normalizeFuel_same ops ops' r 0
    (⟨rfl, rfl⟩ : Same
      ({ matrix := diagMatrix d r r, diag := [], accumulator := ops.init } : Smith.Result α r r)
      ({ matrix := diagMatrix d r r, diag := [], accumulator := ops'.init } : Smith.Result β r r))
  have hnet := networkFuel_same ops ops' r hnorm
  exact ⟨hnet.matrix, congrArg collect hnet.matrix⟩

/-! # The divisibility bubble network

The executable matrix and compact engines below implement this elementary
list network.  Keeping its order argument separate makes the reason for the
fixed `r` passes explicit: one pass produces a greatest final element for
divisibility, and later passes act only on the remaining prefix. -/

namespace Bubble

/-- Carry one value from left to right using `(gcd, lcm)` comparators. -/
def carry : Nat → List Nat → List Nat
  | a, [] => [a]
  | a, b :: xs => Nat.gcd a b :: carry (Nat.lcm a b) xs

/-- One complete left-to-right adjacent gcd/lcm pass. -/
def pass : List Nat → List Nat
  | [] => []
  | a :: xs => carry a xs

/-- Iterate complete passes. -/
def network : Nat → List Nat → List Nat
  | 0, xs => xs
  | fuel + 1, xs => network fuel (pass xs)

/-- Every element of `xs` divides `z`. -/
def AllDvd (xs : List Nat) (z : Nat) : Prop := ∀ x ∈ xs, x ∣ z

/-- Adjacent divisibility along a list. -/
def Chain : List Nat → Prop
  | [] | [_] => True
  | a :: b :: xs => a ∣ b ∧ Chain (b :: xs)

private theorem carry_length (a : Nat) (xs : List Nat) :
    (carry a xs).length = xs.length + 1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => simp [carry, ih]

private theorem pass_length (xs : List Nat) : (pass xs).length = xs.length := by
  cases xs with
  | nil => rfl
  | cons a xs => simp [pass, carry_length]

private theorem carry_allDvd {a z : Nat} {xs : List Nat}
    (ha : a ∣ z) (hxs : AllDvd xs z) : AllDvd (carry a xs) z := by
  induction xs generalizing a with
  | nil => simpa [carry, AllDvd] using ha
  | cons b xs ih =>
      have hb : b ∣ z := hxs b (by simp)
      have htail : AllDvd xs z := by
        intro x hx
        exact hxs x (by simp [hx])
      have hlcm : Nat.lcm a b ∣ z := Nat.lcm_dvd ha hb
      intro x hx
      simp only [carry, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.dvd_trans (Nat.gcd_dvd_left a b) ha
      · exact ih hlcm htail x hx

private theorem pass_allDvd {xs : List Nat} {z : Nat}
    (h : AllDvd xs z) : AllDvd (pass xs) z := by
  cases xs with
  | nil => simpa [pass, AllDvd]
  | cons a xs =>
      apply carry_allDvd
      · exact h a (by simp)
      · intro x hx
        exact h x (by simp [hx])

private theorem carry_append {a z : Nat} {xs : List Nat}
    (ha : a ∣ z) (hxs : AllDvd xs z) :
    carry a (xs ++ [z]) = carry a xs ++ [z] := by
  induction xs generalizing a with
  | nil =>
      simp only [List.nil_append, carry, List.cons_append, List.nil_append]
      rw [Nat.gcd_eq_left_iff_dvd.mpr ha, Nat.lcm_eq_right_iff_dvd.mpr ha]
  | cons b xs ih =>
      have hb : b ∣ z := hxs b (by simp)
      have htail : AllDvd xs z := by
        intro x hx
        exact hxs x (by simp [hx])
      have hlcm : Nat.lcm a b ∣ z := Nat.lcm_dvd ha hb
      simp only [List.cons_append, carry, List.cons.injEq, true_and]
      exact ih hlcm htail

private theorem pass_append {xs : List Nat} {z : Nat}
    (h : AllDvd xs z) : pass (xs ++ [z]) = pass xs ++ [z] := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      simp only [List.cons_append, pass]
      apply carry_append
      · exact h a (by simp)
      · intro x hx
        exact h x (by simp [hx])

private theorem network_append (fuel : Nat) {xs : List Nat} {z : Nat}
    (h : AllDvd xs z) :
    network fuel (xs ++ [z]) = network fuel xs ++ [z] := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
      calc
        network (fuel + 1) (xs ++ [z]) =
            network fuel (pass (xs ++ [z])) := rfl
        _ = network fuel (pass xs ++ [z]) := by rw [pass_append h]
        _ = network fuel (pass xs) ++ [z] := ih (pass_allDvd h)
        _ = network (fuel + 1) xs ++ [z] := rfl

private theorem network_allDvd (fuel : Nat) {xs : List Nat} {z : Nat}
    (h : AllDvd xs z) : AllDvd (network fuel xs) z := by
  induction fuel generalizing xs with
  | zero => exact h
  | succ fuel ih =>
      rw [network]
      exact ih (pass_allDvd h)

private theorem carry_split (a : Nat) (xs : List Nat) :
    ∃ ys z, carry a xs = ys ++ [z] ∧ ys.length = xs.length ∧
      a ∣ z ∧ AllDvd ys z := by
  induction xs generalizing a with
  | nil => exact ⟨[], a, rfl, rfl, Nat.dvd_refl a, by simp [AllDvd]⟩
  | cons b xs ih =>
      obtain ⟨ys, z, hcarry, hlen, hlead, hall⟩ := ih (Nat.lcm a b)
      refine ⟨Nat.gcd a b :: ys, z, ?_, by simp [hlen], ?_, ?_⟩
      · simp only [carry, List.cons_append, List.cons.injEq, true_and]
        exact hcarry
      · exact Nat.dvd_trans (Nat.dvd_lcm_left a b) hlead
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Nat.dvd_trans (Nat.gcd_dvd_left a b)
            (Nat.dvd_trans (Nat.dvd_lcm_left a b) hlead)
        · exact hall x hx

private theorem pass_split {a : Nat} {xs : List Nat} :
    ∃ ys z, pass (a :: xs) = ys ++ [z] ∧ ys.length = xs.length ∧
      AllDvd ys z := by
  obtain ⟨ys, z, hcarry, hlen, _hlead, hall⟩ := carry_split a xs
  exact ⟨ys, z, hcarry, hlen, hall⟩

private theorem chain_append {xs : List Nat} {z : Nat}
    (hc : Chain xs) (hd : AllDvd xs z) : Chain (xs ++ [z]) := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      cases xs with
      | nil =>
          simpa [Chain] using hd a (by simp)
      | cons b xs =>
          simp only [Chain] at hc ⊢
          exact ⟨hc.1, ih hc.2 (by
            intro x hx
            exact hd x (by simp [hx]))⟩

private theorem network_chain_length (n : Nat) (xs : List Nat)
    (hlen : xs.length = n) : Chain (network n xs) := by
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil =>
          subst n
          trivial
      | cons a xs =>
          have hn : n = xs.length + 1 := by simpa using hlen.symm
          obtain ⟨ys, z, hpass, hys, hall⟩ := pass_split (a := a) (xs := xs)
          have hlt : ys.length < n := by omega
          have hchain := ih ys.length hlt ys rfl
          rw [hys] at hchain
          rw [hn, network, hpass, network_append xs.length hall]
          exact chain_append hchain (by
            simpa [hys] using network_allDvd xs.length hall)

/-- `length xs` complete adjacent passes always produce a divisibility
chain. -/
theorem network_chain (xs : List Nat) : Chain (network xs.length xs) :=
  network_chain_length xs.length xs rfl

/-- The same comparator network on a fixed-length vector. -/
@[expose]
def vectorStep (v : Vector Nat r) (i j : Fin r) : Vector Nat r :=
  (v.set i.val (Nat.gcd v[i] v[j]) i.isLt).set j.val
    (Nat.lcm v[i] v[j]) j.isLt

@[expose]
def vectorPassFuel : Nat → Nat → Vector Nat r → Vector Nat r
  | 0, _, v => v
  | fuel + 1, index, v =>
      if h : index + 1 < r then
        vectorPassFuel fuel (index + 1)
          (vectorStep v ⟨index, by omega⟩ ⟨index + 1, h⟩)
      else v

@[expose]
def vectorPass (v : Vector Nat r) : Vector Nat r :=
  vectorPassFuel (r - 1) 0 v

@[expose]
def vectorNetwork : Nat → Vector Nat r → Vector Nat r
  | 0, v => v
  | fuel + 1, v => vectorNetwork fuel (vectorPass v)

private theorem vectorPassFuel_toList (fuel index : Nat) (v : Vector Nat r)
    (hsize : index + fuel + 1 = r) :
    (vectorPassFuel fuel index v).toList =
      v.toList.take index ++ carry (v[index]'(by omega))
        (v.toList.drop (index + 1)) := by
  induction fuel generalizing index v with
  | zero =>
      have hi : index < r := by omega
      rw [vectorPassFuel]
      have hdrop : v.toList.drop (index + 1) = [] := by
        apply List.drop_eq_nil_of_le
        have : v.toList.length ≤ index + 1 := by simp; omega
        exact this
      calc
        v.toList = v.toList.take index ++ v.toList.drop index :=
          (List.take_append_drop index v.toList).symm
        _ = v.toList.take index ++
            v.toList[index]'(by simpa using hi) :: v.toList.drop (index + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hi)]
        _ = v.toList.take index ++
            v[index] :: v.toList.drop (index + 1) := by
          rw [Vector.getElem_toList]
        _ = v.toList.take index ++ carry v[index] (v.toList.drop (index + 1)) := by
          rw [hdrop]
          rfl
  | succ fuel ih =>
      rw [vectorPassFuel]
      have hi : index + 1 < r := by omega
      rw [dif_pos hi]
      let i : Fin r := ⟨index, by omega⟩
      let j : Fin r := ⟨index + 1, hi⟩
      let w := vectorStep v i j
      rw [ih (index + 1) w (by omega)]
      have hir : index < r := by omega
      have hmin : min index r = index := Nat.min_eq_left (Nat.le_of_lt hir)
      have htake : w.toList.take (index + 1) =
          v.toList.take index ++ [Nat.gcd v[index] v[index + 1]] := by
        apply List.ext_getElem
        · simp
          omega
        · intro k hk hk'
          by_cases hkpre : k < index
          · have hki : k ≠ index := by omega
            have hkj : k ≠ index + 1 := by omega
            have hik : index ≠ k := Ne.symm hki
            have hjk : index + 1 ≠ k := Ne.symm hkj
            simp [List.getElem_append, hkpre, w, vectorStep, i, j,
              Vector.getElem_set, hki, hkj, hik, hjk, hir, hi, hmin]
          · have hkeq : k = index := by simp at hk hk'; omega
            subst k
            simp [List.getElem_append, w, vectorStep, i, j,
              Vector.getElem_set, hir, hi, hmin]
      have hget : w[index + 1] = Nat.lcm v[index] v[index + 1] := by
        simp [w, vectorStep, i, j, Vector.getElem_set, hir, hi]
      have hdrop : w.toList.drop (index + 1 + 1) =
          v.toList.drop (index + 1 + 1) := by
        apply List.ext_getElem
        · simp
        · intro k hk hk'
          have hki : index + 1 + 1 + k ≠ index := by omega
          have hkj : index + 1 + 1 + k ≠ index + 1 := by omega
          have hik : index ≠ index + 1 + 1 + k := Ne.symm hki
          have hjk : index + 1 ≠ index + 1 + 1 + k := Ne.symm hkj
          simp [w, vectorStep, i, j, Vector.getElem_set, hir, hi,
            hki, hkj, hik, hjk]
      rw [htake, hget, hdrop]
      have hsplit : v.toList.drop (index + 1) =
          v[index + 1] :: v.toList.drop (index + 1 + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hi)]
        rw [Vector.getElem_toList]
      rw [hsplit]
      simp [carry, List.append_assoc]

theorem vectorPass_toList (v : Vector Nat r) :
    (vectorPass v).toList = pass v.toList := by
  cases r with
  | zero =>
      unfold vectorPass pass
      simp only [Nat.zero_sub, vectorPassFuel]
      cases hvalues : v.toList with
      | nil => rfl
      | cons a xs =>
          have hlen : v.toList.length = 0 := by simp
          simp [hvalues] at hlen
  | succ r =>
      cases hvalues : v.toList with
      | nil =>
          have hlen : v.toList.length = r + 1 := by simp
          simp [hvalues] at hlen
      | cons a xs =>
          have ha : v[0] = a := by
            have hzero : v.toList[0] = a := by simp [hvalues]
            rw [Vector.getElem_toList] at hzero
            exact hzero
          unfold vectorPass pass
          simpa [hvalues, ha] using
            vectorPassFuel_toList r 0 v (by omega)

theorem vectorNetwork_toList (fuel : Nat) (v : Vector Nat r) :
    (vectorNetwork fuel v).toList = network fuel v.toList := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
      rw [vectorNetwork, network, ih, vectorPass_toList]

theorem vectorNetwork_chain (v : Vector Nat r) :
    Chain (vectorNetwork r v).toList := by
  rw [vectorNetwork_toList]
  simpa using network_chain v.toList

/-- Remove the zero suffix from a natural-number chain. -/
@[expose]
def nonzeros : List Nat → List Nat
  | [] => []
  | x :: xs => if x = 0 then [] else x :: nonzeros xs

@[simp] private theorem nonzeros_replicate_zero (n : Nat) :
    nonzeros (List.replicate n 0) = [] := by
  cases n with
  | zero => rfl
  | succ n => rw [List.replicate_succ, nonzeros, if_pos rfl]

private theorem chain_zero_all {xs : List Nat} (h : Chain (0 :: xs)) :
    ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [Chain] at h
      have ha : a = 0 := by simpa using h.1
      subst a
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact ih h.2 x hx

private theorem all_zero_replicate (xs : List Nat)
    (h : ∀ x ∈ xs, x = 0) : xs = List.replicate xs.length 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have ha : a = 0 := h a (by simp)
      subst a
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
      apply ih
      intro x hx
      exact h x (by simp [hx])

/-- A divisibility chain is its nonzero prefix followed by zeros; the retained
prefix is positive and remains a divisibility chain. -/
theorem chain_split (xs : List Nat) (h : Chain xs) :
    ∃ k,
      xs = nonzeros xs ++ List.replicate k 0 ∧
      Chain (nonzeros xs) ∧
      (∀ x ∈ nonzeros xs, 0 < x) := by
  induction xs with
  | nil => exact ⟨0, by simp [nonzeros], by simp [nonzeros, Chain], by simp [nonzeros]⟩
  | cons a xs ih =>
      cases xs with
      | nil =>
          by_cases ha : a = 0
          · subst a
            exact ⟨1, by simp [nonzeros], by simp [nonzeros, Chain], by
              simp [nonzeros]⟩
          · exact ⟨0, by simp [nonzeros, ha], by simp [nonzeros, ha, Chain], by
              intro x hx
              simp [nonzeros, ha] at hx
              subst x
              omega⟩
      | cons b xs =>
          simp only [Chain] at h
          by_cases ha : a = 0
          · subst a
            have hb : b = 0 := by simpa using h.1
            subst b
            have hall : ∀ x ∈ 0 :: 0 :: xs, x = 0 := by
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | rfl | hx
              · rfl
              · rfl
              · exact chain_zero_all h.2 x hx
            have hrep := all_zero_replicate (0 :: 0 :: xs) hall
            refine ⟨(0 :: 0 :: xs).length, ?_, by simp [nonzeros, Chain], ?_⟩
            · rw [hrep]
              simp
            · intro x hx
              rw [hrep] at hx
              simp at hx
          · obtain ⟨k, hsplit, hchain, hpos⟩ := ih h.2
            refine ⟨k, ?_, ?_, ?_⟩
            · rw [nonzeros, if_neg ha]
              simpa only [List.cons_append] using congrArg (List.cons a) hsplit
            · by_cases hb : b = 0
              · subst b
                simp [nonzeros, ha, Chain]
              · simp only [nonzeros, if_neg ha, if_neg hb, Chain] at hchain ⊢
                exact ⟨h.1, hchain⟩
            · intro x hx
              rw [nonzeros, if_neg ha] at hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · omega
              · exact hpos x hx

/-- Any adjacent pair in a chain satisfies divisibility. -/
theorem chain_get {xs : List Nat} (h : Chain xs) (i : Nat)
    (hi : i + 1 < xs.length) : xs[i]'(by omega) ∣ xs[i + 1]'hi := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases xs with
      | nil => simp at hi
      | cons b xs =>
          simp only [Chain] at h
          cases i with
          | zero => simpa using h.1
          | succ i =>
              have hitail : i + 1 < (b :: xs).length := by
                simp only [List.length_cons] at hi ⊢
                omega
              simpa using ih h.2 i hitail

end Bubble

/-! # Compact executable engine

The proof-oriented engine above mirrors elementary matrix updates directly.
The public diagonal path uses the same decisions and accumulator operations
while keeping only the diagonal vector as working state, allocating the dense
form once at the end. -/

namespace Compact

/-- Diagonal values paired with the optional accumulator. -/
structure Result (α : Type) (r : Nat) where
  values : Vector Int r
  accumulator : α

/-- First nonzero value at or after `start`. -/
@[expose]
def findNonzero? (values : Vector Int r) (start : Nat) : Option (Fin r) :=
  (List.finRange r).find? fun i =>
    decide (start ≤ i.val) && decide (values[i] ≠ 0)

/-- Swap diagonal positions and apply the matching row and column swaps. -/
@[expose]
def swap (ops : Smith.Accumulator α r r) (s : Result α r)
    (i j : Fin r) : Result α r :=
  if i = j then s
  else
    { values := s.values.swap i.val j.val i.isLt j.isLt
      accumulator := ops.colSwap (ops.rowSwap s.accumulator i j) i j }

/-- Move nonzeros before zeros and make each moved pivot positive. -/
@[expose]
def normalizeFuel (ops : Smith.Accumulator α r r) :
    Nat → Nat → Result α r → Result α r
  | 0, _, s => s
  | fuel + 1, target, s =>
      if ht : target < r then
        match findNonzero? s.values target with
        | none => s
        | some found =>
            let pivot : Fin r := ⟨target, ht⟩
            let moved := swap ops s pivot found
            let p := moved.values[pivot]
            let normalized :=
              if p < 0 then
                { moved with
                  values := moved.values.set pivot.val (-p) pivot.isLt
                  accumulator := ops.rowNegate moved.accumulator pivot }
              else moved
            normalizeFuel ops fuel (target + 1) normalized
      else s

/-- Compact normalization phase. -/
@[expose]
def normalize (ops : Smith.Accumulator α r r) (s : Result α r) : Result α r :=
  normalizeFuel ops r 0 s

/-- Compact adjacent gcd/lcm update, with the same accumulator operations as
the proof-oriented matrix step. -/
@[expose]
def pairStep (ops : Smith.Accumulator α r r) (s : Result α r)
    (i j : Fin r) : Result α r :=
  let a := s.values[i]
  let b := s.values[j]
  if a = 0 then
    if b = 0 then s else swap ops s i j
  else if b = 0 then s
  else if a = b then s
  else
    let (g, u, v) := HexArith.Int.extGcd a b
    let g' := Int.ofNat g
    let qa := HexArith.Int.exactDiv a g'
    let qb := HexArith.Int.exactDiv b g'
    let c := -(HexArith.Int.exactDiv (b * v) g')
    { values := (s.values.set i.val g' i.isLt).set j.val
        (HexArith.Int.exactDiv (a * b) g') j.isLt
      accumulator := ops.rowAdd
        (ops.colCombine (ops.rowAdd s.accumulator j i 1)
          i j u v (-qb) qa) i j c }

/-- Form-only adjacent update. Keeping the vector as the sole recursive state
lets compiled `Vector.set` reuse its uniquely owned array instead of retaining
it through an irrelevant accumulator record. -/
@[expose]
def pairValues (values : Vector Int r) (i j : Fin r) : Vector Int r :=
  let a := values[i]
  let b := values[j]
  if a = 0 then
    if b = 0 then values else values.swap i.val j.val i.isLt j.isLt
  else if b = 0 then values
  else if a = b then values
  else
    let g' := Int.ofNat (HexArith.Int.extGcd a b).1
    (values.set i.val g' i.isLt).set j.val
      (HexArith.Int.exactDiv (a * b) g') j.isLt

/-- Array-only implementation of `pairValues`; the size proof is erased and
the tail-recursive callers retain unique ownership of the backing array. -/
@[expose]
def pairArray (values : Array Int) (hsize : values.size = r)
    (i j : Fin r) : Array Int :=
  let hi : i.val < values.size := by omega
  let hj : j.val < values.size := by omega
  let a := values[i.val]'hi
  let b := values[j.val]'hj
  if a = 0 then
    if b = 0 then values else values.swap i.val j.val hi hj
  else if b = 0 then values
  else if a = b then values
  else
    let g' := Int.ofNat (HexArith.Int.extGcd a b).1
    let first := values.set i.val g' hi
    first.set j.val (HexArith.Int.exactDiv (a * b) g') (by simpa [first] using hj)

theorem pairArray_size (values : Array Int) (hsize : values.size = r)
    (i j : Fin r) : (pairArray values hsize i j).size = r := by
  simp only [pairArray]
  by_cases ha : values[i.val]'(by omega) = 0
  · rw [if_pos ha]
    by_cases hb : values[j.val]'(by omega) = 0
    · rw [if_pos hb]; exact hsize
    · rw [if_neg hb]; simpa using hsize
  · rw [if_neg ha]
    by_cases hb : values[j.val]'(by omega) = 0
    · rw [if_pos hb]; exact hsize
    · rw [if_neg hb]
      split <;> simp [hsize]

private theorem pairArray_eq (values : Array Int) (hsize : values.size = r)
    (i j : Fin r) :
    pairArray values hsize i j = (pairValues ⟨values, hsize⟩ i j).toArray := by
  simp only [pairArray, pairValues, Fin.getElem_fin, Vector.getElem_mk]
  by_cases ha : values[i.val]'(by omega) = 0
  · simp only [ha, if_pos]
    by_cases hb : values[j.val]'(by omega) = 0
    · simp only [hb, if_pos]
    · simp [hb]
  · simp only [ha, if_neg]
    by_cases hb : values[j.val]'(by omega) = 0
    · simp [hb]
    · simp only [hb, if_neg]
      by_cases hab : values[i.val]'(by omega) = values[j.val]'(by omega)
      · simp [hab]
      · simp [hab]

/-- Array-only consecutive adjacent updates. -/
@[expose]
def passArrayFuel : (fuel index : Nat) → (values : Array Int) →
    values.size = r → Array Int
  | 0, _, values, _ => values
  | fuel + 1, index, values, hsize =>
      if h : index + 1 < r then
        let next := pairArray values hsize ⟨index, by omega⟩ ⟨index + 1, h⟩
        passArrayFuel fuel (index + 1) next (pairArray_size values hsize _ _)
      else values

theorem passArrayFuel_size (fuel index : Nat) (values : Array Int)
    (hsize : values.size = r) :
    (passArrayFuel fuel index values hsize).size = r := by
  induction fuel generalizing index values with
  | zero => exact hsize
  | succ fuel ih =>
      rw [passArrayFuel]
      split
      · exact ih _ _ (pairArray_size values hsize _ _)
      · exact hsize

/-- Array-only fixed bubble network. -/
@[expose]
def networkArrayFuel : (fuel : Nat) → (values : Array Int) →
    values.size = r → Array Int
  | 0, values, _ => values
  | fuel + 1, values, hsize =>
      let next := passArrayFuel (r - 1) 0 values hsize
      networkArrayFuel fuel next (passArrayFuel_size (r - 1) 0 values hsize)

theorem networkArrayFuel_size (fuel : Nat) (values : Array Int)
    (hsize : values.size = r) :
    (networkArrayFuel fuel values hsize).size = r := by
  induction fuel generalizing values with
  | zero => exact hsize
  | succ fuel ih =>
      rw [networkArrayFuel]
      exact ih _ (passArrayFuel_size (r - 1) 0 values hsize)

private theorem pairValues_eq (ops : Smith.Accumulator α r r) (s : Result α r)
    (i j : Fin r) : pairValues s.values i j = (pairStep ops s i j).values := by
  simp only [pairValues, pairStep]
  by_cases ha : s.values[i] = 0
  · rw [if_pos ha, if_pos ha]
    by_cases hb : s.values[j] = 0
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, swap]
      split
      · rename_i hij
        subst j
        exact (hb ha).elim
      · rfl
  · rw [if_neg ha, if_neg ha]
    by_cases hb : s.values[j] = 0
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      by_cases hab : s.values[i] = s.values[j]
      · rw [if_pos hab, if_pos hab]
      · rw [if_neg hab, if_neg hab]

/-- Consecutive form-only adjacent updates. -/
@[expose]
def passValuesFuel : Nat → Nat → Vector Int r → Vector Int r
  | 0, _, values => values
  | fuel + 1, index, values =>
      if h : index + 1 < r then
        passValuesFuel fuel (index + 1)
          (pairValues values ⟨index, by omega⟩ ⟨index + 1, h⟩)
      else values

/-- One form-only adjacent pass. -/
@[expose]
def passValues (values : Vector Int r) : Vector Int r :=
  passValuesFuel (r - 1) 0 values

/-- Fixed form-only bubble network. -/
@[expose]
def networkValuesFuel : Nat → Vector Int r → Vector Int r
  | 0, values => values
  | fuel + 1, values => networkValuesFuel fuel (passValues values)

/-- Run normalization once, then the accumulator-free diagonal network. -/
@[expose]
def runValues (d : Vector Int r) : Vector Int r :=
  let normalized := normalize (Smith.formAccumulator r r)
    ({ values := d, accumulator := () } : Result Unit r)
  let values := networkArrayFuel r normalized.values.toArray normalized.values.size_toArray
  ⟨values, networkArrayFuel_size r _ normalized.values.size_toArray⟩

/-- Execute consecutive compact adjacent steps beginning at `index`. -/
@[expose]
def passFuel (ops : Smith.Accumulator α r r) :
    Nat → Nat → Result α r → Result α r
  | 0, _, s => s
  | fuel + 1, index, s =>
      if h : index + 1 < r then
        passFuel ops fuel (index + 1)
          (pairStep ops s ⟨index, by omega⟩ ⟨index + 1, h⟩)
      else s

/-- One full compact adjacent pass. -/
@[expose]
def pass (ops : Smith.Accumulator α r r) (s : Result α r) : Result α r :=
  passFuel ops (r - 1) 0 s

/-- Fixed compact bubble network. -/
@[expose]
def networkFuel (ops : Smith.Accumulator α r r) :
    Nat → Result α r → Result α r
  | 0, s => s
  | fuel + 1, s => networkFuel ops fuel (pass ops s)

/-- Extract the positive prefix represented by the final diagonal vector. -/
@[expose]
def collect (values : Vector Int r) : List Int :=
  values.toList.takeWhile fun d => decide (d ≠ 0)

/-- Run the compact diagonal schedule with the requested accumulator. -/
@[expose]
def run (ops : Smith.Accumulator α r r) (d : Vector Int r) : Result α r :=
  networkFuel ops r (normalize ops { values := d, accumulator := ops.init })

private theorem passValuesFuel_eq (ops : Smith.Accumulator α r r)
    (fuel index : Nat) (s : Result α r) :
    passValuesFuel fuel index s.values = (passFuel ops fuel index s).values := by
  induction fuel generalizing index s with
  | zero => rfl
  | succ fuel ih =>
      rw [passValuesFuel, passFuel]
      split
      · rw [pairValues_eq]
        exact ih _ _
      · rfl

private theorem passValues_eq (ops : Smith.Accumulator α r r) (s : Result α r) :
    passValues s.values = (pass ops s).values := by
  exact passValuesFuel_eq ops (r - 1) 0 s

private theorem passArrayFuel_eq (fuel index : Nat) (values : Array Int)
    (hsize : values.size = r) :
    passArrayFuel fuel index values hsize =
      (passValuesFuel fuel index ⟨values, hsize⟩).toArray := by
  induction fuel generalizing index values with
  | zero => rfl
  | succ fuel ih =>
      rw [passArrayFuel, passValuesFuel]
      split
      · let next := pairArray values hsize
          ⟨index, by omega⟩ ⟨index + 1, by assumption⟩
        have hp := pairArray_eq values hsize
          ⟨index, by omega⟩ ⟨index + 1, by assumption⟩
        have hv : (⟨next, pairArray_size values hsize _ _⟩ : Vector Int r) =
            pairValues ⟨values, hsize⟩ ⟨index, by omega⟩
              ⟨index + 1, by assumption⟩ := by
          symm
          rw [Vector.eq_mk]
          exact hp.symm
        calc
          passArrayFuel fuel (index + 1) next _ =
              (passValuesFuel fuel (index + 1)
                ⟨next, pairArray_size values hsize _ _⟩).toArray := ih _ _ _
          _ = _ := by rw [hv]
      · rfl

private theorem networkValuesFuel_eq (ops : Smith.Accumulator α r r)
    (fuel : Nat) (s : Result α r) :
    networkValuesFuel fuel s.values = (networkFuel ops fuel s).values := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [networkValuesFuel, networkFuel, passValues_eq]
      exact ih _

private theorem networkArrayFuel_eq (fuel : Nat) (values : Array Int)
    (hsize : values.size = r) :
    networkArrayFuel fuel values hsize =
      (networkValuesFuel fuel ⟨values, hsize⟩).toArray := by
  induction fuel generalizing values with
  | zero => rfl
  | succ fuel ih =>
      rw [networkArrayFuel, networkValuesFuel]
      have hp := passArrayFuel_eq (r := r) (r - 1) 0 values hsize
      let next := passArrayFuel (r - 1) 0 values hsize
      have hv : (⟨next, passArrayFuel_size (r - 1) 0 values hsize⟩ : Vector Int r) =
          passValues ⟨values, hsize⟩ := by
        symm
        rw [Vector.eq_mk]
        exact hp.symm
      calc
        networkArrayFuel fuel next _ =
            (networkValuesFuel fuel
              ⟨next, passArrayFuel_size (r - 1) 0 values hsize⟩).toArray := ih _ _
        _ = _ := by rw [hv]

theorem runValues_eq (d : Vector Int r) :
    runValues d = (run (Smith.formAccumulator r r) d).values := by
  unfold runValues run
  let normalized := normalize (Smith.formAccumulator r r)
    ({ values := d, accumulator := () } : Result Unit r)
  have harr := networkArrayFuel_eq r normalized.values.toArray
    normalized.values.size_toArray
  have hnetwork := networkValuesFuel_eq (Smith.formAccumulator r r) r normalized
  have hv : (⟨networkArrayFuel r normalized.values.toArray
      normalized.values.size_toArray,
      networkArrayFuel_size r _ normalized.values.size_toArray⟩ : Vector Int r) =
      networkValuesFuel r normalized.values := by
    symm
    rw [Vector.eq_mk]
    exact harr.symm
  exact hv.trans hnetwork

/-- View compact state through the existing shape predicate. -/
@[expose]
def erase (s : Result α r) : Smith.Result α r r :=
  { matrix := diagMatrix s.values r r
    diag := collect s.values
    accumulator := s.accumulator }

/-- Full Smith-data candidate from the compact transform run. -/
@[expose]
def candidateData (d : Vector Int r) : SmithData r r :=
  let result := run (Smith.transformAccumulator r r) d
  let diag := collect result.values
  { rank := diag.length
    diag := ⟨diag.toArray, by simp⟩
    left := result.accumulator.left
    leftInv := result.accumulator.leftInv
    right := result.accumulator.right
    rightInv := result.accumulator.rightInv }

/-- Compact runs with different companions have identical diagonal values. -/
structure Same (s : Result α r) (t : Result β r) : Prop where
  values : s.values = t.values

private theorem swap_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) {s : Result α r} {t : Result β r}
    (h : Same s t) (i j : Fin r) : Same (swap ops s i j) (swap ops' t i j) := by
  rcases s with ⟨values, acc⟩
  rcases t with ⟨values', acc'⟩
  rcases h with ⟨rfl⟩
  simp only [swap]
  split <;> exact ⟨rfl⟩

private theorem normalizeFuel_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (fuel target : Nat)
    {s : Result α r} {t : Result β r} (h : Same s t) :
    Same (normalizeFuel ops fuel target s) (normalizeFuel ops' fuel target t) := by
  induction fuel generalizing target s t with
  | zero => exact h
  | succ fuel ih =>
      rcases s with ⟨values, acc⟩
      rcases t with ⟨values', acc'⟩
      rcases h with ⟨rfl⟩
      rw [normalizeFuel, normalizeFuel]
      by_cases ht : target < r
      · rw [dif_pos ht, dif_pos ht]
        cases hf : findNonzero? values target with
        | none => simp only [hf]; exact ⟨rfl⟩
        | some found =>
            simp only [hf]
            let pivot : Fin r := ⟨target, ht⟩
            have hmoved := swap_same ops ops'
              (⟨rfl⟩ : Same
                ({ values := values, accumulator := acc } : Result α r)
                ({ values := values, accumulator := acc' } : Result β r))
              pivot found
            rcases hmoved with ⟨hvalues⟩
            by_cases hp : (swap ops
                ({ values := values, accumulator := acc } : Result α r)
                pivot found).values[pivot] < 0
            · have hp' : (swap ops'
                  ({ values := values, accumulator := acc' } : Result β r)
                  pivot found).values[pivot] < 0 := by
                rw [← hvalues]
                exact hp
              rw [if_pos hp, if_pos hp']
              apply ih
              exact ⟨by rw [hvalues]⟩
            · have hp' : ¬ (swap ops'
                  ({ values := values, accumulator := acc' } : Result β r)
                  pivot found).values[pivot] < 0 := by
                rw [← hvalues]
                exact hp
              rw [if_neg hp, if_neg hp']
              exact ih (target + 1) ⟨hvalues⟩
      · rw [dif_neg ht, dif_neg ht]
        exact ⟨rfl⟩

private theorem pairStep_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) {s : Result α r} {t : Result β r}
    (h : Same s t) (i j : Fin r) : Same (pairStep ops s i j) (pairStep ops' t i j) := by
  rcases s with ⟨values, acc⟩
  rcases t with ⟨values', acc'⟩
  rcases h with ⟨rfl⟩
  simp only [pairStep]
  by_cases ha : values[i] = 0
  · rw [if_pos ha, if_pos ha]
    by_cases hb : values[j] = 0
    · rw [if_pos hb, if_pos hb]
      exact ⟨rfl⟩
    · rw [if_neg hb, if_neg hb]
      exact swap_same ops ops' ⟨rfl⟩ i j
  · rw [if_neg ha, if_neg ha]
    by_cases hb : values[j] = 0
    · rw [if_pos hb, if_pos hb]
      exact ⟨rfl⟩
    · rw [if_neg hb, if_neg hb]
      by_cases hab : values[i] = values[j]
      · rw [if_pos hab, if_pos hab]
        exact ⟨rfl⟩
      · rw [if_neg hab, if_neg hab]
        exact ⟨rfl⟩

private theorem passFuel_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (fuel index : Nat)
    {s : Result α r} {t : Result β r} (h : Same s t) :
    Same (passFuel ops fuel index s) (passFuel ops' fuel index t) := by
  induction fuel generalizing index s t with
  | zero => exact h
  | succ fuel ih =>
      rw [passFuel, passFuel]
      by_cases hi : index + 1 < r
      · rw [dif_pos hi, dif_pos hi]
        exact ih (index + 1) (pairStep_same ops ops' h
          ⟨index, by omega⟩ ⟨index + 1, hi⟩)
      · rw [dif_neg hi, dif_neg hi]
        exact h

private theorem pass_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) {s : Result α r} {t : Result β r}
    (h : Same s t) : Same (pass ops s) (pass ops' t) := by
  unfold pass
  exact passFuel_same ops ops' (r - 1) 0 h

private theorem networkFuel_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (fuel : Nat)
    {s : Result α r} {t : Result β r} (h : Same s t) :
    Same (networkFuel ops fuel s) (networkFuel ops' fuel t) := by
  induction fuel generalizing s t with
  | zero => exact h
  | succ fuel ih =>
      rw [networkFuel.eq_def, networkFuel.eq_def]
      exact ih (pass_same ops ops' h)

/-- Companion-parametric agreement of the compact engine. -/
theorem run_same (ops : Smith.Accumulator α r r)
    (ops' : Smith.Accumulator β r r) (d : Vector Int r) :
    Same (run ops d) (run ops' d) := by
  unfold run normalize
  apply networkFuel_same
  apply normalizeFuel_same
  exact ⟨rfl⟩

end Compact

end Smith.Diagonal

/-- Smith form of a diagonal matrix without allocating transforms. -/
@[expose]
def snfDiagonal {r : Nat} (d : Vector Int r) : Matrix Int r r :=
  diagMatrix (Smith.Diagonal.Compact.runValues d) r r

/-- Smith data for a diagonal matrix, including both transforms and inverses. -/
@[expose]
def snfDiagonalData {r : Nat} (d : Vector Int r) : SmithData r r :=
  Smith.Diagonal.Compact.candidateData d

end Hex.Matrix
