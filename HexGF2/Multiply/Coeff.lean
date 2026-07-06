/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.Basic
public import HexGF2.Clmul
public import HexGF2.Multiply.MulWords
import all HexGF2.Multiply.WordBits
import all HexGF2.Multiply.WordFold
import all HexGF2.Multiply.MulWords

public section
set_option backward.proofsInPublic true

/-!
Coefficient-level scaffolding: `clmulCoeffAt`, `xorBoolList`,
`xorWordList`, `clmulWordAt`, and the word-array-to-coefficient lemmas.
-/
namespace Hex
namespace GF2Poly
@[expose]
def clmulCoeffAt (idx : Nat) (x y : UInt64) (n : Nat) : Bool :=
  if n / 64 = idx then
    (((clmul x y).2 >>> (n % 64).toUInt64) &&& 1) != 0
  else if n / 64 = idx + 1 then
    (((clmul x y).1 >>> (n % 64).toUInt64) &&& 1) != 0
  else
    false

/-- XOR-fold a list of bits: `xorBoolList bits` is the parity of `bits`,
folding `!=` from `false`, so it is `true` exactly when an odd number of
entries are `true`. The carryless-multiplication proofs reduce each output
coefficient to such an XOR fold over a list of partial-product bits. -/
@[expose]
def xorBoolList (bits : List Bool) : Bool :=
  bits.foldl (fun acc bit => acc != bit) false

private theorem Bool.bne_assoc (a b c : Bool) :
    ((a != b) != c) = (a != (b != c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem foldl_bne_start (bits : List Bool) (acc : Bool) :
    bits.foldl (fun acc bit => acc != bit) acc =
      (acc != xorBoolList bits) := by
  unfold xorBoolList
  induction bits generalizing acc with
  | nil =>
      cases acc <;> rfl
  | cons bit bits ih =>
      simp only [List.foldl_cons]
      rw [ih (acc != bit), ih (false != bit)]
      generalize htail : List.foldl (fun acc bit => acc != bit) false bits = tail
      cases acc <;> cases bit <;> cases tail <;> rfl

/-- `xorBoolList` on a cons: the parity of `bit :: bits` is `bit` XORed with
the parity of the tail. -/
private theorem xorBoolList_cons (bit : Bool) (bits : List Bool) :
    xorBoolList (bit :: bits) = (bit != xorBoolList bits) := by
  unfold xorBoolList
  simp only [List.foldl_cons]
  rw [foldl_bne_start]
  cases bit <;> rfl

/-- `xorBoolList` distributes over list append: the parity of `xs ++ ys` is
the XOR of the two parities. -/
private theorem xorBoolList_append (xs ys : List Bool) :
    xorBoolList (xs ++ ys) = (xorBoolList xs != xorBoolList ys) := by
  unfold xorBoolList
  rw [List.foldl_append, foldl_bne_start]
  simp [xorBoolList]

private theorem Bool.bne_medial (a b c d : Bool) :
    ((a != b) != (c != d)) = ((a != c) != (b != d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem List.flatMap_const_nil {α β : Type} (xs : List α) :
    xs.flatMap (fun _ => ([] : List β)) = [] := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem List.flatMap_empty_input {α β : Type} (f : α → List β) :
    ([] : List α).flatMap f = [] := by
  rfl

private theorem List.flatMap_singleton {α β : Type} (xs : List α) (f : α → β) :
    xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem List.flatMap_congr_left {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

/-- Split a `flatMap` whose body is a pointwise append `left x ++ right x`:
its parity is the XOR of the parities of the two component `flatMap`s. -/
private theorem xorBoolList_flatMap_append {α : Type}
    (xs : List α) (left right : α → List Bool) :
    xorBoolList (xs.flatMap fun x => left x ++ right x) =
      (xorBoolList (xs.flatMap left) != xorBoolList (xs.flatMap right)) := by
  induction xs with
  | nil =>
      simp [xorBoolList]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append, xorBoolList_append, ih, xorBoolList_append]
      generalize xorBoolList (left x) = a
      generalize xorBoolList (List.flatMap left xs) = b
      generalize xorBoolList (right x) = c
      generalize xorBoolList (List.flatMap right xs) = d
      cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Swap the two summation indices of a rectangular `range m × range n` XOR
fold of scalar `term i j`: folding row-by-row equals folding column-by-column.
This is the parity analogue of swapping a double sum, used to reorder the
word-pair contributions in the clmul proof. -/
private theorem xorBoolList_wordPairs_swap
    (m n : Nat) (term : Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).map (fun j => term i j))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun j => (List.range m).map (fun i => term i j))
          (List.range n)) := by
  induction m with
  | zero =>
      simp [xorBoolList, List.flatMap_const_nil]
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, ih, List.flatMap_empty_input]
      simp only [List.append_nil]
      have hcols :
          xorBoolList
              (List.flatMap
                (fun j => (List.range m ++ [m]).map (fun i => term i j))
                (List.range n)) =
            (xorBoolList
                (List.flatMap
                  (fun j => (List.range m).map (fun i => term i j))
                  (List.range n)) !=
              xorBoolList ((List.range n).map (fun j => term m j))) := by
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [xorBoolList_flatMap_append, List.flatMap_singleton]
      rw [hcols]

/-- Congruence for `flatMap` under `xorBoolList`: if `left x` and `right x`
have the same parity for every `x ∈ xs`, the two flat-mapped lists have the
same overall parity. -/
private theorem xorBoolList_flatMap_congr_xor {α : Type}
    {xs : List α} {left right : α → List Bool}
    (h : ∀ x, x ∈ xs → xorBoolList (left x) = xorBoolList (right x)) :
    xorBoolList (xs.flatMap left) = xorBoolList (xs.flatMap right) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append, h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

/-- Flatten a nested XOR fold: XOR-folding the per-element parities
`xorBoolList (terms x)` equals the parity of the single flattened list
`xs.flatMap terms`. -/
private theorem xorBoolList_map_xorBoolList {α : Type}
    (xs : List α) (terms : α → List Bool) :
    xorBoolList (xs.map (fun x => xorBoolList (terms x))) =
      xorBoolList (xs.flatMap terms) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [xorBoolList_cons, xorBoolList_append, ih]

/-- Merge two maps combined by `!=` into one: if `left x != right x = both x`
pointwise on `xs`, then the XOR of the two mapped parities equals the parity
of the single `both`-mapped list. -/
private theorem xorBoolList_map_bne_congr {α : Type}
    {xs : List α} {left right both : α → Bool}
    (h : ∀ x, x ∈ xs → (left x != right x) = both x) :
    (xorBoolList (xs.map left) != xorBoolList (xs.map right)) =
      xorBoolList (xs.map both) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [xorBoolList_cons, xorBoolList_cons, xorBoolList_cons, Bool.bne_medial, h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

/-- List-valued version of `xorBoolList_map_bne_congr`: if the parities of
`left x` and `right x` XOR to that of `both x` pointwise on `xs`, the XOR of
the two flat-mapped parities equals the parity of the `both` flatMap. -/
private theorem xorBoolList_flatMap_bne_congr {α : Type}
    {xs : List α} {left right both : α → List Bool}
    (h : ∀ x, x ∈ xs →
      (xorBoolList (left x) != xorBoolList (right x)) = xorBoolList (both x)) :
    (xorBoolList (xs.flatMap left) != xorBoolList (xs.flatMap right)) =
      xorBoolList (xs.flatMap both) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append, xorBoolList_append,
        Bool.bne_medial, h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

/-- List-valued analogue of `xorBoolList_wordPairs_swap`: for a
`term : Nat → Nat → List Bool`, the parity of the nested `range m × range n`
flatMap is independent of which index is iterated outermost. -/
private theorem xorBoolList_flatMap_ranges_swap_list
    (m n : Nat) (term : Nat → Nat → List Bool) :
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).flatMap (fun j => term i j))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun j => (List.range m).flatMap (fun i => term i j))
          (List.range n)) := by
  calc
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).flatMap (fun j => term i j))
          (List.range m))
        = xorBoolList
            ((List.range m).map
              (fun i => xorBoolList
                ((List.range n).flatMap (fun j => term i j)))) := by
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            ((List.range m).map
              (fun i => xorBoolList
                ((List.range n).map (fun j => xorBoolList (term i j))))) := by
            congr 1
            apply List.map_congr_left
            intro i _hi
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            (List.flatMap
              (fun i => (List.range n).map (fun j => xorBoolList (term i j)))
              (List.range m)) := by
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            (List.flatMap
              (fun j => (List.range m).map (fun i => xorBoolList (term i j)))
              (List.range n)) := by
            exact xorBoolList_wordPairs_swap m n (fun i j => xorBoolList (term i j))
    _ = xorBoolList
            ((List.range n).map
              (fun j => xorBoolList
                ((List.range m).map (fun i => xorBoolList (term i j))))) := by
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
            ((List.range n).map
              (fun j => xorBoolList
                ((List.range m).flatMap (fun i => term i j)))) := by
            congr 1
            apply List.map_congr_left
            intro j _hj
            rw [xorBoolList_map_xorBoolList]
    _ = xorBoolList
        (List.flatMap
          (fun j => (List.range m).flatMap (fun i => term i j))
          (List.range n)) := by
            rw [xorBoolList_map_xorBoolList]

/-- Reindex a triple XOR from the left-associated word-pair grouping
`(i,j),k` to the right-associated grouping `i,(j,k)`, keeping the outer
source word `i` fixed and swapping the two inner finite ranges. -/
private theorem xorBoolList_wordTriples_assoc
    (m n o : Nat) (term : Nat → Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j => (List.range o).map (fun k => term i j k))
              (List.range n))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k => (List.range n).map (fun j => term i j k))
              (List.range o))
          (List.range m)) := by
  apply xorBoolList_flatMap_congr_xor
  intro i _hi
  exact xorBoolList_wordPairs_swap n o (fun j k => term i j k)

/-- Array-specialized triple reindexing theorem for raw multiplication
associativity proof terms.  Later coefficient lemmas instantiate `term` with
the source-word contribution predicate built from `xs[i]!`, `ys[j]!`, and
`zs[k]!`. -/
private theorem xorBoolList_sourceTriples_assoc
    (xs ys zs : Array UInt64) (term : Nat → Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j => (List.range zs.size).map (fun k => term i j k))
              (List.range ys.size))
          (List.range xs.size)) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k => (List.range ys.size).map (fun j => term i j k))
              (List.range zs.size))
          (List.range xs.size)) := by
  exact xorBoolList_wordTriples_assoc xs.size ys.size zs.size term

/-- XOR a list of machine words as the word-level analogue of `xorBoolList`. -/
@[expose]
def xorWordList : List UInt64 → UInt64
  | [] => 0
  | word :: words => word ^^^ xorWordList words

/-- The raw word contribution of a single `clmul x y` placed at word offset
`idx`, projected to result word slot `slot`. -/
@[expose]
def clmulWordAt (idx : Nat) (x y : UInt64) (slot : Nat) : UInt64 :=
  if slot = idx then
    (clmul x y).2
  else if slot = idx + 1 then
    (clmul x y).1
  else
    0

private theorem UInt64.xor_assoc (a b c : UInt64) :
    (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_xor, Nat.xor_assoc]

private theorem UInt64.xor_zero (a : UInt64) :
    a ^^^ 0 = a := by
  apply UInt64.toNat_inj.mp
  simp

private theorem UInt64.zero_xor (a : UInt64) :
    0 ^^^ a = a := by
  apply UInt64.toNat_inj.mp
  simp

private theorem Array.getElem!_setIfInBounds_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (v : α) (hne : i ≠ j) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hne]
  · simp [hi]

private theorem replicate_zero_getElem! (size slot : Nat) :
    (Array.replicate size (0 : UInt64))[slot]! = 0 := by
  rw [Array.getElem!_eq_getD]
  by_cases hslot : slot < (Array.replicate size (0 : UInt64)).size
  · have hslot' : slot < size := by
      simpa using hslot
    simp [Array.getD, hslot']
  · have hslot' : size ≤ slot := by
      simpa using Nat.le_of_not_gt hslot
    simp [Array.getD, hslot']
    rfl

private theorem xorWordList_append (xs ys : List UInt64) :
    xorWordList (xs ++ ys) = xorWordList xs ^^^ xorWordList ys := by
  induction xs with
  | nil =>
      simp [xorWordList]
  | cons x xs ih =>
      simp only [List.cons_append, xorWordList]
      rw [ih, UInt64.xor_assoc]

private theorem xorClmulAt_getElem!_contrib
    (acc : Array UInt64) {idx slot : Nat} (x y : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size) :
    (xorClmulAt acc idx x y)[slot]! =
      acc[slot]! ^^^ clmulWordAt idx x y slot := by
  unfold xorClmulAt clmulWordAt
  by_cases hLow : slot = idx
  · subst slot
    simp [hidx]
  · by_cases hHigh : slot = idx + 1
    · subst slot
      simp [hidx, hidxNext]
    · have hLow' : idx ≠ slot := Ne.symm hLow
      have hHigh' : idx + 1 ≠ slot := Ne.symm hHigh
      rcases hprod : clmul x y with ⟨hi, lo⟩
      simp [hidx, hidxNext, hLow, hHigh,
        Array.getElem!_setIfInBounds_ne, hLow', hHigh']

private theorem foldl_xorClmulAt_getElem!_contrib
    (js : List Nat) (acc : Array UInt64) (idx : Nat) (x : UInt64)
    (ys : Array UInt64) (slot : Nat)
    (hbound : ∀ j ∈ js, idx + j + 1 < acc.size) :
    (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)[slot]! =
      (acc[slot]! ^^^
        xorWordList (js.map (fun j => clmulWordAt (idx + j) x ys[j]! slot))) := by
  induction js generalizing acc with
  | nil =>
      simp [xorWordList]
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons]
      have htail := ih (xorClmulAt acc (idx + j) x ys[j]!)
        (by
          intro j' hj'
          have h := hbound j' (by simp [hj'])
          simpa [xorClmulAt_size] using h)
      rw [htail]
      have hhead := xorClmulAt_getElem!_contrib acc (idx := idx + j)
        (slot := slot) x ys[j]!
        (by
          have h := hbound j (by simp)
          omega)
        (hbound j (by simp))
      rw [hhead, xorWordList, UInt64.xor_assoc]

private theorem foldl_mulWords_getElem!_contrib
    (is : List Nat) (acc : Array UInt64) (xs ys : Array UInt64) (slot : Nat)
    (hbound : ∀ i ∈ is, ∀ j ∈ List.range ys.size, i + j + 1 < acc.size) :
    (is.foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      acc)[slot]! =
      (acc[slot]! ^^^
        xorWordList
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
            is)) := by
  induction is generalizing acc with
  | nil =>
      simp [xorWordList]
  | cons i is ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      have htail := ih
        ((List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!) acc)
        (by
          intro i' hi' j hj
          have h := hbound i' (by simp [hi']) j hj
          simpa [foldl_xorClmulAt_size] using h)
      rw [htail]
      have hinner := foldl_xorClmulAt_getElem!_contrib
        (List.range ys.size) acc i xs[i]! ys slot
        (by
          intro j hj
          exact hbound i (by simp) j hj)
      rw [hinner, xorWordList_append, UInt64.xor_assoc]

/-- Bit `n` of the carry-less word-pair product vanishes when the left
factor word is zero; the left base case of the bilinearity ladder. -/
private theorem clmulCoeffAt_zero_left (idx : Nat) (y : UInt64) (n : Nat) :
    clmulCoeffAt idx 0 y n = false := by
  unfold clmulCoeffAt
  rw [clmul_zero_left]
  by_cases hLow : n / 64 = idx
  · simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1 <;> simp [hLow, hHigh]

/-- `clmulCoeffAt` is bilinear (XOR-additive) in its left factor: bit `n` of
the product against `x ^^^ y` is the `bne` of the two single-factor bits. -/
private theorem clmulCoeffAt_xor_left
    (idx : Nat) (x y z : UInt64) (n : Nat) :
    clmulCoeffAt idx (x ^^^ y) z n =
      (clmulCoeffAt idx x z n != clmulCoeffAt idx y z n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · simp [hLow]
    rw [clmul_xor_left_snd_bit]
  · by_cases hHigh : n / 64 = idx + 1
    · simp [hHigh]
      rw [clmul_xor_left_fst_bit]
    · simp [hLow, hHigh]

/-- Bit `n` of the carry-less word-pair product vanishes when the right
factor word is zero; the right base case of the bilinearity ladder. -/
private theorem clmulCoeffAt_zero_right (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x 0 n = false := by
  unfold clmulCoeffAt
  rw [clmul_zero_right]
  by_cases hLow : n / 64 = idx
  · simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1 <;> simp [hLow, hHigh]

/-- `clmulCoeffAt` is bilinear (XOR-additive) in its right factor: bit `n` of
the product against `y ^^^ z` is the `bne` of the two single-factor bits. -/
private theorem clmulCoeffAt_xor_right
    (idx : Nat) (x y z : UInt64) (n : Nat) :
    clmulCoeffAt idx x (y ^^^ z) n =
      (clmulCoeffAt idx x y n != clmulCoeffAt idx x z n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · simp [hLow]
    rw [clmul_xor_right_snd_bit]
  · by_cases hHigh : n / 64 = idx + 1
    · simp [hHigh]
      rw [clmul_xor_right_fst_bit]
    · simp [hLow, hHigh]

/-- Iterating left bilinearity over a word list: bit `n` of the product of a
folded `xorWordList` against `z` is the XOR-sum of the per-word bits. -/
private theorem clmulCoeffAt_xorWordList_left
    (words : List UInt64) (idx : Nat) (z : UInt64) (n : Nat) :
    clmulCoeffAt idx (xorWordList words) z n =
      xorBoolList (words.map (fun word => clmulCoeffAt idx word z n)) := by
  induction words with
  | nil =>
      change clmulCoeffAt idx 0 z n = false
      exact clmulCoeffAt_zero_left idx z n
  | cons word words ih =>
      rw [xorWordList, clmulCoeffAt_xor_left]
      change (clmulCoeffAt idx word z n != clmulCoeffAt idx (xorWordList words) z n) =
        xorBoolList (clmulCoeffAt idx word z n ::
          words.map (fun word => clmulCoeffAt idx word z n))
      rw [xorBoolList_cons, ih]

/-- Iterating right bilinearity over a word list: bit `n` of the product of
`x` against a folded `xorWordList` is the XOR-sum of the per-word bits. -/
private theorem clmulCoeffAt_xorWordList_right
    (words : List UInt64) (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x (xorWordList words) n =
      xorBoolList (words.map (fun word => clmulCoeffAt idx x word n)) := by
  induction words with
  | nil =>
      change clmulCoeffAt idx x 0 n = false
      exact clmulCoeffAt_zero_right idx x n
  | cons word words ih =>
      rw [xorWordList, clmulCoeffAt_xor_right]
      change (clmulCoeffAt idx x word n != clmulCoeffAt idx x (xorWordList words) n) =
        xorBoolList (clmulCoeffAt idx x word n ::
          words.map (fun word => clmulCoeffAt idx x word n))
      rw [xorBoolList_cons, ih]

/-- Accumulating one `xorClmulAt acc idx x y` step flips bit `n` of the
running `coeffWords` by exactly that pair's `clmulCoeffAt idx x y` bit. -/
private theorem coeffWords_xorClmulAt_contrib
    (acc : Array UInt64) {idx n : Nat} (x y : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n != clmulCoeffAt idx x y n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low acc x y hidx hLow]
    simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high acc x y hidx hidxNext hHigh]
      simp [hHigh]
    · rw [coeffWords_xorClmulAt_ne acc x y hLow hHigh]
      simp [hLow, hHigh]

/-- Folding `xorClmulAt` over the inner `j`-list flips bit `n` of `coeffWords`
by the XOR-sum of the per-`j` `clmulCoeffAt (idx + j) x ys[j]!` contributions. -/
private theorem foldl_xorClmulAt_coeff_contrib
    (js : List Nat) (acc : Array UInt64) (idx : Nat) (x : UInt64)
    (ys : Array UInt64) (n : Nat)
    (hbound : ∀ j ∈ js, idx + j + 1 < acc.size) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)
        n =
      (coeffWords acc n !=
        xorBoolList (js.map (fun j => clmulCoeffAt (idx + j) x ys[j]! n))) := by
  induction js generalizing acc with
  | nil =>
      simp [xorBoolList]
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons]
      have hidx : idx + j < acc.size := by
        have h := hbound j (by simp)
        omega
      have hidxNext : idx + j + 1 < acc.size := hbound j (by simp)
      rw [ih]
      · rw [coeffWords_xorClmulAt_contrib acc x ys[j]! hidx hidxNext]
        rw [xorBoolList_cons, Bool.bne_assoc]
      · intro j' hj'
        have h := hbound j' (by simp [hj'])
        simpa [xorClmulAt_size] using h

/-- Folding the full nested `i`/`j` accumulation flips bit `n` of `coeffWords`
by the flat XOR-sum over every `(i, j)` word-pair `clmulCoeffAt` contribution. -/
private theorem foldl_mulWords_coeff_contrib
    (is : List Nat) (acc : Array UInt64) (xs ys : Array UInt64) (n : Nat)
    (hbound : ∀ i ∈ is, ∀ j ∈ List.range ys.size, i + j + 1 < acc.size) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      (coeffWords acc n !=
        xorBoolList
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulCoeffAt (i + j) xs[i]! ys[j]! n))
            is)) := by
  induction is generalizing acc with
  | nil =>
      simp [xorBoolList]
  | cons i is ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      · have hinner := foldl_xorClmulAt_coeff_contrib
          (List.range ys.size) acc i xs[i]! ys n
          (by
            intro j hj
            exact hbound i (by simp) j hj)
        rw [hinner, xorBoolList_append, Bool.bne_assoc]
      · intro i' hi' j hj
        have h := hbound i' (by simp [hi']) j hj
        simpa [foldl_xorClmulAt_size] using h

/-- Capstone: bit `n` of `mulWords xs ys` is the flat XOR over all `(i, j)`
word-pair `clmulCoeffAt (i + j) xs[i]! ys[j]!` contributions, starting from the
all-zero accumulator. -/
private theorem coeffWords_mulWords_contrib (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs ys) n =
      xorBoolList
        (List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulCoeffAt (i + j) xs[i]! ys[j]! n))
          (List.range xs.size)) := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · have hxsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hxs
    simp [hxs, hxsize, coeffWords_empty, xorBoolList]
  · by_cases hys : ys.isEmpty
    · have hysize : ys.size = 0 := by
        simpa [Array.isEmpty] using hys
      have hflat :
          List.flatMap (fun _ : Nat => ([] : List Bool)) (List.range xs.size) = [] := by
        generalize hlist : List.range xs.size = is
        induction is with
        | nil => rfl
        | cons i is ih =>
            simp [List.flatMap_cons]
      simp [hxs, hys, hysize, coeffWords_empty, xorBoolList, hflat]
    · simp [hxs, hys]
      rw [foldl_mulWords_coeff_contrib]
      · rw [coeffWords_replicate_zero]
        simp
      · intro i hi j hj
        have hi' : i < xs.size := List.mem_range.mp hi
        have hj' : j < ys.size := List.mem_range.mp hj
        simp
        omega

/-- A raw product word is the XOR of all source word-pair contributions whose
low or high `clmul` word lands in that result slot. -/
private theorem mulWords_getElem!_contrib
    (xs ys : Array UInt64) (slot : Nat) :
    (mulWords xs ys)[slot]! =
      xorWordList
        (List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
          (List.range xs.size)) := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · have hxsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hxs
    simp [hxs, hxsize, xorWordList]
    rfl
  · by_cases hys : ys.isEmpty
    · have hysize : ys.size = 0 := by
        simpa [Array.isEmpty] using hys
      have hflat :
          List.flatMap (fun _ : Nat => ([] : List UInt64)) (List.range xs.size) = [] := by
        generalize hlist : List.range xs.size = is
        induction is with
        | nil => rfl
        | cons i is ih =>
            simp [List.flatMap_cons]
      simp [hxs, hys, hysize, xorWordList, hflat]
      rfl
    · simp [hxs, hys]
      rw [foldl_mulWords_getElem!_contrib]
      · rw [replicate_zero_getElem!, UInt64.zero_xor]
      · intro i hi j hj
        have hi' : i < xs.size := List.mem_range.mp hi
        have hj' : j < ys.size := List.mem_range.mp hj
        simp
        omega

/-- Expand a later `clmul` coefficient whose left input is an intermediate raw
product word into source word-pair contributions. -/
private theorem clmulCoeffAt_mulWords_left_contrib
    (xs ys : Array UInt64) (slot idx : Nat) (z : UInt64) (n : Nat) :
    clmulCoeffAt idx (mulWords xs ys)[slot]! z n =
      xorBoolList
        ((List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
          (List.range xs.size)).map
          (fun word => clmulCoeffAt idx word z n)) := by
  rw [mulWords_getElem!_contrib, clmulCoeffAt_xorWordList_left]

/-- Expand a later `clmul` coefficient whose right input is an intermediate raw
product word into source word-pair contributions. -/
private theorem clmulCoeffAt_mulWords_right_contrib
    (ys zs : Array UInt64) (slot idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x (mulWords ys zs)[slot]! n =
      xorBoolList
        ((List.flatMap
          (fun j =>
            (List.range zs.size).map
              (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
          (List.range ys.size)).map
          (fun word => clmulCoeffAt idx x word n)) := by
  rw [mulWords_getElem!_contrib, clmulCoeffAt_xorWordList_right]

/-- Source-word contribution list for one coefficient of the left-associated
raw product `(xs * ys) * zs`.  The outer product contributes a word slot and a
`zs` source word; each such intermediate word is expanded back to the
`xs`/`ys` source pair contributions that created it. -/
@[expose]
def leftAssocSourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) : List Bool :=
  List.flatMap
    (fun slot =>
      List.flatMap
        (fun k =>
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
            (List.range xs.size)).map
            (fun word => clmulCoeffAt (slot + k) word zs[k]! n))
        (List.range zs.size))
    (List.range (mulWords xs ys).size)

/-- Source-word contribution list for one coefficient of the right-associated
raw product `xs * (ys * zs)`.  The outer product contributes an `xs` source
word and an intermediate word slot; each intermediate word is expanded back to
the `ys`/`zs` source pair contributions that created it. -/
@[expose]
def rightAssocSourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) : List Bool :=
  List.flatMap
    (fun i =>
      List.flatMap
        (fun slot =>
          (List.flatMap
            (fun j =>
              (List.range zs.size).map
                (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
            (List.range ys.size)).map
            (fun word => clmulCoeffAt (i + slot) xs[i]! word n))
        (List.range (mulWords ys zs).size))
    (List.range xs.size)

/-- Contributions from one fixed source triple `(i,j,k)` to the left-associated
word product, varying only the intermediate `(xs * ys)` result slot. -/
@[expose]
def leftAssocFixedTripleContribs
    (i j k : Nat) (x y z : UInt64) (n slotBound : Nat) : List Bool :=
  (List.range slotBound).map
    (fun slot => clmulCoeffAt (slot + k) (clmulWordAt (i + j) x y slot) z n)

/-- Contributions from one fixed source triple `(i,j,k)` to the right-associated
word product, varying only the intermediate `(ys * zs)` result slot. -/
@[expose]
def rightAssocFixedTripleContribs
    (i j k : Nat) (x y z : UInt64) (n slotBound : Nat) : List Bool :=
  (List.range slotBound).map
    (fun slot => clmulCoeffAt (i + slot) x (clmulWordAt (j + k) y z slot) n)

/-- The selected bit of one machine word, using the same projection shape as
the existing coefficient lemmas. -/
@[expose]
def wordBitAt (word : UInt64) (bit : Nat) : Bool :=
  (((word >>> bit.toUInt64) &&& 1) != 0)

private theorem wordBitAt_getElem!_eq_coeff
    (p : GF2Poly) {i bit : Nat} (hbit : bit < 64) :
    wordBitAt p.words[i]! bit = p.coeff (64 * i + bit) := by
  have hdiv : (64 * i + bit) / 64 = i := by
    rw [Nat.mul_add_div (by decide : 64 > 0), Nat.div_eq_of_lt hbit, Nat.add_zero]
  have hmod : (64 * i + bit) % 64 = bit := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hbit
  rw [Array.getElem!_eq_getD]
  simp [coeff, coeffWords, wordBitAt, hdiv, hmod, default]

/-- The one-hot contribution of a selected source bit of a word. -/
@[expose]
def oneHotBitWord (word : UInt64) (bit : Nat) : UInt64 :=
  if wordBitAt word bit then
    (1 : UInt64) <<< bit.toUInt64
  else
    0

private theorem xorWordList_oneHotBitWords_eq (word : UInt64) :
    xorWordList ((List.range 64).map (fun bit => oneHotBitWord word bit)) = word := by
  simp [xorWordList, oneHotBitWord, wordBitAt, List.range, List.range.loop]
  bv_decide

private theorem clmulCoeffAt_zero_word_right (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x 0 n = false :=
  clmulCoeffAt_zero_right idx x n

private theorem clmul_rightBitFold_low
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).2 bit =
      xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit)) := by
  have hlow : bit / 64 = 0 := Nat.div_eq_of_lt hbit
  have hmod : bit % 64 = bit := Nat.mod_eq_of_lt hbit
  have hcoeff :
      wordBitAt (clmul x y).2 bit = clmulCoeffAt 0 x y bit := by
    unfold wordBitAt clmulCoeffAt
    simp [hlow, hmod]
  rw [hcoeff]
  calc
    clmulCoeffAt 0 x y bit =
        clmulCoeffAt 0 x (xorWordList ((List.range 64).map
          (fun bit => oneHotBitWord y bit))) bit := by
          rw [xorWordList_oneHotBitWords_eq]
    _ = xorBoolList
        (List.map (fun word => clmulCoeffAt 0 x word bit)
          ((List.range 64).map (fun bit => oneHotBitWord y bit))) := by
          rw [clmulCoeffAt_xorWordList_right]
    _ = xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit)) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro b hb
          cases hyb : wordBitAt y b
          · simp [oneHotBitWord, hyb, clmulCoeffAt_zero_word_right]
          · simp [oneHotBitWord, hyb]
            unfold clmulCoeffAt wordBitAt
            simp [hlow, hmod]

private theorem clmul_rightBitFold_high
    (x y : UInt64) {bit : Nat} (hbit : bit < 64) :
    wordBitAt (clmul x y).1 bit =
      xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit)) := by
  have hhigh : (bit + 64) / 64 = 0 + 1 := by omega
  have hmod : (bit + 64) % 64 = bit := by omega
  have hcoeff :
      wordBitAt (clmul x y).1 bit = clmulCoeffAt 0 x y (bit + 64) := by
    unfold wordBitAt clmulCoeffAt
    simp [hhigh, hmod]
  rw [hcoeff]
  calc
    clmulCoeffAt 0 x y (bit + 64) =
        clmulCoeffAt 0 x (xorWordList ((List.range 64).map
          (fun bit => oneHotBitWord y bit))) (bit + 64) := by
          rw [xorWordList_oneHotBitWords_eq]
    _ = xorBoolList
        (List.map (fun word => clmulCoeffAt 0 x word (bit + 64))
          ((List.range 64).map (fun bit => oneHotBitWord y bit))) := by
          rw [clmulCoeffAt_xorWordList_right]
    _ = xorBoolList
        ((List.range 64).map
          (fun b =>
            wordBitAt y b &&
              wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit)) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro b hb
          cases hyb : wordBitAt y b
          · simp [oneHotBitWord, hyb, clmulCoeffAt_zero_word_right]
          · simp [oneHotBitWord, hyb]
            unfold clmulCoeffAt wordBitAt
            simp [hhigh, hmod]

private theorem xorBoolList_range_false (n : Nat) :
    xorBoolList ((List.range n).map (fun _ => false)) = false := by
  induction n with
  | zero =>
      simp [xorBoolList]
  | succ n ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append, ih]
      simp [xorBoolList]

private theorem xorBoolList_map_and_left (value : Bool) (bits : List Bool) :
    xorBoolList (bits.map (fun bit => value && bit)) =
      (value && xorBoolList bits) := by
  cases value
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, ih]
        simp
  · induction bits with
    | nil =>
        simp [xorBoolList]
    | cons bit bits ih =>
        rw [List.map_cons, xorBoolList_cons, xorBoolList_cons, ih]
        simp

private theorem Bool.and_swap_middle (a b c : Bool) :
    (b && (a && c)) = ((a && b) && c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem xorBoolList_range_single_decide {n source : Nat} (value : Bool)
    (hsource : source < n) :
    xorBoolList ((List.range n).map (fun a => value && decide (a = source))) =
      value := by
  induction n generalizing source with
  | zero =>
      omega
  | succ n ih =>
      rw [List.range_succ, List.map_append, xorBoolList_append]
      by_cases hlast : source = n
      · have hleft :
            (List.range n).map (fun a => value && decide (a = source)) =
              (List.range n).map (fun _ => false) := by
          apply List.map_congr_left
          intro a ha
          have ha_lt : a < n := List.mem_range.mp ha
          simp [show a ≠ source by omega]
        rw [hleft, xorBoolList_range_false]
        simp [xorBoolList, hlast]
      · have hsource_lt : source < n := by omega
        rw [ih hsource_lt]
        simp [xorBoolList, show n ≠ source by omega]

private theorem xorBoolList_wordBitAt_sum_eq
    (x : UInt64) {b target : Nat} (hle : b ≤ target) (hsource : target - b < 64) :
    xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = target))) =
      wordBitAt x (target - b) := by
  rw [show
      (List.range 64).map (fun a => wordBitAt x a && decide (a + b = target)) =
        (List.range 64).map
          (fun a => wordBitAt x (target - b) && decide (a = target - b)) by
    apply List.map_congr_left
    intro a ha
    have ha_lt : a < 64 := List.mem_range.mp ha
    by_cases h : a = target - b
    · subst h
      simp [show target - b + b = target by omega]
    · have hsum : a + b ≠ target := by omega
      simp [h, hsum]]
  exact xorBoolList_range_single_decide (wordBitAt x (target - b)) hsource

private theorem xorBoolList_wordBitAt_sum_eq_false_of_target_lt
    (x : UInt64) {b target : Nat} (hlt : target < b) :
    xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = target))) =
      false := by
  rw [show
      (List.range 64).map (fun a => wordBitAt x a && decide (a + b = target)) =
        (List.range 64).map (fun _ => false) by
    apply List.map_congr_left
    intro a _ha
    simp [show a + b ≠ target by omega]]
  exact xorBoolList_range_false 64

private theorem xorBoolList_wordBitAt_sum_eq_false_of_source_ge
    (x : UInt64) {b target : Nat} (_hle : b ≤ target) (hsource : 64 ≤ target - b) :
    xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = target))) =
      false := by
  rw [show
      (List.range 64).map (fun a => wordBitAt x a && decide (a + b = target)) =
        (List.range 64).map (fun _ => false) by
    apply List.map_congr_left
    intro a ha
    have ha_lt : a < 64 := List.mem_range.mp ha
    simp [show a + b ≠ target by omega]]
  exact xorBoolList_range_false 64

private theorem clmul_oneHot_source_low
    (x : UInt64) {b bit : Nat} (hb : b < 64) (hbit : bit < 64) :
    wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).2 bit =
      xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = bit))) := by
  by_cases hbZero : b = 0
  · subst hbZero
    rw [clmul_oneHot_snd x hb]
    exact (xorBoolList_wordBitAt_sum_eq x (b := 0) (target := bit)
      (by omega) hbit).symm
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hbZero
    by_cases hle : b ≤ bit
    · change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).2 >>>
          bit.toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit)))
      rw [clmul_oneHot_low_bit_shifted x hbPos hb hbit hle]
      change wordBitAt x (bit - b) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit)))
      exact (xorBoolList_wordBitAt_sum_eq x (b := b) (target := bit) hle (by omega)).symm
    · have hlt : bit < b := Nat.lt_of_not_ge hle
      change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).2 >>>
          bit.toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit)))
      rw [clmul_oneHot_low_bit_before_shift_false x hbPos hb hlt]
      exact (xorBoolList_wordBitAt_sum_eq_false_of_target_lt x hlt).symm

private theorem clmul_oneHot_source_high
    (x : UInt64) {b bit : Nat} (hb : b < 64) (hbit : bit < 64) :
    wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit =
      xorBoolList
        ((List.range 64).map
          (fun a => wordBitAt x a && decide (a + b = bit + 64))) := by
  by_cases hbZero : b = 0
  · subst hbZero
    rw [clmul_oneHot_fst x hb]
    simp only [if_true]
    have hzero : wordBitAt 0 bit = false := by
      simp [wordBitAt]
    rw [hzero]
    exact (xorBoolList_wordBitAt_sum_eq_false_of_source_ge x
      (b := 0) (target := bit + 64) (by omega) (by omega)).symm
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hbZero
    by_cases hleBit : b ≤ bit
    · change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).1 >>>
          bit.toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit + 64)))
      rw [clmul_oneHot_high_bit_after_carry_false x hb hbit hleBit]
      exact (xorBoolList_wordBitAt_sum_eq_false_of_source_ge x
        (b := b) (target := bit + 64) (by omega) (by omega)).symm
    · have hbitLt : bit < b := Nat.lt_of_not_ge hleBit
      have hsourceLt : bit + 64 - b < 64 := by omega
      have hsumGe : 64 ≤ bit + 64 - b + b := by omega
      have hsumEq : bit + 64 - b + b - 64 = bit := by omega
      have hleft :
          wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1 bit =
            wordBitAt (clmul x ((1 : UInt64) <<< b.toUInt64)).1
              (bit + 64 - b + b - 64) := by
        rw [hsumEq]
      rw [hleft]
      change ((((clmul x ((1 : UInt64) <<< b.toUInt64)).1 >>>
          (bit + 64 - b + b - 64).toUInt64) &&& 1) != 0) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit + 64)))
      rw [clmul_oneHot_high_bit_carry_word x hbPos hb hsourceLt hsumGe]
      change wordBitAt x (bit + 64 - b) =
        xorBoolList
          ((List.range 64).map
            (fun a => wordBitAt x a && decide (a + b = bit + 64)))
      exact (xorBoolList_wordBitAt_sum_eq x
        (b := b) (target := bit + 64) (by omega) hsourceLt).symm


end GF2Poly
end Hex
