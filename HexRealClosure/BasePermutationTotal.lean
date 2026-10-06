/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePermutation
import all HexRealClosure.BasePermutation
import all HexRealClosure.BaseTower
import all HexRealClosure.BaseMap

public section
namespace Hex.RealClosure.BaseContext.BaseTower

private theorem word_self (keys : List ConstantKey) (offset : Nat) :
    word keys keys offset = some [] := by
  induction keys generalizing offset with
  | nil => simp [word]
  | cons key rest ih => simp [word, List.findIdx?_cons, ih]

/-- Every provider bound satisfies the exact key binding for the identity map. -/
theorem bindings_identity (keys : List ConstantKey) :
    bindings keys keys (FieldEmbedding.identity (BaseTower keys.length)) = true := by
  apply List.all_eq_true.mpr
  intro i member
  apply List.any_eq_true.mpr
  refine ⟨i, member, ?_⟩
  simp only [FieldEmbedding.identity_value, decide_true, Bool.true_and]

private theorem additional_self (keys : List ConstantKey) :
    keys.reverse.filter (fun key => !keys.contains key) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro key member
  have present : key ∈ keys := List.mem_reverse.mp member
  simp only [List.contains_iff_mem.mpr present, Bool.not_true]
  decide

private theorem comp_identity (n : Nat) :
    (FieldEmbedding.identity (BaseTower n)).comp (FieldEmbedding.identity (BaseTower n)) =
      FieldEmbedding.identity (BaseTower n) := rfl

private theorem extend_self (n : Nat) (total : n + (n - n) = n) :
    (Eq.rec (motive := fun m _ => FieldEmbedding (BaseTower n) (BaseTower m))
      (extend n (n - n)) total) =
      FieldEmbedding.identity (BaseTower n) := by
  generalize count : n - n = extra at total ⊢
  have zero : extra = 0 := by omega
  cases zero
  rfl

theorem extend_generator (n extra j : Nat) (bound : j < n) :
    (extend n extra).value (generator n j bound) =
      generator (n + extra) (extra + j) (by omega) := by
  induction extra with
  | zero =>
    simp only [extend, Nat.zero_add, Nat.add_zero, FieldEmbedding.identity_value]
  | succ extra ih =>
    rw [extend, FieldEmbedding.comp_value, FieldEmbedding.constants_value, ih]
    simp only [Nat.add_succ, Nat.succ_add, generator]

private theorem extend_cast (n extra m : Nat) (total : n + extra = m)
    (j : Nat) (bound : j < n) :
    (Eq.rec (motive := fun depth _ => FieldEmbedding (BaseTower n) (BaseTower depth))
      (extend n extra) total).value (generator n j bound) =
      generator m (extra + j) (by omega) := by
  cases total
  exact extend_generator n extra j bound

/-- The actual checked factory accepts every context with distinct keys as its own target. -/
theorem Inclusion.make?_self (keys : List ConstantKey) (unique : keys.Nodup) :
    (Inclusion.make? keys keys).isSome = true := by
  unfold Inclusion.make?
  simp only [unique, and_self, ↓reduceIte, Nat.le_refl, ↓reduceDIte,
    additional_self, List.nil_append, word_self]
  simp only [bind, Option.bind, exchange?, extend_self, comp_identity,
    bindings_identity, ↓reduceDIte, Option.isSome_some]

/-- A rational source has no provider generators to bind. -/
theorem bindings_empty (keys : List ConstantKey)
    (embedding : FieldEmbedding (BaseTower 0) (BaseTower keys.length)) :
    bindings [] keys embedding = true := rfl

/-- Every distinct-key target accepts the actual rational inclusion factory. -/
theorem Inclusion.make?_rational (keys : List ConstantKey) (unique : keys.Nodup) :
    (Inclusion.make? [] keys).isSome = true := by
  have all : keys.reverse.filter (fun _ => true) = keys.reverse :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  unfold Inclusion.make?
  simp only [List.nodup_nil, unique, and_self, ↓reduceIte, List.length_nil,
    Nat.zero_le, ↓reduceDIte, List.contains_nil, Bool.not_false, all, List.reverse_nil,
    List.append_nil, word_self, bind, Option.bind, exchange?, bindings_empty,
    ↓reduceDIte, Option.isSome_some]

/-- The transposition of adjacent positions, counted from the outside. -/
@[expose] def transpose (i j : Nat) : Nat :=
  if j = i then i + 1 else if j = i + 1 then i else j

theorem transpose_lt (n i j : Nat) (position : i + 1 < n) (bound : j < n) :
    transpose i j < n := by
  unfold transpose
  split <;> rename_i h
  · exact position
  · split
    · omega
    · exact bound

private theorem transpose_succ (i j : Nat) :
    transpose (i + 1) (j + 1) = transpose i j + 1 := by
  unfold transpose
  by_cases first : j = i
  · subst j; simp
  · by_cases second : j = i + 1
    · subst j; simp
    · simp [first, second]

/-- The actual adjacent exchange sends every generator to its transposed position. -/
theorem adjacent_generator (n i : Nat) (position : i + 1 < n) (j : Nat) (bound : j < n) :
    (adjacent n i position).value (generator n j bound) =
      generator n (transpose i j) (transpose_lt n i j position bound) := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero =>
        cases j with
        | zero =>
          change (FieldEmbedding.swap (BaseTower n)).value RationalFn.X = RationalFn.C RationalFn.X
          exact FieldEmbedding.swap_outer
        | succ j =>
          cases j with
          | zero =>
            change (FieldEmbedding.swap (BaseTower n)).value (RationalFn.C RationalFn.X) = RationalFn.X
            exact FieldEmbedding.swap_inner
          | succ j =>
            simp only [show transpose 0 (j + 2) = j + 2 by
              simp [transpose, show j + 2 ≠ 1 by omega]]
            change (FieldEmbedding.swap (BaseTower n)).value
              (RationalFn.C (RationalFn.C (generator n j (by omega)))) = _
            exact FieldEmbedding.swap_coefficient _
      | succ i =>
        cases j with
        | zero =>
          simp only [show transpose (i + 1) 0 = 0 by simp [transpose]]
          change (adjacent (n + 1) i (by omega)).rationalFunctions.value RationalFn.X = RationalFn.X
          exact FieldEmbedding.rationalFunctions_X _
        | succ j =>
          simp only [transpose_succ]
          change (adjacent (n + 1) i (by omega)).rationalFunctions.value
            (RationalFn.C (generator (n + 1) j (by omega))) =
              RationalFn.C (generator (n + 1) (transpose i j) _)
          rw [FieldEmbedding.rationalFunctions_value, RationalFn.mapCoeffs_C, ih]

/-- Generator positions follow the same ordered transpositions as the native maps. -/
@[expose] def image (positions : List Nat) (j : Nat) : Nat :=
  positions.foldl (fun previous i => transpose i previous) j

theorem image_append (first second : List Nat) (j : Nat) :
    image (first ++ second) j = image second (image first j) := by
  exact List.foldl_append

private theorem image_bubble (offset index j : Nat) :
    image ((List.range index).reverse.map (fun i => offset + i)) j =
      if j = offset + index then offset
      else if offset ≤ j ∧ j < offset + index then j + 1 else j := by
  induction index generalizing j with
  | zero =>
    simp only [List.range_zero, List.reverse_nil, List.map_nil, image, List.foldl_nil,
      Nat.add_zero]
    repeat first | omega | split
  | succ index ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    change image ((List.range index).reverse.map (fun i => offset + i))
      (transpose (offset + index) j) = _
    rw [ih]
    unfold transpose
    repeat first | omega | split

theorem image_lt (n : Nat) (positions : List Nat)
    (bounds : ∀ i ∈ positions, i + 1 < n) (j : Nat) (bound : j < n) :
    image positions j < n := by
  induction positions generalizing j with
  | nil => exact bound
  | cons i rest ih =>
    exact ih (fun k member => bounds k (List.mem_cons_of_mem i member))
      (transpose i j) (transpose_lt n i j (bounds i (List.mem_cons_self)) bound)

/-- The actual exchange factory accepts every sequence of valid adjacent positions. -/
theorem exchange?_success (n : Nat) (positions : List Nat)
    (bounds : ∀ i ∈ positions, i + 1 < n) :
    (exchange? n positions).isSome = true := by
  induction positions with
  | nil => rfl
  | cons i rest ih =>
    have first := bounds i (List.mem_cons_self)
    simp only [exchange?, first, ↓reduceDIte, Option.isSome_map]
    exact ih (fun k member => bounds k (List.mem_cons_of_mem i member))

/-- Accepted native compositions act on generators in their actual execution order. -/
theorem exchange?_generator (n : Nat) (positions : List Nat)
    (bounds : ∀ i ∈ positions, i + 1 < n)
    (map : FieldEmbedding (BaseTower n) (BaseTower n)) (accepted : exchange? n positions = some map)
    (j : Nat) (bound : j < n) :
    map.value (generator n j bound) = generator n (image positions j) (image_lt n positions bounds j bound) := by
  induction positions generalizing map j with
  | nil =>
    simp only [exchange?, Option.some.injEq] at accepted
    subst map
    exact FieldEmbedding.identity_value _
  | cons i rest ih =>
    have first := bounds i (List.mem_cons_self)
    simp only [exchange?, first, ↓reduceDIte] at accepted
    cases later : exchange? n rest with
    | none => simp only [later, Option.map_none] at accepted; contradiction
    | some following =>
      simp only [later, Option.map_some, Option.some.injEq] at accepted
      subst map
      rw [FieldEmbedding.comp_value, adjacent_generator]
      exact ih (fun k member => bounds k (List.mem_cons_of_mem i member)) following later
        (transpose i j) (transpose_lt n i j first bound)

private theorem additional_perm (source target : List ConstantKey)
    (sourceUnique : source.Nodup) (targetUnique : target.Nodup) (included : source ⊆ target) :
    (target.reverse.filter (fun key => !source.contains key) ++ source.reverse).Perm target.reverse := by
  have sourceReverse : source.reverse.Nodup := sourceUnique.perm (List.reverse_perm source).symm
  have targetReverse : target.reverse.Nodup := targetUnique.perm (List.reverse_perm target).symm
  have retained : (target.reverse.filter (fun key => source.contains key)).Perm source.reverse := by
    apply List.perm_iff_count.mpr
    intro key
    rw [List.Nodup.count (targetReverse.filter (fun key => source.contains key)), sourceReverse.count]
    have membership : key ∈ target.reverse.filter (fun key => source.contains key) ↔ key ∈ source.reverse := by
      simp only [List.mem_filter, List.mem_reverse, List.contains_iff_mem]
      exact ⟨And.right, fun present => ⟨included present, present⟩⟩
    simp only [membership]
  have partition := List.filter_append_perm (fun key => !source.contains key) target.reverse
  simp only [Bool.not_not] at partition
  exact (retained.symm.append_left _).trans partition

private theorem word_success (source target : List ConstantKey) (offset : Nat)
    (permutation : source.Perm target) : (word source target offset).isSome = true := by
  induction target generalizing source offset with
  | nil =>
    have empty : source = [] := List.eq_nil_of_length_eq_zero (by simpa using permutation.length_eq)
    subst source
    rfl
  | cons key target ih =>
    have present : key ∈ source := permutation.symm.subset List.mem_cons_self
    have found : source.findIdx? (fun previous => previous == key) =
        some (source.findIdx (fun previous => previous == key)) :=
      List.findIdx?_eq_some_of_exists ⟨key, present, by simp⟩
    have reduced : (source.erase key).Perm target := by
      simpa using permutation.erase key
    have later := ih (source.erase key) (offset + 1) reduced
    simp only [word, found, bind, Option.bind]
    cases result : word (source.erase key) target (offset + 1) with
    | none => simp only [result, Option.isSome_none] at later; contradiction
    | some positions => rfl

private theorem word_fixed (source target : List ConstantKey) (offset : Nat)
    (positions : List Nat) (accepted : word source target offset = some positions)
    (j : Nat) (before : j < offset) : image positions j = j := by
  induction target generalizing source offset positions with
  | nil =>
    simp only [word] at accepted
    split at accepted
    · cases Option.some.inj accepted
      rfl
    · contradiction
  | cons key target ih =>
    simp only [word] at accepted
    cases found : source.findIdx? (fun previous => previous == key) with
    | none => simp only [found, bind, Option.bind] at accepted; contradiction
    | some index =>
      simp only [found, bind, Option.bind] at accepted
      cases later : word (source.erase key) target (offset + 1) with
      | none => simp only [later] at accepted; contradiction
      | some remaining =>
        simp only [later, Option.pure_def, Option.some.injEq] at accepted
        subst positions
        rw [image_append, image_bubble]
        simp only [show j ≠ offset + index by omega, show ¬(offset ≤ j ∧ j < offset + index) by omega,
          ↓reduceIte]
        exact ih (source.erase key) (offset + 1) remaining later (by omega)

private theorem word_binding (source target : List ConstantKey) (offset : Nat)
    (positions : List Nat) (accepted : word source target offset = some positions)
    (j : Nat) (bound : j < source.length) :
    ∃ k, ∃ targetBound : k < target.length,
      source[j] = target[k] ∧ image positions (offset + j) = offset + k := by
  induction target generalizing source offset positions j with
  | nil =>
    simp only [word] at accepted
    split at accepted
    · rename_i empty
      have size : source.length = 0 := List.length_eq_zero_iff.mpr (List.isEmpty_iff.mp empty)
      omega
    · contradiction
  | cons key target ih =>
    simp only [word] at accepted
    cases found : source.findIdx? (fun previous => previous == key) with
    | none => simp only [found, bind, Option.bind] at accepted; contradiction
    | some index =>
      simp only [found, bind, Option.bind] at accepted
      obtain ⟨indexBound, matched, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
      have erase : source.erase key = source.eraseIdx index := by
        rw [List.erase_eq_eraseIdx, List.idxOf?, found]
      have reducedSize : (source.erase key).length = source.length - 1 := by
        rw [erase, List.length_eraseIdx]
        simp only [indexBound, ↓reduceIte]
      cases later : word (source.erase key) target (offset + 1) with
      | none => simp only [later] at accepted; contradiction
      | some remaining =>
        simp only [later, Option.pure_def, Option.some.injEq] at accepted
        subst positions
        by_cases selected : j = index
        · subst j
          refine ⟨0, by simp, ?_, ?_⟩
          · simpa using eq_of_beq matched
          · rw [image_append, image_bubble]
            simp only [↓reduceIte, Nat.add_zero]
            exact word_fixed (source.erase key) target (offset + 1) remaining later offset (by omega)
        · by_cases before : j < index
          · have reducedBound : j < (source.erase key).length := by omega
            have coefficient : (source.erase key)[j] = source[j] := by
              simp only [erase]
              exact List.getElem_eraseIdx_of_lt _ before
            obtain ⟨k, targetBound, binding, moved⟩ :=
              ih (source.erase key) (offset + 1) remaining later j reducedBound
            refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
            · simpa only [List.getElem_cons_succ] using coefficient.symm.trans binding
            · rw [image_append, image_bubble]
              simp only [show offset + j ≠ offset + index by omega,
                show offset ≤ offset + j ∧ offset + j < offset + index by omega, and_self, ↓reduceIte]
              rw [show offset + j + 1 = offset + 1 + j by omega, moved]
              omega
          · have reducedBound : j - 1 < (source.erase key).length := by omega
            have coefficient : (source.erase key)[j - 1] = source[j] := by
              simp only [erase]
              have previous := List.getElem_eraseIdx_of_ge
                (l := source) (i := index) (j := j - 1) (by simpa only [erase] using reducedBound)
                (by omega)
              simpa only [show j - 1 + 1 = j by omega] using previous
            obtain ⟨k, targetBound, binding, moved⟩ :=
              ih (source.erase key) (offset + 1) remaining later (j - 1) reducedBound
            refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
            · simpa only [List.getElem_cons_succ] using coefficient.symm.trans binding
            · rw [image_append, image_bubble]
              simp only [show offset + j ≠ offset + index by omega,
                show ¬(offset ≤ offset + j ∧ offset + j < offset + index) by omega, ↓reduceIte]
              rw [show offset + j = offset + 1 + (j - 1) by omega, moved]
              omega

private theorem word_bounds (n : Nat) (source target : List ConstantKey)
    (offset : Nat) (positions : List Nat) (size : source.length + offset = n)
    (accepted : word source target offset = some positions) :
    ∀ i ∈ positions, i + 1 < n := by
  induction target generalizing source offset positions with
  | nil =>
    simp only [word] at accepted
    split at accepted
    · cases Option.some.inj accepted
      simp
    · contradiction
  | cons key target ih =>
    simp only [word] at accepted
    cases found : source.findIdx? (fun previous => previous == key) with
    | none => simp only [found, bind, Option.bind] at accepted; contradiction
    | some index =>
      simp only [found, bind, Option.bind] at accepted
      obtain ⟨indexBound, matched, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
      have present : key ∈ source := by
        rw [← eq_of_beq matched]
        exact List.getElem_mem indexBound
      cases later : word (source.erase key) target (offset + 1) with
      | none => simp only [later] at accepted; contradiction
      | some remaining =>
        simp only [later, Option.pure_def, Option.some.injEq] at accepted
        subst positions
        intro i member
        rcases List.mem_append.mp member with first | rest
        · obtain ⟨j, inRange, rfl⟩ := List.mem_map.mp first
          have before : j < index := List.mem_range.mp (List.mem_reverse.mp inRange)
          omega
        · have reduced : (source.erase key).length + (offset + 1) = n := by
            rw [List.length_erase_of_mem present]
            omega
          exact ih (source.erase key) (offset + 1) remaining reduced later i rest

private theorem word_checked (source target additional : List ConstantKey) (extra : Nat)
    (total : source.length + extra = target.length) (additionalSize : additional.length = extra)
    (positions : List Nat) (accepted : word (additional ++ source.reverse) target.reverse 0 = some positions)
    (map : FieldEmbedding (BaseTower target.length) (BaseTower target.length))
    (acceptedMap : exchange? target.length positions = some map) :
    bindings source target
      ((Eq.rec (motive := fun depth _ => FieldEmbedding (BaseTower source.length) (BaseTower depth))
        (extend source.length extra) total).comp map) = true := by
  have size : (additional ++ source.reverse).length + 0 = target.length := by
    simp only [List.length_append, List.length_reverse, additionalSize]
    omega
  have bounds := word_bounds target.length (additional ++ source.reverse) target.reverse 0 positions size accepted
  apply List.all_eq_true.mpr
  intro i _
  have inputBound : extra + i.val < (additional ++ source.reverse).length := by
    simp only [List.length_append, List.length_reverse, additionalSize]
    omega
  obtain ⟨k, targetBound, key, moved⟩ :=
    word_binding (additional ++ source.reverse) target.reverse 0 positions accepted (extra + i.val) inputBound
  have targetBound' : k < target.length := by simpa only [List.length_reverse] using targetBound
  have inputKey : (additional ++ source.reverse)[extra + i.val] = source.reverse[i] := by
    simpa only [additionalSize, Nat.add_comm, Fin.getElem_fin] using
      (List.getElem_append_right' additional (l₂ := source.reverse) (i := i.val)
        (by simpa only [List.length_reverse] using i.isLt)).symm
  apply List.any_eq_true.mpr
  refine ⟨⟨k, targetBound'⟩, List.mem_finRange _, ?_⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    exact inputKey.symm.trans key
  · apply decide_eq_true
    rw [FieldEmbedding.comp_value, extend_cast]
    rw [exchange?_generator target.length positions bounds map acceptedMap]
    simp only [Nat.zero_add] at moved
    simp only [moved]

/-- The native key-bound factory accepts every distinct-key source contained
in a distinct-key target, including arbitrary changes of provider order. -/
theorem Inclusion.make?_success (source target : List ConstantKey)
    (sourceUnique : source.Nodup) (targetUnique : target.Nodup) (included : source ⊆ target) :
    (Inclusion.make? source target).isSome = true := by
  let additional := target.reverse.filter (fun key => !source.contains key)
  have permutation : (additional ++ source.reverse).Perm target.reverse :=
    additional_perm source target sourceUnique targetUnique included
  have size : additional.length + source.length = target.length := by
    simpa only [List.length_append, List.length_reverse] using permutation.length_eq
  have depth : source.length ≤ target.length := by omega
  let extra := target.length - source.length
  have additionalSize : additional.length = extra := by dsimp [extra]; omega
  have total : source.length + extra = target.length := by dsimp [extra]; omega
  obtain ⟨positions, accepted⟩ :=
    Option.isSome_iff_exists.mp (word_success (additional ++ source.reverse) target.reverse 0 permutation)
  have bounds := word_bounds target.length (additional ++ source.reverse) target.reverse 0 positions
    (by simp only [List.length_append, List.length_reverse]; omega) accepted
  obtain ⟨map, acceptedMap⟩ := Option.isSome_iff_exists.mp (exchange?_success target.length positions bounds)
  have checked := word_checked source target additional extra total additionalSize positions accepted map acceptedMap
  dsimp only [additional] at accepted
  dsimp only [extra] at checked
  simp only [Inclusion.make?, sourceUnique, targetUnique, and_self, ↓reduceIte,
    depth, ↓reduceDIte, accepted, bind, Option.bind, acceptedMap, checked, Option.isSome_some]

/-- A checked native map includes every source provider key in its target. -/
theorem Inclusion.subset {source target : List ConstantKey} (inclusion : Inclusion source target) :
    source ⊆ target := by
  intro key present
  obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp (List.mem_reverse.mpr present)
  have sourceBound : i < source.length := by simpa only [List.length_reverse] using bound
  obtain ⟨j, binding, _⟩ := inclusion.binding ⟨i, sourceBound⟩
  have keyEqual : target.reverse[j] = key := by
    simp only [Fin.getElem_fin] at binding
    exact binding.symm.trans equal
  apply List.mem_reverse.mp
  rw [← keyEqual]
  exact List.getElem_mem _

/-- The checked factory accepts exactly distinct key paths with source keys
contained in the target. Literal variable bindings supply necessity. -/
theorem Inclusion.make?_isSome (source target : List ConstantKey) :
    (Inclusion.make? source target).isSome = true ↔
      source.Nodup ∧ target.Nodup ∧ source ⊆ target := by
  constructor
  · intro accepted
    have unique : source.Nodup ∧ target.Nodup := by
      by_cases present : source.Nodup ∧ target.Nodup
      · exact present
      · simp only [Inclusion.make?, present, ↓reduceIte, Option.isSome_none,
          Bool.false_eq_true] at accepted
    obtain ⟨inclusion, produced⟩ := Option.isSome_iff_exists.mp accepted
    exact ⟨unique.1, unique.2, inclusion.subset⟩
  · rintro ⟨sourceUnique, targetUnique, included⟩
    exact Inclusion.make?_success source target sourceUnique targetUnique included

end Hex.RealClosure.BaseContext.BaseTower

namespace Hex.RealClosure.BaseContext

/-- The actual real-provider chain factory accepts every distinct-key inclusion,
without rebuilding the chains or their provider progress proofs. -/
theorem RealChain.reorder?_success {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    (target : RealChain registry L targetApprox targetSign)
    (source : RealChain registry K sourceApprox sourceSign)
    (sourceUnique : source.keys.Nodup) (targetUnique : target.keys.Nodup)
    (included : source.keys ⊆ target.keys) : (target.reorder? source).isSome = true := by
  simp only [RealChain.reorder?, Option.isSome_map]
  exact BaseTower.Inclusion.make?_success source.keys target.keys sourceUnique targetUnique included

/-- Real-prefix reordering accepts exactly distinct contained provider paths. -/
theorem RealChain.reorder?_isSome {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    (target : RealChain registry L targetApprox targetSign)
    (source : RealChain registry K sourceApprox sourceSign) :
    (target.reorder? source).isSome = true ↔
      source.keys.Nodup ∧ target.keys.Nodup ∧ source.keys ⊆ target.keys := by
  simp only [RealChain.reorder?, Option.isSome_map, BaseTower.Inclusion.make?_isSome]

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.BaseTower.Inclusion.make?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.Inclusion.make?_self
/-- info: 'Hex.RealClosure.BaseContext.BaseTower.adjacent_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.adjacent_generator
/-- info: 'Hex.RealClosure.BaseContext.BaseTower.Inclusion.make?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.Inclusion.make?_success
/-- info: 'Hex.RealClosure.BaseContext.RealChain.reorder?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.reorder?_success

/-- info: 'Hex.RealClosure.BaseContext.BaseTower.Inclusion.subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.Inclusion.subset

/-- info: 'Hex.RealClosure.BaseContext.BaseTower.Inclusion.make?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.Inclusion.make?_isSome

/-- info: 'Hex.RealClosure.BaseContext.RealChain.reorder?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.reorder?_isSome
