/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.SupportPartition
public import HexBerlekampZassenhaus.Classical.CombinationIterator

public section
set_option backward.proofsInPublic true

/-!
# Streaming direct-combination iterator

The runtime iterator does not allocate a list of combinations.  These theorems
relate its depth-first traversal to the extensional
`subsetsOfSizeWithComplement` specification used only in proofs.
-/

namespace HexBerlekampZassenhausMathlib

/-- Structural facts for a size-indexed selected/rejected partition. -/
theorem subsetsOfSizeWithComplement_structure {α : Type} [DecidableEq α] :
    ∀ (xs selected remaining : List α) (choose : Nat),
      xs.Nodup →
      (selected, remaining) ∈
        Hex.subsetsOfSizeWithComplement xs choose →
      selected.Nodup ∧
        remaining.Nodup ∧
        Disjoint selected.toFinset remaining.toFinset ∧
        selected.toFinset ∪ remaining.toFinset = xs.toFinset ∧
        selected.length = choose := by
  intro xs
  induction xs with
  | nil =>
      intro selected remaining choose _ hmem
      cases choose with
      | zero =>
          simp only [Hex.subsetsOfSizeWithComplement, List.mem_singleton,
            Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          simp
      | succ choose =>
          simp [Hex.subsetsOfSizeWithComplement] at hmem
  | cons x xs ih =>
      intro selected remaining choose hnodup hmem
      have hx : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnodup).2
      cases choose with
      | zero =>
          simp only [Hex.subsetsOfSizeWithComplement, List.mem_singleton,
            Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          simp [hnodup]
      | succ choose =>
          simp only [Hex.subsetsOfSizeWithComplement, List.mem_append,
            List.mem_map] at hmem
          rcases hmem with
            ⟨⟨selected, remaining⟩, hmem, hshape⟩ |
            ⟨⟨selected, remaining⟩, hmem, hshape⟩
          · simp only [Prod.mk.injEq] at hshape
            obtain ⟨rfl, rfl⟩ := hshape
            obtain ⟨hsel, hrem, hdisj, hunion, hlen⟩ :=
              ih selected remaining choose hxs hmem
            have hxsel : x ∉ selected := fun hxmem =>
              hx ((Hex.subsetsOfSizeWithComplement_mem xs choose
                (selected, remaining) hmem).1 x hxmem)
            have hxrem : x ∉ remaining := fun hxmem =>
              hx ((Hex.subsetsOfSizeWithComplement_mem xs choose
                (selected, remaining) hmem).2 x hxmem)
            refine ⟨List.nodup_cons.mpr ⟨hxsel, hsel⟩, hrem, ?_, ?_, by simp [hlen]⟩
            · rw [Finset.disjoint_left]
              intro a ha ar
              have ha' : a = x ∨ a ∈ selected.toFinset := by
                simpa using ha
              rcases ha' with rfl | ha
              · exact hxrem (by simpa using ar)
              · exact Finset.disjoint_left.mp hdisj ha ar
            · ext y
              have hu :
                  y ∈ selected.toFinset ∪ remaining.toFinset ↔
                    y ∈ xs.toFinset := by rw [hunion]
              simp only [List.toFinset_cons, Finset.mem_union,
                Finset.mem_insert, List.mem_toFinset] at hu ⊢
              tauto
          · simp only [Prod.mk.injEq] at hshape
            obtain ⟨rfl, rfl⟩ := hshape
            obtain ⟨hsel, hrem, hdisj, hunion, hlen⟩ :=
              ih selected remaining (choose + 1) hxs hmem
            have hxsel : x ∉ selected := fun hxmem =>
              hx ((Hex.subsetsOfSizeWithComplement_mem xs (choose + 1)
                (selected, remaining) hmem).1 x hxmem)
            have hxrem : x ∉ remaining := fun hxmem =>
              hx ((Hex.subsetsOfSizeWithComplement_mem xs (choose + 1)
                (selected, remaining) hmem).2 x hxmem)
            refine ⟨hsel, List.nodup_cons.mpr ⟨hxrem, hrem⟩, ?_, ?_, hlen⟩
            · rw [Finset.disjoint_left]
              intro a ha ar
              have ar' : a = x ∨ a ∈ remaining.toFinset := by
                simpa using ar
              rcases ar' with rfl | ar
              · exact hxsel (by simpa using ha)
              · exact Finset.disjoint_left.mp hdisj ha ar
            · ext y
              have hu :
                  y ∈ selected.toFinset ∪ remaining.toFinset ↔
                    y ∈ xs.toFinset := by rw [hunion]
              simp only [List.toFinset_cons, Finset.mem_union,
                Finset.mem_insert, List.mem_toFinset] at hu ⊢
              tauto

/-- Filtering a list by a predicate produces the corresponding member of the
size-indexed selected/rejected enumerator. -/
theorem filter_split_mem_subsetsOfSizeWithComplement
    {α : Type} (P : α → Bool) :
    ∀ xs : List α,
      (xs.filter P, xs.filter (fun x => !P x)) ∈
        Hex.subsetsOfSizeWithComplement xs (xs.filter P).length := by
  intro xs
  induction xs with
  | nil => simp [Hex.subsetsOfSizeWithComplement]
  | cons x xs ih =>
      cases hx : P x with
      | false =>
          simp only [List.filter_cons, hx, Bool.false_eq_true, if_false,
            Bool.not_false, if_true]
          cases hlen : (xs.filter P).length with
          | zero =>
              have hfilter : xs.filter P = [] :=
                List.length_eq_zero_iff.mp hlen
              have hall : ∀ a ∈ xs, P a = false := by
                intro a ha
                cases hpa : P a with
                | false => rfl
                | true =>
                    have : a ∈ xs.filter P :=
                      List.mem_filter.mpr ⟨ha, hpa⟩
                    rw [hfilter] at this
                    contradiction
              have hreject :
                  xs.filter (fun a => !P a) = xs := by
                apply List.filter_eq_self.mpr
                intro a ha
                simp [hall a ha]
              simp [Hex.subsetsOfSizeWithComplement, hfilter, hreject]
          | succ n =>
              simp only [Hex.subsetsOfSizeWithComplement, List.mem_append,
                List.mem_map]
              exact Or.inr ⟨(xs.filter P, xs.filter fun x => !P x), by
                simpa [hlen] using ih, rfl⟩
      | true =>
          simp only [List.filter_cons, hx, if_true, Bool.not_true,
            Bool.false_eq_true, if_false, List.length_cons,
            Hex.subsetsOfSizeWithComplement, List.mem_append, List.mem_map]
          exact Or.inl
            ⟨(xs.filter P, xs.filter fun x => !P x), ih, rfl⟩

private theorem directSelectedDegree_cons_reverse
    (basis : Hex.LiftData)
    (head x : Hex.DirectLiftedIndex basis)
    (selectedRev : List (Hex.DirectLiftedIndex basis)) :
    Hex.directSelectedDegree basis
        (head :: (x :: selectedRev).reverse) =
      Hex.directSelectedDegree basis (head :: selectedRev.reverse) +
        (Hex.directLiftedFactor basis x).degree?.getD 0 := by
  simp [Hex.directSelectedDegree, Hex.directSelectedFactors,
    List.reverse_cons, List.map_append, List.foldl_append]

private theorem directSelectedTrail_cons_reverse
    (basis : Hex.LiftData)
    (head x : Hex.DirectLiftedIndex basis)
    (selectedRev : List (Hex.DirectLiftedIndex basis)) :
    Hex.directSelectedTrail basis
        (head :: (x :: selectedRev).reverse) =
      Hex.directSelectedTrail basis (head :: selectedRev.reverse) *
          (Hex.directLiftedFactor basis x).coeff 0 %
        (Hex.liftModulus basis : Int) := by
  simp [Hex.directSelectedTrail, Hex.directSelectedFactors,
    List.reverse_cons, List.map_append, List.foldl_append]

private theorem tryDirectCandidate_eq_tryDirectSplit
    (coreLc : Int) (target : Hex.ZPoly) (basis : Hex.LiftData)
    (selected : List (Hex.DirectLiftedIndex basis))
    (selectedDegree : Nat) (selectedTrail : Int)
    (hdegree :
      selectedDegree = Hex.directSelectedDegree basis selected)
    (htrail :
      selectedTrail = Hex.directSelectedTrail basis selected) :
    Hex.tryDirectCandidate coreLc target (Hex.liftModulus basis)
        (Hex.directSelectedFactors basis selected) selectedDegree selectedTrail =
      Hex.tryDirectSplit coreLc target basis selected := by
  rw [hdegree, htrail]
  rfl

/-- A successful leaf exposes its exact indexed split and candidate check. -/
theorem scanDirectCombinations_found
    (coreLc : Int) (target : Hex.ZPoly) (basis : Hex.LiftData)
    (head : Hex.DirectLiftedIndex basis) :
    ∀ (xs : List (Hex.DirectLiftedIndex basis)) (choose : Nat)
      (selectedRev rejectedRev : List (Hex.DirectLiftedIndex basis))
      (selectedDegree : Nat) (selectedTrail : Int)
      (split : Hex.DirectSplit basis) (tried : Nat),
      selectedDegree =
          Hex.directSelectedDegree basis (head :: selectedRev.reverse) →
      selectedTrail =
          Hex.directSelectedTrail basis (head :: selectedRev.reverse) →
      Hex.scanDirectCombinations coreLc target basis head xs choose
          selectedRev rejectedRev selectedDegree selectedTrail =
        .found split tried →
      ∃ selected remaining,
        (selected, remaining) ∈
          Hex.subsetsOfSizeWithComplement xs choose ∧
        split.selected =
          head :: (selectedRev.reverse ++ selected) ∧
        split.remaining = rejectedRev.reverse ++ remaining ∧
        Hex.tryDirectSplit coreLc target basis split.selected =
          some (split.candidate, split.quotient) := by
  intro xs
  induction xs with
  | nil =>
      intro choose selectedRev rejectedRev selectedDegree selectedTrail
        split tried hdegree htrail h
      cases choose with
      | zero =>
          simp only [Hex.scanDirectCombinations] at h
          split at h
          next candidate quotient heval =>
            cases h
            refine ⟨[], [], ?_, ?_, ?_, ?_⟩
            · simp [Hex.subsetsOfSizeWithComplement]
            · simp
            · simp
            · rw [tryDirectCandidate_eq_tryDirectSplit
                coreLc target basis (head :: selectedRev.reverse)
                selectedDegree selectedTrail hdegree htrail] at heval
              exact heval
          next =>
            contradiction
      | succ choose =>
          simp [Hex.scanDirectCombinations] at h
  | cons x xs ih =>
      intro choose selectedRev rejectedRev selectedDegree selectedTrail
        split tried hdegree htrail h
      cases choose with
      | zero =>
          simp only [Hex.scanDirectCombinations] at h
          split at h
          next candidate quotient heval =>
            cases h
            refine ⟨[], x :: xs, ?_, ?_, ?_, ?_⟩
            · simp [Hex.subsetsOfSizeWithComplement]
            · simp
            · simp
            · rw [tryDirectCandidate_eq_tryDirectSplit
                coreLc target basis (head :: selectedRev.reverse)
                selectedDegree selectedTrail hdegree htrail] at heval
              exact heval
          next =>
            contradiction
      | succ choose =>
          simp only [Hex.scanDirectCombinations] at h
          generalize hincluded :
              Hex.scanDirectCombinations coreLc target basis head xs choose
                (x :: selectedRev) rejectedRev
                (selectedDegree +
                  (Hex.directLiftedFactor basis x).degree?.getD 0)
                (selectedTrail *
                    (Hex.directLiftedFactor basis x).coeff 0 %
                  (Hex.liftModulus basis : Int)) =
              included at h
          have hdegree' :
              selectedDegree +
                  (Hex.directLiftedFactor basis x).degree?.getD 0 =
                Hex.directSelectedDegree basis
                  (head :: (x :: selectedRev).reverse) := by
            rw [directSelectedDegree_cons_reverse, ← hdegree]
          have htrail' :
              selectedTrail *
                    (Hex.directLiftedFactor basis x).coeff 0 %
                  (Hex.liftModulus basis : Int) =
                Hex.directSelectedTrail basis
                  (head :: (x :: selectedRev).reverse) := by
            rw [directSelectedTrail_cons_reverse, ← htrail]
          cases included with
          | found includedSplit includedTried =>
              cases h
              obtain ⟨selected, remaining, hmem, hselected, hremaining, heval⟩ :=
                ih choose (x :: selectedRev) rejectedRev
                  _ _ split tried hdegree' htrail' hincluded
              refine ⟨x :: selected, remaining, ?_, ?_, hremaining, heval⟩
              · simp only [Hex.subsetsOfSizeWithComplement, List.mem_append,
                  List.mem_map]
                exact Or.inl ⟨(selected, remaining), hmem, rfl⟩
              · simpa [List.reverse_cons, List.append_assoc] using hselected
          | exhausted includedTried =>
              generalize hrejected :
                  Hex.scanDirectCombinations coreLc target basis head xs
                    (choose + 1) selectedRev (x :: rejectedRev)
                    selectedDegree selectedTrail = rejected at h
              cases rejected with
              | exhausted rejectedTried =>
                  contradiction
              | found rejectedSplit rejectedTried =>
                  cases h
                  obtain ⟨selected, remaining, hmem, hselected, hremaining, heval⟩ :=
                    ih (choose + 1) selectedRev (x :: rejectedRev)
                      selectedDegree selectedTrail split rejectedTried
                      hdegree htrail hrejected
                  refine ⟨selected, x :: remaining, ?_, hselected, ?_, heval⟩
                  · simp only [Hex.subsetsOfSizeWithComplement, List.mem_append,
                      List.mem_map]
                    exact Or.inr ⟨(selected, remaining), hmem, rfl⟩
                  · simpa [List.reverse_cons, List.append_assoc] using hremaining

/-- Every extensionally specified working split is reached by the streaming
iterator (possibly after an earlier working split). -/
theorem scanDirectCombinations_finds
    (coreLc : Int) (target : Hex.ZPoly) (basis : Hex.LiftData)
    (head : Hex.DirectLiftedIndex basis) :
    ∀ (xs : List (Hex.DirectLiftedIndex basis)) (choose : Nat)
      (selectedRev rejectedRev : List (Hex.DirectLiftedIndex basis))
      (selectedDegree : Nat) (selectedTrail : Int)
      (selected remaining : List (Hex.DirectLiftedIndex basis))
      (candidate quotient : Hex.ZPoly),
      selectedDegree =
          Hex.directSelectedDegree basis (head :: selectedRev.reverse) →
      selectedTrail =
          Hex.directSelectedTrail basis (head :: selectedRev.reverse) →
      (selected, remaining) ∈
          Hex.subsetsOfSizeWithComplement xs choose →
      Hex.tryDirectSplit coreLc target basis
          (head :: (selectedRev.reverse ++ selected)) =
        some (candidate, quotient) →
      ∃ split tried,
        Hex.scanDirectCombinations coreLc target basis head xs choose
          selectedRev rejectedRev selectedDegree selectedTrail =
        .found split tried := by
  intro xs
  induction xs with
  | nil =>
      intro choose selectedRev rejectedRev selectedDegree selectedTrail
        selected remaining candidate quotient hdegree htrail hmem hworks
      cases choose with
      | zero =>
          simp only [Hex.subsetsOfSizeWithComplement, List.mem_singleton,
            Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          simp only [List.append_nil] at hworks
          rw [← tryDirectCandidate_eq_tryDirectSplit
            coreLc target basis (head :: selectedRev.reverse)
            selectedDegree selectedTrail hdegree htrail] at hworks
          simp only [Hex.scanDirectCombinations, hworks]
          exact ⟨_, 1, rfl⟩
      | succ choose =>
          simp [Hex.subsetsOfSizeWithComplement] at hmem
  | cons x xs ih =>
      intro choose selectedRev rejectedRev selectedDegree selectedTrail
        selected remaining candidate quotient hdegree htrail hmem hworks
      cases choose with
      | zero =>
          simp only [Hex.subsetsOfSizeWithComplement, List.mem_singleton,
            Prod.mk.injEq] at hmem
          obtain ⟨rfl, rfl⟩ := hmem
          simp only [List.append_nil] at hworks
          rw [← tryDirectCandidate_eq_tryDirectSplit
            coreLc target basis (head :: selectedRev.reverse)
            selectedDegree selectedTrail hdegree htrail] at hworks
          simp only [Hex.scanDirectCombinations, hworks]
          exact ⟨_, 1, rfl⟩
      | succ choose =>
          simp only [Hex.subsetsOfSizeWithComplement, List.mem_append,
            List.mem_map] at hmem
          rcases hmem with
            ⟨⟨selected, remaining⟩, hmem, hshape⟩ |
            ⟨⟨selected, remaining⟩, hmem, hshape⟩
          · simp only [Prod.mk.injEq] at hshape
            obtain ⟨rfl, rfl⟩ := hshape
            have hworks' :
                Hex.tryDirectSplit coreLc target basis
                    (head :: ((x :: selectedRev).reverse ++ selected)) =
                  some (candidate, quotient) := by
              simpa [List.reverse_cons, List.append_assoc] using hworks
            obtain ⟨split, tried, hfound⟩ :=
              ih choose (x :: selectedRev) rejectedRev
                (selectedDegree +
                  (Hex.directLiftedFactor basis x).degree?.getD 0)
                (selectedTrail *
                    (Hex.directLiftedFactor basis x).coeff 0 %
                  (Hex.liftModulus basis : Int))
                selected remaining candidate quotient
                (by rw [directSelectedDegree_cons_reverse, ← hdegree])
                (by rw [directSelectedTrail_cons_reverse, ← htrail])
                hmem hworks'
            simp only [Hex.scanDirectCombinations, hfound]
            exact ⟨split, tried, rfl⟩
          · simp only [Prod.mk.injEq] at hshape
            obtain ⟨rfl, rfl⟩ := hshape
            generalize hincluded :
                Hex.scanDirectCombinations coreLc target basis head xs choose
                  (x :: selectedRev) rejectedRev
                  (selectedDegree +
                    (Hex.directLiftedFactor basis x).degree?.getD 0)
                  (selectedTrail *
                      (Hex.directLiftedFactor basis x).coeff 0 %
                    (Hex.liftModulus basis : Int)) =
                included
            cases included with
            | found split tried =>
                simp only [Hex.scanDirectCombinations, hincluded]
                exact ⟨split, tried, rfl⟩
            | exhausted triedLeft =>
                have hworks' :
                    Hex.tryDirectSplit coreLc target basis
                        (head :: (selectedRev.reverse ++ selected)) =
                      some (candidate, quotient) :=
                  hworks
                obtain ⟨split, tried, hfound⟩ :=
                  ih (choose + 1) selectedRev (x :: rejectedRev)
                    selectedDegree selectedTrail selected remaining
                    candidate quotient hdegree htrail hmem hworks'
                simp only [Hex.scanDirectCombinations, hincluded, hfound]
                exact ⟨split, triedLeft + tried, rfl⟩

/-- Successful exact quotient and candidate identities at a checked leaf. -/
theorem tryDirectSplit_some
    {coreLc : Int} {target : Hex.ZPoly} {basis : Hex.LiftData}
    {selected : List (Hex.DirectLiftedIndex basis)}
    {candidate quotient : Hex.ZPoly}
    (h :
      Hex.tryDirectSplit coreLc target basis selected =
        some (candidate, quotient)) :
    candidate =
        Hex.directCandidate coreLc (Hex.liftModulus basis)
          (Hex.directSelectedFactors basis selected) ∧
      quotient * candidate = target := by
  unfold Hex.tryDirectSplit Hex.tryDirectCandidate at h
  split at h
  · simp only at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨quotient', hquotient', hresult⟩ := h
      cases hresult
      exact ⟨rfl, Hex.exactQuotient?_product hquotient'⟩
    · contradiction
  · contradiction

end HexBerlekampZassenhausMathlib
