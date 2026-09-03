/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CanonSpec
import all HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.Refine

public section

/-!
Code-comparison faithfulness: the transcription's lazily threaded
level-code comparison (`compCanon` / `eqlevCanon` / `canoncode`)
implements lexicographic comparison of the current path's refinement
codes against the incumbent leaf's code list. This is the code-side
counterpart of `LeafFaithful`, and the per-event clause suite the
domination induction threads through the search quartet.

The discipline being captured, with `cs` the codes of the current
path (one per level, `1`-indexed) and `bs` the incumbent's codes
(`canonlevel` of them, extended by the sentinel):

- `compCanon = 0` means the path's codes match the incumbent's
  through the whole path, and `eqlevCanon` records the path length;
- `compCanon = -1` means the codes diverged downward at some level
  `j`, `eqlevCanon` is frozen at `j - 1`, and no comparison deeper
  than `j` is ever consulted — lexicographically the whole subtree
  is smaller;
- `compCanon = 1` means the codes diverged upward at `j`; from `j`
  on, `othernode` overwrites `canoncode` with the path's own codes,
  so that when the path reaches a leaf and is installed the stored
  code list is already the new incumbent's.

`CodeCmpInv` packages the three states with the exact `canoncode`
contents; the events are `otherNodePrep` (one comparison step),
`recover` (the unwind restore, in two forms: the invariant-carrying
one and the reset form used after a leaf whose `compCanon` was
repurposed for the row comparison), `firstterminal` (the seed), and
the pure incumbent installation (`install_codeInv`, the code-`3`
core). `codeInv_keyCmp_lt`/`gt` are the payoff: a frozen comparison
decides the key order of every leaf below the node against the
incumbent, whatever the deeper codes and rows are.
-/

namespace Hex.GraphIso.Nauty

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! # Codes stay below the sentinel -/

/-- Every refinement code is strictly below the sentinel. -/
theorem refine_longcode_lt (ctx : Ctx) (level : Nat) (lab ptn : Array Nat)
    (active numcells : Nat) :
    (refine ctx level lab ptn active numcells).longcode < codeSentinel := by
  rw [refine]
  show cleanup _ < codeSentinel
  rw [cleanup, codeSentinel]
  exact Nat.mod_lt _ (by omega)

/-! # The incumbent's extended code list -/

/-- The incumbent's code at level `i` (`1`-indexed): the stored codes,
then the sentinel at every deeper level. -/
@[expose] def bcode (bs : List Nat) (i : Nat) : Nat :=
  if i - 1 < bs.length then bs[i - 1]! else codeSentinel

theorem bcode_of_le {bs : List Nat} {i : Nat} (h1 : 1 ≤ i)
    (h2 : i ≤ bs.length) : bcode bs i = bs[i - 1]! := by
  rw [bcode, ite_eq_left (by omega : i - 1 < bs.length)]

theorem bcode_sentinel {bs : List Nat} {i : Nat}
    (h : bs.length < i) : bcode bs i = codeSentinel := by
  rw [bcode, ite_eq_right (by omega : ¬(i - 1 < bs.length))]

theorem bcode_lt {bs : List Nat} {i : Nat}
    (hblt : ∀ b ∈ bs, b < codeSentinel) (h1 : 1 ≤ i)
    (h2 : i ≤ bs.length) : bcode bs i < codeSentinel := by
  rw [bcode_of_le h1 h2, getElem!_pos _ _ (by omega)]
  exact hblt _ (List.getElem_mem _)

/-! # List access helpers -/

private theorem getElem!_append_left' {xs ys : List Nat} {i : Nat}
    (h : i < xs.length) : (xs ++ ys)[i]! = xs[i]! := by
  have hxy : i < (xs ++ ys).length := by
    rw [List.length_append]
    omega
  rw [getElem!_pos (xs ++ ys) i hxy, getElem!_pos xs i h,
    List.getElem_append_left h]

private theorem getElem!_take' {l : List Nat} {m i : Nat}
    (him : i < m) (hil : i < l.length) : (l.take m)[i]! = l[i]! := by
  have hti : i < (l.take m).length := by
    rw [List.length_take]
    omega
  rw [getElem!_pos (l.take m) i hti, getElem!_pos l i hil,
    List.getElem_take]

/-- The extended incumbent list `bs ++ [codeSentinel]` reads as
`bcode` at every position up to and including the sentinel. -/
theorem getElem!_append_sentinel {bs : List Nat} {i : Nat}
    (h : i ≤ bs.length) :
    (bs ++ [codeSentinel])[i]! = bcode bs (i + 1) := by
  rcases Nat.lt_or_ge i bs.length with hlt | hge
  · rw [getElem!_append_left' hlt, bcode,
      ite_eq_left (by omega : i + 1 - 1 < bs.length)]
    show bs[i]! = bs[i + 1 - 1]!
    rfl
  · have hie : i = bs.length := by omega
    subst hie
    have hsz : bs.length < (bs ++ [codeSentinel]).length := by
      rw [List.length_append]
      simp
    rw [getElem!_pos (bs ++ [codeSentinel]) bs.length hsz,
      List.getElem_concat_length, bcode_sentinel (by omega)]
    rfl

/-! # Positional lexicographic comparison -/

/-- A strict drop at position `p` after agreement below it decides the
lexicographic comparison downward. -/
theorem listCmp_lt_of_prefix :
    ∀ (p : Nat) (xs ys : List Nat), p < xs.length → p < ys.length →
      (∀ i, i < p → xs[i]! = ys[i]!) → xs[p]! < ys[p]! →
      listCmp compare xs ys = .lt
  | p, [], ys, hx, _, _, _ => absurd hx (by simp)
  | p, x :: xs, [], _, hy, _, _ => absurd hy (by simp)
  | 0, x :: xs, y :: ys, _, _, _, hlt => by
    rw [listCmp]
    have hc : compare x y = .lt := by
      rw [Nat.compare_eq_lt]
      simpa using hlt
    rw [hc]
  | p + 1, x :: xs, y :: ys, hx, hy, hpre, hlt => by
    rw [listCmp]
    have hxy : x = y := by
      have h0 := hpre 0 (by omega)
      simpa using h0
    subst hxy
    rw [(Nat.compare_eq_eq (a := x) (b := x)).mpr rfl]
    refine listCmp_lt_of_prefix p xs ys (by simpa using hx)
      (by simpa using hy) (fun i hi => ?_) (by simpa using hlt)
    have h := hpre (i + 1) (by omega)
    simpa using h

/-- A strict rise at position `p` after agreement below it decides the
lexicographic comparison upward. -/
theorem listCmp_gt_of_prefix :
    ∀ (p : Nat) (xs ys : List Nat), p < xs.length → p < ys.length →
      (∀ i, i < p → xs[i]! = ys[i]!) → ys[p]! < xs[p]! →
      listCmp compare xs ys = .gt
  | p, [], ys, hx, _, _, _ => absurd hx (by simp)
  | p, x :: xs, [], _, hy, _, _ => absurd hy (by simp)
  | 0, x :: xs, y :: ys, _, _, _, hlt => by
    rw [listCmp]
    have hc : compare x y = .gt := by
      rw [Nat.compare_eq_gt]
      simpa using hlt
    rw [hc]
  | p + 1, x :: xs, y :: ys, hx, hy, hpre, hlt => by
    rw [listCmp]
    have hxy : x = y := by
      have h0 := hpre 0 (by omega)
      simpa using h0
    subst hxy
    rw [(Nat.compare_eq_eq (a := x) (b := x)).mpr rfl]
    refine listCmp_gt_of_prefix p xs ys (by simpa using hx)
      (by simpa using hy) (fun i hi => ?_) (by simpa using hlt)
    have h := hpre (i + 1) (by omega)
    simpa using h

/-! # The code-comparison invariant -/

/-- The lazily threaded code comparison state, relative to the current
path's codes `cs` (levels `1 .. cs.length`) and the incumbent's codes
`bs` (levels `1 .. bs.length`, sentinel beyond). -/
structure CodeCmpInv (nn : Nat) (cs bs : List Nat)
    (canoncode : Array Nat) (canonlevel : Nat)
    (eqlevCanon compCanon : Int) : Prop where
  /-- The code store always has `nn + 2` slots. -/
  size : canoncode.size = nn + 2
  /-- `canonlevel` counts the incumbent's codes. -/
  blen : canonlevel = bs.length
  /-- The incumbent's leaf is at a real level. -/
  bbound : bs.length ≤ nn
  /-- Stored incumbent codes are real codes. -/
  blt : ∀ b ∈ bs, b < codeSentinel
  /-- Path codes are real codes. -/
  clt : ∀ c ∈ cs, c < codeSentinel
  /-- The comparison trichotomy: full agreement, or a frozen
  divergence at level `j` with matched prefix below it. -/
  tri :
    (compCanon = 0 ∧ eqlevCanon = Int.ofNat cs.length ∧
      cs.length ≤ bs.length ∧
      ∀ i, 1 ≤ i → i ≤ cs.length → cs[i - 1]! = bcode bs i) ∨
    (∃ j, 1 ≤ j ∧ j ≤ cs.length ∧ j ≤ bs.length + 1 ∧
      eqlevCanon = Int.ofNat (j - 1) ∧
      (∀ i, 1 ≤ i → i < j → cs[i - 1]! = bcode bs i) ∧
      ((compCanon = -1 ∧ cs[j - 1]! < bcode bs j) ∨
       (compCanon = 1 ∧ j ≤ bs.length ∧ bcode bs j < cs[j - 1]!)))
  /-- Outside the upward-divergence overwrite window, the store holds
  the incumbent's codes (sentinel at `bs.length + 1`). -/
  content : ∀ i, 1 ≤ i → i ≤ bs.length + 1 →
    (compCanon = 1 → i ≤ eqlevCanon.toNat ∨ cs.length < i) →
    canoncode[i]! = bcode bs i
  /-- Inside the overwrite window, the store holds the path's codes. -/
  over : compCanon = 1 → ∀ i, eqlevCanon.toNat < i → i ≤ cs.length →
    canoncode[i]! = cs[i - 1]!

/-! # The payoff: a frozen comparison decides the key order -/

/-- With `compCanon = -1`, every leaf below the node compares below
the incumbent on codes, whatever the deeper codes are. -/
theorem codeInv_listCmp_lt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    (ext : List Nat) :
    listCmp compare (cs ++ ext) (bs ++ [codeSentinel]) = .lt := by
  rcases hinv.tri with ⟨hcc, -⟩ | ⟨j, hj1, hjL, hjm, -, hpre, hcase⟩
  · cases hcc
  rcases hcase with ⟨-, hlt⟩ | ⟨hcc, -⟩
  · refine listCmp_lt_of_prefix (j - 1) _ _
      (by rw [List.length_append]; omega)
      (by rw [List.length_append]; simp; omega)
      (fun i hi => ?_) ?_
    · rw [getElem!_append_left' (by omega),
        getElem!_append_sentinel (by omega)]
      have hp := hpre (i + 1) (by omega) (by omega)
      simpa using hp
    · rw [getElem!_append_left' (by omega),
        getElem!_append_sentinel (by omega),
        (by omega : j - 1 + 1 = j)]
      exact hlt
  · cases hcc

/-- With `compCanon = 1`, every leaf below the node compares above
the incumbent on codes, whatever the deeper codes are. -/
theorem codeInv_listCmp_gt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 1)
    (ext : List Nat) :
    listCmp compare (cs ++ ext) (bs ++ [codeSentinel]) = .gt := by
  rcases hinv.tri with ⟨hcc, -⟩ | ⟨j, hj1, hjL, hjm, -, hpre, hcase⟩
  · cases hcc
  rcases hcase with ⟨hcc, -⟩ | ⟨-, hjb, hgt⟩
  · cases hcc
  · refine listCmp_gt_of_prefix (j - 1) _ _
      (by rw [List.length_append]; omega)
      (by rw [List.length_append]; simp; omega)
      (fun i hi => ?_) ?_
    · rw [getElem!_append_left' (by omega),
        getElem!_append_sentinel (by omega)]
      have hp := hpre (i + 1) (by omega) (by omega)
      simpa using hp
    · rw [getElem!_append_left' (xs := cs) (ys := ext) (by omega),
        getElem!_append_sentinel (by omega),
        (by omega : j - 1 + 1 = j)]
      exact hgt

/-- The key-level form of `codeInv_listCmp_lt`. -/
theorem codeInv_keyCmp_lt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon (-1))
    (ext r1 r2 : List Nat) :
    keyCmp ⟨cs ++ ext, r1⟩ ⟨bs ++ [codeSentinel], r2⟩ = .lt := by
  rw [keyCmp]
  show (match listCmp compare (cs ++ ext) (bs ++ [codeSentinel]) with
    | .eq => listCmp rowCmp r1 r2
    | .lt => .lt
    | .gt => .gt) = .lt
  rw [codeInv_listCmp_lt hinv ext]

/-- The key-level form of `codeInv_listCmp_gt`. -/
theorem codeInv_keyCmp_gt {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat} {eqlevCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon 1)
    (ext r1 r2 : List Nat) :
    keyCmp ⟨cs ++ ext, r1⟩ ⟨bs ++ [codeSentinel], r2⟩ = .gt := by
  rw [keyCmp]
  show (match listCmp compare (cs ++ ext) (bs ++ [codeSentinel]) with
    | .eq => listCmp rowCmp r1 r2
    | .lt => .lt
    | .gt => .gt) = .gt
  rw [codeInv_listCmp_gt hinv ext]

/-! # Projections of the events -/

private theorem otherNodePrep_canonlevel (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).canonlevel = st.canonlevel := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlevel, ite_self]

private theorem otherNodePrep_compCanon (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).compCanon =
      if st.eqlevCanon == Int.ofNat level - 1 then
        (if code < st.canoncode[level]! then (-1 : Int)
         else if code > st.canoncode[level]! then 1 else 0)
      else st.compCanon := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.compCanon, apply_ite SearchSt.eqlevCanon,
    apply_ite SearchSt.canoncode, apply_ite SearchSt.firstcode,
    apply_ite SearchSt.eqlevFirst, ite_self]
  all_goals repeat' split
  all_goals rfl

private theorem otherNodePrep_eqlevCanon (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).eqlevCanon =
      if st.eqlevCanon == Int.ofNat level - 1 then
        (if code < st.canoncode[level]! then st.eqlevCanon
         else if code > st.canoncode[level]! then st.eqlevCanon
         else Int.ofNat level)
      else st.eqlevCanon := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.eqlevCanon, apply_ite SearchSt.canoncode,
    apply_ite SearchSt.firstcode, apply_ite SearchSt.eqlevFirst,
    ite_self]
  all_goals repeat' split
  all_goals rfl

private theorem otherNodePrep_canoncode (level code : Nat)
    (st : SearchSt) :
    (otherNodePrep level code st).canoncode =
      if (if st.eqlevCanon == Int.ofNat level - 1 then
            (if code < st.canoncode[level]! then (-1 : Int)
             else if code > st.canoncode[level]! then 1 else 0)
          else st.compCanon) > 0 then
        st.canoncode.set! level code
      else st.canoncode := by
  rw [otherNodePrep]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canoncode, apply_ite SearchSt.compCanon,
    apply_ite SearchSt.eqlevCanon, apply_ite SearchSt.firstcode,
    apply_ite SearchSt.eqlevFirst, ite_self]
  all_goals repeat' split
  all_goals rfl

private theorem recover_canoncode (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canoncode = st.canoncode := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canoncode, ite_self]

private theorem recover_canonlevel (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).canonlevel = st.canonlevel := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.canonlevel, ite_self]

private theorem recover_eqlevCanon (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).eqlevCanon =
      if Int.ofNat level ≤ st.eqlevCanon then Int.ofNat level
      else st.eqlevCanon := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.eqlevCanon, ite_self]

private theorem recover_compCanon (n inf level : Nat) (st : SearchSt) :
    (recover n inf level st).compCanon =
      if Int.ofNat level ≤ st.eqlevCanon then 0
      else st.compCanon := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.compCanon, apply_ite SearchSt.eqlevCanon,
    ite_self]

/-! # Event: one `othernode` comparison step -/

/-- One `otherNodePrep` step at level `cs.length + 1` with fresh code
`code` extends the comparison invariant by one level. -/
theorem otherNodePrep_codeInv {nn : Nat} {cs bs : List Nat}
    {st : SearchSt} {code : Nat}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hcode : code < codeSentinel)
    (hLnn : cs.length + 1 ≤ nn + 1) :
    CodeCmpInv nn (cs ++ [code]) bs
      (otherNodePrep (cs.length + 1) code st).canoncode
      (otherNodePrep (cs.length + 1) code st).canonlevel
      (otherNodePrep (cs.length + 1) code st).eqlevCanon
      (otherNodePrep (cs.length + 1) code st).compCanon := by
  have hclt' : ∀ c ∈ cs ++ [code], c < codeSentinel := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hinv.clt c h
    · rw [List.mem_singleton.mp h]
      exact hcode
  have hlast : (cs ++ [code])[cs.length]! = code := by
    have hsz : cs.length < (cs ++ [code]).length := by
      rw [List.length_append]
      simp
    rw [getElem!_pos (cs ++ [code]) cs.length hsz,
      List.getElem_concat_length]
    rfl
  have hkeep : ∀ i, 1 ≤ i → i ≤ cs.length →
      (cs ++ [code])[i - 1]! = cs[i - 1]! :=
    fun i h1 h2 => getElem!_append_left' (by omega)
  rw [otherNodePrep_canonlevel, otherNodePrep_compCanon,
    otherNodePrep_eqlevCanon, otherNodePrep_canoncode]
  rcases hinv.tri with ⟨hcc, hec, hLm, hmatch⟩ |
    ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
  · -- the path matched through `cs.length`: the comparison fires
    have hcond : (st.eqlevCanon == Int.ofNat (cs.length + 1) - 1) =
        true := by
      rw [beq_iff_eq, hec]
      simp only [Int.ofNat_eq_natCast]
      omega
    have hread : st.canoncode[cs.length + 1]! =
        bcode bs (cs.length + 1) :=
      hinv.content (cs.length + 1) (by omega) (by omega)
        (fun h => by rw [hcc] at h; cases h)
    simp only [ite_eq_left hcond, hread]
    rcases Nat.lt_trichotomy code (bcode bs (cs.length + 1)) with
      hlt | heq | hgt
    · -- downward divergence at the new level
      simp only [ite_eq_left hlt,
        ite_eq_right (by omega : ¬((-1 : Int) > 0))]
      refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt', ?_,
        ?_, ?_⟩
      · refine Or.inr ⟨cs.length + 1, by omega, by simp, by omega,
          by rw [hec]; simp only [Int.ofNat_eq_natCast]; omega, fun i h1 h2 => ?_, Or.inl ⟨rfl, ?_⟩⟩
        · rw [hkeep i h1 (by omega)]
          exact hmatch i h1 (by omega)
        · rw [(by omega : cs.length + 1 - 1 = cs.length), hlast]
          exact hlt
      · intro i h1 h2 _
        exact hinv.content i h1 h2
          (fun h => by rw [hcc] at h; cases h)
      · intro h
        cases h
    · -- the new level also matches
      simp only [
        ite_eq_right (by omega : ¬(code < bcode bs (cs.length + 1))),
        ite_eq_right (by omega : ¬(code > bcode bs (cs.length + 1))),
        ite_eq_right (by omega : ¬((0 : Int) > 0))]
      have hLm' : cs.length + 1 ≤ bs.length := by
        rcases Nat.lt_or_ge cs.length bs.length with h | h
        · omega
        · exfalso
          have hs : bcode bs (cs.length + 1) = codeSentinel :=
            bcode_sentinel (by omega)
          rw [hs] at heq
          omega
      refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt', ?_,
        ?_, ?_⟩
      · refine Or.inl ⟨rfl, by simp, by simp; omega,
          fun i h1 h2 => ?_⟩
        rw [List.length_append, List.length_singleton] at h2
        rcases Nat.lt_or_ge i (cs.length + 1) with hi | hi
        · rw [hkeep i h1 (by omega)]
          exact hmatch i h1 (by omega)
        · have hie : i = cs.length + 1 := by omega
          subst hie
          rw [(by omega : cs.length + 1 - 1 = cs.length), hlast, heq]
      · intro i h1 h2 _
        exact hinv.content i h1 h2
          (fun h => by rw [hcc] at h; cases h)
      · intro h
        cases h
    · -- upward divergence at the new level: the overwrite begins
      simp only [
        ite_eq_right (by omega : ¬(code < bcode bs (cs.length + 1))),
        ite_eq_left (show code > bcode bs (cs.length + 1) from hgt),
        ite_eq_left (by omega : (1 : Int) > 0)]
      have hjb : cs.length + 1 ≤ bs.length := by
        rcases Nat.lt_or_ge cs.length bs.length with h | h
        · omega
        · exfalso
          have hs : bcode bs (cs.length + 1) = codeSentinel :=
            bcode_sentinel (by omega)
          rw [hs] at hgt
          omega
      refine ⟨by rw [Array.size_set!]; exact hinv.size, hinv.blen,
        hinv.bbound, hinv.blt, hclt', ?_, ?_, ?_⟩
      · refine Or.inr ⟨cs.length + 1, by omega, by simp, by omega,
          by rw [hec]; simp only [Int.ofNat_eq_natCast]; omega, fun i h1 h2 => ?_,
          Or.inr ⟨rfl, hjb, ?_⟩⟩
        · rw [hkeep i h1 (by omega)]
          exact hmatch i h1 (by omega)
        · rw [(by omega : cs.length + 1 - 1 = cs.length), hlast]
          exact hgt
      · intro i h1 h2 hgd
        have hguard := hgd rfl
        rw [hec] at hguard
        simp only [Int.ofNat_eq_natCast, List.length_append,
          List.length_singleton] at hguard
        have hine : i ≠ cs.length + 1 := by omega
        rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hine h.symm)]
        exact hinv.content i h1 h2
          (fun h => by rw [hcc] at h; cases h)
      · intro _ i hilo hihi
        rw [hec] at hilo
        simp only [Int.ofNat_eq_natCast] at hilo
        rw [List.length_append, List.length_singleton] at hihi
        have hie : i = cs.length + 1 := by omega
        subst hie
        rw [Array.getElem!_set!_self _ _ _
            (by rw [hinv.size]; omega),
          (by omega : cs.length + 1 - 1 = cs.length), hlast]
  · -- the comparison is frozen at divergence level `j`
    have hcond : ¬((st.eqlevCanon == Int.ofNat (cs.length + 1) - 1) =
        true) := by
      rw [beq_iff_eq, hec]
      intro h
      simp only [Int.ofNat_eq_natCast] at h
      omega
    simp only [ite_eq_right hcond]
    rcases hcase with ⟨hcc, hlt⟩ | ⟨hcc, hjb, hgt⟩
    · -- frozen downward: nothing changes
      simp only [hcc, ite_eq_right (by omega : ¬((-1 : Int) > 0))]
      refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt', ?_,
        ?_, ?_⟩
      · refine Or.inr ⟨j, hj1, by simp; omega, hjm, hec,
          fun i h1 h2 => ?_, Or.inl ⟨rfl, ?_⟩⟩
        · rw [hkeep i h1 (by omega)]
          exact hpre i h1 h2
        · rw [hkeep j hj1 hjL]
          exact hlt
      · intro i h1 h2 _
        exact hinv.content i h1 h2
          (fun h => by rw [hcc] at h; cases h)
      · intro h
        omega
    · -- frozen upward: the overwrite window extends
      simp only [hcc, ite_eq_left (by omega : (1 : Int) > 0)]
      refine ⟨by rw [Array.size_set!]; exact hinv.size, hinv.blen,
        hinv.bbound, hinv.blt, hclt', ?_, ?_, ?_⟩
      · refine Or.inr ⟨j, hj1, by simp; omega, hjm, hec,
          fun i h1 h2 => ?_, Or.inr ⟨rfl, hjb, ?_⟩⟩
        · rw [hkeep i h1 (by omega)]
          exact hpre i h1 h2
        · rw [hkeep j hj1 hjL]
          exact hgt
      · intro i h1 h2 hgd
        have hguard := hgd rfl
        rw [hec] at hguard
        simp only [Int.ofNat_eq_natCast, List.length_append,
          List.length_singleton] at hguard
        have hine : i ≠ cs.length + 1 := by
          rcases hguard with h | h
          · omega
          · omega
        rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hine h.symm)]
        refine hinv.content i h1 h2 (fun _ => ?_)
        rw [hec]
        simp only [Int.ofNat_eq_natCast]
        rcases hguard with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · intro _ i hilo hihi
        rw [hec] at hilo
        simp only [Int.ofNat_eq_natCast] at hilo
        rw [List.length_append, List.length_singleton] at hihi
        rcases Nat.lt_or_ge i (cs.length + 1) with hi | hi
        · have hine : i ≠ cs.length + 1 := by omega
          rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hine h.symm),
            hkeep i (by omega) (by omega)]
          refine hinv.over hcc i ?_ (by omega)
          rw [hec]
          simp only [Int.ofNat_eq_natCast]
          omega
        · have hie : i = cs.length + 1 := by omega
          subst hie
          rw [Array.getElem!_set!_self _ _ _
              (by rw [hinv.size]; omega),
            (by omega : cs.length + 1 - 1 = cs.length), hlast]

/-! # Event: the unwind restore -/

/-- `recover` under a live (non-overwriting) comparison: unwinding to
`lvl` truncates the path and restores full agreement when the match
reached `lvl`. -/
theorem recover_codeInv {nn N inf : Nat} {cs bs : List Nat}
    {st : SearchSt} {lvl : Nat}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hcc : st.compCanon ≤ 0)
    (hlvl : lvl ≤ cs.length) :
    CodeCmpInv nn (cs.take lvl) bs
      (recover N inf lvl st).canoncode
      (recover N inf lvl st).canonlevel
      (recover N inf lvl st).eqlevCanon
      (recover N inf lvl st).compCanon := by
  have hlen : (cs.take lvl).length = lvl := by
    rw [List.length_take]
    omega
  have hclt' : ∀ c ∈ cs.take lvl, c < codeSentinel :=
    fun c hc => hinv.clt c (List.mem_of_mem_take hc)
  have htake : ∀ i, 1 ≤ i → i ≤ lvl →
      (cs.take lvl)[i - 1]! = cs[i - 1]! :=
    fun i h1 h2 => getElem!_take' (by omega) (by omega)
  rw [recover_canoncode, recover_canonlevel, recover_eqlevCanon,
    recover_compCanon]
  rcases hinv.tri with ⟨hcc0, hec, hLm, hmatch⟩ |
    ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
  · -- full agreement: the reset restores agreement at `lvl`
    rw [hec, ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega), ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega)]
    refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt', ?_,
      ?_, ?_⟩
    · refine Or.inl ⟨rfl, by rw [hlen], by omega,
        fun i h1 h2 => ?_⟩
      rw [hlen] at h2
      rw [htake i h1 h2]
      exact hmatch i h1 (by omega)
    · intro i h1 h2 _
      exact hinv.content i h1 h2
        (fun h => by rw [hcc0] at h; cases h)
    · intro h
      cases h
  · rcases hcase with ⟨hcc1, hlt⟩ | ⟨hcc1, -, -⟩
    · -- frozen downward divergence
      rcases Nat.lt_or_ge (j - 1) lvl with hjlvl | hjlvl
      · -- the divergence survives the truncation
        rw [hec, ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega), ite_eq_right (by simp only [Int.ofNat_eq_natCast]; omega)]
        refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt',
          ?_, ?_, ?_⟩
        · refine Or.inr ⟨j, hj1, by rw [hlen]; omega, hjm, rfl,
            fun i h1 h2 => ?_, Or.inl ⟨hcc1, ?_⟩⟩
          · rw [htake i h1 (by omega)]
            exact hpre i h1 h2
          · rw [htake j hj1 (by omega)]
            exact hlt
        · intro i h1 h2 _
          exact hinv.content i h1 h2
            (fun h => by rw [hcc1] at h; cases h)
        · intro h
          rw [hcc1] at h
          cases h
      · -- the truncation ends at or before the matched prefix
        rw [hec, ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega), ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega)]
        refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt',
          ?_, ?_, ?_⟩
        · refine Or.inl ⟨rfl, by rw [hlen], by omega,
            fun i h1 h2 => ?_⟩
          rw [hlen] at h2
          rw [htake i h1 h2]
          exact hpre i h1 (by omega)
        · intro i h1 h2 _
          exact hinv.content i h1 h2
            (fun h => by rw [hcc1] at h; cases h)
        · intro h
          cases h
    · rw [hcc1] at hcc
      omega

/-- `recover` after a leaf event that repurposed `compCanon` for the
row comparison: the pre-leaf state matched through the whole path
(`compCanon = 0` invariant), so unwinding to any `lvl` within the
path resets to full agreement whatever `compCanon` currently holds. -/
theorem recover_codeInv_reset {nn N inf : Nat} {cs bs : List Nat}
    {st : SearchSt} {lvl : Nat}
    (hinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon 0)
    (hlvl : lvl ≤ cs.length) :
    CodeCmpInv nn (cs.take lvl) bs
      (recover N inf lvl st).canoncode
      (recover N inf lvl st).canonlevel
      (recover N inf lvl st).eqlevCanon
      (recover N inf lvl st).compCanon := by
  have hlen : (cs.take lvl).length = lvl := by
    rw [List.length_take]
    omega
  have hclt' : ∀ c ∈ cs.take lvl, c < codeSentinel :=
    fun c hc => hinv.clt c (List.mem_of_mem_take hc)
  rcases hinv.tri with ⟨-, hec, hLm, hmatch⟩ | ⟨j, _, _, _, _, _,
    hcase⟩
  · rw [recover_canoncode, recover_canonlevel, recover_eqlevCanon,
      recover_compCanon, hec, ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega), ite_eq_left (by simp only [Int.ofNat_eq_natCast]; omega)]
    refine ⟨hinv.size, hinv.blen, hinv.bbound, hinv.blt, hclt', ?_,
      ?_, ?_⟩
    · refine Or.inl ⟨rfl, by rw [hlen], by omega, fun i h1 h2 => ?_⟩
      rw [hlen] at h2
      rw [getElem!_take' (by omega) (by omega)]
      exact hmatch i h1 (by omega)
    · intro i h1 h2 _
      exact hinv.content i h1 h2 (fun h => by cases h)
    · intro h
      cases h
  · rcases hcase with ⟨hcc, -⟩ | ⟨hcc, -⟩
    · cases hcc
    · cases hcc

/-! # Event: seeding and installing the incumbent -/

private theorem forIn_range_eq'' {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_copy_eq {src : Array Nat} :
    ∀ (l : List Nat) (dst : Array Nat),
      (forIn l dst (fun i r =>
        pure (ForInStep.yield (r.set! i (src[i]!)))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! i (src[i]!)) dst
  | [], _ => rfl
  | i :: l, dst => by
    rw [List.forIn_cons, List.foldl_cons]
    exact forIn_copy_eq l _

private theorem foldl_copy_size {src : Array Nat} :
    ∀ (l : List Nat) (dst : Array Nat),
      (l.foldl (fun r i => r.set! i (src[i]!)) dst).size =
        dst.size
  | [], _ => rfl
  | i :: l, dst => by
    rw [List.foldl_cons, foldl_copy_size l, Array.size_set!]

private theorem foldl_copy_getElem {src : Array Nat} :
    ∀ {m : Nat} (dst : Array Nat) (q : Nat),
      ((List.range m).foldl (fun r i => r.set! i (src[i]!)) dst)[q]! =
        if q < m ∧ q < dst.size then src[q]! else dst[q]! := by
  intro m
  induction m with
  | zero =>
    intro dst q
    rw [List.range_zero, List.foldl_nil,
      ite_eq_right (by rintro ⟨h, -⟩; omega)]
  | succ m ih =>
    intro dst q
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rcases Decidable.em (q = m) with rfl | hne
    · rcases Nat.lt_or_ge q dst.size with hqs | hqs
      · rw [Array.getElem!_set!_self _ _ _
          (by rw [foldl_copy_size]; exact hqs),
          ite_eq_left ⟨by omega, hqs⟩]
      · rw [getElem!_neg _ _ (by
            rw [Array.size_set!, foldl_copy_size]; omega),
          getElem!_neg dst q (by omega),
          ite_eq_right (by rintro ⟨-, h⟩; omega)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hne h.symm),
        ih dst q]
      rcases Decidable.em (q < m ∧ q < dst.size) with hc | hc
      · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc.2⟩]
      · rw [ite_eq_right hc, ite_eq_right (by
          rintro ⟨h1, h2⟩
          exact hc ⟨by omega, h2⟩)]

private theorem firstterminal_canonlevel (level : Nat)
    (st : SearchSt) :
    (firstterminal level st).canonlevel = level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem firstterminal_eqlevCanon (level : Nat)
    (st : SearchSt) :
    (firstterminal level st).eqlevCanon = Int.ofNat level := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem firstterminal_compCanon (level : Nat)
    (st : SearchSt) :
    (firstterminal level st).compCanon = 0 := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]

private theorem firstterminal_canoncode (level : Nat) (st : SearchSt) :
    (firstterminal level st).canoncode =
      ((List.range (level + 1)).foldl
        (fun r i =>
          r.set! i ((st.firstcode.set! (level + 1) codeSentinel)[i]!))
        st.canoncode).set! (level + 1) codeSentinel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]
  rw [forIn_range_eq'', forIn_copy_eq]
  rfl

/-- `firstterminal` seeds the comparison invariant: the first leaf's
codes become the incumbent with full agreement recorded. -/
theorem firstterminal_codeInv {nn : Nat} {cs : List Nat}
    {st : SearchSt}
    (hsize : st.canoncode.size = nn + 2)
    (hLnn : cs.length ≤ nn)
    (hfc : ∀ i, 1 ≤ i → i ≤ cs.length → st.firstcode[i]! = cs[i - 1]!)
    (hclt : ∀ c ∈ cs, c < codeSentinel) :
    CodeCmpInv nn cs cs
      (firstterminal cs.length st).canoncode
      (firstterminal cs.length st).canonlevel
      (firstterminal cs.length st).eqlevCanon
      (firstterminal cs.length st).compCanon := by
  rw [firstterminal_canonlevel, firstterminal_eqlevCanon,
    firstterminal_compCanon, firstterminal_canoncode]
  have hget : ∀ i, 1 ≤ i → i ≤ cs.length + 1 →
      (((List.range (cs.length + 1)).foldl
        (fun r j => r.set! j
          ((st.firstcode.set! (cs.length + 1) codeSentinel)[j]!))
        st.canoncode).set! (cs.length + 1) codeSentinel)[i]! =
      bcode cs i := by
    intro i h1 h2
    rcases Decidable.em (i = cs.length + 1) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _
        (by rw [foldl_copy_size, hsize]; omega),
        bcode_sentinel (by omega)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hne h.symm),
        foldl_copy_getElem,
        ite_eq_left ⟨by omega, by rw [hsize]; omega⟩,
        Array.getElem!_set!_ne _ _ _ _ (by omega),
        hfc i h1 (by omega), bcode_of_le h1 (by omega)]
  refine ⟨?_, rfl, hLnn, hclt, hclt, ?_, ?_, ?_⟩
  · rw [Array.size_set!, foldl_copy_size]
    exact hsize
  · refine Or.inl ⟨rfl, rfl, Nat.le_refl _, fun i h1 h2 => ?_⟩
    rw [bcode_of_le h1 h2]
  · intro i h1 h2 _
    exact hget i h1 h2
  · intro h
    cases h

/-- Installing the current path as the new incumbent (the code-`3`
core): after a non-downward comparison, the store already holds the
path's codes, so recording the path as incumbent with the sentinel
stamped re-seeds the invariant at full agreement. -/
theorem install_codeInv {nn : Nat} {cs bs : List Nat}
    {canoncode : Array Nat} {canonlevel : Nat}
    {eqlevCanon compCanon : Int}
    (hinv : CodeCmpInv nn cs bs canoncode canonlevel eqlevCanon
      compCanon)
    (hne : compCanon ≠ -1)
    (hLnn : cs.length ≤ nn) :
    CodeCmpInv nn cs cs
      (canoncode.set! (cs.length + 1) codeSentinel)
      cs.length (Int.ofNat cs.length) 0 := by
  have hstore : ∀ i, 1 ≤ i → i ≤ cs.length →
      canoncode[i]! = cs[i - 1]! := by
    intro i h1 h2
    rcases hinv.tri with ⟨hcc, hec, hLm, hmatch⟩ |
      ⟨j, hj1, hjL, hjm, hec, hpre, hcase⟩
    · rw [hinv.content i h1 (by omega)
        (fun h => by rw [hcc] at h; cases h)]
      exact (hmatch i h1 h2).symm
    · rcases hcase with ⟨hcc, -⟩ | ⟨hcc, hjb, -⟩
      · exact absurd hcc hne
      · rcases Nat.lt_or_ge i j with hij | hij
        · rw [hinv.content i h1 (by omega) (fun _ => Or.inl (by
            rw [hec]
            simp only [Int.ofNat_eq_natCast]
            omega))]
          exact (hpre i h1 hij).symm
        · refine hinv.over hcc i ?_ h2
          rw [hec]
          simp only [Int.ofNat_eq_natCast]
          omega
  refine ⟨?_, rfl, hLnn, hinv.clt, hinv.clt, ?_, ?_, ?_⟩
  · rw [Array.size_set!]
    exact hinv.size
  · refine Or.inl ⟨rfl, rfl, Nat.le_refl _, fun i h1 h2 => ?_⟩
    rw [bcode_of_le h1 h2]
  · intro i h1 h2 _
    rcases Decidable.em (i = cs.length + 1) with rfl | hne'
    · rw [Array.getElem!_set!_self _ _ _
        (by rw [hinv.size]; omega),
        bcode_sentinel (by omega)]
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hne' h.symm),
        hstore i h1 (by omega), bcode_of_le h1 (by omega)]
  · intro h
    cases h

end Hex.GraphIso.Nauty
