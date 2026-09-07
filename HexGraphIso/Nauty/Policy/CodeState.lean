/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.Policy.State
public import HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- The canonical comparison machine, including its ghost incumbent
codes during an upward overwrite. -/
abbrev Codes (cs bs : List Nat) (st : Search n) : Prop :=
  CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon st.compCanon

/-- The executable incumbent, read only when code storage is stable. -/
@[expose] def Search.best (ctx : Ctx n) (st : Search n) : Option (Key n) :=
  if st.canonlevel = 0 then none else
    some ⟨(List.range' 1 st.canonlevel).map (fun i => st.canoncode[i]!) ++
      [codeSentinel], leafRows ctx st.canonlab⟩

/-- The semantic incumbent represented by a ghost code sequence. -/
@[expose] def Search.key (ctx : Ctx n) (bs : List Nat) (st : Search n) : Option (Key n) :=
  if bs = [] then none else some (incKey ctx bs st.canonlab)

/-- Stable code storage contains the ghost incumbent's entire code list. -/
theorem code_read {cs bs : List Nat} {st : Search n} {comparison : Int}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon comparison)
    (hne : comparison ≠ 1) :
    (List.range' 1 st.canonlevel).map (fun i => st.canoncode[i]!) = bs := by
  refine List.ext_getElem (by simp [h.blen]) fun i hi hb => ?_
  rw [List.getElem_map, List.getElem_range']
  have hc := h.content (i + 1) (by omega) (by omega) (fun he => (hne he).elim)
  have hbc : bcode bs (i + 1) = bs[i]! := bcode_of_le (by omega) (by omega)
  rw [hbc, getElem!_pos bs i hb] at hc
  simpa only [Nat.add_comm, Nat.one_mul] using hc

/-- The stable executable reading agrees with the semantic incumbent. -/
theorem best_eq_key {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    {comparison : Int}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon comparison)
    (hne : comparison ≠ 1) : st.best ctx = st.key ctx bs := by
  rw [Search.best, Search.key, code_read h hne, h.blen]
  cases bs <;> simp [incKey]

/-- Comparing the next refinement code extends the current path. -/
theorem Codes.compare {cs bs : List Nat} {st : Search n} {code : Nat}
    (h : Codes cs bs st) (hc : code < codeSentinel) (hlen : cs.length ≤ n) :
    Codes (cs ++ [code]) bs (compareCodes (cs.length + 1) code st) := by
  have h' := otherNodePrep_codeInv (st := st.view) h hc (by omega)
  rw [← view_compareCodes] at h'
  exact h'

/-- Installing a leaf makes its path the canonical code sequence. The
premise describes code comparison before the row verdict repurposes it. -/
theorem Codes.install {cs bs : List Nat} {st : Search n} {comparison : Int}
    (h : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon comparison)
    (hne : comparison ≠ -1) (hlen : cs.length ≤ n) (sr : Nat) :
    Codes cs cs (install cs.length sr st) :=
  install_codeInv h hne hlen

/-- The first leaf seeds the canonical comparison machine. -/
theorem firstterminal_codes {cs : List Nat} {st : Search n}
    (hsize : st.canoncode.size = n + 2) (hlen : cs.length ≤ n)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length → st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel) :
    Codes cs cs (firstterminal cs.length st) := by
  have h := firstterminal_codeInv (st := st.view) hsize hlen hcodes hlt
  rw [← view_firstterminal] at h
  exact h

/-- The first installed incumbent is the reached leaf, with no placeholder
key before it. -/
theorem firstterminal_best {ctx : Ctx n} {cs : List Nat} {st : Search n}
    (hne : cs ≠ []) (hsize : st.canoncode.size = n + 2) (hlen : cs.length ≤ n)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length → st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel) :
    (firstterminal cs.length st).best ctx = some (pathLeafKey ctx cs st.lab) := by
  rw [best_eq_key (firstterminal_codes hsize hlen hcodes hlt) (by change (0 : Int) ≠ 1; decide)]
  simp only [Search.key, hne, ↓reduceIte]
  rfl

/-- A completed leaf has either retained its code verdict or used a
negative row verdict after full code agreement. Both forms recover to a
canonical code machine at every earlier level. -/
inductive Settled (cs bs : List Nat) (st : Search n) : Prop where
  /-- The code comparison itself remains valid. -/
  | codes (machine : Codes cs bs st) (nonpos : st.compCanon ≤ 0)
  /-- Row rejection changed the comparison value, with all codes tied. -/
  | rows (machine : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon 0)
      (negative : st.compCanon < 0)

/-- Either settled form exposes the same semantic incumbent. -/
theorem Settled.read {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Settled cs bs st) : st.best ctx = st.key ctx bs := by
  cases h with
  | codes hm hn => exact best_eq_key hm (by omega)
  | rows hm _ => exact best_eq_key hm (by decide)

/-- A settled comparison can be reindexed across changes to other fields. -/
theorem Settled.congr {cs bs : List Nat} {st out : Search n}
    (h : Settled cs bs st) (hc : out.canoncode = st.canoncode)
    (hl : out.canonlevel = st.canonlevel) (he : out.eqlevCanon = st.eqlevCanon)
    (hp : out.compCanon = st.compCanon) : Settled cs bs out := by
  cases h with
  | codes hm hn =>
    apply Settled.codes
    · show CodeCmpInv n cs bs _ _ _ _
      rwa [hc, hl, he, hp]
    · rwa [hp]
  | rows hm hn =>
    apply Settled.rows
    · rwa [hc, hl, he]
    · rwa [hp]

/-- Recovering either settled leaf verdict truncates the current path
and restores the ordinary canonical comparison invariant. -/
theorem Settled.recover {cs bs : List Nat} {st : Search n} {level : Nat}
    (h : Settled cs bs st) (hlen : level ≤ cs.length) (inf : Nat) :
    Codes (cs.take level) bs (recoverLevels level (recoverPtn inf level st)) := by
  cases h with
  | codes hm hn =>
    have h' := recover_codeInv (st := st.view) (inf := inf) hm hn hlen
    rw [← view_recover] at h'
    exact h'
  | rows hm _ =>
    have h' := recover_codeInv_reset (st := st.view) (inf := inf) hm hlen
    rw [← view_recover] at h'
    exact h'

end Hex.GraphIso.Nauty.Engine
