/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Receipt
import all HexGraphIso.Nauty.Correct.Generation.Carry
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {base : List (Fin n)}

/-- Stabilizing a reached frame fixes the individualized base because
those vertices are singleton cells in that frame. -/
theorem frame_fixes {level : Nat} {st : SearchSt n} {γ : Array Nat}
    (hfixed : FixedCells level st) (hsize : st.lab.size = n)
    (hbase : ∀ b ∈ base, st.fixedpts.mem b.val = true)
    (hstab : CellStab st.ptn level st.lab γ) :
    ∀ b ∈ base, γ[b.val]! = b.val := by
  intro b hb
  obtain ⟨pos, hpos, hat, hcell⟩ := hfixed b.val b.isLt (hbase b hb)
  have hf := cellStab_fixes (by omega : pos < st.lab.size) hcell hstab
  rwa [hat] at hf

/-- The return-level stabilization invariant supplies exactly the fixed
base condition needed when a first-path sweep resumes. -/
theorem return_fixes {level : Nat} {st out : SearchSt n}
    {trail : FrameTrail} {entry : TrailEntry} {r : Int}
    (hreturn : ReturnStab trail r out) (hlevel : Int.ofNat level ≤ r)
    (hentry : trail level = some entry)
    (hlab : entry.frame.rsLab = st.lab) (hptn : entry.frame.rsPtn = st.ptn)
    (hfixed : FixedCells level st) (hsize : st.lab.size = n)
    (hbase : ∀ b ∈ base, st.fixedpts.mem b.val = true) :
    ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val := by
  intro γ hγ
  have hs := hreturn level entry hlevel hentry γ (by simpa using hγ)
  rw [hlab, hptn] at hs
  exact frame_fixes hfixed hsize hbase hs

/-- The path stabilization invariant places every possible image of the
first child in the initial target window of its sweep. -/
theorem Cover.window {st : SearchSt n} {level tc len : Nat} {guide : Fin n}
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    (hlab : LabOk st.lab n) (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.lab.size)
    (hbase : ∀ b : Fin n, st.fixedpts.mem b.val = true → b ∈ base)
    (hguide : (windowSet n st.lab tc len).mem guide.val = true) :
    Cover G base guide (windowSet n st.lab tc len) none := by
  apply Cover.start
  intro v hv
  obtain ⟨p, hp, hfix, rfl⟩ := hv
  exact window_stable hpath hlab hcell hrange hp
    (fun b hb => hfix b (hbase b hb)) guide hguide

/-- A skipped first-path child uses the live frame's stabilization proof
and the final trace inclusion; no certificate is constructed by search. -/
theorem Cover.frameSkip {st : SearchSt n} {level : Nat} {guide tv : Fin n}
    {tcell : VSet n} {cursor : Option Nat}
    (h : Cover G base guide tcell cursor)
    (hnext : tcell.nextElem cursor = some tv.val)
    (horbits : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (htrace : ∀ γ ∈ st.genTrace, γ ∈ Aut.trace G)
    (hstab : ∀ γ ∈ st.genTrace.toList, CellStab st.ptn level st.lab γ)
    (hfixed : FixedCells level st) (hsize : st.lab.size = n)
    (hbase : ∀ b ∈ base, st.fixedpts.mem b.val = true)
    (hne : st.orbits[tv.val]! ≠ tv.val) : Cover G base guide tcell (some tv.val) := by
  exact h.orbitSkip hnext horbits (fun γ hγ => htrace γ (by simpa using hγ))
    (fun γ hγ => frame_fixes hfixed hsize hbase (hstab γ hγ)) hne

end Hex.GraphIso.Nauty.Generation
