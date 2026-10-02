/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceSweep
public import HexGraphIso.Nauty.Sparse.GenerationTrace
public import HexGraphIso.Nauty.Policy.Generated.Receipt
import all HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Nauty.Generation.Canon
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- All three actual native reference-return alternatives discharge the
current stabilizer-orbit obligation in a containing generated group.
The shared group relation uses the sparse graph's semantic interpretation;
every child call, scatter, label position and orbit pointer is native. -/
theorem receipt {G : GraphIso.Sparse.Colored n k} {gs : List (Perm n)} {base : List (Fin n)}
    {guide tv : Fin n} {tcLevel fuel level numcells tc : Nat} {first short : Bool}
    {st out : State n} {cell : VSet n} {previous : Option Nat}
    (h : Nauty.Generation.Cover G.toDense gs base guide cell previous)
    (hready : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (htarget : Generic.Target State.frame level tc cell st)
    (hnext : cell.nextElem previous = some tv.val)
    (hpast : Nauty.Generation.CanonPast level tc previous st)
    (hcall : Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv.val st) =
        (.unwind level short, out))
    (hr : RefReturn (Graph.context G.graph) level out)
    (hsaved : Saved G out) (horbits : OrbitTrace G out) (hsound : TraceOk G out)
    (htrace : Realizes G gs out.genTrace.toList)
    (hfix : ∀ gamma ∈ out.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val)
    (hfirst : out.firstlab[tc]! = guide.val) (hcoset : out.cosetindex = tv.val) :
    Nauty.Generation.Cover G.toDense gs base guide cell (some tv.val) := by
  have hv := VSet.nextElem_mem hnext
  have hpos : tc < n := by
    obtain ⟨len, hcell, _⟩ := htarget
    obtain ⟨_, hlen, hrange⟩ := hcell (mem_ne_empty hv)
    omega
  have hcurrent := hready.child_chosen (tcLevel := tcLevel) (fuel := fuel) hn hl first false htarget hv
  rw [hcall] at hcurrent
  cases hr with
  | first returned carrier =>
    exact h.reference hnext (fun _ => Nauty.Generation.Carries.refl G.toDense gs base guide)
      carrier htrace hfix hpos hfirst hcurrent
  | canon returned carrier =>
    have he := hready.canon_earlier (tcLevel := tcLevel) (fuel := fuel) hn hl first false htarget hpast hnext
    rw [hcall] at he
    have hearlier := he returned.symm
    let u : Fin n := ⟨out.canonlab[tc]!, cellsReach_lt hsaved.canonical.2 tc hpos⟩
    exact h.reference (u := u) hnext (fun hu => h.before hnext hu hearlier)
      carrier htrace hfix hpos rfl hcurrent
  | orbit returned smaller =>
    apply h.orbitSkip hnext (horbits hsound) htrace
      (fun gamma hgamma => hfix gamma (Array.mem_toList_iff.mp hgamma))
    rw [hcoset] at smaller
    omega

end Hex.GraphIso.Nauty.Sparse.Generation
