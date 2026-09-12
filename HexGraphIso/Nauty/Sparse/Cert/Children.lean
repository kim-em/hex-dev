/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Autom
public import HexGraphIso.Nauty.Sparse.Cert.Siblings

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- Check all target positions, replaying ordinary children once and copying
earlier attainment flags only through checked automorphisms of child cells. -/
@[expose] def checkChildren (G : Hex.SparseGraph n) (level : Nat)
    (lab ptn : Array Nat) (tc : Nat) (check : Nat → CertNode → Option Bool)
    (cs : List CertNode) : Option Bool := do
  let child := fun o => breakout n lab ptn (level + 1) tc lab[tc + o]!
  let flags ← Replay.scan check (fun o earlier raw =>
    Replay.checkAutom G (level + 1) (child earlier).1 (child o).1 (child o).2.1 raw) #[] cs
  Replay.all (fun o => some flags[o]!) (List.range cs.length)

/-- Sibling reference replay covers the whole target cell. Both the ordinary
child rule and the automorphism rule preserve exact attainment. -/
theorem checkChildren_valid {G : Hex.SparseGraph n} {B : Key n}
    {tcLevel fuel level numcells tc : Nat} {lab ptn : Array Nat} {active : VSet n}
    {check : Nat → CertNode → Option Bool} {cs : List CertNode} {a : Bool}
    (hp : SpecNode G level lab ptn active numcells)
    (heq : Equitable (Graph.context G) level lab ptn)
    (hc : IsCell ptn level tc cs.length) (hb : tc + cs.length ≤ n) (hn : 1 < cs.length)
    (hcheck : ∀ o c b, o < cs.length → check o c = some b →
      let child := breakout n lab ptn (level + 1) tc lab[tc + o]!
      Replay.Valid G B (specLeaves G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
        (numcells + 1)) b)
    (h : checkChildren G level lab ptn tc check cs = some a) :
    Replay.Valid G B ((List.range cs.length).flatMap fun o =>
      let child := breakout n lab ptn (level + 1) tc lab[tc + o]!
      specLeaves G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2 (numcells + 1)) a := by
  let child := fun o => breakout n lab ptn (level + 1) tc lab[tc + o]!
  let P := fun o b => o < cs.length → Replay.Valid G B
    (specLeaves G tcLevel fuel (level + 1) (child o).1 (child o).2.1 (child o).2.2
      (numcells + 1)) b
  rw [checkChildren] at h
  obtain ⟨flags, hscan, hall⟩ := Option.bind_eq_some_iff.mp h
  have hs := Replay.scan_valid (P := P)
    (fun o c b h ho => hcheck o c b ho h) (fun o earlier raw b hlt hprev hw ho => ?_)
    (by simp) hscan
  · apply Replay.all_valid (fun o ho b hf => ?_) hall
    have ho' : o < cs.length := List.mem_range.mp ho
    cases Option.some.inj hf
    have hsize : flags.size = cs.length := by simpa using hs.1
    exact hs.2 o (by rw [hsize]; exact ho') ho'
  · have hearlier : earlier < cs.length := Nat.lt_trans hlt ho
    have hfirst := hp.child heq hc hb hn hearlier
    have hnext := hp.child heq hc hb hn ho
    obtain ⟨p, hautom, hcells⟩ := Replay.checkAutom_sound
      hfirst.node.labSize hnext.node.labSize hnext.node.ptnSize hnext.node.ptnEnd hw
    exact (hprev hearlier).map hfirst hnext p hautom hcells

/-- If every emitted record succeeds at its actual target offset, the full
ordered scan succeeds. Earlier attainment flags may have either value. -/
theorem checkChildren_exists {G : Hex.SparseGraph n} {level tc : Nat}
    {lab ptn : Array Nat} {check : Nat → CertNode → Option Bool} {cs : List CertNode}
    (hsteps : ∀ o (ho : o < cs.length) (seen : Array Bool), seen.size = o →
      let child := fun j => breakout n lab ptn (level + 1) tc lab[tc + j]!
      ∃ a, Replay.sibling check (fun j earlier raw => Replay.checkAutom G (level + 1)
        (child earlier).1 (child j).1 (child j).2.1 raw) seen cs[o] = some a) :
    ∃ a, checkChildren G level lab ptn tc check cs = some a := by
  obtain ⟨flags, hf⟩ := Replay.scan_exists (seen := #[]) (fun o ho s hs =>
    hsteps o ho s (by simpa using hs))
  obtain ⟨a, ha⟩ := Replay.all_exists (xs := List.range cs.length)
    (check := fun o => some flags[o]!) (fun o _ => ⟨flags[o]!, rfl⟩)
  exact ⟨a, by simp only [checkChildren, hf]; exact ha⟩

end Hex.GraphIso.Nauty.Sparse.Compact
