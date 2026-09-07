/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Counter
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- The guiding visit of a first-path sweep and its actual recovered
tail. This proof witness exposes the setup already established by the
correctness induction, without rerunning or instrumenting the search. -/
inductive FirstHead (G : Colored n k) (ctx : Ctx n)
    (inf tcLevel specFuel runFuel level numcells tc len tv1 e : Nat)
    (codes : List Nat) (rsLab rsPtn : Array Nat) (tcell : VSet n)
    (pre : SearchSt n) (trail : FrameTrail) : Prop where
  | intro {offset : Nat} {child out : SearchSt n} {r : Int}
      {fs : List Nat} {best : Option (Key n)} {eventTrail : FrameTrail}
      (next : tcell.nextElem none = some tv1)
      (orbit : (pre.orbits[tv1]! == tv1) = true)
      (lab : pre.lab = rsLab) (ptn : pre.ptn = rsPtn)
      (path : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 level pre)
      (offsetLt : offset < len) (atOffset : rsLab[tc + offset]! = tv1)
      (childEq : child = { pre with
        lab := (breakout n pre.lab pre.ptn (level + 1) tc tv1).1
        ptn := (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.1
        active := (breakout n pre.lab pre.ptn (level + 1) tc tv1).2.2
        fixedpts := pre.fixedpts.insert tv1
        cosetindex := tv1 })
      (first : FirstInv G ctx (level + 1) codes (numcells + 1) child
        (trail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩))
      (childPath : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 (level + 1) child)
      (boundary : child.noncheaplevel ≤ level + 1)
      (desc : CheapDesc ctx (level + 1) child.noncheaplevel
        (refine ctx (level + 1) child.lab child.ptn child.active (numcells + 1)))
      (orbits : OrbSound (OrbConn child.genTrace.toList n) child.orbits n)
      (call : firstPathNode ctx inf tcLevel runFuel (level + 1) (numcells + 1) child = (r, out))
      (run : FirstRun G ctx tcLevel specFuel runFuel (level + 1) codes fs child out
        (numcells + 1) best
        (trail.push level ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
        eventTrail r)
      (keep : FirstKeep ctx (level + 1) child out fs best)
      (tail : ¬ r < Int.ofNat level →
        let cleaned := { out with
          gcaFirst := level, stabvertex := tv1, fixedpts := out.fixedpts.erase tv1 }
        let cleared := clearShortIf out.needshortprune cleaned
        let cell := if out.needshortprune then shortprune tcell cleared else tcell
        FirstTail G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
          codes fs rsLab rsPtn pre n (some tv1) cell (recover n inf level cleared) best eventTrail) :
      FirstHead G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
        codes rsLab rsPtn tcell pre trail

end Hex.GraphIso.Nauty.Generation
