/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxBoundary
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.FirstCompare
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.CodeCalls
import all HexGraphIso.Nauty.Policy.ReturnCodes
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- Every actual node returns settled incumbent codes on an extension
of its incoming path, including the initial first descent. -/
theorem NodeInput.codes {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let out := (node first ctx (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    ∃ bs' fs', ReturnCodes ctx f.codes bs' fs' out ∧
      Generic.Grows (f.entry.key ctx bs) (out.best ctx) := by
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  cases first with
  | false =>
    obtain ⟨bs', hr, hg⟩ := node_codes hn0 hgsz hsymm hloop h.entry.1 h.fuel h.frame.length h.entry.2
    refine ⟨bs', fs, hr, ?_⟩
    rwa [hr.read]
  | true =>
    obtain ⟨hp, hbs, _, _, ht, hsize, hcodes, hlt, _⟩ := h.entry
    obtain ⟨last, leaf, path⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
      hn0 h.frame.positive h.frame.partition (empty_orbits hp.orbits ht) h.fuel
    obtain ⟨fs', bs', _, _, hr⟩ := firstPath_codes hn0 hgsz hsymm hloop path hp hsize
      h.fuel h.frame.length hcodes hlt
    refine ⟨bs', fs', hr, ?_⟩
    intro b hb
    simp only [Search.key, hbs, ↓reduceIte] at hb
    cases hb

/-- Cleanup preserves a settled receipt, and recovery identifies the
next sweep's ghost incumbent with the actual returned stored key. -/
theorem NodeInput.recovered_codes {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {first : Bool} {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel first f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (afterFirst : Bool) (tv1 tv : Nat) :
    let out := (node first ctx (n + 2) tcLevel fuel f.level f.numcells f.entry).2
    let middle := if afterFirst then afterChildFirst (f.level - 1) tv1 out else out
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := recoverLevels f.codes.length (recoverPtn (n + 2) f.codes.length left)
    ∃ bs' fs', Comparison ctx f.codes bs' fs' ready ∧ ready.compCanon ≤ 0 ∧
      ready.best ctx = ready.key ctx bs' ∧ out.best ctx = ready.key ctx bs' := by
  intro out middle left ready
  obtain ⟨bs', fs', hr, _⟩ := h.codes hgsz hsymm hloop
  have hm : ReturnCodes ctx f.codes bs' fs' middle := by
    dsimp only [middle]
    split <;> exact hr.fields rfl rfl rfl
  have hl := hm.leave tv
  have hk : left.key ctx bs' = out.key ctx bs' := by
    dsimp only [left, middle]
    split <;> rfl
  refine ⟨bs', fs', hl.recover (n + 2), recover_nonpos hl.nonpos _ _,
    (hl.resumed (n + 2)).read, ?_⟩
  rw [hr.read, recover_key, hk]

end Hex.GraphIso.Nauty.Engine.Max
