/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SturmCheck
public import HexRealRoots.Chain
public import HexPolyZ.Core

public section

/-!
# Builder for multiplication-only Sturm replays

This is compiled preparation code, outside the proof trust boundary. It
instruments the existing sign-managed pseudo-remainder loop with an accumulated
integer scale and quotient, then retains a candidate only when the small
`SturmReplay.check` verifier accepts it.

The literal chain starts with the supplied polynomial itself, rather than its
primitive part. This matters for nonprimitive carrier polynomials.
-/

namespace Hex.RCF

/-- Accumulated identity for one pseudo-remainder computation. Intended
semantics: `scale leftScale dividend = quotient * divisor + remainder`. -/
private structure SpemWitness where
  leftScale : Int
  quotient : ZPoly
  remainder : ZPoly

/-- Instrument `ZPoly.spemAux` while accumulating its exact scale and
quotient. Each reduction step multiplies the previous identity by the positive
absolute leading coefficient of `g` and adds the cancelled leading monomial to
the quotient. Unlike `ZPoly.spemAux`, the zero-fuel case accepts only a state
that has already reached a genuine stopping condition. -/
private def buildSpemAux (g : ZPoly) : Nat → SpemWitness → Option SpemWitness
  | 0, state =>
      if state.remainder.isZero then some state
      else if (DensePoly.degree? state.remainder).getD 0 <
          (DensePoly.degree? g).getD 0 then some state
      else none
  | fuel + 1, state =>
      if state.remainder.isZero then some state
      else if (DensePoly.degree? state.remainder).getD 0 <
          (DensePoly.degree? g).getD 0 then some state
      else
        let cg := DensePoly.leadingCoeff g
        let lr := DensePoly.leadingCoeff state.remainder
        let a := if cg < 0 then -cg else cg
        let b := if cg < 0 then -lr else lr
        let k := (DensePoly.degree? state.remainder).getD 0 -
          (DensePoly.degree? g).getD 0
        buildSpemAux g fuel {
          leftScale := a * state.leftScale
          quotient := DensePoly.scale a state.quotient + DensePoly.monomial k b
          remainder := ZPoly.spemStep g state.remainder }

/-- Compute one pseudo-remainder together with its exact multiplication
witness. The dividend size is the same structural fuel used by `ZPoly.spem`. -/
private def buildSpem (dividend divisor : ZPoly) : Option SpemWitness :=
  buildSpemAux divisor dividend.size {
    leftScale := 1
    quotient := 0
    remainder := dividend }

/-- Extend a replay until its current entry is a nonzero constant. A zero
remainder before that point detects a nonsquarefree input; fuel exhaustion is
rejected directly. -/
private def buildReplayAux (derivScale : Int) :
    Nat → ZPoly → ZPoly → Array ZPoly → Array SturmStep → Option SturmReplay
  | 0, _, _, _, _ => none
  | fuel + 1, prev, cur, chain, steps =>
      if cur.size = 1 then
        some { chain, derivScale, steps }
      else if cur.isZero then none
      else
        match buildSpem prev cur with
        | none => none
        | some witness =>
            if witness.remainder.isZero then none
            else
              let rightScale := ZPoly.content witness.remainder
              if rightScale ≤ 0 then none
              else
                let next := -(ZPoly.primitivePart witness.remainder)
                let step : SturmStep := {
                  leftScale := witness.leftScale
                  quotient := witness.quotient
                  rightScale }
                buildReplayAux derivScale fuel cur next
                  (chain.push next) (steps.push step)

/-- Build an unchecked replay candidate for a positive-degree polynomial. -/
private def buildSturmReplayRaw? (f : ZPoly) : Option SturmReplay :=
  match f.degree? with
  | some (_ + 1) =>
      let deriv := DensePoly.derivative f
      if deriv.isZero then none
      else
        let derivScale := ZPoly.content deriv
        let s₁ := ZPoly.primitivePart deriv
        buildReplayAux derivScale f.size f s₁ #[f, s₁] #[]
  | _ => none

/-- Build and verify a multiplication-only generalized Sturm replay.

The compiled builder may use pseudo-remainders and primitive parts, but a
candidate crosses the boundary only after the multiplication-only checker
accepts it. -/
def buildSturmReplay? (f : ZPoly) : Option SturmReplay :=
  match buildSturmReplayRaw? f with
  | none => none
  | some replay => if replay.check f then some replay else none

/-- Every certificate returned by the builder has passed the kernel-facing
Boolean checker. -/
theorem check_of_build_eq_some {f : ZPoly} {replay : SturmReplay}
    (h : buildSturmReplay? f = some replay) : replay.check f = true := by
  unfold buildSturmReplay? at h
  split at h
  · contradiction
  · split at h
    · simp_all
    · contradiction

end Hex.RCF
