/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PolyOps.Laws

public section

/-! Raw coefficient arrays and replayable semantic degree. Every stored coefficient is visited
once, including coefficients below the leading term, so invalid lower coefficients cannot be
hidden by a nonzero leading coefficient. -/

namespace Hex.PolyOps

/-- Bytes in an unsigned base-128 variable-length integer literal, including zero. -/
@[expose] def natBytes (n : Nat) : Nat := n.log2 / 7 + 1

/-- Each certificate entry is tied to its index in the original array. Replay also checks
that indices occur exactly once, in order; arbitrary supplied entries are not trusted. -/
abbrev DegreeEntry (ops : CoeffOps C) (p : Array C) :=
  (i : Fin p.size) × (z : Bool) × ops.Evidence (.zero p[i] z)

structure DegreeEvidence (ops : CoeffOps C) (p : Array C) where
  degree : Option Nat
  entries : Array (DegreeEntry ops p)

/-- Scan the stored length using semantic zero decisions, retaining all checked evidence.
No failure carries a partial degree or certificate. -/
@[expose] def degreeWith (ops : CoeffOps C) (p : Array C) : ops.Run (DegreeEvidence ops p) := do
  charge .evidenceNodes
  charge .evidenceBytes (2 * natBytes p.size + 1)
  let mut degree := none
  let mut entries := #[]
  for h : i in [:p.size] do
    charge .steps
    let z ← ops.zeroWith p[i]
    charge .evidenceNodes
    charge .evidenceBytes (natBytes i + 1)
    entries := entries.push ⟨⟨i, h.upper⟩, z⟩
    if !z.1 then degree := some i
  return ⟨degree, entries⟩

/-- Replay consumes the supplied evidence, never invoking a zero producer. Extra, omitted,
duplicated, reordered, or inconsistent entries are rejected. -/
@[expose] def checkDegree (ops : CoeffOps C) (p : Array C) (e : DegreeEvidence ops p) :
    ops.Run Unit := do
  charge .evidenceNodes
  charge .evidenceBytes (natBytes e.entries.size + 1 + e.degree.elim 0 natBytes)
  charge .steps
  if e.entries.size != p.size then
    fun b => .rejected (.evidence "degree certificate length") b
  else
    let mut degree := none
    for h : i in [:e.entries.size] do
      charge .steps
      let entry := e.entries[i]
      charge .evidenceNodes
      charge .evidenceBytes (natBytes entry.1.val + 1)
      if entry.1.val != i then
        return ← fun b => .rejected (.evidence "degree certificate index") b
      ops.checkWith (.zero p[entry.1] entry.2.1) entry.2.2
      if !entry.2.1 then degree := some i
    if degree == e.degree then return ()
    else fun b => .rejected (.evidence "degree certificate value") b

/-- The checker for a coefficientwise identity works with a difference produced by checked
arithmetic; it records the negation, addition, and resulting zero evidence. -/
structure EqualityEvidence (ops : CoeffOps C) (a b : C) where
  negative : C
  difference : C
  negation : ops.Evidence (.neg b negative)
  subtraction : ops.Evidence (.add a negative difference)
  zero : ops.Evidence (.zero difference true)

/-- Certify the asserted equality `a = b`. A checked nonzero difference refutes that
assertion and returns `rejected`. Semantic equality decisions use `zeroWith` on a checked
difference; this helper produces evidence specifically for an asserted identity. -/
@[expose] def equalWith (ops : CoeffOps C) (a b : C) : ops.Run (EqualityEvidence ops a b) := do
  let n ← ops.negWith b
  let d ← ops.addWith a n.1
  let z ← ops.zeroWith d.1
  if h : z.1 = true then
    ops.retainWith n.1
    ops.retainWith d.1
    charge .evidenceNodes
    charge .evidenceBytes 1
    return ⟨n.1, d.1, n.2, d.2, h ▸ z.2⟩
  else fun rest => .rejected (.invariant "asserted coefficient equality is false") rest

@[expose] def checkEquality (ops : CoeffOps C) (a b : C) (e : EqualityEvidence ops a b) :
    ops.Run Unit := do
  charge .evidenceNodes
  charge .evidenceBytes 1
  ops.retainWith e.negative
  ops.retainWith e.difference
  ops.checkWith (.neg b e.negative) e.negation
  ops.checkWith (.add a e.negative e.difference) e.subtraction
  ops.checkWith (.zero e.difference true) e.zero

/-- Coefficient access defaults to the record's semantic zero, without any instance on C. -/
@[expose] def coeff (ops : CoeffOps C) (p : Array C) (i : Nat) : C := p[i]?.getD ops.zero

abbrev IdentityEvidence (ops : CoeffOps C) (p q : Array C) :=
  Array ((i : Fin (max p.size q.size)) × EqualityEvidence ops (coeff ops p i) (coeff ops q i))

/-- Certify the asserted coefficientwise identity `p = q`; a refuted assertion is rejected.
Reconstruction checks use this contract to certify an identity they claim to satisfy. -/
@[expose] def identityWith (ops : CoeffOps C) (p q : Array C) :
    ops.Run (IdentityEvidence ops p q) := do
  charge .evidenceNodes
  charge .evidenceBytes (natBytes (max p.size q.size))
  let mut entries := #[]
  for h : i in [:max p.size q.size] do
    charge .steps
    let e ← equalWith ops (coeff ops p i) (coeff ops q i)
    charge .evidenceNodes
    charge .evidenceBytes (natBytes i)
    entries := entries.push ⟨⟨i, h.upper⟩, e⟩
  return entries

@[expose] def checkIdentity (ops : CoeffOps C) (p q : Array C) (e : IdentityEvidence ops p q) :
    ops.Run Unit := do
  charge .evidenceNodes
  charge .evidenceBytes (natBytes e.size)
  charge .steps
  if e.size != max p.size q.size then
    fun b => .rejected (.evidence "identity certificate length") b
  else
    for h : i in [:e.size] do
      charge .steps
      let entry := e[i]
      charge .evidenceNodes
      charge .evidenceBytes (natBytes entry.1.val)
      if entry.1.val != i then
        return ← fun b => .rejected (.evidence "identity certificate index") b
      checkEquality ops (coeff ops p entry.1) (coeff ops q entry.1) entry.2
    return ()

/-- Accepted equality evidence denotes equal coefficients, even with noninjective models. -/
theorem checkEquality_sound [Lean.Grind.CommRing D] [LE D] [LT D]
    [Std.IsLinearOrder D] [Std.LawfulOrderLT D] [Lean.Grind.OrderedRing D]
    (ops : CoeffOps C) (m : Interpretation C D) (laws : CoefficientLaws ops m)
    (a b : C) (e : EqualityEvidence ops a b) {start finish : Budget}
    (h : checkEquality ops a b e start = .ok () finish) : m.denote a = m.denote b := by
  obtain ⟨_, _, _, h⟩ := Result.bind_ok h
  obtain ⟨_, _, _, h⟩ := Result.bind_ok h
  obtain ⟨_, _, _, h⟩ := Result.bind_ok h
  obtain ⟨_, _, _, h⟩ := Result.bind_ok h
  obtain ⟨_, _, hn, h⟩ := Result.bind_ok h
  obtain ⟨_, _, ha, hz⟩ := Result.bind_ok h
  obtain ⟨nb, nb', hn⟩ := ops.checkWith_accepted _ _ hn
  obtain ⟨ab, ab', ha⟩ := ops.checkWith_accepted _ _ ha
  obtain ⟨zb, zb', hz⟩ := ops.checkWith_accepted _ _ hz
  have hn := laws.check_sound _ nb _ nb' hn
  have ha := laws.check_sound _ ab _ ab' ha
  have hz := laws.check_sound _ zb _ zb' hz
  simp only [Claim.Holds] at hn ha hz
  have hzero := hz.2.mp trivial
  grind

end Hex.PolyOps
