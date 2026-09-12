/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Literal.Compact

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Sizes of the actual certificate, including every reference payload.
These counters use unbounded natural numbers and one tree traversal. -/
structure CertStats where
  records : Nat
  automorphisms : Nat
  permutationEntries : Nat
deriving Repr, BEq

mutual

@[expose] def CertNode.stats : CertNode → CertStats
  | .leaf | .codePrune => ⟨1, 0, 0⟩
  | .autom _ raw => ⟨1, 1, raw.size⟩
  | .node cs =>
    let s := CertNode.statsList cs
    { s with records := s.records + 1 }

@[expose] def CertNode.statsList : List CertNode → CertStats
  | [] => ⟨0, 0, 0⟩
  | c :: cs =>
    let a := c.stats
    let b := CertNode.statsList cs
    ⟨a.records + b.records, a.automorphisms + b.automorphisms,
      a.permutationEntries + b.permutationEntries⟩

end

theorem CertNode.records_pos (c : CertNode) : 0 < c.stats.records := by
  cases c <;> simp [CertNode.stats]

namespace Compact

/-- Apply the certificate-record limit before replaying any proof rule.
`none` is exhaustion, `some false` is a rejected certificate, and only
`some true` supplies an accepted canonical key. -/
@[expose] def checkRecords? (maxRecords : Nat) (G : GraphIso.Sparse.Colored n k)
    (cert : CertNode) (B : Key n) : Option Bool :=
  if cert.stats.records ≤ maxRecords then some (checkKey G cert B) else none

/-- Successful bounded replay has exactly the unlimited checker's verdict,
and its complete certificate fits the record limit. -/
theorem checkRecords?_eq_some {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {cert : CertNode} {B : Key n} {b : Bool} :
    checkRecords? maxRecords G cert B = some b ↔
      cert.stats.records ≤ maxRecords ∧ checkKey G cert B = b := by
  simp only [checkRecords?]
  split <;> simp_all <;> omega

theorem checkRecords?_sound {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {cert : CertNode} {B : Key n} (h : checkRecords? maxRecords G cert B = some true) :
    canonSpecKey G = B :=
  checkKey_sound (checkRecords?_eq_some.mp h).2

theorem checkRecords?_none {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {cert : CertNode} {B : Key n} :
    checkRecords? maxRecords G cert B = none ↔ maxRecords < cert.stats.records := by
  simp only [checkRecords?]
  split <;> simp_all

theorem checkRecords?_zero (G : GraphIso.Sparse.Colored n k) (cert : CertNode) (B : Key n) :
    checkRecords? 0 G cert B = none := checkRecords?_none.mpr cert.records_pos

/-- Every unlimited produced certificate is admitted once the finite record
limit covers its actual size. No isomorphism conclusion follows from exhaustion. -/
theorem produceRoot_records (G : GraphIso.Sparse.Colored n k) (gens : List (Perm n))
    (maxRecords : Nat)
    (h : (produceRoot G gens (canonSpecKey G)).stats.records ≤ maxRecords) :
    checkRecords? maxRecords G (produceRoot G gens (canonSpecKey G)) (canonSpecKey G) = some true :=
  checkRecords?_eq_some.mpr ⟨h, produceRoot_replays G gens⟩

end Compact

namespace Literal.Compact

/-- Literal record-limited replay has the native checker's exact verdict. -/
@[expose] def checkRecords? (maxRecords : Nat) (G : GraphIso.Sparse.Colored n k)
    (cert : CertNode) (B : Key n) : Option Bool :=
  if cert.stats.records ≤ maxRecords then some (checkKey G cert B) else none

theorem checkRecords?_eq : @checkRecords? = @Sparse.Compact.checkRecords? := by
  funext n k maxRecords G cert B
  simp only [checkRecords?, Sparse.Compact.checkRecords?, checkKey_eq]

theorem checkRecords?_sound {maxRecords : Nat} {G : GraphIso.Sparse.Colored n k}
    {cert : CertNode} {B : Key n} (h : checkRecords? maxRecords G cert B = some true) :
    canonSpecKey G = B :=
  Sparse.Compact.checkRecords?_sound (by simpa only [checkRecords?_eq] using h)

end Literal.Compact
end Hex.GraphIso.Nauty.Sparse
