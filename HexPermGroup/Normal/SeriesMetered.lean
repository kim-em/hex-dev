/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.DerivedBounded
public import HexPermGroup.Normal.SeriesBounded

public section

namespace Hex.PermGroup.Series

open Execution

/-- The term cap and producer meter are independent. A term cap yields a checked
prefix; exhausting producer work yields no solvability verdict. -/
@[expose] def construct {budget : Budget} (terms : Nat) (G : Group n) :
    Run budget {result : BoundedResult G // result.certificate.terms ≤ terms} := do
  reserve .nodes 1
  reserve .certificates 1
  if ht : G.isTrivial = true then
    return ⟨.ofResult (Result.trivial G ht), by
      simp [BoundedResult.ofResult, Result.trivial, Partial.terms, Certificate.terms]⟩
  else
    match hk : terms with
    | 0 => return ⟨.pending G ht, by simp [BoundedResult.pending, Partial.terms]⟩
    | k + 1 =>
      let d ← Derived.construct G
      let queries := G.generators.size + d.group.generators.size
      reserve .sifts ((n + 1) * queries)
      reserve .images ((2 * n * n + n) * queries)
      if he : d.group.sameGroup G = true then
        return ⟨.ofResult (Result.perfect G d ht he), by
          simp [hk, BoundedResult.ofResult, Result.perfect, Partial.terms, Certificate.terms]⟩
      else
        let tail ← construct k d.group
        return ⟨.prepend G d he tail.val, by
          simpa only [hk, BoundedResult.prepend, Partial.terms] using Nat.succ_le_succ tail.property⟩

end Hex.PermGroup.Series

namespace Hex.PermGroup.Group

/-- Bound the complete cost of derived steps as well as the number of terms.
Every successful result carries its checked-prefix and term-count contracts;
only a terminal certificate yields a solvability answer. -/
@[expose] def derivedSeriesWithin (budget : Execution.Budget) (G : Group n) (terms : Nat) :
    Execution.Measured budget {result : Series.BoundedResult G // result.certificate.terms ≤ terms} :=
  Execution.run budget (Series.construct terms G)

end Hex.PermGroup.Group
