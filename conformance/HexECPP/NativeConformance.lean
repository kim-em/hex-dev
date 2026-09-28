/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPP.Search

/-! Arithmetic proposals, exceptional twist families, shared allocation
exhaustion and native subject binding. Composite failures carry no verdict. -/

open Hex.ECPP

#guard CM.symbol 2 13 == -1
#guard CM.symbol 2 17 == 1
#guard CM.symbol 5 25 == 0
#guard CM.rootValid 35 1 34
#guard !CM.rootValid 35 2 6
#guard !CM.normValid 13 3 1 1
#guard CM.normValid 13 3 7 1
#guard CM.sqrt? 13 2 10 == some 7 || CM.sqrt? 13 2 10 == some 6
#guard CM.norm? 13 3 6 == some (5, 3)
#guard (CM.curves 13 ⟨3, 0⟩ 2).length == 6
#guard (CM.curves 17 ⟨4, 1728⟩ 3).length == 4
#guard (CM.curves 101 ⟨7, -3375⟩ 2).length == 2
#guard (CM.traces 3 7 1).length == 6
#guard (CM.traces 4 4 3).length == 4
#guard (inverse? 35 15).isNone

-- Every successful root is checked, even for nonsquarefree inputs.
#guard ([9, 25, 35, 49, 101, 113].all fun n => (List.range n).all fun a =>
  (CM.sqrt? n 2 a).all (CM.rootValid n a))

private def exhausted (n : Nat) (b : SearchBudget) (r : Resource) : Bool :=
  match (produce n 0 b).result with
  | .error e => e.resource == r
  | .ok _ => false

#guard exhausted 2 { maxBits := 0 } .inputBits
#guard exhausted 2 { maxDepth := 0 } .depth
#guard exhausted 2 { maxFactorWork := 0 } .factorWork
#guard exhausted 2 { maxOutputBits := 0 } .outputBits
#guard exhausted 2 { maxMemo := 0 } .memo

private def hard : Nat := 177080666831933235355717939809840315427
#guard exhausted hard { maxCandidates := 0 } .candidates
#guard exhausted hard { maxRoots := 0 } .roots
#guard exhausted hard { maxNonresidues := 0 } .nonresidues
#guard exhausted hard { maxPoints := 0 } .points
#guard exhausted hard { maxScalarWork := 0 } .scalarWork
#guard exhausted hard { maxDepth := 1 } .depth
#guard exhausted hard { nonresidueRetries := 0 } .portfolio
#guard exhausted hard { pointRetries := 0 } .portfolio

#guard ([0, 1, 4, 9, 25, 35, 49, 121, 100003 * 100003].all fun n =>
  (produce n 0).result.toOption.isNone)
#guard (produce 17 0).result.toOption.any (checkAt 17)
#guard (produce hard 0).result.toOption.any (checkAt hard)
#guard !(produce hard 0).result.toOption.any (checkAt (hard + 2))
#guard (produce hard 0).state.rand == (produce hard 0).state.rand
#guard (produce hard 0).state.stats.scalarWork > 0

-- A failed recursive branch is charged and later candidates can still succeed.
private def shallow := produce hard 0 { maxDepth := 3 }
#guard shallow.result.toOption.any (checkAt hard)
#guard shallow.state.stats.backtracks == 13
