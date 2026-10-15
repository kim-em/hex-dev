/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients

public section

namespace Hex.RCF.NormalizedInputs

open Hex.RCF.RealCoefficients

@[expose] def exposedRep : RefinedIsolation CubeTwo.polynomial :=
  ⟨⟨CubeTwo.square, .ofWitness (by decide)⟩, by decide⟩

-- Executable data remain available to compilation, but this definition's body
-- is deliberately unavailable to the kernel in an importing module.
def hiddenRep : RefinedIsolation CubeTwo.polynomial := exposedRep

@[expose] def exposedAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized CubeTwo.polynomial (by rfl) (by decide)
    (by decide) CubeTwo.checked CubeTwo.squarefree exposedRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

@[expose] def hiddenAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized CubeTwo.polynomial (by rfl) (by decide)
    (by decide) CubeTwo.checked CubeTwo.squarefree hiddenRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

@[expose] def exposed : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic exposedAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      CubeTwo.polynomial (by rfl) (by decide) (by decide)
      CubeTwo.checked CubeTwo.squarefree exposedRep _)).trans
      ((HexRootsTheory.RefinedIsolation.meetsRealAxis_iff exposedRep).mp (by decide)))

@[expose] def hidden : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic hiddenAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      CubeTwo.polynomial (by rfl) (by decide) (by decide)
      CubeTwo.checked CubeTwo.squarefree hiddenRep _)).trans
      ((HexRootsTheory.RefinedIsolation.meetsRealAxis_iff hiddenRep).mp (by decide)))

end Hex.RCF.NormalizedInputs
