/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.LocalSample

public section

namespace Hex.RealClosure.Tower.Sample
variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable {polynomials : List parent.Poly} (family : Family parent polynomials) (original : Model parent K)

example (x : K) : ∃! region, region ∈ family.cells ∧ region.Mem original x :=
  family.cells_unique original x

example (sample : Tower.Sample parent) (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.contains sample.value = true ∧ ∀ x, sample.cell.Mem realization.target x →
        sample.signs polynomials = polynomials.map (fun p => (SignType.sign
          ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) :=
  family.sector_signs original sample present

example (empty : family.boundaries = []) :
    ∃ sample, family.sectorBetween? .negInf .posInf = some sample :=
  family.sectorBetween?_success original .whole (family.wholeLine_mem empty)
    .negInf .posInf .negInf .posInf rfl rfl rfl

example (before after : List (Root parent)) (a b : Root parent)
    (adjacent : family.boundaries = before ++ a :: b :: after) :
    ∃ sample, family.sectorBetween? (.finite a) (.finite b) = some sample :=
  family.sectorBetween?_success original (.between a b) (family.bounded_mem before after a b adjacent)
    (.finite a) (.finite b) (.finite a) (.finite b) rfl rfl rfl

example (first : Root parent) (rest : List (Root parent))
    (boundary : family.boundaries = first :: rest) :
    ∃ sample, family.sectorBetween? .negInf (.finite first) = some sample :=
  family.sectorBetween?_success original (.left first) (family.leftRay_mem first rest boundary)
    .negInf (.finite first) .negInf (.finite first) rfl rfl rfl

example (before : List (Root parent)) (last : Root parent)
    (boundary : family.boundaries = before ++ [last]) :
    ∃ sample, family.sectorBetween? (.finite last) .posInf = some sample :=
  family.sectorBetween?_success original (.right last) (family.rightRay_mem before last boundary)
    (.finite last) .posInf (.finite last) .posInf rfl rfl rfl

end Hex.RealClosure.Tower.Sample
