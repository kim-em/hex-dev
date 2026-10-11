/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Native sample coefficient conversion" =>
%%%
tag := "hex-rcf-sample-conversion"
%%%

A `Tower.Sample` evaluates coefficient polynomials after entering its own
context. {name Hex.RCF.RealCoefficients.NativeSamples.row_converted}`NativeSamples.row_converted`
proves that its complete source row agrees with native specialization at the
converted coordinates. It consumes the actual owner conversion model over an
ordered model field; that field can be non-Archimedean. It assumes no global
ordinary-real interpretation of the parent context. The shared specialization
proof is generalized to that model field, retaining its existing real API.
{name Hex.RCF.RealCoefficients.NativeSamples.sign_converted}`sign_converted`
retains every original divisor's sign. In an infinite model field,
{name Hex.RCF.RealCoefficients.NativeSamples.size_converted}`size_converted`
also preserves normalized sizes, hence degrees, including zero polynomials and
leading cancellation. The owner interpretations reflect zero without identifying
distinct nonzero representations; no global real reader is used for this step.

Here the public section constructor supplies the conversion for its selected
root. The coefficient coordinates enter that same context before evaluation:

```lean
open Hex.RealClosure Hex.RCF.RealCoefficients in
example {registry : BaseContext.Registry}
    {parent : Tower.Context registry}
    (original : Tower.Model parent ℝ)
    (descriptor : Hex.SignDet.Descriptor
      parent.Value Tower.Signature
      parent.sign parent.signature)
    (values : Fin n → parent.Value)
    (formula : Hex.RealFormula.QF (n + 1)) :
    let sample :=
      Tower.Sample.section parent descriptor
    ∃ conversion : Tower.Conversion.Model
        sample.input original,
      sample.signs
          (RepresentationSpecialize.prepare
            values formula) =
        NativeSpecialize.row
          sample.input.context
          (sample.input.value ∘ values)
          sample.value formula := by
  obtain ⟨conversion, _, _, _⟩ :=
    Tower.Sample.section_correct descriptor original
  exact ⟨conversion,
    NativeSamples.row_converted
      original _ conversion values formula⟩
```

The [sample conversion regressions](../../../conformance/HexRCF/NativeSamplesConformance.lean)
use the actual selected positive root of `X²-2`. Its row retains zero and
repeated-root atoms, leading cancellation, and the `(1, 2]` guard atoms. Changing
the source coefficient from `2` to `-2` changes the row at that same root;
an empty atom traversal remains empty. Size tests distinguish zero from nonzero
constants and retain repeated-root degrees and leading cancellation. Native
execution and ordinary-kernel row proofs check the same expected sign words
separately. A nested section uses the actual selected √2 coefficient in
`x² - c`; conversion retains its fixed selected embedding and polynomial sizes.
Its native source and converted rows are both `[0, 1, -1]`. The nested kernel
proofs establish the coordinate identity and row/size conversion; they do not
quote that computed sign word.

{name Hex.RCF.RealCoefficients.NativeSamples.true_real}`NativeSamples.true_real`
consumes a true sample row, authenticated converted coordinate identities and
strict nonzero parent-context signs for every supplied original divisor, using
an infinite model field. It derives the
matrix, sizes of the original parent polynomials and real nonvanishing
at one reader. {name Hex.RCF.RealCoefficients.NativeSamples.not_forall}`NativeSamples.not_forall`
uses a false point row for a universal counterexample. The target provider
history and source identities remain explicit. These point laws establish the
coefficient-conversion bridge; a complete sample certificate must still check
cell membership and full coverage. They do not implement frozen replay or
source-goal quotation.
