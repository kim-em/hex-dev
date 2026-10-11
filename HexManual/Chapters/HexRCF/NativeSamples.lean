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
`x² - c`; the owner conversion model retains its selected embedding and polynomial sizes.
Its source and converted rows are both `[0, 1, -1]`, with separate ordinary-kernel
proofs using the selected root’s actual facts. Changing the coefficient to the
negative conjugate gives `[1, 1, -1]` at the same upper root, also kernel-checked.
The source size words are independently kernel-checked. Actual point consumers
construct the rational provider history and inherited coefficient identities for
the X²−2 section: a true row retains the parent divisor `2`, and a false row
proves `¬ ∀ x : ℝ, x² > 2`.

The [infinitesimal-parent sample regression](../../../conformance/HexRCF/NativeSampleModelConformance.lean)
constructs the owner's ordered real-closed reference field from an actual
infinitesimal base history. Its point sample is the native infinitesimal itself.
A converted true row yields one ordinary real point with `0 < x < 1`, retaining
that same original value as a nonzero divisor. No inherited source coordinate
pins this guard to a predetermined real number. The sample and guard are realized
together; an infinitesimal is never used as a real witness.

{name Hex.RCF.RealCoefficients.NativeSamples.true_real}`NativeSamples.true_real`
consumes a true sample row, inherited base/provider coordinate identities and
strict nonzero parent-context signs for every supplied original divisor, using
an infinite model field. It derives the
matrix, sizes of the original parent polynomials and real nonvanishing
at one reader. {name Hex.RCF.RealCoefficients.NativeSamples.not_forall}`NativeSamples.not_forall`
uses a false point row with those same inherited coordinates for a universal
counterexample; it takes no divisor guards. The target provider
history and inherited identities remain explicit. `Origin.RealValue` only fixes
values embedded from the staged base/provider; it does not fix arbitrary
algebraic suffix coordinates such as the nested √2 coefficient. That test's
`coefficient_fixed` is an identity in the owner conversion model, not an input to
these point APIs. Proving selected-root source identities at the finite reader
remains a separate obligation. These point laws establish the
coefficient-conversion bridge; a complete sample certificate must still check
cell membership and full coverage. They do not implement frozen replay or
source-goal quotation.
