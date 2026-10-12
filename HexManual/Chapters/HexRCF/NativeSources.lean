/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRCF.RealCoefficients

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Selected coefficient identities at one real reader" =>
%%%
tag := "hex-rcf-native-source-identities"
%%%

An algebraic coefficient in a tower is not necessarily inherited from its base.
A finite reader must identify its selected real conjugate together with the
sample. {name Hex.RCF.RealCoefficients.NativeSources.true_real}`NativeSources.true_real`
adds a coefficient-selection formula in the existing shared syntax to the source
matrix. Both are realized at one reader. A proof that the selection has a unique
real coefficient valuation once inherited identities are fixed identifies the
original source coefficients. The actual provider history retains those
inherited identities at the same reader.
No `Origin.RealValue` premise is required for those algebraic suffix coordinates.

The selection is a formula on the coefficient coordinates; lifting it leaves
the quantified variable unused. Its equations, isolating inequalities and the
source matrix share one native row. This example extracts an ordinary witness
from that row and a supplied uniqueness proof:

```lean
open Hex Hex.RealClosure Hex.RCF.RealCoefficients in
example {registry : BaseContext.Registry}
    (context : Tower.Context registry)
    (following : context.origin.base.Realization)
    (values : Fin n → context.Value)
    (source : Fin n → ℝ)
    (selection : RealFormula.QF n)
    (unique : ∀ coefficients : Fin n → ℝ,
      (∀ i, context.origin.RealValue following
        (values i) (source i) →
          coefficients i = source i) →
      selection.toProp coefficients →
        coefficients = source)
    (sample : context.Value)
    (matrix : RealFormula.QF (n + 1))
    (truth : Samples.Row.eval
      (.and selection.lift matrix)
      (NativeSpecialize.row context values sample
        (.and selection.lift matrix)) = some true) :
    ∃ x : ℝ,
      matrix.toProp (RealFormula.append source x) := by
  obtain ⟨read, domain, closed, negative, fixed,
    present, sizes, meaning, guards, base⟩ :=
    NativeSources.true_real context following
      values source selection unique sample matrix
      [] (by simp) truth
  exact ⟨read sample, meaning⟩
```

The [source-identity regressions](../../../conformance/HexRCF/NativeSourcesConformance.lean)
use the actual selected positive root α of `X²−2` and a further selected root
of `X²−α`. They identify α by `α² = 2` and `1 < α < 2`, then prove
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2` through this joint reader.
The coefficient's real identity is a conclusion of the selection proof, not
an assumed inherited-base identity. Changing α to its negative conjugate at
the same upper sample changes the complete native word from
`[0, 1, -1, 0, 1, -1]` to `[0, -1, -1, 1, 1, -1]`, and the joint formula is false.
These sign words have independent ordinary-kernel proofs and compiled controls.
A second test leaves an inherited coefficient unconstrained by the selection.
Its actual origin/provider identity fixes that coordinate as 2, while the
selection fixes the first coordinate as positive √2 at the same reader.
Its matrix `x·c₀−c₁=0` uses both coordinates, and the reader exports its truth.
The concrete fixture uses non-module imports, which expose private definitions
in this toolchain; the generic library laws use module imports without `import all`.

{name Hex.RCF.RealCoefficients.NativeSources.not_forall}`NativeSources.not_forall`
uses the selection conjoined with the negated matrix for a universal
counterexample. It retains supplied nonzero guards at the same
reader. The regression refutes `∀ x, x² > α` with α authenticated as positive
√2 and retains a supplied nonzero α guard. This fixture has no source division.
A zero difference `α−α` has sign zero
and cannot satisfy the nonzero-guard premise. These are direct API controls;
they do not add automatic guard collection to this point law.

Provider history, the selection's uniqueness proof, native row truth and every
supplied nonzero guard sign remain explicit inputs. `true_real` retains source
polynomial sizes, coefficient domains and
identities, and guards at the same reader. Finite approximation intervals alone do not uniquely identify a
registered π or e; those sources require their authenticated provider identities.
This API does not construct a selection from arbitrary source syntax, read a
complete frozen context certificate, establish cell coverage, or implement
algebraic-only decision completeness. The original `rcf` frontend still needs
that assembly to consume these point laws generally.

A checked rational root descriptor can supply its own selector. The owner's
constraints include its defining polynomial, strict finite endpoint bounds and
ordered derivative signs. {name Hex.RCF.RealCoefficients.NativeSelection.selection}`NativeSelection.selection`
translates those constraints into the existing integer schema using a positive
common denominator. {name Hex.RCF.RealCoefficients.NativeSelection.identity}`identity`
reuses the descriptor's count-one proof to identify the selected root at any
coefficient coordinate. No separate root-uniqueness argument is needed:

```lean
open Hex Hex.RealClosure Hex.RCF.RealCoefficients in
example {version : Nat} (root : Root version)
    (coefficients : Fin 1 → ℝ)
    (meaning : (NativeSelection.selection 0 root.raw).toProp
      coefficients) : coefficients = fun _ => root.real :=
  NativeSelection.unique root coefficients meaning
```

{name Hex.RCF.RealCoefficients.NativeSelection.translate}`translate` also accepts
a proved zero-reflecting rational projection. The
[generated-selector regressions](https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/NativeSelectionConformance.lean)
consume the actual wrapped rational predecessor's frozen √2 descriptor. Its
ordered constraints, rather than handwritten quadratic/interval atoms, identify
the source coefficient. The joint native row composes an existing source fact with the further-root
example through `NativeSources.true_real`, and the negative conjugate makes that
same native formula false. Invalid requested signs and unequal query/sign
lengths translate to false; no trailing constraint is silently dropped.
A second frozen rational descriptor retains both derivative signs and the
nonintegral bounds 7/5 and 3/2. Its checked selector has the exact ordered atoms
`x²−2=0`, `2*x>0`, `2>0`, `5*x−7>0`, `2*x−3<0`.
{name Hex.RCF.RealCoefficients.NativeSelection.translate_identity}`translate_identity`
reuses the same owner uniqueness law for wrapped rational projections.

{name Hex.RCF.RealCoefficients.NativeSelection.relation}`relation` ties a
coefficient coordinate to a rational polynomial of a selected generator.
{name Hex.RCF.RealCoefficients.NativeSelection.relation_correct}`relation_correct`
proves the exact value equation after positive denominator clearing. The tests
identify `α²−1` as 1 from positive √2, and translate `c₁=c₀²/3−1/5` into exactly
`15*c₁−5*c₀²+3=0`. This uses the existing polynomial representation and arithmetic.
It does not authenticate arbitrary nested context/provider-history records,
collect source divisions, establish cell coverage, or quote a general `rcf`
proof. Concrete fixtures retain their private-import boundary; a generic
conformance module composes the public selector and finite-reader laws with
ordinary public imports in the existing CI target. Kernel inventories and compiled controls remain
separate evidence.
