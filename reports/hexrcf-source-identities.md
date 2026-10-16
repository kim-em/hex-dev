# Checked identities for selected source coefficients

A polynomial equation does not identify a real conjugate. A source coefficient
also carries a selected embedding. The optional adapter's
[SourceIdentity](../adapters/HexRCF/RealCoefficients/SourceIdentity.lean) composes
existing native scalar-sign correspondence with the source polynomial and its
isolating square. It uses the existing `DensePoly`, native contexts, ordinary
real models and selected-root uniqueness theorem.

`observe` reads an actual `Algebraic.SignFact` at its original selected root.
Its polynomial must equal the requested stored polynomial, and its interpreted
coefficients must equal the rational source query. `margin` constructs the
rational polynomial

```text
2 w² − b² − a² + 2 a X − X²
```

for a square with real centre coordinate `a`, imaginary coordinate `b` and
half-width `w`. Its positive sign proves strict membership in the square's
circumscribed disc on the real axis. `select` combines that margin with the
source equation and the actual count-one square witness to identify the
source's selected real value. Both observations concern the same value.
`evaluate`, `equation` and `positive` provide the coefficient-map boundary for
queries evaluated at an ordinary-real model's stored coordinate; they reuse
the existing operation-only polynomial transport and model sign laws.

The two selection helpers exposed by
[CommonPresentation](../adapters/HexRCF/RealCoefficients/CommonPresentation.lean)
retain their existing proofs. No decoder, arithmetic implementation, formula
syntax or root-isolation algorithm is copied into this module.

The [source regression](../conformance/HexRCF/SourceIdentityCases.lean)
constructs actual native assembly from the retained selected-root context and
independently checks scalar packets for the source equation and disc margin.
It proves that the retained coefficient denotes `Real.sqrt 2`. The
[fresh consumer](../conformance/HexRCF/SourceIdentityKernel.lean) checks actual
theorem bodies, the exact three-axiom closure and required selection/scalar
bridges. It explicitly excludes the fixture's older `Data.alpha_value` and
`Data.selectedSqrt` theorems. Native production supplies data; ordinary-kernel
replay supplies the proof.

The [complete-cell source consumer](../conformance/HexRCF/CellReplay/Assembled.lean)
uses this coefficient identity when quoting the original real proposition.
Its independent audit also excludes both older alias theorems. Changed
polynomials, the negative embedding with an unchanged formula, a foreign
coefficient and omitted original divisors retain their existing refusal and
state-restoration controls. The scalar codec still contains legitimate checked
fixture facts; this work does not remove that finite-input restriction.

The [manual](../HexManual/Chapters/HexRCF/AlgebraicCells.lean) explains this
source-selection boundary alongside complete-cell quotation and real-model
construction. The optional umbrella and default Lake target include the new
module; the published base umbrella remains independent of the family.

This is a fixed-input source-authentication composition, not general frozen
proposal/history reconstruction or a new default tactic backend. General
provider/predecessor histories, all-live transport, strict compiled rejection
of arbitrary missing intermediate records, accepted algebraic completeness,
realization and the remaining stress/performance evidence are still required
by #10358. The separate unrelated-cubic public-decoder experiments do not
establish accepted source reconstruction. No general performance improvement
is claimed. Existing #10633/#10634 implementations and measured limitations
remain unchanged.
