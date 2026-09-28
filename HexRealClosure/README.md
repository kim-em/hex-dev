# Rational selected-root expressions

`Root.validate` checks a `Hex.SignDet.RawDescriptor Rat Nat` against its exact
version tag. The tag is a `Nat` and does not yet own a defining polynomial or
dependency graph. An `Expression d` stores a rational polynomial evaluated at the
real root selected by `d`. Its arithmetic is polynomial arithmetic; distinct
expressions can have the same value. `Expression.sign?` uses checked joint sign
determination. `Expression.inverse?` computes a gcd/cofactor split and a scaled
Bézout candidate, then checks its product at the selected root. A successful
inverse has a proof of its real value in
`adapters/HexRealClosureMathlib/SelectedRoot.lean`.
The companion also proves that the selected root lies in the computed cofactor
for a nonzero value, that squarefreeness makes this cofactor coprime to the
operand, and that the scaled Bézout candidate has product one. Once both sign queries
return, `inverse?` cannot fail its candidate check. Total sign-query producer
success remains an upstream requirement.

```lean
let d ← Root.validate 7 raw
let a : Expression d := ⟨DensePoly.ofCoeffs #[0, 1]⟩
let sign ← a.sign?.toOption
let inverse ← a.inverse?.toOption
```

Both sign and inverse expose producer errors. `inverse?` returns `none` only
for a checked zero; a failed product check returns `InverseError.candidate`.
`Expression.transport` accepts checked `SignDet.Reencoding` evidence; its real
value is preserved. `Root.rebind?` revalidates the same root under a new context
version, and `Expression.rebind` transports a polynomial through that checked
conversion. `Expression.split?` combines cofactor re-encoding and rebinding;
`Expression.refine` transports stored values through both checks.
`Root.validate_context` rejects raw evidence from another context version.
The checked rebind preserves the selected value, but a version change alone
does not enforce context ownership or transport dependent objects. Full
context changes and nested transport remain separate. The `Expression` API
still exposes producer errors; `Element` below supplies a total rational-base
path.

Run `lake build HexRealClosure.Tests HexQuerySemantics` and
`python3 HexRealClosure/verify.py` from the repository root. The test uses
`(X²−2)(X−3)` with the root in `(1,2)`, plus a non-monic definition and a
checked factor split. The Python oracle computes exact arithmetic in ℚ(√2)
independently of Lean for 29 cases and is run manually; CI builds the Lean
`#guard` tests.
The companion proofs inherit the named #10389 admission in
`HexRealRootsMathlib.Tarski.check_rootSum`; no new admission is used here.

`adapters/HexRealClosureMathlib/Canonical.lean` uses the existing integer
root-list completeness theorem to show that every checked rational selected
root has a matching `RealAlgebraicNumber`, even when its defining polynomial
is reducible. `Expression.canonicalValue` evaluates the stored polynomial
using canonical real-algebraic arithmetic; its real value agrees with
`Expression.denote`; expression equality, addition, subtraction, negation,
multiplication, successful inversion, returned signs and checked refinement
agree. A checked zero inverse also has canonical value zero.

`Root.canonical?` clears denominators, enumerates the existing canonical real
roots and selects the entry matching the descriptor's interval and derivative
signs. `Root.toCanonical` returns that entry, and `Expression.toCanonical`
evaluates a stored polynomial using canonical arithmetic. The companion proves
the search always succeeds for a validated descriptor and that these
executable conversions equal the selected real value and the semantic
`canonicalValue`. The root-list search can be more expensive than local sign
queries; callers evaluating several expressions at one root can hoist
`Root.toCanonical`. The tests include a negative root with an unbounded lower
endpoint. This conversion does not replace the general tower representation.

`Element d` packs a rational polynomial with a canonical stored zero: a
polynomial that vanishes at the selected root is stored as `none`, and every
stored nonzero polynomial carries the result of that executable check. Ordinary
addition, negation, subtraction, multiplication, inversion and sign are total.
`Element.equal` packs the difference, so distinct stored polynomials can compare
equal; structural `==` only compares their stored forms. The companion proves
zero reflection, preservation of the arithmetic and sign, and value
preservation when an element is repacked through checked re-encoding, rebinding
or a factor split. The semantic `Value d` is the image subfield of the
canonical real algebraic numbers, and `Element.toValue` carries each total
operation to that lawful ordered field. For a literally monic, integral
defining polynomial, packing retains the remainder before
the selected-root zero check; the companion proves that this preserves the
selected value and integrality of clean inputs. Nonmonic definitions keep
their original representatives, as do monic definitions with fractional
coefficients. The retained remainder has degree below the defining polynomial.
Each uncached `Element.ofPoly` call searches the canonical root list, including
when the polynomial represents zero. On a stored nonzero element, uncached
`Element.value` and `Element.sign` also repeat the search. Use
`Root.Handle.Value` below for polynomial work that
reuses one selected-root search. The general tower's cost targets remain to be
implemented.

The companion's `polyValue` maps `DensePoly (Element d)` into polynomials over
the lawful `Value d` field. It reflects zero and preserves degree, coefficients,
arithmetic, derivative, evaluation, division and remainder, and supplies the
gcd association and extended-gcd Bézout identity. This uses the shared
noninjective polynomial interpretation rather than assuming raw coefficient
field laws. The runnable nested-coefficient example divides `Y²−2` by
`Y−α`; its remainder `α²−2` is semantically zero but not the zero rational
polynomial. It also checks extended gcd and differentiation.

`Element.transportPoly`, `rebindPoly` and `refinePoly` move every packed
coefficient through a checked root or context change. The companion proves
zero reflection, degree preservation and coefficientwise value preservation.
`polyDenote` maps `polyValue` into the shared canonical real-algebraic field.
All three transported polynomials have the same image there, even when their
stored coefficient representations differ. A runnable factor-split example
checks the three paths, including an interior zero coefficient and a square
coefficient that becomes constant after the split.

`Root.handle` searches for the checked descriptor's canonical selected root
once. `h.pack`, `h.add`, `h.mul`, `h.inv` and `h.value` reuse that root for
packed values. `h.equal` compares represented values by packing their
difference; structural `==` only compares stored representatives.
`Root.Handle.Value h` supplies ordinary arithmetic instances
for polynomial coefficients sharing the handle, so generic `DensePoly`
division also reuses it. Explicit target handles let polynomial transport
share one selected-root search across all transported coefficients. The
computational equalities to the original `Element` operations and the
companion's value theorems preserve their proved meaning. The handle is
indexed by its checked descriptor, so it cannot be used for a different
context version without a checked conversion. Bind it once as
`let h := d.handle` and pass `h` to cached values; writing `d.handle` afresh
at each call repeats the search.

`Yun.decompose` runs the specified finite recurrence over an executable
ordered field. `Yun.decomposeRaw` runs the same recurrence on packed tower
coefficients, where stored equality need not be value equality. The zero and
nonzero-constant cases, including acceptance by replay, have direct proofs.
For a positive-degree input whose monic gcd with its derivative is one,
the producer returns its leading coefficient and its monic associate with
multiplicity one, and this result is proved to pass replay. These squarefree
producer proofs use the same field instances as the executable API.
Runnable checks cover a
non-monic input, gaps in multiplicities, mixed zero and nonzero roots with a
fractional unit, a repeated irreducible quadratic, and coefficients in
`ℚ(√2)`.
The optional `Yun.check` recomputes the product and degree, checks positive
ordered multiplicities and nonconstant monic factors, and checks squarefree and
pairwise gcd conditions. Core lemmas extract those accepted conditions; the
Mathlib companion transports the product to mathematical polynomials and
proves that accepted rational factors are squarefree and pairwise coprime.
For every field embedding of ℚ, accepted factors cover exactly the roots of
the input, and each factor label is the multiplicity of its roots in the
input. This includes irrational real roots after mapping to ℝ.
`Yun.map_decomposeRaw` transports the raw recurrence through a zero-reflecting
coefficient map that preserves its arithmetic. The companion instantiates
this theorem for cached rational selected-root coefficients; their inverse
semantics retain the named `Tarski.check_rootSum` admission (#10389).
Arbitrary ordered coefficient towers still need their interpretation laws.
`Yun.Invariant.init`, `step` and `component` in the companion prove the
repeated-factor recurrence's pointwise root invariant over characteristic-zero
fields, including nonmonic inputs. Over an algebraically closed field, the
remaining-multiplicity weight decreases on every nonconstant round and starts
at the original degree. `Invariant.loop_weight` proves that any additional fuel
leaves the output unchanged; `initial_loop_bound` is its one-step corollary for
the initial state. The bound covers gaps with no emitted factor. These
proofs use ordinary kernel checking and have no admitted dependencies.
`decompose_bound` transports this result through an algebraic closure to every
characteristic-zero field. `ordered_bound` applies it to the public executable
field instances using a Mathlib field structure that preserves their arithmetic.
The public API requires `Std.LawfulOrderLT`; its natural casts are proved
injective, making the exclusion of positive characteristic explicit.
`decompose_root` proves that every input root appears in the actual producer
output with its original multiplicity, without a replay-acceptance premise.
`decompose_factor` proves monicity, positive degree and labels for every emitted
factor. `decompose_reconstruct` proves that their powered product reconstructs
the input, and `decompose_degree` proves exact degree accounting.
`decompose_factor_gcd` and `decompose_coprime` prove the executable squarefreeness
and distinct-label coprimality checks over every characteristic-zero field.
The raw recurrence
also has strictly increasing labels and retains the input's leading coefficient
without requiring field laws on stored syntax.
`decompose_sound` combines these results to prove that every public
ordered-field `decompose` result passes `check`, including repeated factors.
These producer proofs have no admitted dependencies and retain the field
operations used by the executable API.

For existing canonical number-field arithmetic and conversions, see the
[number-field chapter](../HexManual/Chapters/HexNumberField.lean) and
[real-algebraic chapter](../HexManual/Chapters/HexRealAlgebraic.lean).
