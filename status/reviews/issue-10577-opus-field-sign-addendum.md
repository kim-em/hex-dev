# Independent field-sign scaffolding review addendum

I've finished reading both FieldSign files, the RealSign owner files, both conformance modules and the CI wiring. Here is the review.

## Phase-2/3 review addendum: `signField` (HexRealAlgebraic / HexRealAlgebraicMathlib)

**Provenance.** My first git command worked; after that Bash was denied, so the rest of the review comes from reading files. `git diff --stat 9498f1e2d HEAD` was empty for all six files (the two FieldSign files, the two conformance modules and both RealSign files). The working tree doesn't modify them either, so they are unchanged from that base. One thing to fix in the record: the subject of `9498f1e2d` is "Bind serialized coefficient sign requests to checked original queries (#10632)", not #10641. I did not build anything. The verdicts below rely on CI's existing elaboration of these modules.

### Types, hypotheses, delegation

- `signField (generator : RealAlgebraicNumber) (value : QAdjoin generator.toAlgebraic) : Int := value.signApprox generator.property` (`HexRealAlgebraic/FieldSign.lean:12-14`).
  - It delegates directly to `QAdjoin.signApprox`, using the subtype's own reality proof (`RealAlgebraicNumber := {a // a.isReal = true}`, with `toAlgebraic := a.val`).
  - There is no second canonical conversion and no new algorithm. This matches the SPEC at `SPEC/Libraries/hex-real-algebraic.md:499-502`.
  - A nonreal generator cannot be expressed at this type, so rejecting it stays the owner's job. That is covered at `conformance/HexNumberField/Conformance.lean:653-654`.
- The Mathlib-free boundary holds: the file imports only `HexRealAlgebraic.Order` and `HexNumberField.RealSign`, and both are Mathlib-free.
- `signField_spec` is exactly `QAdjoin.signApprox_spec value generator.property`. Its right-hand side is the selected embedding `PolyQuot.toComplex value rep rep_mk`, the same one the owner uses, so this is the strongest available statement.
- `signField_eq` connects that to `RealAlgebraicNumber.sign` through `sign_eq` and `PolyQuot.toAlgebraicNumber_toComplex`. The proof is a trichotomy case split, which is sound.
- Panic exposure: the `panicWith 0` fallback in `signApprox` is proved unreachable (`signApprox?_isSome`). It could only hide a failure behind a passing `#guard` when the true sign is 0, and zero values always take the exact constant branch.

### Conformance

**Wrapper checks** (`conformance/HexRealAlgebraic/FieldSignConformance.lean`). Each check compares `signField` with the canonical `(ofAlgebraic? value.toAlgebraicNumber).sign`, which is exactly the right-hand side of `signField_eq`. The cases cover:
- Constants 0 and ±1.
- Both embeddings of √2, and ∛2.
- A zero produced by reduction: `x^3 - 2` in ℚ(∛2) reduces to 0.
- Negative values.
- A degree-4 common field ℚ(√2, √3), built from two different generators, with its degree asserted (`natDegree == 4`).
- Tiny positive values: `(x−1)^80` is about 2^-102 at √2, and `(√2−√3)^20` is about 2^-33. These go beyond the 16-bit and 32-bit probes.

**Branch witnesses.** These sit with the owner (`conformance/HexNumberField/Conformance.lean:617-651`):
- The endpoint branch, for both signs, with `initial?` and `refined?` asserted `none`.
- The refined branch.
- The constant branch.

Because `signField` is a definitional wrapper, those witnesses carry over to it. Taken together, the operation and edge coverage is enough for Phase 3.

**Axiom guards** (`conformance/HexRealAlgebraicMathlib/FieldSignConformance.lean`). Both theorems are pinned to `[propext, Classical.choice, Quot.sound]`, so there is no `sorryAx` and no `Lean.ofReduceBool`. These guards also cover `signApprox_spec`, `signApprox?_spec`, `signApprox?_isSome` and `endpoint?_isSome` transitively. The `#guard`s run through the evaluator; there is no `native_decide`.

**Wiring.** Both modules are in the `HexConformance` globs (`lakefile.lean:1120-1122`), which `ci.yml:405` builds.

### Findings (none blocking)

1. **Low, API: redundant hypothesis on `signField_eq`** (`HexRealAlgebraicMathlib/FieldSign.lean:24`).
   - The theorem asks the caller for `value.toAlgebraicNumber.isReal = true`. That fact always follows from `generator.property`.
   - The derivation already exists, but only as a local `have valueReal` inside `signApprox_eq` (`HexNumberFieldMathlib/RealSign.lean:134-137`). No public lemma provides it.
   - Callers therefore have to find the proof somewhere else. For example, `conformance/HexSignDetMathlib/FieldConformance.lean:54` takes it from `(Coefficients.ofField …).property`.
   - Fix: promote that `have` to a public `QAdjoin.toAlgebraicNumber_isReal (value) (real : generator.isReal = true)`, then either drop the hypothesis or add a variant without it. This is not a soundness issue.
2. **Low, docs: README verification command is incomplete** (`HexRealAlgebraic/README.md:60`). It lists `HexRealAlgebraic.Conformance HexRealAlgebraic.ReprChecks` but leaves out both `FieldSignConformance` modules. CI builds them anyway, but someone verifying locally from the README would skip them.
3. **Nit: broader import than needed** (`HexRealAlgebraic/FieldSign.lean:7`). The definition only needs `HexRealAlgebraic.Basic`, but it imports `HexRealAlgebraic.Order`. The Mathlib side gets `Order` through `HexRealAlgebraicMathlib.Order` anyway. This is harmless.
4. **Informational:** the wrapper checks are differential only. A bug shared with `RealAlgebraicNumber.sign` would not show up here. That is acceptable, because `sign` has its own literal checks in `HexRealAlgebraic.Conformance` and `signField_eq` proves the two agree.

### Verdict

With the checks CI already compiles, the scaffolding and test surface are enough for Phase 2 (the API typechecks against the SPEC, delegates as specified, and its correspondence theorems use only the three standard axioms) and for Phase 3 (operations and edge cases are covered, with branch witnesses in the owner module and the axiom guards in place). None of the findings blocks anything; 1 and 2 are worthwhile small follow-ups. This review makes no Phase-4 or timing claims.


## Response

The conformance declaration now names signField and its separate field-sign module; the matrix includes the computational and proved surfaces. Both scaffolding tokens include this independent addendum. The README verification command includes both field-sign conformance modules. The full corrected local conformance build passes and the ordinary-kernel theorem guards admit only the standard three logical axioms.

Base 9498f1e2d is the #10632 merge and already includes parent 990282187 (#10641), which introduced the field-sign modules; the evidence names the introducing owner commit separately. The redundant correspondence hypothesis and broad import are harmless API/organization follow-ups in inherited source. They are not changed under this readiness assignment, which preserves the public surface and does not polish parent-library proof APIs. Phase 4 remains incomplete.
