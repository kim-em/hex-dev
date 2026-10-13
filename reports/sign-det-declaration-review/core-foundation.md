# Sign-determination computational foundation

This assessment covers the 35 named handwritten declarations in `Matrix`,
`Support`, `Reference` and `SignOperands`, plus the `System` equality instance.
Names are relative to `Hex.SignDet`. It is a partial core review: the remaining
computational modules, compiled-use assessment, lints and performance acceptance
are separate requirements. Neither library advances beyond Phase 5 here.
The [source bindings](core-foundation-manifest.json) identify the reviewed
modules and updated clients by their content hashes.

## Matrix

| Declaration | Assessment |
| --- | --- |
| `power` | The cases zero, one and two avoid generic exponentiation; larger exponents retain ordinary integer powers. The operation is total, including zero to the zeroth power. |
| `power_eq` | Characterizes every natural exponent, not only the BKR fast cases. Its simp annotation removes the helper in mathematical identities. |
| `entry` | Multiplies paired exponent/sign coordinates and returns one on an empty word. `zip` truncates unmatched words; checked shape hypotheses are therefore essential in semantic consumers. |
| `entry_append` | Matching left word lengths prevent truncation across the split and give the tensor product identity. Right word lengths need no extra premise for this finite algebraic identity. |
| `momentMatrix` | Uses the supplied row and column vectors in their literal order. Dimensions are enforced by the type, while valid words are enforced by the checker. |
| `System` | Keeps counts and moments as integers, with an explicit scaled left inverse and denominator. It makes no intrinsic claim of root coverage or invertibility. Each field is needed by checking or count recovery. |
| `System` equality instance | Compares all six literal fields, including inverse and denominator. The decision uses constructor equality; it does not identify semantically equivalent certificates. |
| `System.check` | Checks arities, exponents zero through two, sign codes, distinct columns, nonnegative counts, nonzero denominator and both matrix identities. It accepts dimension zero with a nonzero denominator and imposes no unjustified positivity condition on that denominator. |
| `System.check_eq` | Characterizes every executed guard with list membership propositions. It applies to arbitrary supplied systems and both directions of acceptance, including dimension zero. It intentionally lacks a simp annotation that would expand every accepted system into large quantified formulas. |
| `System.rows_valid` | Exposes accepted exponent-row widths and bounds in the Boolean-list form used by native producer clients. It follows the acceptance equivalence without re-unfolding the checker. |
| `System.columns_valid` | Exposes accepted column widths and ternary coordinates, retaining literal sign words and empty dimensions. |
| `System.columns_nodup` | Supplies distinct candidate columns directly to table and count-recovery clients. It does not establish coverage of observations. |
| `System.counts_nonneg` | Supplies the actual nonnegative-count guard to integer and rational solve clients. Positivity after pruning remains separate. |
| `System.identities` | Supplies the smaller matrix-identity API needed by inversion and uniqueness. It uses `check_eq` without reopening the Boolean implementation. |
| `scale_identity_vec` | Gives the ordered vector effect of a scaled identity for every integer scalar, including zero. Componentwise proof matches the executed matrix/vector operation. |
| `System.unique` | A nonzero integer denominator permits cancellation after applying the supplied left inverse. Uniqueness does not imply that the candidate columns cover actual observations. |

## Support

| Declaration | Assessment |
| --- | --- |
| `product` | Enumerates concatenations in left-major order. Empty inputs and duplicate words retain their literal list behavior; distinctness requires additional width and child-support facts elsewhere. |
| `length_product` | Characterizes the exact product length, including empty supports, without assuming distinctness. |
| `mem_product` | Requires membership in both children and preserves concatenation order. It makes no converse claim that would be false without fixed child widths. |
| `System.positive` | Selects precisely the strictly positive count indices in finite-index order, preserving the pruning order used by native computation. |
| `System.support` | Maps those indices to the supplied columns; support is computed rather than trusted as a separately supplied certificate field. |
| `System.mem_support` | Uses accepted-system uniqueness and a positive coordinate of another solution. The caller must establish actual-count equations on a complete candidate support separately. |
| `System.retainedMatrix` | Selects the computed positive columns and preserves every original row. The companion's basis proofs use this representation, including zero retained width. |

## Reference

| Declaration | Assessment |
| --- | --- |
| `words` | Enumerates ordered words with the first coordinate varying slowest. The zero-length case is the singleton empty word; a repeated alphabet is not deduplicated. |
| `referencePrepared` | Constructs the full ternary reference system with exactly ordered exponent/sign words. It remains an exponential small-case comparator, with the same `Except BuildError` contract and supplied prepared domain as the ordinary builder. Production recursion does not fall back to this operation. |

## Finite sign dependencies

| Declaration | Assessment |
| --- | --- |
| `ReductionStep.signOperands` | Includes both supplied scales, regardless of eventual acceptance or use. |
| `reductionOperands` | Preserves all occurrences and includes extra malformed steps, so a rejected certificate cannot omit dependencies from the congruence hypothesis. |
| `ReductionStep.check_sign_congr` | Agreement on both scales preserves the actual step checker; polynomial identities and literal bindings remain checked. |
| `Reduction.checkFrom_sign_congr` | Induction covers missing and extra factors/steps as well as accepted chains. It transports checker results, not just successful producer outputs. |
| `QueryReduction.checkFrom_sign_congr` | Preserves query order and index progression; the empty and mismatched cases remain part of the theorem. |
| `momentSignOperands` | Includes optional reduction scales and the actual shared Tarski certificate's operands. Integer moments and query bindings are separate checks. |
| `checkMoment_sign_congr` | Composes reduction and Tarski congruence without removing arithmetic or context checks, whether the optional reduction is present or absent. |
| `Node.signOperands` | Includes preparation and every indexed moment/reduction. A native domain cache does not shrink the hypotheses of full replay. |
| `Node.check_sign_congr` | Preserves the actual node result for arbitrary matrices and witnesses. Rank, support and literal guards are unaffected by changing the sign provider. |
| `Replay.signOperands` | Traverses the literal tree, preserving repeated subtrees and values as occurrences. Evidence sharing across coefficient-field levels belongs to another API. |
| `Replay.check_sign_congr` | Structural induction preserves both child restrictions, their support-completeness checks and all rejection paths. It neither constructs coefficient evidence nor proves a joint field realization. |

## API changes and validation

The new `System.check_eq` is available through ordinary `import HexSignDet`.
`System.identities` uses the characterization; `System.counts_eq` and the
companion's `System.foundation_counts` use its named distinctness projection
with their existing statements and coverage hypotheses. Table, codec, rank-basis, recursive
producer and integer/rational solve clients also consume the characterization
or its named guard projections. They retain every original hypothesis. The computational definitions and
checker guards do not change.
The manual names this distinction between integer-system acceptance and root
support completeness; existing owner examples remain the mathematical examples.

Local builds pass the matrix target and core/companion proof clients.
The computational conformance target applies the public characterization to an
accepted empty system and guards the new lemma's transitive axioms as exactly
`propext`, `Classical.choice` and `Quot.sound`. Full monorepo and manual builds
cover the integrated tree. These proof checks do not establish computational
performance or finish the whole-core Phase-6 assessment.
