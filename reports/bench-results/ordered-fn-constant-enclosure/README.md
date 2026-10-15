# Constant-polynomial enclosure investigation

This candidate is **not selected for expansion**. The complete bounded comparison
improves the three selected approximation cases by 2.5–3.2%; its predeclared
criterion requires more than 10% improvement at 12288. No full comparison,
unchanged rerun or phase promotion follows from this result.

The implementation preserves the kernel-facing `Real.enclose` reference and
proves a compiler replacement that returns exact zero for an empty polynomial,
the caller's coefficient enclosure for a singleton, and the existing fold for
larger polynomials. The public `enclose_C` lemma retains the canonical-zero
exception for arbitrary providers. The runtime path preserves coefficient
refinement and omits the unused argument request for constant polynomials.
Generated native C confirms that branch behavior. No mathematical or runtime
speed claim follows solely from the source inspection.

The frozen source is retained by `audit/issue-10575-constant-enclosure-source-v1`.
Its semantic/conformance build passes 3,275 jobs; the native build and guarded
ordinary-kernel axiom checks pass 3,341 jobs. Both new theorems have exactly the
three standard axioms. All 122 freshly emitted real fixtures are byte-identical
to the existing fixtures and pass the pinned exact FLINT/Z3/Fraction oracle.

The unmodified parent is `7244ae8f3c0c9f7eedc4112f2a2b79b45e2ff1fa`.
Both fresh builds bind 5,152 source/configuration inputs, 89 native import files
and the same sixteen exact clean package pins. Only `Real.lean` differs in the
native import paths; the broader snapshot also differs in the test axiom guards.
The compiler and benchmark source/configurations are unchanged. The parent
executable is byte-identical to the earlier unmodified-parent executable
`0b260f7a83bab62a936c7cbb9a1334f55524ebe94bf366d715fb1378614fdeb5`.
This is a same-compiler parent comparison, not the required full historical
Phase-6 baseline comparison.

| Approximation parameter | Parent median ns/call | Candidate median ns/call | Change |
| --- | ---: | ---: | ---: |
| 10240 | 2,825,551,378 | 2,754,691,205 | −2.507835% |
| 12288 | 4,372,825,678 | 4,233,445,494 | −3.187417% |
| 16384 | 8,625,052,572 | 8,408,391,672 | −2.511995% |

All eighteen arms complete, with three trial-major adjacent AB/BA/AB trials,
one automatically leased CPU and no sample rejection or quiet-core condition.
All result hashes agree per parameter; all source, tool, pin and executable
integrity checks pass. The child invocation commit describes the invocation
checkout; producer commits and binary hashes are bound separately.

The first source preflight failed to import the existing benchmark helper.
The original script, decision and failure log are retained. The import path was
corrected before any reservation or measurement; the unchanged source/binary
bindings, question, schedule and criterion were then bound to the corrected
script. The system Python also lacked Z3; rerunning the exact oracle in the
existing pinned oracle environment passes. Neither setup error supplied timing
evidence. The measurement attempt itself completes once, and its reservation
remains consumed.

The manifest binds compressed and original bytes for the complete measurement
capture and supporting records. No native executables or profiling binaries are
committed. The retained script computes independent-arm medians; its narrow
expansion criterion is not a native whole-library performance pass. The original
four OrderedFn Phase-6 findings remain unresolved.
