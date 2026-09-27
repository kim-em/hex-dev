# General determinant proof evaluator evidence

The archived measured Bird evaluator and the pinned Mathlib `norm_det`/`ring`
comparator were built as fresh Lean modules on one automatically leased CPU per
serial batch. Each arm had an adjacent import-only baseline. The no-answer
result comparator built a sigma value by simplifying the determinant with
`norm_det`, then let `rfl` assign the resulting value; the Hex arm used `det%`.
Both arms' declaration checks and output cleanup were inside the timed build.
The raw samples, build output, host observations, source hashes and import
baselines are in the linked JSON files below.
An archive retains the exact measured probe sources. The active probe files
subsequently received required copyright headers, and their import-only
baselines had trailing blank lines removed. Their executable Lean content is
otherwise identical.

The integrated evaluator now retains symbolic quotients as compact atoms and
expands only indexed relation collisions. That policy has kernel and direct
cache tests, but **no timed samples from this 30-minute allowance**. The table
therefore describes the archived measured snapshot, not current-source speed.
Current-source gains, ties, losses and declines are all unmeasured.

| Archived snapshot case | Mathlib net median (ms) | Hex net median (ms) | Observed direction |
| --- | ---: | ---: | --- |
| Numeric 2×2 equality | 15.3 | 11.5 | tie |
| Symbolic 2×2 equality | 81.2 | −12.2 | Hex gain |
| Numeric 2×2 result | 4.1 | 54.3 | Hex loss |
| Symbolic 2×2 result | 44.1 | 39.7 | tie |
| Quotient 2×2 equality | 129.4 | −8.2 | Hex gain |
| Quadratic 4×4 equality | −18.7 | 32.3 | Hex loss |
| Quadratic 4×4 result | 114.6 | 34.9 | Hex gain |

These are the six paired medians of each proof build minus its immediately
adjacent import-only build, rounded to 0.1 ms. A negative net median means
import/build variation exceeded the small proof increment; it is not negative
proof time. Differences below 5 ms are shown as ties. The other directions are
descriptive, not claims of statistical superiority. In particular, the
symbolic equality and result forms remain explicit or opt-in.

The broader final-source batch retained two complete pairs per arm for the
4×4 two-term and degree-eight quotient cases, product denominators 5×5,
identity-plus-rank-one 5×5, dense generic-ring 4×4, dependent-row independent
quotients 6×6, rank-one 10×10, and the nonzero 3×3 and identity-plus-rank-one
4×4 result cases. All checked successfully. Its six-pair qualification is
**incomplete**, so those observations are unmeasured for a final performance
classification. A composite-characteristic equality was omitted from timing:
the prescribed unmodified Mathlib comparator could not prove the value modulo
4; the Hex proof is in the kernel test corpus. There were no Hex capability or
budget declines in the completed probes. No profile was collected within this
measurement allowance.

The initial seven-case batch completed six pairs with a different numeric
routing path and is retained as diagnostic evidence, not used in the table. The
broad snapshot batch used 768.1 seconds and the focused six-pair batch used 480.2
seconds. Together with 473.2 seconds from the initial batch and about 49
seconds of diagnostic builds, the aggregate was about 1,770 seconds, below
the 1,800-second cap. Every build was limited to 60 seconds; no timed process
hit that limit. The focused batch ran on CPU 3 and the broad batch on CPU 48.

The prototype at revision `dccd276f7` established relation cancellation and
reported two-pair wins and losses on different generated fixtures. Its final
cache and diagnostic fixes had correctness validation but no new timings.
Those prototype numbers are **not** a direct speed baseline for the integrated
source. The current source has no valid final-source speed comparison with
Mathlib or the prototype under the exhausted allowance. The snapshot results
show three apparent gains, two ties and two losses on small cases, no Hex
declines, and incomplete larger-case coverage. They do not justify a matrix
family dispatcher or a default simp registration.

- [Focused six-pair raw results](bench-results/det-general-focused-issue-10432.json)
- [Broad partial raw results](bench-results/det-general-final-issue-10432.json)
- [Initial diagnostic batch](bench-results/det-general-issue-10432.json)
- [Measured probe source archive](bench-results/det-general-sources-issue-10432.tar.gz)
