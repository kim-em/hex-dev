# MetiTarski degree ladder capture

This archive retains all command logs, functional and measured-input packets,
independent oracle outputs, raw timings, host metadata and seven measured
source snapshots. The two executables are omitted; their SHA-256 identities
remain in the original manifest and archive index. `analysis.json` and the
tables are recomputed from every retained raw point.

<!-- metitarski-results -->
## Retained results

Measured source: `14b03f863df9341f411a1f3df7461f41b82d4ab7`.

Completed samples: 24 of 24 attempts.

| Degree | Completed trials | Median ms | Range ms | Median ms / n³ | Head bytes | Descriptor bytes |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | 6 | 213.826 | 147.106–259.516 | 7.919 | 59 | 21688 |
| 5 | 6 | 469.475 | 314.137–533.768 | 3.756 | 65 | 60790 |
| 7 | 6 | 731.902 | 611.720–984.343 | 2.134 | 71 | 121854 |
| 9 | 6 | 1299.439 | 1051.705–1600.144 | 1.782 | 77 | 204318 |

Harness verdict: `inconclusive`; slope: `-1.404948`; leading points dropped: `0`.

The ranges and medians use every completed trial. The raw export retains each
batch duration, repeat count, signal-floor flag and failure status; the derived
analysis retains them by degree. The harness verdict is reported separately
from these descriptive observations. This finite ladder does not establish
asymptotic complexity or acceptance of the other Phase 4 families.
<!-- /metitarski-results -->
