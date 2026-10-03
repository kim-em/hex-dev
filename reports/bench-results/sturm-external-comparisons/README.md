# Complete Sturm query comparisons

Classification: informational fixed endpoints and protocol controls. No
complexity mode, absolute regression budget, literal-certificate equivalence
or proof-checking performance is claimed. The four fixed queries on T_8 and
(-2,2) are one, X, X−1 and T_8, with exact results 8,0,−8,0.

[Metadata](metadata.json) records the clean source, pinned interpreter, host
library path, automatically leased CPU, load, complete commands and adjacent
alternating AB/BA order. [Analysis](analysis.json) joins all 64 comparison arms:
all 32 pairs match complete Option Int hashes and their expected-result guards.
Two four-repeat protocol controls are also retained. No completed sample is
discarded, trimmed for host load or replaced by a rerun.

Inputs and coefficient contexts are prepared once per child. Requests call
the root API, filter the open interval, evaluate the whole query and sum exact
signs. Root-production APIs, JSON transport, and temporary cleanup are timed.
The driver caches no roots; persistent backend contexts may retain internal
caches. The harness makes one untimed warmup before tuning/batching. These
are complete valid-domain query endpoints, not isolated root-isolation times
or general guarded-domain/proof surface comparisons.

| Query | Comparator | Native median µs | External median µs | Median paired external/native |
| --- | --- | ---: | ---: | ---: |
| Count | Flint | 103.683 | 205.975 | 1.981380 |
| Count | Z3 | 101.917 | 110.095 | 1.082383 |
| Mixed | Flint | 86.485 | 232.745 | 2.691172 |
| Mixed | Z3 | 86.462 | 147.870 | 1.719067 |
| Negative | Flint | 113.371 | 259.596 | 2.284023 |
| Negative | Z3 | 114.763 | 160.647 | 1.399890 |
| Common | Flint | 97.618 | 16421.518 | 168.350949 |
| Common | Z3 | 99.728 | 447.880 | 4.488035 |

Protocol medians are 6.734 µs for FLINT and 6.594 µs for Z3, with the same
count payload hash. Z3 Count's overhead is 5.989% of its external median,
above the policy's 5% adjustment threshold. Subtracting the Z3 protocol median
from each paired external observation gives a median adjusted ratio of
**1.017671**, alongside its raw **1.082383**. [Analysis](analysis.json) retains
both ratios for every pair. This framing adjustment does not isolate a pure
algorithm body. Ratios compare these precise boundaries on this source
and host, not a portable algorithm ranking. The common-factor query is zero
at every root: the shared Sturm reduction and external root/evaluation methods
perform different work while returning the same full query. The FLINT driver
uses generic real-qqbar Horner evaluation through `gr_mul` and `gr_add` at each
root. Its Common ratio describes that driver; optimized polynomial evaluation
with minimal-polynomial reduction is a different comparator implementation.

The exact endpoint unit tests cover positive, negative, mixed and zero sums,
repeated FLINT temporary-value cleanup, unsupported-version rejection,
malformed/unknown requests and Boolean control validation. A missing
interpreter fails the compiled verifier. The existing oracle job runs these
four tests; no new CI job is introduced.
