# Matrix primitive admission and ownership checks

Build and snapshot identifiers below may be capsule-only identifiers after a
squash merge. The public head `1d902daa8e` differs from the measured validation
source `ec3800f694` only in reports and capsules; their implementation sources
are identical. Later test refinements have their own validation record.

Source fingerprint `1e1015abfc77`, commit `ec3800f694598dd3cdf69180328fda43b955cf11`,
snapshot `8672bd465e0262b22a29f22c975c22d9cfe8aaa2`. Fresh compute SHA256
`9844bd85e3d231c6440de965fc611e62abe681f2b404372a6bd1dad67cdfbf82` and reference
`6a2ffc60d63a010cb65ff5b5bf15ba838ede1b06f259c1cd2d32401083e75a57`. These are different executables
from the earlier timing campaigns; no timing is transferred to this source.

Validation admits at most 65,537 row entries independently of ambient matrix
width, up to 2^32−1 columns. The same 524,296-byte inspection bound remains.
Zero-buffer allocation shares the matrix provider's existing allocation helper,
with its documented one-MiB cap and original portable fallback. The column-map
append-zero provider retains its separate 4096-byte slice contract.

All nine project checks and eight Clang 23.1.3/GCC 16.2 ASan/UBSan variants
pass. Tests assert exclusive ownership of admitted result/pair/outcome/statistics
records and fresh zero buffers, as well as unchanged borrowed records/buffers.
The public portable F4 call must perform matrix work while validation, zero,
scan, gather, bulk and byte-provider counters remain unchanged. Seeds use the
printed HEX_GROEBNER_TEST_SEED value. The complete compiled case sweep reports
the first failing field, input, limits and counters; elaboration uses a smaller
sweep. The initial missing-PyYAML environment failure is retained with its
successful retry. No library change was needed to repair that environment.

The following untimed diagnostic runs each unique timing-suite input once
through normal and link-wrapped drivers. All 30 complete unchecked-candidate
outputs, metadata and resource counters agree after removing candidateNanos.
They remain unchecked candidates; this is not independent final certification.

| Suite | Cases | Validation admitted/declined | Zero admitted/declined | Bulk admitted/declined |
| --- | ---: | ---: | ---: | ---: |
| small | 16 | 42372/0 | 56/0 | 182/28 |
| medium | 14 | 174106/0 | 208/0 | 114/104 |

Every standalone primitive call in these suites is admitted. Many other
matrices finish inside the bulk provider; admission counts alone do not measure
phase time or identify the remaining bottleneck. Per-case counts, exact inputs,
full outputs, instrumentation source and build metadata remain in the capsule.
The first diagnostic command/schema mistakes are retained separately. Timing
fields in those raw outputs are not scientific performance samples.

[Raw capsule](raw/matrix-primitives-review-1e1015abfc77.tar.gz), SHA256
`1f3fdd19e40bf9bb9447554331f18a0b85c5517fde3b2d43913d9744134a0091`; 150 source blobs and 355 payload digests verified.
The source overlays are self-contained; local build/snapshot identifiers need
not resolve as public GitHub commits after rebasing. The fastest-open-source
milestone remains open.


The final coverage source is commit `c5ae6c427c4839d3bca0f40d4f7f2b591ca5a137`, family fingerprint
`4dce30af383e`. All nine project checks and eight sanitizer variants
pass. Test seeds are parsed strictly and printed; six adjacent seeds cover
both 3/4-column shapes, all six nonzero F7 coefficients and six Mersenne
constants. Malformed seed input is rejected explicitly. The public portable
F4 check additionally watches column translation, index remapping, zero append,
continuation and product counters. The elaboration sweep includes both column
and counter declines, using named row cases.

Each variant records 1,771,570 validation and 29,962 zero-buffer calls before
its F4 diagnostics. The six traced integration cases admit 84 calls of each.
These counts belong to this validation source; the older counts above retain
their original source scope. No implementation or timing claim is transferred.

[Final coverage capsule](raw/matrix-primitives-seed-coverage.tar.gz), SHA256
`218392b095efb3ab4106b299b43542513e1912555d91d15afbd2e1ff0e0c2467`; 150 source blobs and 189 payload digests verified.
Local commit identifiers can become capsule-only identifiers after squash
merging. Original environment failures and their successful retries remain.
