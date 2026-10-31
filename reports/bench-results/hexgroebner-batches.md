# Sugar-batch cap comparisons

The frozen 16-input diagnostic suite was measured with the packed native
monomial engine at source fingerprint `2a390ee6b209`, before the common-workspace
reservation cleanup. These parameter comparisons use the same binary within
each experiment and identical field, order, output and resource contracts.
The exact source is retained in the [source archive](hexgroebner-native-monomials-sources-2a390ee6b209.tar.gz).

Each experiment uses one leased CPU, one computation thread, adjacent AB then
BA blocks per input, a 10-second deadline, 16 GiB address-space limit and 64 MiB
output limit. Every completed sample is retained. Whole-process time includes
startup, input and output; internal candidate times and all counters are also
recorded. Certification and kernel checking are excluded. Both experiments
complete all 64 samples; every coefficient and exponent of their 32 paired
full reduced bases agrees.

| Cap comparison | CPU | Eco10 B/A, p = 32003 | Eco10 B/A, p = 2147483647 |
| --- | ---: | ---: | ---: |
| 64 → 256 | 7 | 0.741 | 0.747 |
| 256 → 1024 | 6 | 0.911 | 0.923 |

At `p = 32003`, Eco10 rounds fall from 38 to 20 to 15, matrix input/output
entries from 8,867,016 to 4,588,163 to 3,380,974, and charged work from
295,082,444 to 212,486,341 to 193,985,379. Reimer-5 changes from 26 rounds to
24 at cap 256 and stays at 24 at cap 1024. Its first comparison improves by
about 3%; the second has effectively unchanged work and small timing increases.
The other 12 inputs have identical work, round and matrix-entry counts at all
three caps. Their observed timing changes, including increases, remain in the
records; they do not demonstrate algorithmic gains on those cases.

The default cap is 1024. Larger batches can increase instantaneous matrix size
on other inputs; matrix, memory and work limits remain enforced and callers
may select smaller batches. The diagnostic suite was used to choose this
parameter and is not a held-out or balanced acceptance result. This experiment
makes no performance leadership claim.

The [64/256 metadata](hexgroebner-batch256-2a390ee6b209.json) and
[raw archive](hexgroebner-batch256-2a390ee6b209.tar.gz), and the
[256/1024 metadata](hexgroebner-batch1024-2a390ee6b209.json) and
[raw archive](hexgroebner-batch1024-2a390ee6b209.tar.gz), contain every input,
output, comparison, exact driver, script, sample and host observation.
Archive SHA256 checksums are respectively
`ebdddabe90120908dc8a851c8ba3699bc7f941909a96f19ce3a1d7e0a028f833`
and `574a13684689d39a4143a26bd1988b63566f7a732ad5a64ee5f59d5f6d018f5f`.

## Per-input matrix and process peaks at the reviewed source

Source `0a10ed40d7a4` includes common workspace accounting, shared checked
append logic, geometry validation and explicit telemetry. The same 16 inputs
were measured with cap 256 (A) and cap 1024 (B), using adjacent AB/BA blocks on
leased CPU 39 under the same limits above. All 64 samples complete and all 32
paired full bases agree. Peak RSS is the maximum process observation over the
two blocks. Matrix rows and entries are maxima over individual calls; entries
count logical validated input plus output, including shared buffers, rather
than physical live heap. The largest selected batch is reported separately
from its configured cap.

| Input | Peak RSS KiB, A → B | Peak matrix rows, A → B | Peak entries/call, A → B | Largest batch, A → B | Wall B/A |
| --- | ---: | ---: | ---: | ---: | ---: |
| cyclic5-15 | 67,344 → 67,344 | 49 → 49 | 1,375 → 1,375 | 17 → 17 | 0.989 |
| cyclic5-31 | 67,344 → 67,340 | 49 → 49 | 1,375 → 1,375 | 17 → 17 | 0.988 |
| cyclic6-15 | 69,396 → 69,396 | 191 → 191 | 13,310 → 13,310 | 58 → 58 | 0.998 |
| cyclic6-31 | 69,392 → 69,392 | 191 → 191 | 13,310 → 13,310 | 58 → 58 | 0.993 |
| kat6-15 | 69,392 → 69,392 | 141 → 141 | 4,555 → 4,555 | 23 → 23 | 0.998 |
| kat6-31 | 69,396 → 69,392 | 141 → 141 | 4,555 → 4,555 | 23 → 23 | 1.004 |
| eco10-15 | 93,964 → 93,944 | 4,446 → 4,472 | 503,482 → 496,823 | 256 → 482 | 0.925 |
| eco10-31 | 93,940 → 93,832 | 4,446 → 4,472 | 503,494 → 496,835 | 256 → 482 | 0.921 |
| noon4-15 | 69,396 → 69,396 | 151 → 151 | 2,587 → 2,587 | 18 → 18 | 1.005 |
| noon4-31 | 69,396 → 69,396 | 151 → 151 | 2,587 → 2,587 | 18 → 18 | 1.003 |
| reimer5-15 | 73,488 → 73,488 | 679 → 679 | 81,064 → 81,064 | 92 → 92 | 0.996 |
| reimer5-31 | 73,492 → 73,492 | 679 → 679 | 81,064 → 81,064 | 92 → 92 | 0.995 |
| minrank_d_2_p_2_q_3_r_2-15 | 67,344 → 67,348 | 11 → 11 | 279 → 279 | 2 → 2 | 1.015 |
| minrank_d_2_p_2_q_3_r_2-31 | 67,340 → 67,340 | 11 → 11 | 279 → 279 | 2 → 2 | 1.006 |
| quadratic5-32003 | 67,348 → 67,344 | 89 → 89 | 4,557 → 4,557 | 20 → 20 | 1.003 |
| quadratic5-2147483647 | 69,396 → 69,392 | 89 → 89 | 4,557 → 4,557 | 20 → 20 | 0.993 |

The cap choice is driven primarily by Eco10 on this diagnostic suite. Its
maximum selected batch is 482, its peak row count rises slightly, and neither
observed process RSS nor peak entry count grows materially. Reimer-5 and the
other inputs do not benefit from the 256-to-1024 change in work counts. This is
an explicit implementation choice, not evidence about untested inputs or the
SPEC acceptance suite; matrix and memory allowances still bound larger cases.

[Reviewed-source metadata](hexgroebner-batch1024-0a10ed40d7a4.json),
[raw records](hexgroebner-batch1024-0a10ed40d7a4.tar.gz) and
[exact source](hexgroebner-batch1024-sources-0a10ed40d7a4.tar.gz) are retained.
