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
