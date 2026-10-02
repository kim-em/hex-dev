# Allocation in coefficient-height normalization

The existing family uses `P=X³−1` and queries `[cX²,cX,c]`, where
`c=2^H−1`. The [height model](sign-det-height-model.md) defines the inputs,
actual normalization/checking operations and their fingerprints. This capture
measures those two phases, including their fingerprints, with untimed input
preparation. It does not measure full BKR production or general Sturm-chain
coefficient growth.

The [retained capture](data/sign-det-allocations/height-25b179f5c/metadata.json)
has 42 completed observations: three trial-major rounds over seven heights,
with normalization followed by checking at each height. It uses clean source
`25b179f5c8f2143cd77753cd8c802d364aefd958` on shared host `chungus2`,
automatically leased CPU 65. No completed sample is omitted and no rerun was
used. The sources and executable match the earlier joint and matrix captures;
their hashes are unchanged before and after measurement.

The [allocation method](sign-det-allocation-method.md) counts successful
requests at seven intercepted Lean, mimalloc and GMP entry points. Nested
wrapped calls are counted once. Units are cumulative requested bytes, with
rounded small-object requests; these are not live heap bytes or peak memory.
The retained generated C binds the actual callbacks and supported return ABIs.
All three controlled ABI fixtures pass. Every measured call returns the same
fingerprint with and without instrumentation, invokes its wrapper once, and
has matching per-entry-point counters and DHAT weighted events.

A separate post-capture `inspect-height-phases` execution validates every
input/reduction field and binds all 42 fingerprints to the height-tagged
ordinary results. Its command, log, executable hash and source-unchanged check
are retained in `height-inspection.json`; that inspection is explicitly later
than the capture, rather than capture-time provenance. The fingerprints are
finite checksums; the phase inspection supplies the literal formula checks.

All three rounds have identical allocation counters at each height/operation:

| Coefficient bits | Operation | Lean bytes | Mimalloc bytes | GMP bytes | Total bytes |
| ---: | --- | ---: | ---: | ---: | ---: |
| 8192 | Normalization | 2,616 | 240 | 97,320 | 100,176 |
| 8192 | Checking | 3,512 | 240 | 174,752 | 178,504 |
| 16384 | Normalization | 2,616 | 240 | 192,552 | 195,408 |
| 16384 | Checking | 3,512 | 240 | 345,760 | 349,512 |
| 32768 | Normalization | 2,616 | 240 | 383,016 | 385,872 |
| 32768 | Checking | 3,512 | 240 | 687,776 | 691,528 |
| 65536 | Normalization | 2,616 | 240 | 763,944 | 766,800 |
| 65536 | Checking | 3,512 | 240 | 1,371,808 | 1,375,560 |
| 131072 | Normalization | 2,616 | 240 | 1,650,984 | 1,653,840 |
| 131072 | Checking | 3,512 | 240 | 2,739,872 | 2,743,624 |
| 262144 | Normalization | 2,616 | 240 | 3,486,744 | 3,489,600 |
| 262144 | Checking | 3,512 | 240 | 5,476,000 | 5,479,752 |
| 524288 | Normalization | 2,616 | 240 | 6,960,552 | 6,963,408 |
| 524288 | Checking | 3,512 | 240 | 10,948,256 | 10,952,008 |

The Lean and mimalloc request totals are constant over this ladder. GMP
checking has 518 successful requests per call; normalization has 285 at
8,192–65,536 bits, 288 at 131,072 bits and 294 at 262,144–524,288 bits.
These observations include actual operand-dependent allocator behavior; they
do not establish a universal allocation bound or explain the changed call
counts. No timing or peak-memory conclusion is taken from instrumented runs.

These are additional allocation observations for the compiled Phase-4 track.
Nested coefficient dependencies, harder coefficient-height families, other
remaining scaling/comparison requirements and memory evidence still need
their own verification.
