# Adjacent early-rejection comparisons

The owned real-algebraic conversion now tests the lazy root's stored refined
isolation before canonicalization. Its companion proves `ofRoot?_eq`: exact
equality with canonical exactification followed by the reality check, for
every lazy root. Nonreal roots can be rejected without changing any retained
canonical value, multiplicity, sorting or zero-polynomial convention.

[capture.py](capture.py) runs four adjacent alternating AB/BA blocks on
`RealAlgebraicPoly.roots` for `X^8−2` and `X^4−√2`. Each arm uses the same
prepared input and complete ordered minimal-polynomial/sign/multiplicity
fingerprint, with separate untimed child warmup. Solving, exactification,
filtering, sorting and fingerprint construction remain timed. CPU 79 was
automatically leased on the shared host; host load is context, not a sample
rejection rule. Every arm is retained; there was no unchanged rerun.

[metadata.json](metadata.json) freezes the before source `c6b821d7b`, the after
source `edb3ef956`, both executable hashes, commands and computational snapshots.
LeanBench's runtime Git environment describes the current working directory,
even when running the older executable. The separately recorded source commit
and executable hash identify each arm; the runtime Git field does not identify
the historical executable's source. Both binary checks and all changed-source
fingerprints remain unchanged throughout collection.

[analyze.py](analyze.py) joins all eight pairs. All 16 arms succeed, match their
expected complete fingerprints and agree within each pair. No failed or
censored arm is omitted.

| Fixture | Before median ms | After median ms | Median adjacent before/after ratio | Observed paired ratio range |
| --- | ---: | ---: | ---: | ---: |
| Rational degree 8 | 1063.963 | 307.115 | 3.412 | 2.987–3.906 |
| Quadratic degree 4 | 661.911 | 294.403 | 2.248 | 1.563–2.994 |

These are host-specific observations, without confidence intervals or a
scientific budget. Canonical real-root enumeration remains far slower than
the external root backends; rejecting the nonreal roots resolves avoidable
work, but does not resolve repeated canonical isolation of retained roots.
The exact executables and raw records are also retained persistently under
`/home/kim/.local/state/hex/issue-10577-measurements/`.

[source-equivalence.json](source-equivalence.json) identifies every fingerprinted
source against `89bed09cf`, including the definitionally equal predicate alias
and the unregistered manual-probe additions. The original measured commits
remain reachable through the pushed `issue-10577-root-measurement-source`
branch. Timings remain attributed to their recorded sources. The current
collector gained its clean-checkout preflight after these measurements; the
original collector is retained in [collection-driver.py.txt](collection-driver.py.txt). Profile manifests that say
`dirty: true` accompany unchanged computational snapshots and exact binaries.
