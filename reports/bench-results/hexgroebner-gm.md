# Gebauer–Möller pair installation

Source fingerprint `9f64edec57c7` compares product/resolved-chain criteria (A)
with minimal-LCM installation and proper-LCM chain pruning (B), in the same
executable. Inputs, prime 65,537, grevlex variable precedence, native arithmetic,
row updates, batching, allowances and full canonical output contracts match.
The scalar row route is a separate option. A one-billion-unit work allowance
is nonbinding for these calls.

Measurements use Lean `v4.35.0-rc3` on shared host `chungus2`, one computational
thread pinned to automatically leased CPU 32. Each case runs adjacent AB and
BA blocks, retaining three repetitions per arm with a 0.5-second inner floor.
All 48 scheduled samples complete successfully and every full structural basis
hash matches. Input generation is excluded. Canonicalization, F4 rounds, final
interreduction, interchange decoding and hashing are included. These calls
produce unchecked candidates; certificate generation, independent verification
and kernel checking are excluded.

The [metadata](hexgroebner-gm-9f64edec57c7.measurement.json) retains the exact
script, commands, affinity, load, toolchain, compiler and binary identity.
The [source manifest](hexgroebner-gm-9f64edec57c7.manifest) identifies the
implementation. The [raw archive](hexgroebner-gm-9f64edec57c7.tar.gz) retains
all sixteen exports and logs, including sample variability, memory and floor
flags. Its SHA256 is
`fffee8f5aa6575af4486525588af02e0ee731d232db55e1b1707fed268014146`.
The [analysis](hexgroebner-gm-9f64edec57c7.analysis.json) contains every paired
ratio and observed hash.

| Case | AB medians A → B | BA medians A → B | Paired geometric mean B/A |
| --- | ---: | ---: | ---: |
| cyclic-5 | 7.607 → 4.746 ms | 7.552 → 4.705 ms | 0.623 |
| cyclic-6 | 98.875 → 42.190 ms | 98.871 → 42.437 ms | 0.428 |
| Katsura-3 | 0.392 → 0.398 ms | 0.389 → 0.396 ms | 1.018 |
| Reimer-5 | 782.022 → 242.443 ms | 780.230 → 241.374 ms | 0.310 |

The three larger calls show approximately 38%, 57% and 69% less time.
Katsura-3 is about 2% slower. Extra installation/sorting work is a possible
explanation; its isolated time has not been measured. That regression remains
in the results.
These fixed cases make no asymptotic complexity claim and are not the SPEC's
balanced acceptance suite. They establish neither external performance
leadership nor a compiler/runtime impossibility.

Installation groups exactly equal LCM identifiers, preferring product pairs
and then the earliest old basis index. Increasing mathematical monomial order
places every proper divisor before its multiple. Minimal new LCMs filter
redundant pairs; product pairs remain available as filters even though their
obligations resolve immediately. At selection, a proper-LCM chain uses two
strictly smaller LCMs. Install-time dependencies require the lexicographic measure consisting of LCM,
maximum basis index and representative priority: an old pair can have the same
LCM and a smaller maximum index. Selection-time proper chains decrease the LCM
strictly. Such omissions remain separate from completed/resolved pairs and are
never inserted into the resolved-pair set. The basis is retained
without deletion or renumbering. Full F4 invariant and termination proofs remain
required; the independent checker must still validate every final S-pair.

All 567 conformance systems agree with the product/resolved-chain reference,
serial batching and scalar row arithmetic, and match both SymPy F5B and
Singular across seven primes and three orders. GM pruning is exercised on
303 cases. Charged work decreases on 256, increases on 206 and is unchanged
on 105. The largest increase is 7.45% (`p2/lex/generated-2`: 1514 vs 1409 units).
Matrix input/output entries decrease on 211 cases and increase on one. The
reference route here is the in-build route, whose endpoint-scan charges differ
from the earlier committed engine; the counts are operational units, not time.
Explicit queue-state tests cover equal-LCM protection, product-pair preference,
proper dependencies and the distinction from resolved pairs. Resource-boundary and resumability sweeps cover the lex S-pair example where
GM pruning occurs, as well as the original grevlex example. Strategy-switch
resumes in both directions preserve the result and advanced counters.
The larger Reimer-5 benchmark output also agrees independently with Singular;
the [verification archive](hexgroebner-gm-reimer5-verification.tar.gz) retains
the input, full basis, driver and verification script.

A [separate matched msolve sweep](hexgroebner-msolve-gm.md) on the unchanged
16-input diagnostic suite completes and verifies all inputs, while retaining
substantial external performance losses. It is not a leadership result.

The fixed benchmark names now select the default GM route with a one-billion-unit
work allowance. Earlier reports identify their own source fingerprints and
measured the pre-GM route with its stated allowance. Those historical observations
are not silently reinterpreted as measurements of this implementation.
