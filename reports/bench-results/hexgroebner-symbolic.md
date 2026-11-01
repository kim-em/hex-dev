# Packed reducer lookup and sparse-first F4 targets

The implementation combines bounded packed reducer lookup with stable
sparse-first ordering of joint Macaulay target rows. Sugar scheduling and known
reducer pivots retain their contracts. Independent normal forms keep input
positions, and traced production pairs each polynomial with its derivation root.
Singletons require no sorting work. Matrix sorting and index preparation charge
parent allowances before executing their work.

Reducer preference stays in Lean: a stable ordering of global LIFO leaves
assigns explicit positive priorities by sparsity, then higher leading degree.
Native lookup finds the least supplied priority among dividing leaves. The C
binding does not implement the F4 preference policy. Sealed index construction
prevents replacing its tree or packed snapshot. Lookup requires the associated
immutable basis and arena; append and widening preserve existing identifiers.
Read-only calls admit at most 2048 nodes, 2047 edges, arity 4096 and 4095 charged
visits. Larger/incompatible indices and insufficient preparation allowances use
the original traversal. The portable packed model and original traversal check
exact results, ties and exhausted prefixes.

Measured source `a5989cb5e42e`, computational commit
`764d471c2c`, identifies the revised implementation and runner. A fresh detached
188-job build freezes both drivers and checks actual initializer linkage. The
new executable SHA256 is
`c32894d658346428dfb9adc7bfbcb31ded0d1767389ebd8cce3409d2253b3429`.
Baseline `17aa8e10ff23` has executable SHA256
`604abe19262994f76561ccc9e1479a9028ef072d8e18c8844724ec033141c17f`.
Before/after mode validates each executable against its own manifest and requires
complete reduced bases and all computation metadata to agree. Algorithm counters
may differ. A changed baseline hash is rejected before any measured process.
Exact Git blobs, source/toolchain identities, helpers and raw outputs are retained.

Each campaign uses 16 development inputs in seven families at primes 32003 and
2147483647, one algorithm thread and an automatically leased CPU of the shared
AMD EPYC 9455 host. Arms are adjacent AB then BA. First and single permitted
unchanged repeat are retained: before/after CPU37/38, exact msolve CPU39/30,
probabilistic msolve CPU38/37. Campaign types run concurrently on distinct leased
CPUs; this is placement, not isolation. All six campaigns solve 32/32 complete
basis pairs, with 64/64 successful processes and zero failures or timeouts each.
Every completed sample and outlier remains. No further unchanged repeat is used.

Candidate time includes canonicalization, F4 and final interreduction. Process
time adds launch, initialization, parse, full output and identical GNU-time
wrappers; child RSS is measured after exec. Certificate generation, independent
final certification and kernel checking are excluded. This development corpus
is not the SPEC's balanced/held-out performance acceptance suite. Wider fields,
extensions, parallel scaling, other comparators, trace/probabilistic support and
deterministic producer proofs remain required. No leadership or compiler-change
impossibility claim is made.

| Pooled before/after, 64 pairs | Candidate B/A | Process B/A |
| --- | ---: | ---: |
| Geometric mean | 0.9074 | 0.8922 |
| Median | 0.9347 | 0.9457 |
| Range | 0.5052–5.3336 | 0.5375–2.2607 |

Equal-family process ratio is 0.8825. The 5.3336 candidate outlier is retained;
Noon and MinRank candidate family means regress. Ratios do not imply a uniform
gain. At the large prime, Reimer entries fall 960252→435489 and rounds 26→19;
Eco entries fall 3268590→2939286. Complete bases remain equal.

| Family | Candidate B/A | Process B/A | Hex/msolve exact | Hex/msolve probabilistic |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 0.9669 | 0.9630 | 1.9232 | 1.8690 |
| kat | 0.9175 | 0.9623 | 1.3417 | 1.2618 |
| eco | 0.7597 | 0.7766 | 4.4319 | 5.6609 |
| noon | 1.3312 | 1.0250 | 1.3905 | 1.1320 |
| reimer | 0.5165 | 0.5682 | 5.3780 | 5.0015 |
| minrank | 1.0542 | 1.0010 | 0.9945 | 1.1834 |
| dense-quadratic | 0.9734 | 0.9938 | 1.4137 | 1.3014 |

The fixed benchmark sweep on CPU42 retains all 120 registered points, five
declared repetitions per case and adjacent AB/BA. Ratios normalize actual inner
repeats; complete structural result hashes agree. No fixed-case repeat is used.
Its baseline is packed comparison `802ae51122d7`, whose exact source blobs and
frozen executable hash are also retained in the fixed capsule.

| Fixed case | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 1.0473 | 1.0474 | 1.0344–1.0690 |
| cyclic5 | 1.0031 | 1.0037 | 0.9933–1.0113 |
| cyclic6 | 0.9513 | 0.9519 | 0.9450–0.9561 |
| katsura3 | 1.0062 | 1.0019 | 0.9817–1.0351 |
| reimer5 | 0.5159 | 0.5161 | 0.5129–0.5176 |
| cyclic6Small | 0.9465 | 0.9463 | 0.9423–0.9531 |

msolve source is `3672113ee2c696a2ac9c637636e0f7214f500ba1`, Clang 23.1.3
with effective `-O3 -march=native` recorded in its engine ELF. GMP/MPFR/FLINT
are 6.3.0/4.2.2/3.6.0. Configure cannot find `omp.h`; both arms request one
algorithm thread. The direct `.libs/msolve` ELF uses its recorded neogb path.
Modes 2/42 request full reduced grevlex output. Its `-v 2` diagnostics and
uncontrolled mode-42 seeds remain in stderr and process time. Engine hashes and
build inputs are checked before/after. Full inputs and outputs are compared.

| Pooled comparator observation | Exact Hex/msolve | Probabilistic Hex/msolve |
| --- | ---: | ---: |
| Equal-family mean | 1.9822 | 1.9731 |
| All-pair mean | 1.9747 | 1.9597 |
| Median | 1.5773 | 1.4840 |
| Range | 0.4300–11.4093 | 0.4224–8.6674 |

Peak before-after RSS is 42516/42072 KiB (A/B).
Peak msolve-l2 RSS is 42176/13408 KiB (A/B).
Peak msolve-l42 RSS is 42148/13408 KiB (A/B).

Earlier `a00d1a3e57a9` observations are separate snapshots, not pooled with the
revised source: candidate/process B/A 0.8455/0.9205, exact/probabilistic
family-balanced comparator means 2.8494/2.7766. The standalone baseline's
2.1939/2.3790 comparator campaigns also remain separate. Cross-campaign ratio
changes are not an adjacent code-effect comparison. Small-case process cost
outside the candidate interval varies substantially; exact durations and all
contexts remain in the capsules.

For the earlier `a00d1a3e57a9` small-case regressions, medians below use eight
samples per arm/family across its two campaigns. Outside time is wall minus
candidate time and includes launch, initialization, parse, output and wrapper;
it does not isolate a particular runtime component or justify filtering.

| Family/arm | Process ms | Candidate ms | Outside ms |
| --- | ---: | ---: | ---: |
| kat, baseline | 15.2213 | 5.4432 | 9.4699 |
| kat, combined | 18.3670 | 5.2587 | 13.4453 |
| dense-quadratic, baseline | 11.3196 | 3.4888 | 7.8218 |
| dense-quadratic, combined | 11.2900 | 3.3889 | 7.8726 |

The earlier Eco31 explanatory profile has eight agreeing complete outputs and
counters, 8493 samples at 1999 Hz and zero lost samples. Flat shares include
Mersenne row scanning 17.42%, monomial combination/loop 6.09%, geometry 3.02%,
matrix validation 2.37%, row translation 1.87% and native lookup 1.72%.
Release/allocation/free total 10.71%. These sampled whole-process shares include
profiler overhead and belong to that earlier code. Unresolved kernel symbols
and unreliable unwind chains are retained; only flat symbols are interpreted.
They motivate investigating representation and matrix overhead alongside
arithmetic, and establish no compiler limitation.

The revised implementation passes all 1956 conformance/theory targets, both
567-case CLI output/counter corpora, 175 independent matrix cases, 567 complete
SymPy/Singular bases, 1288 division cases, four Clang and four GCC ASan/UBSan
variants, 32 benchmark checks and dependency/phase/release/header/size checks.
Cases independently check sparsity, degree, LIFO ties and all small exhausted
prefixes, requiring genuine native answers for valid arenas. Oversized and
malformed records are rejected; removing the 2048-node guard is detected by
sanitizers. Index construction/update attempts fail from importing code. Native
counts are 2345 lookups, two intentional declines and 484 F4 calls without
decline. A genuine 78-pair batch and positional independent normal forms have
separate regressions. Only three work counters change in 483/567 fixtures from
the preceding combined implementation.

The linked sparse-target component capsule retains its independent 128-process,
240-point observations and Reimer fixed ratio 0.5361. Rejected source
`29215102b484` reorders independent normal forms and has a complete-basis
mismatch. Its two completed outputs and exact source are retained separately
inside that capsule and never pooled with corrected measurements. Earlier
packed-trie component evidence remains in [its report](hexgroebner-trie.md).

- [ranked-before-after-a5989cb5e42e.tar.gz](raw/ranked-before-after-a5989cb5e42e.tar.gz): `e9eb5d951db153d242eb9cced002e99c0fa1360d4b431ce65f41623b730ecd08`.
- [ranked-before-after-repeat-a5989cb5e42e.tar.gz](raw/ranked-before-after-repeat-a5989cb5e42e.tar.gz): `0321bd2f21accccf45ec4aabc66be634abca27f0c778283c8d8ca5538f6cd7c9`.
- [ranked-msolve-l2-a5989cb5e42e.tar.gz](raw/ranked-msolve-l2-a5989cb5e42e.tar.gz): `47e90ae90745b32ccf3c9c6cc7e1e6ae9fc3221f71287d31f3a5cfea735f5386`.
- [ranked-msolve-l2-repeat-a5989cb5e42e.tar.gz](raw/ranked-msolve-l2-repeat-a5989cb5e42e.tar.gz): `2e918d37c8adcde0c1ad32f7297ba2a2205dc8875f446fdf557bf827fa075388`.
- [ranked-msolve-l42-a5989cb5e42e.tar.gz](raw/ranked-msolve-l42-a5989cb5e42e.tar.gz): `b76587ad3f96d6b7e53bb0daca746f56000aaa30202f65c5776fae9156060d2b`.
- [ranked-msolve-l42-repeat-a5989cb5e42e.tar.gz](raw/ranked-msolve-l42-repeat-a5989cb5e42e.tar.gz): `fdca6fe0256accaf1314ee6204e46828268cdf89909fb312917b9ead5b4e2a22`.
- [ranked-ranked-production-bench-a5989cb5e42e.tar.gz](raw/ranked-ranked-production-bench-a5989cb5e42e.tar.gz): `0c0d9239125c5345799b64499d24335d982362f7f1bd766d3b65512e46012b77`.
- [ranked-validation-a5989cb5e42e.tar.gz](raw/ranked-validation-a5989cb5e42e.tar.gz): `5440ba92e79688d89d4c09aa619c5f4c7cf7e01a451d47eb929b53354e7ee4a0`.
- [combined-before-after-a00d1a3e57a9.tar.gz](raw/combined-before-after-a00d1a3e57a9.tar.gz): `db6d788f85ad37e0d0e3967143fddb023b1df57c1c1353924f32a0fa0e5c6701`.
- [combined-before-after-repeat-a00d1a3e57a9.tar.gz](raw/combined-before-after-repeat-a00d1a3e57a9.tar.gz): `8e766493dd6b4a7072ea776ad6383c1a3aede9ea1b3a0218f76cac53886172a0`.
- [combined-msolve-l2-a00d1a3e57a9.tar.gz](raw/combined-msolve-l2-a00d1a3e57a9.tar.gz): `30a7dd7c89e30dc82c803de1a4e5e613fbe0336c5ab521884b9ae11f15b8c8f5`.
- [combined-msolve-l2-repeat-a00d1a3e57a9.tar.gz](raw/combined-msolve-l2-repeat-a00d1a3e57a9.tar.gz): `820888332743072a12043881b37141ac5c44ff1bd425d2ded2e71d7f620d4e54`.
- [combined-msolve-l42-a00d1a3e57a9.tar.gz](raw/combined-msolve-l42-a00d1a3e57a9.tar.gz): `fa16764e07f30a21d9653ddb4c08cf19bd99376913f834b040049ab37df57ece`.
- [combined-msolve-l42-repeat-a00d1a3e57a9.tar.gz](raw/combined-msolve-l42-repeat-a00d1a3e57a9.tar.gz): `3598fc8b32bd8f5617a6dcb08384f2e0cf7ae0ce2f1d55843da4b255ccacd569`.
- [combined-validation-a00d1a3e57a9.tar.gz](raw/combined-validation-a00d1a3e57a9.tar.gz): `68ae47af6f8f03089d13ea80cd5cd65c360e11b8570dee7a11f02f9cb8089f26`.
- [combined-profile-eco-a00d1a3e57a9.tar.gz](raw/combined-profile-eco-a00d1a3e57a9.tar.gz): `9e847c241e255248b0cceb720721b2a6cbc99b9e417d8e6dd251dcc40419866d`.
- [prototype-sparse-targets-668abb190c63.tar.gz](raw/prototype-sparse-targets-668abb190c63.tar.gz): `0d3f5b42634afd01227d9ad899b6d5b5f0d2a4b23b65186d6256d53f91a46abb`.
