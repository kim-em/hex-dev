# Compact column-map variants

Three development variants replace per-monomial boxed hash lookups during symbolic row construction. None establishes a general speedup suitable for unconditional selection. Keep their sources and complete measurements separate.

The first uses packed u32 positions plus one when the ID prefix contains at most eight slots per matrix column, otherwise a hash map. It also falls back when remaining allowances do not cover packed initialization. The second adds bounded native row translation with four exported byte-push calls per entry. The third chooses its layout from geometry alone and replaces those calls with one reservation and direct u32 stores.

The first two variants have a budget-dependent layout: a larger allowance can select extra packed initialization and exhaust later where a smaller allowance takes the cheaper hash route. Do not adopt that policy. The third fixes it. All variants preserve exact ID equality, duplicate-ID replacement and missing-ID behavior. Packed memory is charged cumulatively and can change exhaustion thresholds; it is not inferred from work-only fixtures.

Each frozen variant has a fresh detached production and benchmark build. Baseline source is `e878b78cf727`; its compute SHA256 is `fb6a033166de667e753df9ba554203503bb7bb9e89ad893f351f18f064eb2a1d`. Both arms use the restored SDK Clang/LLD 23.1.0 wrapper; native FFI uses Clang 23.1.3. The relocatable helper and flags are retained. Older toolchain arrangements are separate build variants.

Manual shared-host measurements use EPYC 9455, one requested algorithm thread and an automatically leased CPU, adjacent AB/BA. Every completed sample, outlier, failure, host activity observation and child RSS remains. Each small/medium CLI and fixed observation has its first campaign and sole unchanged repeat; no further unchanged repeat is used. These development suites are not held-out SPEC acceptance.

| Source | Suite | Campaign | CPU | Candidate B/A | Process B/A |
| --- | --- | --- | ---: | ---: | ---: |
| `7df198fe184d` | small | first | 35 | 1.0730 | 0.9256 |
| `7df198fe184d` | small | repeat | 81 | 0.9490 | 0.9603 |
| `7df198fe184d` | medium | first | 5 | 0.8923 | 0.9802 |
| `7df198fe184d` | medium | repeat | 84 | 0.9758 | 0.9629 |
| `9811bea91f2c` | small | first | 68 | 0.8626 | 0.9390 |
| `9811bea91f2c` | small | repeat | 88 | 0.7710 | 0.9486 |
| `9811bea91f2c` | medium | first | 34 | 1.1016 | 0.9954 |
| `9811bea91f2c` | medium | repeat | 25 | 0.8456 | 0.8768 |
| `605f1e427e55` | small | first | 50 | 0.9284 | 1.0662 |
| `605f1e427e55` | small | repeat | 64 | 0.9727 | 0.9275 |
| `605f1e427e55` | medium | first | 87 | 1.2055 | 1.1208 |
| `605f1e427e55` | medium | repeat | 9 | 0.9221 | 0.9489 |

Each source retains 240 successful CLI processes, 120 complete basis pairs and all algorithm statistics. Work and packed allocation differ from the baseline. Emission of all 1,134 F4 fixture records was compared before regeneration: only `work`, `referenceWork` and `serialWork` changed. The fixture does not contain packed-byte counters; exact map tests separately assert those. Several campaigns disagree materially and contain extreme ratios; pooled means must not be read as uniform improvements.

| Source | Fixed campaign | CPU | Case | B/A geomean | Candidate median | Range |
| --- | --- | ---: | --- | ---: | ---: | --- |
| `7df198fe184d` | first | 50 | cyclic4 | 1.0385 | 1.0104 | 0.9848–1.3929 |
| `7df198fe184d` | first | 50 | cyclic5 | 1.0171 | 1.0370 | 0.7928–1.2261 |
| `7df198fe184d` | first | 50 | cyclic6 | 1.0926 | 1.0628 | 0.5633–2.4269 |
| `7df198fe184d` | first | 50 | katsura3 | 0.9545 | 0.9938 | 0.7934–1.0056 |
| `7df198fe184d` | first | 50 | reimer5 | 0.9925 | 1.0040 | 0.3722–2.1101 |
| `7df198fe184d` | first | 50 | cyclic6Small | 0.7865 | 0.9254 | 0.3807–1.7066 |
| `7df198fe184d` | repeat | 15 | cyclic4 | 1.0166 | 1.0231 | 0.9581–1.0488 |
| `7df198fe184d` | repeat | 15 | cyclic5 | 0.5114 | 0.5331 | 0.0485–5.3457 |
| `7df198fe184d` | repeat | 15 | cyclic6 | 0.7832 | 1.0085 | 0.2176–2.4513 |
| `7df198fe184d` | repeat | 15 | katsura3 | 1.2006 | 0.9978 | 0.9636–6.3489 |
| `7df198fe184d` | repeat | 15 | reimer5 | 0.8723 | 0.8401 | 0.3787–3.0963 |
| `7df198fe184d` | repeat | 15 | cyclic6Small | 1.2282 | 1.0072 | 0.3083–4.5040 |
| `9811bea91f2c` | first | 10 | cyclic4 | 1.0182 | 1.0163 | 1.0070–1.0414 |
| `9811bea91f2c` | first | 10 | cyclic5 | 1.1219 | 1.0544 | 0.6127–2.8974 |
| `9811bea91f2c` | first | 10 | cyclic6 | 1.0807 | 0.9841 | 0.5547–2.5087 |
| `9811bea91f2c` | first | 10 | katsura3 | 1.0319 | 1.0176 | 0.9648–1.2411 |
| `9811bea91f2c` | first | 10 | reimer5 | 0.8393 | 0.8784 | 0.2547–2.0277 |
| `9811bea91f2c` | first | 10 | cyclic6Small | 0.9508 | 0.9438 | 0.2887–3.3230 |
| `9811bea91f2c` | repeat | 21 | cyclic4 | 1.1505 | 1.0136 | 0.6533–5.4311 |
| `9811bea91f2c` | repeat | 21 | cyclic5 | 1.2264 | 1.2385 | 0.8324–2.9738 |
| `9811bea91f2c` | repeat | 21 | cyclic6 | 0.9814 | 0.9778 | 0.3243–3.0386 |
| `9811bea91f2c` | repeat | 21 | katsura3 | 1.2020 | 1.0147 | 0.4470–3.9538 |
| `9811bea91f2c` | repeat | 21 | reimer5 | 0.9498 | 1.0432 | 0.3173–2.8186 |
| `9811bea91f2c` | repeat | 21 | cyclic6Small | 0.9646 | 0.9928 | 0.3965–3.0670 |
| `605f1e427e55` | first | 27 | cyclic4 | 1.0061 | 1.0061 | 0.9850–1.0306 |
| `605f1e427e55` | first | 27 | cyclic5 | 0.9836 | 1.0447 | 0.5691–1.3537 |
| `605f1e427e55` | first | 27 | cyclic6 | 0.8654 | 0.9637 | 0.3254–2.5298 |
| `605f1e427e55` | first | 27 | katsura3 | 0.9872 | 0.9868 | 0.9658–1.0171 |
| `605f1e427e55` | first | 27 | reimer5 | 1.0498 | 1.2479 | 0.2105–2.4522 |
| `605f1e427e55` | first | 27 | cyclic6Small | 0.9334 | 1.0096 | 0.3309–3.3288 |
| `605f1e427e55` | repeat | 9 | cyclic4 | 1.0011 | 0.9965 | 0.9781–1.0552 |
| `605f1e427e55` | repeat | 9 | cyclic5 | 1.4687 | 1.1528 | 0.8727–9.9922 |
| `605f1e427e55` | repeat | 9 | cyclic6 | 0.8480 | 1.0269 | 0.2237–1.1446 |
| `605f1e427e55` | repeat | 9 | katsura3 | 0.9831 | 0.9770 | 0.9448–1.0236 |
| `605f1e427e55` | repeat | 9 | reimer5 | 1.1675 | 0.9936 | 0.8850–2.8269 |
| `605f1e427e55` | repeat | 9 | cyclic6Small | 0.9766 | 0.9507 | 0.5526–2.0885 |

All 240 fixed points per source succeed with equal complete structural output hashes. The first prototype has mixed fixed results; the byte-push native variant regresses Cyclic4, Cyclic5 and Katsura3 in both campaigns. The reserve/store variant remains mixed, with Cyclic5 and Reimer5 regressions. No general speedup is established.

Each variant passes library/theory/conformance builds, independent matrix/basis/division oracles, both 1,134-output CLI checks, 32 benchmark checks and project audits. Both native variants also pass four Clang and four GCC ASan/UBSan variants. Counters record 9,269 native column translations from F4 per sanitizer variant. Direct C checks cover a uniquely owned output also passed borrowed. The reserve/store variant additionally checks marked-linear aliases, exclusive growth and reserved capacity; its exact layout and charge tests include pre-existing table bytes and all resource boundaries.

An explanatory profile of `605f1e427e55` on CPU 13 records packed/hash builds: Cyclic7-31 11/17, Eco11-31 18/3, Reimer6-31 19/7 and MinRank 5/0. All four complete bases and counters agree with uninstrumented execution, and profile call counts equal `matrixCalls`. Its durations are excluded from timing estimates. The sparse ID ranges motivate further packed lookup work.

Candidate time includes packing, F4 and final interreduction; process time additionally includes initialization, parsing and output. Certificate production, independent certification and kernel replay are excluded. These results do not establish leadership or a compiler/runtime impossibility.

- [column-map-7df198fe184d.tar.gz](raw/column-map-7df198fe184d.tar.gz): `632b99bd15f0ff3bcc627807b56904d23d80f3d66bc503948c8f26384eeb7783`.
- [column-map-native-9811bea91f2c.tar.gz](raw/column-map-native-9811bea91f2c.tar.gz): `da8e7536b45fe44eff94c6b30cbd3bb9367c84984fd82c921ad355d20988c792`.
- [column-map-reserved-605f1e427e55.tar.gz](raw/column-map-reserved-605f1e427e55.tar.gz): `e6d475998a8153eecf10ad15b5063a11845df8bdb941ec6f467a76ff8ee227de`.
