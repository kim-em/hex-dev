# Original CADE-24 real-closure inputs

The original `cade24ex.zip` is preserved inside the Z3 project ZIP in the
[Microsoft CodePlex archive](https://archive.org/details/sylirana_ms_codeplex_zips).
Its SHA-256 is
`0dc60a4a516748d6cc0b869c621880c241388360ffd6c5b00cec816f36e5bbcf`.
[source.json](source.json) records the exact container URL, byte offsets,
compressed sizes, CRCs and SHA-256 digests of the examples and their source
metadata, plus all 14 script hashes and root-call coefficient lists.

The project's archived CADE24 wiki identifies the examples as supplementary
material for de Moura and Passmore's paper and links download 606232. The
archived release list identifies `cade24ex.zip` under “CADE-24 examples”,
uploaded on 2013-01-20. The corresponding ZIP member is
`releases\0\dbcab2f9-4a7b-4b38-9c20-bad746a07fc9`.
The wiki also points to a separate `cade24` source branch; ordinary Z3 source
snapshots need not contain these examples.

## Literal tower inputs and discrepancies

[tower8.json](tower8.json) transcribes the five executed coefficient lists,
in ascending degree order, retaining selection of returned root index zero.
Their degrees are **4, 2, 4, 5, 5**.

The first polynomial has constant coefficient **`4 − 2ε²`**, whereas the
paper's printed expression contains an additional `+4`. The script polynomial is

`P₀(X) = (X² − 2)((X − ε)² − 2)`.

For `0 < ε < 1`, its four roots in increasing order are
`−√2`, `ε − √2`, `√2`, `ε + √2`. Its defining polynomial is reducible,
as permitted by the library's selected-root contract. The independently checked
no-root result for the paper's printed quartic still applies to that printed
formula; it does not apply to this script input.

The third assignment executes **`X⁴ + 3X³ + r₁X² − 1`**. Its print label and
the paper say `X⁵`; inserting an extra zero into the coefficient list would
change the archived workload. The source transcription follows the executed
list and records the discrepancy explicitly.

The entire syntax trees of `tower8.py` and `tower8_eager_norm.py` agree after
removing the eager script's single
`set_param("rcf.lazy_algebraic_normalization", False)` call. This establishes
identical source inputs and actions for the historical ablation. It is not a
Hex execution or a proof of the semantic outcomes of either implementation.

## Other source inputs and remaining execution

The archive contains `basic.py`, `ex1.py`–`ex7.py`, `nlsat.py`, `rioboo1.py`,
`rioboo2.py` and `strz.py`, as well as the two tower scripts. The inventory
records every literal `MkRoots` call, including calls inside helpers. It does
not expand helpers, reproduce every arithmetic/comparison action, or establish
that a Hex fixture implements those actions.

The `nlsat.py` degree-15 coefficient list and subsequent `Y³ + x³ + 1`
agree with the delivered MetiTarski input. Some script comments and print
labels disagree with their executed lists; use the executed inputs when
porting cases. In particular, `strz.py` exercises numbered cases 2, 3, 4 and
6, rather than every example in the cited collection.

Actual Hex execution of the original tower, its matched storage ablation,
root/equation checks, operation counts and stage measurements remain required.
The source archive supplies no Hex caller approximation procedure or law
evidence for π/e. A case needing those inputs remains unsupported until they
are supplied under the existing real-constant contract. No analytic provider
or replacement constant is introduced by this source inventory.

## Reproduce source verification

Fetch only the three small members, then verify all nested script bytes and
the transcriptions:

```bash
python3 scripts/bench/real_closure_cade24.py fetch /tmp/cade24-original
python3 scripts/bench/real_closure_cade24.py check /tmp/cade24-original
python3 -m unittest scripts.bench.test_real_closure_cade24
```

The fetcher requires a new destination and exact HTTP 206 range responses.
It never reads the whole 41,875,881,318-byte container, extracts files to
paths chosen by that archive, imports its modules or executes its scripts.
Each downloaded member passes a local ZIP-header check, bounded DEFLATE,
CRC and SHA-256 validation. `check` also works offline on the retained three
member files. The originals stay outside Git; the committed inventory retains
their identities and mathematical inputs.

The retained verification output is [source-checks.json](source-checks.json).
It covers source provenance and agreement, with no timing or Phase 4 readiness
claim.
