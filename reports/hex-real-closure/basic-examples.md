# Introductory real-closure examples

The source is section 4, introductory examples, PDF pages 13–14 of
[de Moura and Passmore, CADE 2013](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf).
The PDF SHA-256 is
`4caf52449ebb030fcc9341b864c08b307a944dd0d0fc7fb801413486396d7a19`.
The formulas and operations are transcribed from the paper. The original
`basic.py` archive has not been recovered; this fixture records the stated
operations without claiming script-level identity.

| Source operation | Native construction | Exact Z3 RCF check |
| --- | --- | --- |
| Both roots of `X²-2` | Complete `Context.roots`, comparison and multiplicities | Original selected embeddings, `[-sqrt(2),sqrt(2)]`, multiplicities one |
| `1/sqrt(2)`, `sqrt(2)²`, `sqrt(2)³+1` | Arithmetic in the positive root's owner | All four stored values including the generator |
| Add `ε` after selecting `sqrt(2)` | `enlargeWithParameter?`, original conversion, cached parameter | Original positive embedding in the enlarged base |
| Cube root `β` of `ε` | Complete roots of `X³-ε`, selected-child arithmetic | Multiplicity one, `β³=ε`, `ε<β<1` |
| `1/ε>10^27` | Reciprocal and subtraction | Exact inequality with the original paper integer |
| Cubic and comparison involving `π` | Explicit unsupported records | Required caller provider and progress premises; no surrogate input |

The native driver checks actual descriptor replay graphs and emits complete
contexts and coefficient payloads. The independent oracle checks selected
embeddings, every prescribed value and cached signs using pinned Z3
4.15.4.0; it does not implement native graph replay. Five mutation-test groups
reject changed root selection, order, multiplicities, stage order, original
owners, arithmetic, cached signs, malformed JSON and lost non-coverage.

Build and run `hexrealclosure_basic_conformance`, then run
`scripts/oracle/real_closure_basic.py` on
`conformance-fixtures/HexRealClosure/basic.jsonl`. CI compares fresh native
output with the exact fixture before the independent check.

These are computational correctness fixtures in an ordered real-closed
extension. Simultaneous ordinary-real realization remains a theorem
requirement. No scientific timing sample or Phase-4 attestation is inferred.
Display decimals are not used to identify or compare roots.
