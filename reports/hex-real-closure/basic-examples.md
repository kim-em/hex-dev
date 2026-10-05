# Introductory real-closure examples

The source is section 4, introductory examples, PDF pages 13–14 of
[de Moura and Passmore, CADE 2013](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf).
The PDF SHA-256 is
`4caf52449ebb030fcc9341b864c08b307a944dd0d0fc7fb801413486396d7a19`.
The formulas and operations are transcribed from the paper. The original
`basic.py` archive has not been recovered; this fixture records the stated
operations without claiming script-level identity.

The input lines below retain the paper's spelling and page;
the fixture fields identify their exact native results. Display and decimal
formatting are outside these arithmetic checks.

| Paper input, page | Fixture field |
| --- | --- |
| `MkRoots([-2, 0, 1])`, 13 | Square-root descriptors, order and multiplicities |
| `1/sqrt2`, 13 | Square-root values[1] |
| `sqrt2**2 == 2`, 13 | Square-root values[2] and native equality |
| `sqrt2**3 + 1`, 13 | Square-root values[3] |
| `MkInfinitesimal("eps")`, 13 | Parameter and transported_values |
| `MkRoots([-pi, sqrt2 + pi, eps, 1])[0]`, 13 | Unsupported cubic_coefficients |
| `2 + 2*pi + pi**2 - 2*eps - 2*pi*eps + eps**2 < 2 + 2*pi + pi**2`, 13 | Unsupported comparison |
| `MkRoots([-eps, 0, 0, 1])[0]`, 13 | Infinitesimal root descriptor |
| `eps3 > eps`, 13–14 | Infinitesimal values[2] and signs[2] |
| `1/eps > 1000000000000000000000000000`, 14 | Reciprocal bound |

The unsupported row uses normalized mathematical notation for the exact ascending coefficient list
`[-pi, sqrt(2)+pi, epsilon, 1]` for the paper's cubic and its comparison
`2+2*pi+pi^2-2*epsilon-2*pi*epsilon+epsilon^2 < 2+2*pi+pi^2`.
Both appear on page 13 and require the caller's pi provider. Their formulas
are required by the independent oracle, alongside the non-coverage labels.

| Source operation | Native construction | Exact Z3 RCF check |
| --- | --- | --- |
| Both roots of `X²-2` | Complete `Context.roots`, comparison and multiplicities | Original selected embeddings, `[-sqrt(2),sqrt(2)]`, multiplicities one |
| `1/sqrt(2)`, `sqrt(2)²`, `sqrt(2)³+1` | Arithmetic in the positive root's owner | All four stored values including the generator |
| Add `ε` after selecting `sqrt(2)` | `enlargeWithParameter?`, original conversion, cached parameter | Original positive embedding in the enlarged base |
| Cube root `β` of `ε` | Complete roots of `X³-ε`, selected-child arithmetic | Multiplicity one, `β³=ε`, `ε<β<1` |
| `1/ε>10^27` | Reciprocal and subtraction | Exact inequality with the original paper integer |
| Cubic and comparison involving `π` | Explicit unsupported records | Required caller provider and progress premises; no surrogate input |

The native driver replays the three producer-returned descriptors; enlargement
checks the rebuilt predecessor. It emits complete contexts and coefficient payloads. All four original values are transported,
and the oracle checks the mapped polynomial, endpoints and empty Thom word.

The independent oracle checks selected embeddings, every prescribed value and cached signs using pinned Z3
4.15.4.0; it does not implement native graph replay. Six mutation-test groups reject changed root selection, order, multiplicities, stage order, original
owners, arithmetic, cached signs, transported polynomial/endpoints/Thom data,
malformed JSON and lost non-coverage.

Build and run `hexrealclosure_basic_conformance`, then run
`scripts/oracle/real_closure_basic.py` on
`conformance-fixtures/HexRealClosure/basic.jsonl`. CI compares fresh native
output with the exact fixture before the independent check.

These are computational correctness fixtures in an ordered real-closed
extension. Simultaneous ordinary-real realization remains a theorem
requirement. No scientific timing sample or Phase-4 attestation is inferred.
Display decimals are not used to identify or compare roots.
