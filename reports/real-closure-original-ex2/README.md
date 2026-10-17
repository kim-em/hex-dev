# Original ex2 comparisons with live tower transport

The native `BasicConformance` executable exercises all seven comparisons in
the recovered CADE example `ex2.py`. Its actual output regenerates
[`basic.jsonl`](../../conformance-fixtures/HexRealClosure/basic.jsonl).
The exact Z3 4.15.4 oracle checks 22 stored value entries, plus the reciprocal,
ratio, initial transport and descriptor comparisons. It uses the original
integer bound `10^28`, retaining the existing `10^27` regression separately.

| Original comparison | Result |
|:---|:---|
| `1 / ε > 10^28` | true |
| `(1 + ε) / (1 - ε) > 1` | true |
| `cbrt(ε) > ε` | true |
| `cbrt(ε)^2 > ε` | true |
| `cbrt(ε)^4 > ε` | false |
| `ε₂ < ε` | true |
| `ε₂ < ε^10` | true |

The second infinitesimal enlarges the actual cube-root context. Both the
previous square root and cube root, and all seven computed cube-root values,
are retained. The native emitter checks the transported cubic equation and
signs. The independent oracle compares both selected roots, every defining
coefficient, interval and Thom word, and every transported value. Ten oracle
tests include mutations removing the live cubic root, reordered transport, changed
root data, incorrect powers, and substitution of the old integer bound.

[`evidence.json`](evidence.json) records the original source digest, actual
native executable fingerprint, ordinary module build, capped native build,
and normal conformance execution. The builds use an aggregate 8 GiB cap,
no swap and two Lean threads, with immutable source/tool checks. This is
conformance evidence; it makes no Phase-4 performance or original formatting
coverage claim. The π-dependent introductory cases retain their explicit
unsupported output.

```sh
lake build hexrealclosure_basic_conformance
.lake/build/bin/hexrealclosure_basic_conformance > /tmp/hex-basic.jsonl
python3 scripts/oracle/real_closure_basic.py /tmp/hex-basic.jsonl
python3 -m unittest scripts.oracle.test_real_closure_basic
```

The oracle requires `z3-solver==4.15.4.0`. No approximation provider is needed
for these seven comparisons.
