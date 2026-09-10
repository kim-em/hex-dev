# HexGraphIsoMathlib performance

The bridge encodes finite Mathlib `SimpleGraph` inputs as coloured graphs
and transports the checked result to `Nonempty (G ≃g H)` or
`IsEmpty (G ≃g H)`. The canonical search is measured by
[HexGraphIso's performance suite](hex-graph-iso-performance.md).

The build-only `HexGraphIsoMathlibProofProbe` target measures the bridge
through fresh importers of a common precompiled support module. It has no
Mathlib-importing benchmark executable.

| Input family | Probes |
|---|---|
| `cross-type-goals` | `MathlibPositive10` compares Petersen and Kneser representations on different finite vertex types; `MathlibNegative10` compares Petersen and the pentagonal prism. |
| `random-pair-transport` | `MathlibPositive12` and `MathlibNegative12` transport the fixed random 12-vertex pairs. |

`MathlibBaseline` supplies the matched import cost. Each measured module
contains one tactic invocation and imports no other measured module.
The [archived raw samples](bench-results/hexgraphiso-mathlib-20260903-chungus2.json)
retain three interleaved observations per probe, their host and toolchain,
and the original report's Git blob. They describe that observation's
implementation and host conditions; no current wall-clock claim is inferred
from them. Kernel acceptance and the library's tactic tests verify the
transported answers.
