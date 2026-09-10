# HexLatticeEnum

Mathlib-free exact enumeration of integer row lattices in closed rational
balls, Babai nearest-plane candidates, and all globally closest or shortest
vectors. Independent rectangular and rank-zero bases are supported.

## Quickstart

```lean
import HexLatticeEnum
open Hex Hex.LatticeEnum

def rows : Matrix Int 2 2 := Matrix.ofRows #v[#v[2, 0], #v[1, 2]]
#guard (ofMatrix? rows).map (fun b => (babai b #v[1, 1]).distanceSq) = some 2
#guard (ofMatrix? rows).map (fun b => (closest b #v[1, 1]).distanceSq) = some 1
```

## Functionality

All answers include original-basis integer coefficients, ambient vectors and
exact rational squared distances. Complete lists are unique and sorted by
ambient coordinates. Shortest search excludes zero and includes both signs.
Rank zero has no nonzero shortest vector. Closest search permits targets
outside the row span and retains their orthogonal residual in its bounds.

`prepare` shares exact Gram–Schmidt data; `retarget` reuses it for another
target. `lllPreprocess` provides checked working-basis methods that transport
results back to the original coordinates. Search works on unreduced bases.

The `With` variants accept separate node, answer and certificate-node budgets.
Incomplete results contain checked progress and pending work, without claiming
a global optimum. Certificates prove exhaustive fixed-radius traversal and
attainment of optimal distances. Producers, bounded decoding and all replay
checkers execute without Mathlib or an external search provider.

`checkEnumerationWith`, `checkClosestWith` and `checkShortestWith` bound
replay by total certificate nodes, including across sibling branches.

## Verification

The [companion](../HexLatticeEnumMathlib/README.md) proves unconditional
correctness, arbitrary-certificate soundness, native-certificate acceptance,
LLL transport and real packing geometry. See the [SPEC](SPEC/hex-lattice-enum.md),
[live manual](../HexManual/Chapters/HexLatticeEnum.lean) and
[performance report](../reports/hex-lattice-enum-performance.md).

```sh
lake build HexLatticeEnum HexLatticeEnumMathlib HexLatticeEnumMathlib.Tests \
  HexLatticeEnum.Conformance hexlatticeenum_emit_fixtures hexlatticeenum_bench
python3 scripts/oracle/lattice_enum.py < conformance-fixtures/HexLatticeEnum/latticeenum.jsonl
.lake/build/bin/hexlatticeenum_bench verify
```

## Contributing

Develop in [hex-dev](https://github.com/kim-em/hex-dev). The SPEC, source,
conformance fixtures and manual are maintained together in the monorepo.
