# HexLatticeEnumMathlib

Proofs about the executable definitions in `HexLatticeEnum`; no duplicated
runtime search implementation.

## Quickstart

```lean
import HexLatticeEnumMathlib
open Hex.LatticeEnum HexLatticeEnumMathlib

example (b : Basis n m) (t : Vector Rat m) : (prepare b t).Valid :=
  prepare_valid b t
```

## Functionality

- `prepare_valid` discharges exact Gram–Schmidt identities for every accepted basis.
- `coefficients_ordered`, `nearest_spec` and `enumerate_spec` prove the exact
  coefficient order and complete, sorted, duplicate-free closed-ball enumeration.
- `closest_spec` and `shortest_spec` give global all-ties minimum contracts.
- `enumerateWith_spec`, `closestWith_spec` and `shortestWith_spec` distinguish
  complete answers from sound partial progress; `Within` theorems prove all limits.
- `checkEnumeration_sound`, `checkClosest_sound` and `checkShortest_sound` apply
  to arbitrary accepted certificates. Native producer acceptance is unconditional.
- `lllPreprocess_rows` and `lllPreprocess_reduced` prove exact coordinate recovery
  accepts the LLL result; `change_enumerate` preserves original-basis answers.
- `rationalLattice` and `realLattice` are integer spans. Their correspondence
  theorems preserve distances and global minima, including off-span targets.
- `realLattice_discrete`, `packing_radius` and `kissing_number` connect the
  verified shortest-vector list to lattice geometry within the real span.

## Verification

[Tests.lean](Tests.lean) includes literal kernel certificate replay and
build-only examples of the public contracts. See the
[SPEC](SPEC/hex-lattice-enum-mathlib.md) and the shared
[manual chapter](../HexManual/Chapters/HexLatticeEnum.lean).

## Contributing

Develop proofs alongside the computational definitions in
[hex-dev](https://github.com/kim-em/hex-dev). Keep executable search in the
Mathlib-free companion.
