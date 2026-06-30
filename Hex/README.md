# hex-test-kit

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-test-kit` provides the shared conformance and benchmark helpers used by
the other Hex libraries' test and bench harnesses. It is tooling rather than
a user-facing algebra library, so it ships no algebraic operations of its own.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-test-kit"
git = "https://github.com/kim-em/hex-test-kit.git"
rev = "main"
```

```lean
import Hex.Conformance.Emit
import Hex.BenchOracle.Flint

open Hex.Conformance.Emit
open Hex.BenchOracle.Flint
open Lean (Json)

-- A conformance emit driver writes one JSONL fixture per case, then
-- emits Lean's computed result for each operation under test.
#check (emitMatrixFixture : String → String → List (List Int) → IO Unit)
#check (emitResult : String → String → String → String → IO Unit)

-- A bench driver runs one FLINT comparator op through the shared
-- persistent subprocess and decodes the reply.
#check (runOp : String → String → Array (String × Json) → IO Json)
#check (jsonToInts : Json → IO (List Int))
```

# Functionality

- `Hex.Conformance.Emit`: `IO` helpers that write JSONL records consumed by
  the external oracles (`emitMatrixFixture`, `emitPolyFixture`,
  `emitLatticeFixture`, `emitPrimeFixture`, `emitGfqFieldFixture`, and the
  other per-kind emitters), plus `emitResult` and the result-value builders
  `intMatrixValue`, `polyValue`, `divModValue`, and `latticeValue`. Output
  goes to stdout or to the file named by `HEX_FIXTURE_OUTPUT`.
- `Hex.BenchOracle.Flint`: the persistent-subprocess driver for FLINT
  comparators. `runOp` sends one JSON request through a cached child process
  and returns the unwrapped result; `PersistentComparator` owns the child and
  its stdin handle, and `intsToJson` / `jsonToInts` convert coefficient lists
  to and from JSON.

# Verification

This library is test and bench tooling, so it carries no proofs; everything
it provides is for executable use. The JSON serializer in
`Hex.Conformance.Emit` is hand-rolled to keep the library dependency-free,
and the FLINT driver in `Hex.BenchOracle.Flint` depends only on
`Lean.Data.Json`. Correctness of the data these helpers move is checked
end to end by the conformance and bench harnesses of the libraries that use
them, against the external oracles.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
