# Sign-determination proof examples

`lake build HexSignDetMathlibProofProbe` builds every file in this declared
proof-example root in the existing CI job. The examples consume supplied certificate checks proved by ordinary kernel
reduction and guard their axiom inventories. `Replay` and `Nested` re-export
warm diagnostic theorems; their Boolean reductions are checked in Diagnostics.
They contain no admitted proof or `native_decide`.

- `Replay`: a depth-three shared BKR graph, stale-context rejection and
  mathematical root counts.
- `SelectedSigns`: a literal sign certificate at the positive root of `X²−1`,
  with acceptance of the correct claim and rejection of an incorrect claim.
- `Completion`: completion of a partial encoding of that root to `[+1,+1]`,
  including rejection of a copied context identifier.
- `Reencoding`: checked replacement of the defining polynomial `X` by `2X`,
  including rejection of an unrelated count certificate.
- `Nested`: rational-function coefficients, supplied graph acceptance,
  nonunit-denominator fraction acceptance, arithmetic/context/product rejection,
  an arithmetic rejection cause and normalization-certificate checks.

`lake build HexSignDetMathlibDiagnostics` also runs in the existing CI job.
It builds all retained depth-one, three, five and seven same-level graph checks
and all one- and two-level nested checks under
`conformance/HexSignDetMathlib/Diagnostics`. These correctness fixtures sit
outside the declared proof-example root. It also builds the public-API
correspondence instantiations in `Diagnostics.Conformance` and the headline
axiom inventories in `Diagnostics.RootSemantics`. The depth-three nested fixtures have
observed peak RSS near 18 GiB and use the separate manual target
`HexSignDetMathlibDepthThree`.

The downstream `HexRCF.SignDetFieldProofs` target builds the cubic `QAdjoin`
correspondence instantiations. Compiled conformance separately covers repeated
roots and zero derivatives. Completed measurements and their source archives
remain under `reports/data`; computational Phase-4 scaling, comparison,
allocation and profile obligations are unaffected by this layout.
