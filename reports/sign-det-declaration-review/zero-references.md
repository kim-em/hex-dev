# Companion declarations without compiled references

The [compiled inventory](declaration-use.json) contains 450 constants, including
compiler-generated equations, matchers, recursors and projections. All 226
handwritten declarations match that inventory. Of those, the following 28
public theorems have no references from other compiled declaration types or
bodies in the audited environment. Every handwritten private helper has a
compiled user. Another 83 zero-reference constants are generated; their
elaborator/equation/compiler roles are not separate public API decisions.

An axiom-printing command does not create a referring declaration. Nor does
this model capture external clients, anonymous examples or automation's
registration tables. The assessment therefore retains the useful public
characterizations below, rather than treating this limited count as proof
that they are dead. This is an API disposition, not a claim of complete
Phase-6 use acceptance for the whole library pair.

| Declaration, relative to `Hex.SignDet` | Disposition |
| --- | --- |
| `Descriptor.compare_success` | Retain the actual-success witness alongside the total comparator's mathematical result, for clients distinguishing construction from fallback. |
| `Descriptor.compare_eq_iff` | Retain the direct equality characterization needed by downstream rewrite/proof code. |
| `Descriptor.compare_lt_iff` | Retain the direct forward strict-order characterization. |
| `Descriptor.compare_gt_iff` | Retain the direct reverse strict-order characterization. |
| `Descriptor.buildCompletion_roots` | Retain the bundled constructor result, preserved root and full derivative word; the total-wrapper theorem is a separate use surface. |
| `Descriptor.convert_success` | Retain unconditional checked-conversion production under its value/arithmetic laws; preservation after an assumed successful conversion alone is insufficient. |
| `Dag.selectedSigns_values` | Retain soundness for independently supplied graphs and requested ordered values, rather than only internally assembled selected-sign records. |
| `Dag.readMemo_values` | Retain the distinct boundary where independently supplied memo-domain bindings must be checked. |
| `Descriptor.convert_signAt` | Retain agreement of the actual source and converted total sign operations. |
| `Descriptor.convert_compare` | Retain preservation of all three actual comparison results after converting both roots. |
| `determine_convert_counts` | Retain exact sparse-table count agreement for every word under conversion. |
| `determine_convert_isSome` | Retain domain-only availability agreement over ordered fields; this is weaker than semantic root-count correctness. |
| `Descriptor.buildRoots_convert_isSome` | Retain success-domain preservation of complete actual enumeration. |
| `Descriptor.buildRoots_convert_roots` | Retain equality of the actual ordered returned mathematical root lists, stronger than membership/permutation agreement. |
| `QueryHandle.buildSigns_success` | Retain the prepared-handle constructor-success theorem for callers needing the actual witness. |
| `QueryHandle.signAt_success` | Retain the witness ruling out cached singleton error fallback. |
| `QueryHandle.signAt_correct` | Retain the direct cached total sign characterization, avoiding downstream conversion to the ordinary API. |
| `endpoint_lower` | Retain the strict lower-bound characterization for the executed boundary polynomial. |
| `endpoint_upper` | Retain the strict upper-bound characterization; it is not interchangeable with the lower sign orientation. |
| `Descriptor.refinement_fiber` | Retain the scoped same-head smaller-domain uniqueness result without requiring the general Thom producer theorem. |
| `Descriptor.buildRoots_linear` | Retain direct actual production for linear heads without making clients supply a semantic root-cardinality bound. |
| `Replay.check_counts` | Retain exact vector-count soundness for arbitrary accepted replay; sparse lookup is a different characterization. |
| `Descriptor.build_noError` | Retain the outer diagnostic-totality contract, including raw invalid, absent and ambiguous inputs. |
| `Descriptor.validate_success_iff` | Retain the public validator's exact context/shape/domain/count-one criterion using executable queries. |
| `Descriptor.build_valid_cases` | Retain the exact absent/accepted/ambiguous result trichotomy from semantic fiber cardinality. |
| `determinePrepared_success` | Retain the actual table-success witness ruling out the prepared total wrapper's diagnostic fallback. |
| `RawDescriptor.full_lt_iff` | Retain the direct strict-order characterization of the executed full-word comparator. |
| `Descriptor.buildReencoding_isSome` | Retain the full target validity plus original-root membership criterion for actual re-encoding success. |

## Record-field disposition

`Node.Counted`'s five fields are assessed with its structure, rather than as
five separate handwritten declarations. The generated `counts` projection has
no compiled user in this environment. Its equation follows from `checked`,
`values` and `cover` using support inclusion and `System.foundation_counts`.
Retain the field as an exact-count projection of the producer invariant, so
clients can use that guarantee directly without repeating the derivation.
The [structure assessment](companion.md#treesolve) records this redundancy;
count recovery still needs independent coverage and moment premises.

## Reproducing the inventory

The retained [audit source](audit.lean.txt) imports the full manual, field-proof
applications, all five proof probes, finite/root diagnostics, the integration
consumer and native realization examples. Reproduce the committed inventory:

```sh
cp reports/sign-det-declaration-review/audit.lean.txt \
  conformance/HexSignDetMathlib/Diagnostics/DeclarationAudit.lean
lake build +HexSignDetMathlib.Diagnostics.DeclarationAudit
python3 reports/sign-det-declaration-review/normalize.py
sha256sum reports/sign-det-declaration-review/declaration-use.json
rm conformance/HexSignDetMathlib/Diagnostics/DeclarationAudit.lean
```

The [normalizer](normalize.py) sorts rows by `(module, name)`, sorts `users` and
`axioms`, and writes UTF-8 JSON with sorted object keys, two-space indentation
and a final newline. The manifest's `data_sha256` is SHA-256 of exactly those
committed file bytes. `lake_manifest_sha256` binds the exact package revisions;
`toolchain` binds Lean. The script also records paths from private helpers
through generated users to handwritten production declarations.

The temporary Lean module is not a new CI example or proof-cost benchmark.
Different imported consumer modules can change reference counts without
changing any theorem. Anonymous examples and elaborator registration tables
remain outside this reference model. `Node.Counted.counts` is a generated
projection with the explicit disposition above.
