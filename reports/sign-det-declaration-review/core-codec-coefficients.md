# Stored graph coefficients and finite reader coverage

This assessment covers all 18 named declarations in `Codec/Coefficients`.
The inventories retain literal values in serialized order, including zeros
and duplicates. They perform no coefficient arithmetic or sign searches.
Coverage proves reconstruction of those literals, independently of arithmetic
replay and mathematical interpretation. This is partial computational review,
without a phase or performance attestation.

| Declaration | Assessment |
| --- | --- |
| `Codec.Coefficients.poly` | Enumerates the canonical polynomial's complete stored coefficient array in order. |
| `Codec.Coefficients.endpoint` | Includes the value of a finite endpoint and no values for either infinite endpoint. |
| `Codec.Coefficients.remainder` | Includes both scales and every quotient coefficient; omitting either scale would leave witness reconstruction unsupported. |
| `Codec.Coefficients.terminal` | Includes the terminal scalar and its polynomial coefficients. |
| `Codec.Coefficients.chain` | Includes every chain polynomial, the initial remainder witness, subsequent witnesses and the optional terminal record. Integer degree metadata contains no coefficient values. |
| `Codec.Coefficients.tarski` | Includes the stored head, query polynomial, finite endpoints and both remainder-chain witnesses. Context coverage is supplied separately. |
| `Codec.Coefficients.step` | Includes the next polynomial and complete remainder witness; the step index is an independently checked natural number. |
| `Codec.Coefficients.reduction` | Includes each ordered step and the final polynomial, preserving duplicate and zero values. |
| `Codec.Coefficients.preparation` | Includes every stored query-preparation step; an empty preparation needs no coefficient coverage. |
| `Codec.Coefficients.node` | Includes head, finite endpoints, queries, all moments, optional reductions and optional preparation. Contexts are enumerated separately; integer system and rank-certificate entries use the fixed integer decoder, separately from coefficient coverage. |
| `Codec.Coefficients.graph` | Traverses every stored entry, including unreachable entries. It does not restrict coverage to the selected root's dependency tree. |
| `ValueCodec.Covers` | Requires exact decode-after-encode equality for each member of the supplied finite collection. It imposes no global completeness requirement on a partial reader. |
| `ValueCodec.covers_nil` | Empty finite coverage is unconditional. |
| `ValueCodec.covers_cons` | Coverage of a head and tail is exactly their two coverage conditions, without requiring distinct values. |
| `ValueCodec.covers_append` | Coverage of concatenated inventories is equivalent to coverage of both inventories; the proof preserves literal membership. |
| `ValueCodec.covers_flatMap` | Coverage of flattened inventories is exactly coverage of every constituent inventory, including empty or overlapping lists. |
| `ValueCodec.Lawful.covers` | A globally lawful codec supplies finite coverage; the converse is not claimed. |
| `Dag.encode_leaf` | Actual encoding of a single leaf produces that literal node at index zero with no children. The empty-map proof needs no lawful-hash hypothesis or native hash-table evaluation. It establishes no replay acceptance. |

Nine traversal helpers are individually documented. The finite-reader graph
roundtrip lemmas consume these inventories along with separate context,
shape, subject-binding, reference-index and byte-limit premises. These
inventories are not an assembly theorem for arbitrary registered constants,
context histories or all-live ordinary-real realization.
