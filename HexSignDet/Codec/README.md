# Literal graph byte format

`Dag.encodeBytes` writes a UTF-8 JSON encoding of the supplied graph.
`Dag.decodeBytes` parses and independently replays it for the caller's exact
context, head, endpoints and ordered query list. It returns `Except String`
with an accepted literal tree on success. An error diagnoses malformed input,
a decoding limit or failed certificate replay; it does not decide root
nonexistence. No query producer, root isolation or coefficient refinement runs
inside decoding or replay.

`ValueCodec` supplies encoders and decoders for coefficient values and the
full immutable context. The provided codecs cover canonical `Rat` and `Nat`.
A composite context must encode all its components, including refinement and
embedding data. A hash or a reused numeric identifier cannot replace that
value. The JSON interfaces handle coefficient/context types in `Type`, matching
Lean's JSON API. The computational sign-determination APIs retain their existing
universe polymorphism.

Numeric tokens in this format are integers. Rational coefficients use
`[numerator, denominator]` with a positive coprime denominator; noncanonical
pairs are rejected. Coefficient codecs for other representations must use
integer numeric tokens, strings, arrays or objects. A codec intended for
roundtrips must preserve its entire value. No generic roundtrip theorem for
arbitrary user codecs or the JSON parser is claimed here.

Every structural record is a positional array with exactly the listed fields.
An optional value is `[]` or `[value]`. Arrays and lists retain their original
order; matrices are arrays of rows.

| Record | Fields in order |
| --- | --- |
| Graph | `1`, root index, entries |
| Entry | node, optional `[left, right]` child indices |
| Node | context, head, lower endpoint, upper endpoint, queries, size, system, moments, reductions, optional preparation, basis |
| System | exponent rows, sign columns, counts, values, inverse, denominator |
| Basis | rank, row indices, column indices, denominator, adjugate numerator |
| Tarski certificate | context, head, query polynomial, lower endpoint, upper endpoint, squarefree chain, query chain, lower signs, upper signs, lower variations, upper variations, value |
| Signed-remainder chain | polynomials, degrees, initial step, steps, optional terminal pair |
| Remainder step | left scale, quotient polynomial, right scale |
| Terminal pair | scale, quotient polynomial |
| Reduction step | factor index, next polynomial, remainder step |
| Reduction | steps, result polynomial |
| Query preparation | array of reduction steps |

A polynomial is its coefficient array in increasing exponent order; trailing
literal zeros are rejected. Endpoints are `[0]` for negative infinity,
`[1, value]` for a finite endpoint, and `[2]` for positive infinity.

The parser checks node/system sizes, row and column arities, matrix dimensions,
rank-index bounds, and reduction-index bounds before using the supplied data.
Declared dimensions do not drive allocation: actual array lengths must match
before their elements are decoded. Every entry, including unreachable entries,
is decoded. Child references must point to an earlier entry. Every node and
Tarski certificate must match the caller's full context and root domain.
Independent graph replay then checks the ordered child query lists, support
completeness, exact integer matrix identities, reductions and Tarski evidence.

`Codec.Limits` defaults to 16 MiB, 128 nested arrays/objects and 4,096 digits per
integer token. Callers may supply larger limits. Before JSON parsing, a finite
byte scan checks these limits, string quoting and delimiter depth and rejects
fraction/exponent number syntax. UTF-8 validation precedes parsing. Brackets
and escaped quotes inside strings do not change delimiter depth.

`Dag.decode_replays` proves that success replays the graph returned by the
actual decoder, for arbitrary supplied bytes and codecs. The returned tree
also carries the existing finite checker proof. Conformance compares all
literal fields after rational/context roundtrips, including a produced graph
with query preprocessing and moment reductions. It covers stale composite
contexts, truncated and false evidence, invalid references, malformed sizes,
noncanonical literals and lexical bounds. Byte parsing uses compiled execution;
the separate ordinary-kernel graph probes and axiom audits remain in place.

This format encodes same-level BKR graphs and coefficient values. It does not
yet encode lower-level coefficient-sign proof dependencies or establish
arbitrary-field root/sign semantics. Generic encoder/decoder roundtrip proofs,
nested evidence transport, serialization cost measurements and the other
Phase-4 obligations remain open.
