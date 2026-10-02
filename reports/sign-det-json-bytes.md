# Integer-only JSON bytes

`HexSignDet.Codec.Value` provides a total UTF-8 parser and printer for the
integer-only JSON certificate format. `Codec.Json.Value` contains null,
booleans, signed integers, strings, arrays and ordered object fields. Arrays
and object fields are finite inductive lists. The object representation
preserves duplicate fields and their order literally.

`Codec.Json.readBytes_write` proves, for every value, that parsing its actual
printed bytes returns exactly that value. It has no parser-success premise,
fixed input-size bound or finite-fixture assumption. Its dependencies are
Lean's standard logical axioms only. The constituent decimal, Unicode-string
and token-stream roundtrips are also proved. No Mathlib import or admission
is required.

The printer puts a space after every token, uses canonical signed decimal
integers, and escapes quotation marks, backslashes and control characters.
The parser validates UTF-8, accepts ordinary Unicode and valid UTF-16 escape
pairs, and rejects lone surrogates. Fractional and exponent number syntax are
outside this wire format. Leading zeros, malformed delimiters, missing values,
trailing commas and trailing tokens are rejected. Negative zero is accepted
and prints as zero. Recursion fuel comes from finite input character and token
counts; printing and parsing are ordinary executable operations.

The independent Python oracle sends 324 byte strings to the compiled parser.
Its corpus includes 256 deterministic generated values, large integers,
Unicode/control strings, duplicate object fields, nesting, malformed syntax,
unpaired surrogates and invalid UTF-8. Python's standard parser determines the
expected typed values while retaining object fields and duplicates, with
explicit rejection of noninteger numbers and nonscalar
Unicode strings. Nine oracle tests include rejection of incorrect answers, Boolean/integer
confusion, changed field order, collapsed duplicates and invalid expectations. Ordinary-kernel checking of the
universal theorem is separate from these executable conformance checks.

Reproduce with:

```sh
lake build HexSignDet.JsonBytes hexsigndet_json_bytes
python3 scripts/oracle/sign_det_json_bytes.py
python3 -m unittest scripts.oracle.test_sign_det_json_bytes
```

This backend does not yet replace the existing `Codec.parse` or
`Dag.encodeBytes`. Their certificate-level byte laws still require integration
and a proved bridge for coefficient/context encodings. In particular, a
structured `ValueCodec.Lawful` law alone does not establish byte roundtrips:
a codec can distinguish two representations of the same JSON number even
though a JSON printer normalizes them. The existing `FastCheck.NumberForm`
counterexample remains applicable. No certificate-byte completeness claim
follows merely from the backend theorem.

String-prefix parsing scans only through the current quoted string, rather
than rescanning the whole remaining input for each string token. A proved
prefix-scan law preserves the universal byte roundtrip. The native corpus also
includes 3,000 empty strings, a 25,000-element flat array, a 12,000-character
string and a 4,096-digit integer. The oracle runs the driver with an 8 MiB
stack limit. These cases pass; they do not establish behavior at the existing
16 MiB certificate-byte ceiling. Non-tail recursion in strings, lexing and
array tails still needs assessment at that ceiling before production
integration. The existing certificate byte/depth/digit pre-scan must remain
in front of any replacement parser. The low-level decimal word readers accept
leading zeros; JSON token parsing separately rejects them.
