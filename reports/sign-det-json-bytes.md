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
unpaired surrogates and invalid UTF-8. Python's standard parser checks both the printed values and an independent
constructor inspection of the parsed Lean value, retaining object fields and
duplicates with
explicit rejection of noninteger numbers and nonscalar
Unicode strings. Ten oracle tests include rejection of incorrect answers, Boolean/integer
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

String-prefix parsing scans only through the current quoted string. The byte
lexer, string scanner/reader, structural parser and token producer use verified
accumulator loops: their outputs are proved equal to the original finite
recursive definitions. Native recursion follows array/object nesting rather
than width or string length. The universal byte theorem checks these actual
loops in the ordinary kernel.

The native subprocess environment disables Lean's separate main thread and
sets `LEAN_STACK_SIZE_KB=8192` alongside the 8 MiB OS stack limit. The independent
324-case corpus runs with that enforced stack limit. It includes 3,000
empty strings, a 25,000-element array, a 12,000-character string and a
4,096-digit integer. A separate file-mode capacity check avoids the line
transport and retains the existing lexical byte/depth/digit checks:

```sh
python3 scripts/oracle/sign_det_json_stress.py
```

With the same 8 MiB stack, the compiled parser/printer handles a quoted ASCII
string occupying 16 MiB, a million escaped characters, a two-million-element array, 300,000
object fields with duplicate keys, nesting depth 128 and a 4,096-digit integer.
Python independently compares the input and output values of the parse/print
composition; file mode does not inspect constructors independently. The
324-case line-mode oracle separately does that inspection. The CI oracle runs smaller probes (a 4 MiB string, a million array
elements, a million object fields, 500,000 escaped characters and depth 128) plus byte/depth/digit rejection probes.
Each rejection checks its diagnostic and that no output file was produced.
These are capacity
observations, not timing/scaling evidence or exhaustive coverage of every
input permitted by the limits. They do not exercise derived structural
equality or `Repr` on wide values, or the line driver's recursive constructor
inspection and equality. Depth allowances larger than 128 are unvalidated. The character list, token list and result
still increase memory use; token concatenation can copy data at each nesting
level. The printer adds whitespace and may produce more bytes than the input,
including 16 MiB plus one byte for the ceiling-size string. The escaped-string
probe grows from 2,000,002 to 6,000,003 bytes; arrays grow from 4,000,001 to
8,000,002 bytes; duplicate object fields grow from 1,800,001 to 3,000,002 bytes.
The driver also checks the printed output against the default lexical guard;
the ceiling-size string's extra byte is rejected. A larger output can
require a larger decoding byte allowance. Final certificate integration must
account for that expansion and provide a guarded public decoding entry point.
The low-level `Json.readBytes` is intentionally unguarded; certificate consumers
must use `Codec.checkBytes` first. These probes do not measure peak memory;
character-list storage alone can require hundreds of megabytes near the byte
ceiling. Combined high depth and width and complete memory attribution remain
integration checks. The low-level decimal word readers accept leading
zeros; JSON token parsing separately rejects them.

Stack setup matters for Lean native executables: the v4.35.0-rc3 runtime runs
`main` on a separate thread by default, with a 1 GiB thread stack on 64-bit
hosts. An OS `RLIMIT_STACK` alone does not constrain that explicit thread
stack. Capacity observations made with the earlier OS-only setup are retained
as value/capacity checks, but do not establish an 8 MiB stack bound. The corrected
oracle environment sets `LEAN_MAIN_USE_THREAD=0` and `LEAN_STACK_SIZE_KB=8192`
before launching the executable.
