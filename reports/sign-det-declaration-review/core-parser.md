# Decimal, Unicode, token and recursive JSON parsing

These individual assessments cover all 105 named declarations in the four
parser modules. Reference and native paths are related by exact Lean proofs,
including refusal and insufficient fuel. Byte-resource admission remains the
separate certificate policy; these helpers establish no arithmetic validity.

| Declaration | Assessment |
| --- | --- |
| `Codec.Decimal.readDigits` | Accepts nonempty all-digit text and computes the actual base-ten value; leading-zero JSON restrictions belong to Token.readNumber, not this helper. |
| `Codec.Decimal.readNat` | Validates whole UTF-8 input before the actual digit reader; not a complete JSON-number lexer. |
| `Codec.Decimal.readDigits_repr` | Every natural decimal printer output is nonempty, all digits and reconstructs the exact value; no finite fixture restriction. |
| `Codec.Decimal.readWord` | Consumes exactly the initial digit word and preserves all later characters; an empty prefix rejects. |
| `Codec.Decimal.readWord_repr` | Actual printed digits reconstruct the number and preserve any suffix whose digit prefix is empty. |
| `Codec.Decimal.fromUTF8_toUTF8` | The actual validated UTF-8 conversion preserves every complete original string. |
| `Codec.Decimal.readNat_repr` | Actual natural decimal byte printer/reader roundtrip, without a parser-success premise. |
| `Codec.Decimal.readIntText` | Permits an optional minus and nonempty digit word, rejecting plus/fraction/exponent syntax; JSON leading zeros remain a lexer obligation. |
| `Codec.Decimal.readInt` | Runs actual UTF-8 validation before signed digit reading; it does not authenticate a coefficient or certificate. |
| `Codec.Decimal.head_repr_ne_minus` | Private decimal-printer digit argument excludes a minus at the head of a natural representation. |
| `Codec.Decimal.readIntText_nat` | Private actual unsigned-decimal read agrees with Int.ofNat, without assuming caller syntax success. |
| `Codec.Decimal.readInt_repr` | Actual signed integer decimal printer/reader preserves both Int constructors and arbitrary magnitudes. |
| `Codec.Decimal.readInt_toString` | Standard toString specializes the same actual signed-integer byte roundtrip. |
| `Codec.Str.hex` | Accepts decimal and both-case hexadecimal letters only, returning the exact value below sixteen. |
| `Codec.Str.hex4` | Combines four actual accepted hexadecimal digits with their positional base-sixteen weights. |
| `Codec.Str.readEscape` | Checks JSON simple escapes and four-digit Unicode; combines valid high/low surrogate pairs, rejects lone or malformed pairs, and retains the suffix. |
| `Codec.Str.writeChar` | Escapes quotes/backslashes/control scalars and preserves other actual Unicode scalar characters. |
| `Codec.Str.writeBody` | Maps actual escaping over every character in original order, without adding outer quotes. |
| `Codec.Str.readBody` | Fuel-bounded reference parser rejects raw controls, malformed escapes, missing closing quote and exhaustion; retains the suffix after closure. |
| `Codec.Str.readBodyLoop` | Accumulator parser preserves the same success/refusal conditions while reversing the accumulated prefix exactly once. |
| `Codec.Str.readBodyLoop_eq` | Private induction proves exact accumulator/reference equality for arbitrary prefixes, inputs and fuel, including failures. |
| `Codec.Str.hex_digit` | Private finite hexadecimal digit proof covers every value below sixteen. |
| `Codec.Str.hex4_control` | Private positional arithmetic proof reconstructs each control scalar below thirty-two. |
| `Codec.Str.readEscape_control` | The actual emitted control escape decodes precisely that scalar and leaves an arbitrary suffix untouched. |
| `Codec.Str.readBody_char` | Private actual emitted-character read transfers the remaining body result for quotes, backslashes, controls and ordinary scalars. |
| `Codec.Str.readBody_write` | A sufficient decoded-character fuel bound reconstructs the whole emitted body and retains the arbitrary following suffix. |
| `Codec.Str.writeChar_length` | Private case split establishes every encoded scalar contributes at least one character. |
| `Codec.Str.writeBody_length` | Private actual traversal establishes output-character count bounds original body length. |
| `Codec.Str.write` | Produces the complete quoted JSON string using actual escaping of every scalar. |
| `Codec.Str.scanBody` | Reference quoted-prefix length stops at the first unescaped quote and skips escaped characters; it is not full escape validation. |
| `Codec.Str.scanLoop` | Actual accumulator scan counts the same quoted prefix; subsequent suffix strings are not scanned by this invocation. |
| `Codec.Str.scanLoop_eq` | Private length-decreasing proof transfers exact reference prefix count through arbitrary accumulator values. |
| `Codec.Str.digit_not_delimiter` | Private hexadecimal-digit proof excludes quote/backslash delimiter values used in control escapes. |
| `Codec.Str.scanBody_write` | The scan consumes exactly the emitted body and closing quote, independently of the arbitrary later suffix. |
| `Codec.Str.readBodyLoop_spec` | Public exact native/reference agreement covers malformed input and insufficient fuel, not just emitted strings. |
| `Codec.Str.scanLoop_spec` | Public exact zero-accumulator scan agreement; it makes no syntax-validation claim. |
| `Codec.Str.readPrefix` | Uses actual prefix scan as fuel, returns the decoded string and entire untouched suffix, and rejects a missing initial quote. |
| `Codec.Str.readPrefix_write` | Actual quoted printer/prefix reader preserves every Unicode string and arbitrary following characters. |
| `Codec.Str.writeBytes` | Uses actual quoted escaping then UTF-8 encoding of the complete result. |
| `Codec.Str.readBytes` | Requires valid whole UTF-8 and empty character suffix after the quoted prefix; trailing bytes reject. |
| `Codec.Str.readBytes_write` | Every actual emitted Unicode string byte record reconstructs exactly, with no assumed parser-success or resource policy. |
| `Codec.Token` | Integer-only token constructors retain literal signed integers and strings; lexical tokens alone certify no JSON structure or arithmetic. |
| `Codec.Token.write` | Prints each actual token spelling, using signed decimal and actual quoted Unicode strings. |
| `Codec.Token.readNumber` | Compares the complete digit word with canonical printer spelling, rejecting leading zeroes while preserving later characters; the surrounding lexer also accepts -0 and whitespace, so accepted bytes need not be canonical. |
| `Codec.Token.read` | Reads one literal token and retains its suffix; whitespace handling and whole-stream/JSON structure checking are separate. |
| `Codec.Token.emit` | Adds one actual separator space after each token to prevent numeric/keyword concatenation in reconstruction proofs. |
| `Codec.Token.chars` | Structural character printer preserves literal token values without reparsing emitted integer text. |
| `Codec.Token.emit_eq_chars` | Public exact equality of the two printers covers every token constructor; no byte allocation/timing conclusion follows. |
| `Codec.Token.repr_digits` | Private decimal-printer membership proof covers every digit character of every natural value. |
| `Codec.Token.repr_head` | Private nonempty-printer proof establishes a digit head even with an arbitrary following suffix. |
| `Codec.Token.readNumber_repr` | Private actual digit-token read consumes precisely the printer word before its separator. |
| `Codec.Token.read_emit` | Every actual emitted token reconstructs literally and leaves separator plus arbitrary later characters untouched. |
| `Codec.Token.digit_not_space` | Private digit predicate excludes every supported separator whitespace character. |
| `Codec.Token.repr_dropSpace` | Private whitespace removal leaves a printed natural prefix and arbitrary suffix unchanged. |
| `Codec.Token.dropSpace_emit` | Every token printer starts with a non-whitespace character, so dropping whitespace preserves the whole emitted suffix. |
| `Codec.Token.lex` | Fuel-bounded reference lexer reads every actual token in order and rejects failures/exhaustion; it does not check JSON delimiter grammar. |
| `Codec.Token.writeTokens` | Concatenates every actual separated token in original order, including empty streams. |
| `Codec.Token.lex_space` | Private reference-lexer equality removes one leading separator at the same fuel. |
| `Codec.Token.lex_writeTokens` | Sufficient token fuel reconstructs the complete emitted token stream through actual reference lexing. |
| `Codec.Token.writeTokens_length` | Private structural induction bounds token count by actual emitted character count. |
| `Codec.Token.lexLoop` | Actual accumulator lexer retains all token order and reference refusal branches while traversing token width iteratively. |
| `Codec.Token.lexLoop_eq` | Private induction proves exact accumulator/reference agreement for arbitrary inputs, prefixes and fuel, including rejection. |
| `Codec.Token.lexLoop_spec` | Public exact zero-prefix native/reference agreement applies to malformed streams and insufficient fuel. |
| `Codec.Token.readBytes` | Validates UTF-8 and sets lexer fuel from actual character count; no byte-size/depth policy is imposed here. |
| `Codec.Token.writeBytes` | Prints the actual complete separated stream into UTF-8 bytes. |
| `Codec.Token.readBytes_write` | The actual byte lexer reconstructs every emitted token stream, signed integers and Unicode included; no parser-success premise. |
| `Codec.Json.Value` | Mutual finite JSON data includes null, Boolean, integer, Unicode string, arrays and literal ordered object fields; equality/Repr derive from complete data. |
| `Codec.Json.Values` | Recursive arrays preserve empty/nonempty cases, literal element order and repetitions. |
| `Codec.Json.Fields` | Recursive object fields preserve original key/value order and duplicate keys; they are not a canonical map. |
| `Codec.Json.Value.hash` | Constructor-tagged literal hash includes nested contents; collisions are possible and hashes confer no authenticity. |
| `Codec.Json.Values.hash` | Actual ordered accumulator includes every array value without replacing equality checks. |
| `Codec.Json.Fields.hash` | Actual ordered accumulator includes every literal key/value pair, including duplicate keys. |
| `Codec.Json.Value.tokens` | Complete reference token production preserves every literal constructor and nested value. |
| `Codec.Json.Values.tokens` | Ordered array-body tokens omit a trailing comma; empty arrays produce no body tokens. |
| `Codec.Json.Fields.tokens` | Ordered literal key/colon/value tokens preserve duplicate keys and omit a trailing comma. |
| `Codec.Json.Value.tokensLoop` | Actual value token producer delegates width traversal to accumulators, preserving nested recursion. |
| `Codec.Json.Values.tokensLoop` | Actual array-body accumulator preserves literal value order, commas and supplied reversed prefix. |
| `Codec.Json.Fields.tokensLoop` | Actual object-body accumulator preserves all key/value order, commas and reversed prefix. |
| `Codec.Json.Value.tokensLoop_eq` | Private mutual proof identifies actual token production with the complete reference for every value. |
| `Codec.Json.Values.tokensLoop_eq` | Private mutual proof preserves reversed prefix plus exact ordered reference array tokens. |
| `Codec.Json.Fields.tokensLoop_eq` | Private mutual proof preserves reversed prefix plus exact ordered reference object tokens. |
| `Codec.Json.read` | Reference value parser is fuel-bounded and returns both literal value and suffix; malformed delimiters or unsupported tokens reject. |
| `Codec.Json.readValues` | Reference array parser allows emptiness only initially and requires a value after commas; preserves the suffix after closing delimiter. |
| `Codec.Json.readFields` | Reference object parser requires string keys/colons, forbids trailing commas and preserves every literal field and suffix. |
| `Codec.Json.Values.prepend` | Restores accumulated values onto the exact supplied tail in literal order. |
| `Codec.Json.Fields.prepend` | Restores accumulated key/value fields onto the exact tail, retaining duplicate keys and order. |
| `Codec.Json.readLoop` | Actual value parser retains nested recursion while using width accumulators; malformed and fuel cases are identical to reference. |
| `Codec.Json.readValuesLoop` | Actual array-body accumulator reconstructs ordered values and preserves the tail; initial emptiness and comma rules remain enforced. |
| `Codec.Json.readFieldsLoop` | Actual object-body accumulator reconstructs ordered duplicate-capable fields with exact key/colon/terminator rules. |
| `Codec.Json.readLoop_all` | Private joint fuel induction proves exact native/reference equality for arbitrary value, array and object inputs/prefixes, including all failure branches. |
| `Codec.Json.readLoop_spec` | Public exact native/reference agreement for every token stream and fuel; it assumes neither syntax success nor printer provenance. |
| `Codec.Json.Value.tokensLoop_spec` | Public exact native/reference token-production equality for every literal finite value. |
| `Codec.Json.Value.rank` | Structural parser-fuel bound accounts for both array/object width and nesting, independently of integer magnitudes and Unicode lengths. |
| `Codec.Json.Values.rank` | Array-body rank is one plus maximum of head-value and tail rank; it measures sufficient reference parser recursion, not wall time. |
| `Codec.Json.Fields.rank` | Object-body rank is one plus maximum of value and tail rank; key length does not affect this token-parser bound. |
| `Codec.Json.read_all` | Private joint fuel induction reconstructs all emitted values/bodies with arbitrary suffixes and actual structural-rank conditions. |
| `Codec.Json.read_tokens` | Public reference parser reconstructs all emitted value tokens and arbitrary suffix under its sufficient fuel bound. |
| `Codec.Json.readLoop_tokens` | Public native parser reconstructs actual emitted loop tokens and arbitrary suffix under the same structural-rank fuel bound; existing byte roundtrip uses it. |
| `Codec.Json.Value.rank_lt` | Private mutual proof bounds value rank strictly by complete reference token count. |
| `Codec.Json.Values.rank_le` | Private mutual proof bounds array-body rank by exact reference body token count. |
| `Codec.Json.Fields.rank_le` | Private mutual proof bounds object-body rank by exact reference body token count. |
| `Codec.Json.Value.writeBytes` | Uses the actual token-loop printer and UTF-8 byte emitter on the entire literal value. |
| `Codec.Json.readBytes` | Validates UTF-8/token grammar, parses the actual value using finite token-count fuel, and rejects trailing tokens. No byte/depth/digit policy; guarded certificate readers use checkBytes, while ReprFormat.readPacket deliberately accepts trusted printer text without that policy. |
| `Codec.Json.Value.writeBytes_toList` | Exact ordinary-kernel equality exposes the actual UTF-8 byte list through structural token characters, with no performance claim. |
| `Codec.Json.readBytes_write` | Actual complete byte reconstruction for every finite integer-only JSON value, arbitrary nesting/magnitude/Unicode included; no assumed successful parse. |

Token constructors are separately assessed: punctuation/delimiters and null
carry no payload; Boolean, integer and string tokens retain their literal
values. Value/Values/Fields equality and Repr instances cover complete recursive
data. Their three hash instances include ordered data but cannot authenticate
it or replace equality. Object-field order and duplicate keys are preserved.
