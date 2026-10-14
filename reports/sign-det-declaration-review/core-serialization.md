# Certificate serialization and recursive production

These individual assessments cover 149 named declarations in eleven modules.
Literal reconstruction, caller subject binding and independent arithmetic
replay retain separate contracts. The JSON encoding/decoding classes and
source fields are included; this remains partial computational review.

| Declaration | Assessment |
| --- | --- |
| `ValueCodec` | Two literal encoding/decoding operations; the type alone guarantees neither roundtrip nor mathematical validity. Both fields are documented. |
| `ValueCodec.nat` | Uses exact natural JSON scalar instances, rejecting other kinds and negative numbers. |
| `ValueCodec.rat` | Encodes the canonical numerator/positive denominator pair and rejects zero or noncanonical denominators instead of normalizing untrusted pairs. |
| `Codec.tuple` | Checks exact raw field count before constructing a fixed-size vector or performing positional reads. |
| `Codec.array` | Maps the supplied encoder over every element in literal order, including empty arrays. |
| `Codec.list` | Preserves the entire list through the same ordered array encoding. |
| `Codec.readArray` | Requires an array and reads each actual element in order, propagating decoder errors without filtering. |
| `Codec.readList` | Uses the actual array reader and preserves order and errors when returning a list. |
| `Codec.vector` | Checks actual input length against the declared dimension before decoding and verifies the resulting vector length. |
| `Codec.matrix` | Reads every integer row under both declared dimensions; no matrix identity or rank is asserted. |
| `Codec.encodeMatrix` | Encodes every integer matrix entry in row order, retaining both dimensioned traversals. |
| `Codec.index` | Accepts a natural literal only when strictly below the supplied bound; returns the exact bounded index. |
| `Codec.option` | Uses zero or one array entries to preserve absence/presence and the literal supplied value. |
| `Codec.readOption` | Rejects arrays with more than one entry; the supplied value reader still owns presence decoding. |
| `Codec.poly` | Encodes the existing increasing-exponent coefficient array without arithmetic or semantic normalization. |
| `Codec.readPoly` | Rejects any decoded vector changed by canonical polynomial construction, including trailing stored zeros; arithmetic validity remains separate. |
| `Codec.endpoint` | Retains signed infinity tags or the exact finite coefficient, without validating a root domain. |
| `Codec.readEndpoint` | Checks exact tag/field shape and delegates only the finite value; equal or reversed endpoints remain domain-checker obligations. |
| `Codec.Limits` | Three configurable byte, delimiter-depth and integer-digit bounds; these constrain decoding, not mathematical coefficient arithmetic. All fields are documented. |
| `Codec.forIn_data` | Proves the actual byte-array loop agrees with array iteration, including early exit, without boxing an extra native buffer. |
| `Codec.checkBytes` | Checks actual bytes, quoted/escaped string state, delimiter depth and integer digits before parsing. It is a lexical/resource precheck, not complete JSON syntax validation. |
| `Codec.parse` | Runs that precheck then the actual UTF-8/token/value parser; returns literal JSON or an error, without arithmetic evidence. |
| `Codec.decodePair` | Parses subject first and evidence second before invoking the supplied structured reader; its Type-valued result can be universe-polymorphic. |
| `Codec.parse_write` | Actual printer/parser roundtrip under only the stated precheck, with no parser-success premise or metric-completeness claim. |
| `Codec.decodePair_ok` | Substitutes the actual two accepted parse results before applying the unchanged structured reader. |
| `Codec.decodePair_error` | An error in the first record returns exactly that error without evaluating the evidence parser or reader. |
| `Codec.decodePair_write` | Composes both actual printer/parser laws and preserves the complete reader result, including reader rejection. |
| `ValueCodec.encodeBytes` | Uses the actual integer-only JSON byte printer on the supplied literal encoding. |
| `ValueCodec.decodeBytes` | Runs lexical policy and actual parsing before the supplied partial value decoder. |
| `ValueCodec.decode_encode_of` | A single-value literal roundtrip suffices for actual byte reconstruction under its precheck; no globally lawful decoder is assumed. |
| `ValueCodec.decode_encode` | Global literal law specializes that same actual byte reconstruction; multiple accepted spellings are not claimed canonical. |
| `Codec.descriptor` | Encodes all six raw selected-root fields, including ordered derivative indices/signs, not merely a polynomial/domain hash. |
| `Codec.readDescriptor` | Parses unchecked literal data with exact six-field shape; selected-root existence/uniqueness remains separate. |
| `Codec.readDescriptorBinding` | Requires complete raw equality after parsing; no root or coefficient semantics are inferred. |
| `Codec.readDescriptorBinding_checked` | Accepted binding identifies the exact parsed caller subject, including every literal field. |
| `Codec.readDescriptorBinding_of` | Actual successful parsing of the exact caller raw subject implies binding acceptance without extra root hypotheses. |
| `Codec.read_descriptor_of` | Roundtrip needs only actual context/head/finite-endpoint coverage, preserving derivative lists through existing scalar laws; no global partial-reader law. |
| `Codec.remainder` | Retains both supplied scales and the complete quotient polynomial; it does not compute a division witness. |
| `Codec.readRemainder` | Reads exactly those three fields without checking the division identity or positive scaling. |
| `Codec.terminal` | Retains the literal terminal scale and polynomial, including mathematically invalid witnesses. |
| `Codec.readTerminal` | Reads both literal terminal fields without asserting terminal-gcd correctness. |
| `Codec.chain` | Retains the full polynomial/degree lists, initial witness, ordered steps and optional terminal. |
| `Codec.readChain` | Checks exact five-field syntax and reads every supplied chain component; no replacement chain is produced. |
| `Codec.tarski` | Retains all twelve fields, both complete chains, full subject, endpoint signs, variations and claimed integer value. |
| `Codec.readTarski` | Parses all twelve fields literally; domain, recurrence, signs, variations and root-sum claims remain independent replay obligations. |
| `Codec.reductionStep` | Retains factor index, next polynomial and the complete supplied remainder witness. |
| `Codec.readReductionStep` | Checks factor index below actual arity before construction; arithmetic witnesses remain unchecked raw data. |
| `Codec.reduction` | Retains ordered reduction steps and the literal final polynomial. |
| `Codec.readReduction` | Reads every bounded-index step and final polynomial without proving reduction identities. |
| `Codec.preparation` | Retains the original ordered query-preprocessing step list. |
| `Codec.readPreparation` | Reads each bounded-index preprocessing step without recomputing original query reductions. |
| `Codec.read_remainder` | Global literal coefficient law reconstructs both scales and quotient, without arithmetic correctness hypotheses. |
| `Codec.read_terminal` | Global literal coefficient law reconstructs both terminal fields, including false terminal witnesses. |
| `Codec.read_chain` | Reconstructs the complete ordered chain, degrees, initial/step witnesses and optional terminal under a global coefficient roundtrip law. |
| `Codec.read_tarski` | Reconstructs all twelve literal certificate fields under coefficient/context roundtrip laws; no semantic acceptance premise. |
| `Codec.read_step` | Roundtrip requires the actual factor index below arity; no scale or polynomial identity is assumed. |
| `Codec.read_reduction` | Uses actual membership-wise factor-index bounds for every ordered step and retains the final polynomial. |
| `Codec.read_preparation` | Uses only each actual preprocessing step index bound and the coefficient roundtrip law. |
| `Codec.system` | Retains all six ordered system fields, including counts, moments, inverse entries and denominator; integer identities remain replay obligations. |
| `Codec.readSystem` | Checks every row/column word arity and all size-indexed vectors/matrix before constructing raw system data. |
| `Codec.basis` | Retains claimed rank, ordered bounded indices, denominator and complete inverse block without asserting rank correctness. |
| `Codec.readBasis` | Rejects rank above either supplied dimension before rank-sized reads, and validates every Fin index; nonsingularity is not assumed. |
| `Codec.node` | Retains all eleven literal fields, every moment and reduction witness, optional preparation and complete basis. |
| `Codec.readNode` | Uses one decoded size for all fields; computes rank column dimension from actual positive counts rather than a separate unbound input. |
| `Codec.bindings` | Checks full context/head/endpoints for the node and every moment, using literal equality rather than coefficient interpretation. |
| `Codec.bindings_eq` | Exact bidirectional binding criterion exposes all four node equalities and every stored moment equality, without arithmetic acceptance; reused in the existing false-graph control. |
| `Codec.read_vector_of` | Only actual vector-entry coverage is required; preserves the exact dimension and entry order through the real decoder. |
| `Codec.read_sizedList` | Scalar roundtrip plus the actual list length reconstructs the whole ordered list through a dimensioned vector reader. |
| `Codec.read_system` | All six literal fields reconstruct when actual row/column words have declared arity; no inverse identity premise. |
| `Codec.read_basis` | Actual rank bounds and bounded index vectors suffice for literal basis reconstruction; no mathematical rank premise. |
| `Codec.read_option_of` | Only actual present value coverage is needed; absence roundtrips without calling the value decoder. |
| `Codec.read_node` | All eleven fields reconstruct under global codecs and actual parser-shape bounds; arithmetic identities, root counts and support completeness are not premises. |
| `ValueCodec.Lawful` | Requires encode/decode preservation for every literal value; does not include byte syntax or independent replay soundness. |
| `Codec.read_nat` | Exact natural scalar encode/decode law; appropriate simp normalization. |
| `Codec.read_int` | Exact integer scalar encode/decode law; appropriate simp normalization. |
| `ValueCodec.nat_lawful` | Provides global literal law for the actual natural value codec. |
| `ValueCodec.rat_lawful` | Provides global literal law for canonical rational pairs using positive denominators and mkRat_self. |
| `ValueCodec.Refines` | Every accepted strict read transfers exactly its value to the complete reader; no equality of refusal domains is assumed. |
| `Codec.list_refines` | Private induction follows actual ordered traversal and retains every accepted value under pointwise successful-read refinement. |
| `Codec.readArray_refines` | Successful strict array reads transfer the complete ordered array, preserving literal values; rejected strict inputs need not reject in the complete reader. |
| `Codec.readPoly_refines` | Transfers exact accepted coefficient arrays through the same polynomial canonicality guard; no semantic coefficient equivalence is substituted. |
| `Codec.read_array` | Global element roundtrip law reconstructs the complete ordered array, including empty arrays. |
| `Codec.read_list` | Global element roundtrip law reconstructs every ordered list element via the actual array reader. |
| `Codec.read_list_of` | Only supplied list members must roundtrip, supporting partial readers and bounded indices. |
| `Codec.read_array_of` | Only actual array members must roundtrip; transfers exact list/array representations without strengthening to a global law. |
| `Codec.read_vector` | Global element law reconstructs exact dimensioned vectors through actual shape checks. |
| `Codec.read_option` | Global element law reconstructs presence/absence and the literal present value. |
| `Codec.read_poly` | Global coefficient law reconstructs the canonical stored polynomial vector without interpreting its arithmetic. |
| `Codec.read_poly_of` | Only coefficients in the actual canonical polynomial array need coverage. |
| `Codec.read_endpoint` | Global coefficient law reconstructs both infinities and finite coefficients; no interval-validity premise. |
| `Codec.read_endpoint_of` | Only the actual finite coefficient needs coverage; infinity cases have no coefficient requirement. |
| `Codec.read_jsonArray` | Standard JSON array instances share the same ordered encoder/decoder traversal. |
| `Codec.read_index` | A supplied Fin value roundtrips exactly using its actual strict bound. |
| `Codec.read_matrix` | Actual integer matrix printer/reader preserves both dimensions and every row, including zero dimensions. |
| `Codec.Json` | Alias for the proved integer-only recursive JSON value representation, retaining ordered object fields. |
| `Codec.Json.Values.ofList` | Constructs every literal array element in list order, preserving repetition. |
| `Codec.Json.Values.toList` | Reference structural traversal returns all elements in order, including empty arrays. |
| `Codec.Json.Values.pushArray` | Actual width loop appends every literal element to the supplied prefix array. |
| `Codec.Json.Values.toArray` | Starts that width loop at the empty array; no element filtering or reordering. |
| `Codec.Json.Values.toList_ofList` | Identity from list construction followed by reference traversal; appropriate simp normalization. |
| `Codec.Json.Values.ofList_toList` | Identity from reference traversal followed by reconstruction; appropriate simp normalization. |
| `Codec.Json.Values.pushArray_eq` | Private structural induction identifies the actual width loop with prefix append of the entire reference list. |
| `Codec.Json.Values.toArray_eq` | Actual array conversion agrees with the complete reference list representation. |
| `Codec.Json.Values.toListLoop` | Actual list conversion through the native width loop and array representation. |
| `Codec.Json.Values.toList_impl` | Proved csimp replacement preserves exact reference list semantics while changing only compiled width traversal. |
| `Codec.Json.arr` | Constructs literal recursive array values preserving all ordered elements. |
| `Codec.Json.Value.getArr?` | Accepts only arrays and preserves every element; other JSON kinds return the named error. |
| `Codec.Json.Value.getInt?` | Accepts only literal integer number values; no Boolean/string coercion. |
| `Codec.Json.Value.getNat?` | Accepts only nonnegative integer number values; negative integers and other kinds reject. |
| `Codec.Json.Value.getBool?` | Accepts only literal Boolean values, without numeric coercion. |
| `Codec.Json.Value.getStr?` | Accepts only literal strings, without numeric or key coercion. |
| `Codec.Json.getArr_arr` | Actual array construction and extraction agree on every ordered element; appropriate simp normalization. |
| `Codec.Json.To` | Public type-specific literal encoding class; its one field guarantees no roundtrip or mathematical validity. |
| `Codec.Json.From` | Public partial decoding class; its one field supplies no global law or mathematical validation. |
| `Codec.Json.of` | Delegates to the actual supplied To dictionary; no unmentioned encoding convention is imposed. |
| `Codec.Json.decode` | Delegates to the actual supplied From dictionary, retaining full errors and values. |
| `Codec.Json.of_array` | The actual array instance maps the supplied element dictionary in literal order. |
| `Codec.Json.of_list` | The actual list instance uses the same ordered array construction. |
| `Codec.Json.read_of_nat` | Actual natural scalar dictionaries roundtrip exactly; appropriate simp normalization. |
| `Codec.Json.read_of_int` | Actual integer scalar dictionaries roundtrip exactly; appropriate simp normalization. |
| `Codec.Json.read_of_bool` | Actual Boolean scalar dictionaries roundtrip exactly; appropriate simp normalization. |
| `Codec.Json.read_of_string` | Actual string scalar dictionaries roundtrip exactly; appropriate simp normalization. |
| `Codec.entry` | Retains the complete literal node and the ordered optional child pair. |
| `Codec.graph` | Version-one literal root/entry encoding has exact positional field counts; malformed data can still be printed. |
| `Codec.readChildren` | Requires both supplied child indices strictly below the actual earlier-entry count, preserving left/right order and absence. |
| `Codec.readEntry` | Checks exact pair shape, earlier children and full node/moment subject bindings before returning raw entry data. |
| `Codec.readGraph` | Checks version, existing root, all entries and their actual ordered earlier counts; unreachable entries are parsed and bound too. |
| `Codec.decodeGraph` | Runs actual lexical policy, UTF-8/JSON parsing and complete raw-graph reading; no arithmetic replay is claimed. |
| `Dag.encodeBytes` | Prints all literal graph fields without running a producer or validating mathematical evidence. |
| `Dag.decodeBytes` | Actual parsing followed by independent replay returns a tree with erased checker acceptance; parse/refusal errors are not mathematical nonexistence. |
| `Dag.decodeDescriptor` | Replays against the complete supplied raw descriptor, deriving derivative queries from actual head/indices; serialized count-one assertions are not trusted. |
| `Dag.decodeSigns` | Checks exactly the caller sign vector using supplied joint graph evidence; no selected-sign producer fills missing evidence. |
| `Dag.decodeSigns_evidence` | Arbitrary accepted bytes identify the actual parsed graph, exact selected evidence and unchanged claimed signs, with no printer-success assumption. |
| `Dag.decodeBytes_sign_congr` | Finite sign agreement on every actual decoded graph operand preserves exact parse/replay errors and literal returned tree values. |
| `Dag.decodeSigns_sign_congr` | Finite stored-operand agreement and equal raw descriptor identity preserve exact errors, sign vector and literal evidence; validated proofs may differ. |
| `Dag.decodeDescriptor_sign_congr` | Finite stored-operand agreement preserves raw selected-root identity and supplied evidence, including exact refusal errors. |
| `Dag.decodeDescriptor_raw` | Every accepted descriptor byte read retains all original raw fields, including derivative indices and signs. |
| `Dag.decode_replays` | Arbitrary accepted bytes identify the exact parsed graph and actual replay result; no encoder or global codec law premise. |
| `BuildError` | Six internal construction diagnostics distinguish matrix shape, singularity, integrality, nonnegativity, literal system checking and replay from mathematical domain refusal. |
| `solveSystem` | Computes the actual rational inverse and counts, checks integrality/nonnegativity, clears all inverse denominators together and independently checks the ordered integer identity. |
| `solveScaled` | Uses the supplied integer inverse and denominator; rejects zero denominator, nondivisible counts, negative counts or a failed independent system check. |
| `useReduction` | Requires both the caller reduced flag and positive head degree; nonzero constant domains retain their separate unreduced path. |
| `nodePreparation` | Reuses supplied preprocessing only on that reduction path, otherwise constructs it from the actual original head/queries or returns none. |
| `nodeReduction` | Builds each actual ordered row reduction under exactly the same decision; no mathematical field instance is assumed on storage. |
| `buildNode` | Checks row/column counts, exponent/sign alphabets, arity and distinct columns before actual prepared moments and solving. Optional witnesses and preprocessing are ultimately authenticated by buildPrepared replay. |
| `parentInverse` | Transports the actual child integer adjugate tensor along the proved ordered-row length equality; no independent parent inverse computation is substituted. |
| `buildTreeFrom` | Recurses on actual query length with balanced ordered take/drop, slices preprocessing, and combines retained child supports/inverses. Length<=1 uses leaf support; no fuel cap or full ternary internal fallback. |
| `buildTree` | Constructs preprocessing once for the original query list and passes it into the balanced traversal. |
| `buildPrepared` | Runs the actual producer and independent literal replay before returning a subtype carrying acceptance. Arbitrary storage operations may fail; lawful totality and root semantics remain companion proofs. |

The seven fields of ValueCodec, Limits and the JSON To/From classes are
individually documented. Standard scalar/array/list JSON instances preserve
only their stated literal representations. BuildError's six constructors and
its derived equality/Repr instances are separately reviewed and documented.
The existing FastCheck false-graph roundtrip reuses bindings_eq; reconstructing
that graph does not validate its arithmetic. No producer algorithm changes.
