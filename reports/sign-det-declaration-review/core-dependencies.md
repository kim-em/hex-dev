# Coefficient conversion and dependency envelopes

These assessments cover 34 named declarations in three computational modules
and sixteen structure fields. The local reader's dependent result type owns
mathematical facts; structural reference and literal roundtrip laws do not
assert that arbitrary packet readers are sound. This remains partial API
review and does not establish whole-library phase acceptance.

| Declaration | Assessment |
| --- | --- |
| `RawDescriptor.map` | Maps the literal head and endpoints with zero reflection, keeps the partial derivative indices/signs, and supplies a new literal context. No accepted evidence is copied. |
| `RawDescriptor.map_wellFormed` | Zero reflection preserves head degree and hence the exact Boolean shape result; no arithmetic-preservation or sign-law premise is claimed. |
| `Descriptor.convert` | Calls the actual descriptor builder on mapped raw inputs. Arbitrary conversion can fail; old replay proofs cannot authenticate the target representation. |
| `Dependencies.Reference` | Stores index, coefficient level and complete literal JSON subject; equality is not reduced to a context hash. |
| `Dependencies.Entry` | Stores level, subject, payload and ordered child references. Its type alone enforces no acyclicity, lower level or arithmetic validity. |
| `Dependencies.Graph` | Stores entries and ordered roots, including shared and unreachable packets; validity is separate. |
| `Dependencies.Reference.matches` | Tests exact level and subject equality, without checking the referenced index or interpreting either packet. |
| `Dependencies.Reference.check` | Checks index existence and exact level/subject binding against the literal referenced entry. |
| `Dependencies.Graph.check` | Checks every root and every stored child. Child indices point backward and levels strictly decrease; unreachable packets remain checked. |
| `Dependencies.Checked` | Retains a literal packet and a result of the caller-supplied dependent type. Mathematical acceptance depends on what that type and reader actually establish. |
| `Dependencies.children?` | Reads declared children from the accepted memo in order, requires exact subject/level matching and a lower level; missing or stale references reject before local reading. |
| `Dependencies.step` | Invokes the supplied reader only after child lookup succeeds, and retains its exact dependent result with the supplied entry. Coverage is still the local reader contract. |
| `Dependencies.Graph.validate?` | Rejects structural failures before folding all packets through the actual reader from an empty memo; does not prove the reader sound. |
| `Dependencies.Reference.check_eq` | Bidirectional success criterion gives the exact existing index, level and complete subject; no semantic premise is hidden. |
| `Dependencies.Graph.check_children` | Extracts all backward-index, lower-level and literal-reference conditions for every declared child of every stored entry. |
| `Dependencies.Graph.check_roots` | Extracts index existence and exact level/subject binding for each declared result; repeated roots are allowed. |
| `Dependencies.step_entry` | Accepted local reading returns the exact supplied packet, regardless of the reader result type. |
| `Dependencies.fold_entries` | Private actual-fold induction preserves old memo packets followed by all supplied entries in order; uses step_entry rather than an independent reconstruction. |
| `Dependencies.Graph.validate_entries` | Actual accepted validation returns exactly the full literal entry array, including payloads, children and unreachable entries. |
| `Dependencies.Graph.validate_check` | Accepted typed validation implies its prior structural guard; no semantic reader soundness is inferred. |
| `Dependencies.Reference.codec` | Integer-only JSON tuple retains index, level and complete literal subject; decoder performs syntax/type checks rather than graph validity. |
| `Dependencies.Reference.codec_lawful` | Literal tuple print/read roundtrip for every reference, including invalid indices. |
| `Dependencies.Entry.codec` | Retains level, subject, payload and ordered children literally; parsing supplies raw packets without acceptance. |
| `Dependencies.Entry.codec_lawful` | Literal packet tuple roundtrip uses the reference codec law for every child, with no graph premise. |
| `Dependencies.Graph.codec` | Version-one tuple retains all entries and roots in wire order; unsupported version and malformed tuples reject independently of arithmetic. |
| `Dependencies.Graph.codec_lawful` | Literal envelope print/read roundtrip for arbitrary raw graphs, including structurally invalid ones. |
| `Dependencies.Graph.codec_bytes` | Actual byte parser reconstructs the whole literal graph from printer output under the lexical/resource precheck, without assuming parser success or arithmetic validity. |
| `Dependencies.Decoded` | Stores the parsed graph, typed memo and proofs of ordered requested bindings, structural validity and exact entry retention. It does not require an acceptance derivation for the reader itself. |
| `Dependencies.Decoded.memo_size` | Literal memo-entry equality gives exactly one position per stored packet, including unused packets; existing selection proofs reuse the length law. |
| `Dependencies.Decoded.results` | Selects stored memo values in root order using proved structural bounds and exact memo-entry equality; repeated roots reuse values and cannot fail. |
| `Dependencies.Decoded.results_bound` | Selected memo results have precisely the requested ordered levels and full literal subjects. |
| `Dependencies.Decoded.results_size` | Selected result count equals the requested binding count, including empty and repeated roots. |
| `Dependencies.Graph.decode` | Parses actual bytes, compares complete ordered caller bindings before any local reader, then validates all packets and stores actual accepted memo. No missing evidence is produced. |
| `Dependencies.Graph.decode_encode` | Composes actual printer/parser with the supplied accepted reader result; returns exactly that memo under only the byte precheck and actual validation premise. |


The literal equality/Repr instances preserve complete reference, packet and
root data. Reference fields `index`, `level`, `subject`; entry fields `level`,
`subject`, `payload`, `children`; graph fields `entries`, `roots`; checked fields
`entry`, `value`; and decoded fields `graph`, `memo`, `bound`, `structural`,
`entries` are individually documented. The existing dependency fixture supplies
actual nested sign facts and adversarial packet controls; it is reused here.
