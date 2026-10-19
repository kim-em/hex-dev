# Completion and full-order API review

Names are relative to `Hex.SignDet`. This assessment treats all 17 named
production declarations in `Complete` and its two source-written completion
fields. The computational guards, producer branches and existing theorem
statements are preserved. It remains partial Phase-6 review.

| Declaration | API and proof assessment |
| --- | --- |
| `Thom.select` | Ordered one-based selection returns `none` for zero or missing slots; it invents no default sign. Empty selection succeeds with the empty word. |
| `Thom.select_full` | Valid index bounds identify the exact selected full-word values, preserving caller order and including empty selections. No realization premise is asserted. |
| `RawDescriptor.full` | Overwrites slots with canonical orders one through the native head degree and installs the supplied word; context, head and endpoints stay literal. It does not validate arbitrary signs. |
| `RawDescriptor.full_queries` | The reconstructed derivative queries are independent of the installed sign word; the head and canonical slots determine them. |
| `RawDescriptor.full_queries_length` | Gives exactly one formal derivative query for each positive order through the head's degree. |
| `RawDescriptor.full_wellFormed` | Positive degree, exact word length and ternary entries imply shape acceptance; canonical slots supply distinctness and range. It establishes no root realization. |
| `RawDescriptor.completes` | Checks all four literal context/domain bindings, canonical full slots, and exact restriction to the old selected word. Raw inputs alone provide no count-one evidence. |
| `RawDescriptor.completes_iff` | Full bidirectional characterization exposes every binding and the successful restriction. Both arguments are explicit; the theorem is not a simp rule and does not unfold the finite selection. |
| `Completion` | The target has its own checked descriptor; `agrees` retains exact source bindings and its word restriction. Ordinary unique-root preservation is a companion conclusion under semantic laws. |
| `Completion.bindings` | Uses the full characterization to project every literal binding and restriction, preserving the old statement. |
| `Descriptor.fullOrder` | Requires the same literal head and canonical full slots for both descriptors before comparing sign words. Different heads are refused, even if their word strings coincide. |
| `Descriptor.fullOrder_iff` | Exact success equivalence retains both applicability guards and the finite comparator equation. It does not equate this syntactic order with ordinary-root order. |
| `Descriptor.fullOrder_eq` | Existing forward API is the forward direction of the full equivalence; current producer and semantic consumers retain their statements. |
| `Descriptor.buildCompletion` | Prepares the exact source domain, builds the actual full derivative table, filters by the source restriction and requires exactly one count-one candidate with accepted replay/agreement. Internal diagnostics stay distinct from mathematical producer totality. |
| `Descriptor.buildCompletion_ofTable` | Exact preparation, actual prepared construction and the singleton filtered row discharge the executed completion branches. It authenticates that producer output rather than arbitrary supplied table data. |
| `Descriptor.complete` | Returns the successful completion; a diagnostic error retains the source, whose slots may still be partial. The companion excludes fallback under lawful coefficient interpretations. |
| `Descriptor.complete_ofBuild` | Agreement with an actual successful builder identifies the returned target descriptor without claiming unconditional builder success. |

Both completion fields have source documentation. The public constructor
requires an already checked target and the exact agreement proof. The new
characterizations are used by the existing binding/comparison projections. The
producer proof also uses the reverse completion law to establish agreement.
Native coefficient operations, sign callbacks, optional ordering diagnostics and
the panic fallback remain unchanged. No companion realization or producer proof
is replaced by successful examples.

The source bindings retain the reviewed module, checker, existing conformance
and manual. The conformance suite exercises partial and reordered selections,
negative heads, missing slots, wrong signs and changed context/head/endpoints.
Both new equivalences and both changed binding/comparison projections have
guards for their observed ordinary-kernel axiom sets.
Whole-library usage/lints and the declared computational comparison remain
separate Phase-6 requirements.
No phase, computational performance or distribution eligibility is claimed.
