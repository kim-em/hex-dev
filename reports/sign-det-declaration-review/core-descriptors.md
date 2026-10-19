# Selected descriptor and Thom-vector API review

Names are relative to `Hex.SignDet`. This assessment treats all 46 named
production declarations in `Thom` and `Descriptor`, the raw equality instance,
nine source-written structure fields and the five descriptor-error constructors.
Raw inputs carry no validity proof. Shape acceptance and accepted literal replay
are separate obligations; neither a vector comparator nor an accepted finite
count alone establishes an ordinary-real root interpretation.

## Thom vectors and raw shape

The comparator declarations below are in namespace `Thom`; the other names
are in `Hex.SignDet`.

| Declaration | API and proof assessment |
| --- | --- |
| `RawDescriptor` | Unvalidated literal context/head/endpoints and caller-ordered derivative slots/signs. The six fields have source documentation. Shape and replay guards establish their later invariants. |
| `derivativesFrom` | Executes successive formal differentiation, preserving signs without monic normalization. Finite natural recursion includes the zero-length case. |
| `derivatives` | Requests the head's degree many derivatives; the final derivative is retained in this full list. |
| `derivativesFrom_length` | Exact recurrence length for any requested natural count, without a coefficient-field premise. |
| `RawDescriptor.wellFormed` | Checks positive degree, matching lengths, distinct one-based slots bounded by degree, and ternary signs. A partial raw selection need not include the highest derivative. |
| `RawDescriptor.wellFormed_iff` | Full bidirectional characterization of all five guards. Per-entry membership conditions ignore order; the stored query and sign lists retain it. The explicit theorem exposes these conditions without making conjunction expansion a global simp rule. |
| `RawDescriptor.wellFormed_bounds` | Extracts the checked bounds through the characterization; no unfolding of Boolean guard positions. |
| `RawDescriptor.queries` | Reconstructs actual derivative polynomials in the caller's selected order. Its zero default is excluded by shape bounds when used as a valid selection. |
| `RawDescriptor.wellFormed_length` | Names exact word/query length agreement using the full shape characterization. |
| `compareFrom` | Finite largest-differing-position recursion. A missing next slot, a zero common next sign, or different lengths can return `none`; no guessed root order follows. |
| `compareSigns` | Rejects empty/nonternary words before the finite comparator. It does not check polynomial, context or realization identity. |
| `compareFrom_self` | Unconditionally returns literal vector equality, including the empty list without the separate shape guards. |
| `compareFrom_eq` | Equality result implies identical words; sign-dependent strict branches cannot return equality for different entries. No cross-polynomial root identity is asserted. |
| `compareSigns_eq` | Guarded equality transfers the literal-vector conclusion, without strengthening it to root semantics. |

The raw equality instance compares all six literal fields. It does not compare
mathematical denotations or accepted evidence. The instance's proposition matches
the constructor equality theorem, including slot order and every sign.

## Literal replay and descriptor construction

| Declaration | API and proof assessment |
| --- | --- |
| `RawDescriptor.check` | Checks shape, immutable context, the full recursive replay for reconstructed derivative queries, and count one for the exact raw word. |
| `RawDescriptor.check_iff` | Full acceptance equivalence, including an accepted replay proof and its exact table count. It quantifies over arbitrary supplied replay; no producer equation is assumed. |
| `Descriptor` | Private constructor seals the three documented fields: raw input, exact replay, and its acceptance proof. Ordinary-root meaning is supplied by companion soundness under interpretation laws. |
| `Descriptor.ofChecked` | Restores the exact subject/evidence with an existing literal acceptance proof, without rerunning replay. |
| `Descriptor.ofChecked_raw` | Simp projection preserves literal raw input independently of proof-field representation. |
| `Descriptor.ofChecked_evidence` | Simp projection preserves literal replay, rather than reconstructing another certificate. |
| `Descriptor.ofChecked_eq` | Restoration of an existing checked value is equal to that complete value; proof irrelevance handles proof fields. |
| `Descriptor.ofReplay?` | Checks arbitrary supplied replay and returns `none` on refusal. Refusal does not prove mathematical absence. |
| `Descriptor.ofReplay_data` | Whole-Option data characterization covers both success and rejection while preserving constructor privacy. |
| `Descriptor.ofReplay_self` | Rechecks the existing descriptor's exact raw subject and evidence and restores that same descriptor. Uses its retained literal acceptance and proof irrelevance, without a producer equation or a semantic model. Shared by the root-frame reader and the finite-covered descriptor reader. |
| `Descriptor.ofTable` | Reuses an accepted table and exact count-one row. Its proof applies `check_iff`; the computational data and guards are unchanged. |
| `Descriptor.ofTable_raw` | Exact raw projection from table reuse. Its hypotheses retain the same table/check/count rather than inventing producer provenance. |
| `Descriptor.ofTable_evidence` | Exact replay projection from table reuse, with the same dependent acceptance proof. |
| `Descriptor.ofReplay_ofTable` | Rechecking the same table returns exactly the constructed descriptor. It proves agreement, not equal runtime cost. |
| `Descriptor.ofReplay_isSome` | Option success is equivalent to the complete raw acceptance check. |
| `Descriptor.ofReplay_none` | A rejected literal check returns no descriptor; no claim about unique-root nonexistence follows. |
| `Descriptor.ofReplay_raw` | Any successful validation retains the supplied raw value literally. |
| `Descriptor.ofReplay_evidence` | Any successful validation retains the supplied evidence literally. |
| `RawDescriptor.check_eq` | Existing forward API is preserved as the forward direction of `check_iff`; positional consumers keep their statement. |
| `RawDescriptor.check_count` | With explicit valid observations and replay interpretation, the exact finite observation list contains the selected word once. Repeated observations count separately; ordinary-root distinctness is a companion requirement. |
| `DescriptorError` | Context, malformed, domain, absent and ambiguous constructors remain distinct input diagnostics, nested inside the separate internal `BuildError` layer. |
| `Descriptor.build` | Executes context checking, Sturm preparation, raw shape validation and actual prepared-table construction before count classification. Lawful producer totality remains in the companion. |
| `Descriptor.validate` | Option wrapper keeps only successful diagnostic construction. Internal errors also become `none` for arbitrary operations; the companion excludes them under its hypotheses. |
| `Descriptor.validate_eq_some` | Exact successful-result correspondence with the diagnostic builder, preserving the returned descriptor. |
| `Descriptor.build_raw` | Successful actual construction retains the exact original raw input despite dependent branch proofs. |
| `Descriptor.build_context` | A mismatched context is rejected before domain/shape construction. |
| `Descriptor.build_domain` | Exact failed preparation yields the domain diagnostic when context agrees; an unrelated prepared object cannot discharge it. |
| `Descriptor.build_malformed` | With exact successful preparation and matching context, a rejected shape yields the malformed diagnostic. The diagnostic order is preserved. |
| `Descriptor.build_ok_ofPrepared` | Prepared-table producer success excludes internal errors, while allowing every input diagnostic. No mathematical totality is asserted without that premise. |
| `Descriptor.build_ofCount` | Exact prepared construction plus a count-one word produces an accepted descriptor. Shape/context and successful preparation remain explicit. |
| `Descriptor.build_absent_ofCount` | Exact zero word count produces absence after the required domain/shape/context checks. |
| `Descriptor.build_ambiguous_ofCount` | Exact count different from zero and one produces ambiguity; natural counts make this precisely the multiple-count case. |

## Acceptance scope

The new characterizations preserve all computational definitions and guards.
`wellFormed_bounds`, `wellFormed_length`, `ofTable` and the existing forward
acceptance theorem use them. The owning companion proves selected-root
realization and lawful producer success; this finite API review does not
replace those proofs. Ordinary-root coverage, distinctness and strict
mathematical order require the companion's interpretation and sign hypotheses.

This is partial computational Phase-6 review. Remaining modules, whole-library
use/lint acceptance and the declared computational regression checks remain
required. It makes no phase or publication-eligibility claim.
