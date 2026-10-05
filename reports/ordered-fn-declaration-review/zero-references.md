# Zero-reference declaration dispositions

The frozen compiled snapshot has 49 handwritten declarations with no named
constant-body users. Each has a disposition below. “Public characterizing API”
means the law deliberately exposes promised behavior, as assessed in the
individual declaration tables; it does not assert a discovered production caller.
The distinction remains part of final Phase-6 acceptance, which is not claimed.
No removal candidate was identified among these characterizations.

The inventory scans named imported constants in the `HexManual` closure at the
preserved source tag. That includes the OrderedFn chapter, `Tests` and
`LiouvilleTests`, but not the whole `conformance/`, `bench/` or `examples/` trees.
Named proofs normally retain references to used non-rfl simp/ext/instance lemmas;
those uses **are counted**. Anonymous examples, rfl lemmas reduced by dsimp, and
instances unfolded during elaboration may leave no named reference. Conversely,
a nonzero count can come from a test; it does not prove production use.

`accessibleWf` is the elaboration instance supplying the accessible-subtype
relation for `firstSome`. Its `termination_by` subtype and
`decreasing_by exact ⟨rfl, eq⟩` use the declared `Next` relation, as shown in
[Search](../../HexOrderedFn/Search.lean#L57).

| Declaration | Disposition | Evidence |
| --- | --- | --- |
| `Real.Extension.ext_iff` | retain: public characterizing API | [HexOrderedFn/Extension.lean:51](../../HexOrderedFn/Extension.lean#L51) |
| `Real.Extension.val_C` | retain: rfl characterization/normalization API | [HexOrderedFn/Extension.lean:127](../../HexOrderedFn/Extension.lean#L127) |
| `Real.Extension.val_X` | retain: rfl characterization/normalization API | [HexOrderedFn/Extension.lean:130](../../HexOrderedFn/Extension.lean#L130) |
| `Real.Extension.transport_val` | retain: rfl characterization/normalization API | [HexOrderedFn/Extension.lean:158](../../HexOrderedFn/Extension.lean#L158) |
| `orderSign_range` | retain: public characterizing API | [HexOrderedFn/Infinitesimal.lean:24](../../HexOrderedFn/Infinitesimal.lean#L24) |
| `Infinitesimal.sign_range` | retain: public characterizing API | [HexOrderedFn/Infinitesimal.lean:56](../../HexOrderedFn/Infinitesimal.lean#L56) |
| `Oracle.Bounds.width_neg` | retain: public characterizing API | [HexOrderedFn/Oracle.lean:137](../../HexOrderedFn/Oracle.lean#L137) |
| `Oracle.Bounds.width_add` | retain: public characterizing API | [HexOrderedFn/Oracle.lean:141](../../HexOrderedFn/Oracle.lean#L141) |
| `Real.requestWidth_of_nonpos` | retain: public characterizing API | [HexOrderedFn/Real.lean:63](../../HexOrderedFn/Real.lean#L63) |
| `accessibleWf` | retain: termination elaboration instance | [HexOrderedFn/Search.lean:71](../../HexOrderedFn/Search.lean#L71) |
| `Real.RelativeTranscendence.ne_image` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/LiouvilleTests.lean:263](../../HexOrderedFnMathlib/LiouvilleTests.lean#L263) |
| `Real.evalHom_injective` | retain: public characterizing API | [HexOrderedFnMathlib/Evaluation.lean:66](../../HexOrderedFnMathlib/Evaluation.lean#L66) |
| `Real.evalHom_eq_ratFunc` | retain: public characterizing API | [HexOrderedFnMathlib/Evaluation.lean:79](../../HexOrderedFnMathlib/Evaluation.lean#L79) |
| `Real.registration_source` | retain: rfl characterization/normalization API | [HexOrderedFnMathlib/Extension.lean:43](../../HexOrderedFnMathlib/Extension.lean#L43) |
| `Real.Extension.coreField_eq` | retain: rfl characterization/normalization API | [HexOrderedFnMathlib/Extension.lean:128](../../HexOrderedFnMathlib/Extension.lean#L128) |
| `Real.Extension.sign_neg` | retain: public characterizing API | [HexOrderedFnMathlib/Extension.lean:161](../../HexOrderedFnMathlib/Extension.lean#L161) |
| `Real.Extension.sign_mul` | retain: public characterizing API | [HexOrderedFnMathlib/Extension.lean:167](../../HexOrderedFnMathlib/Extension.lean#L167) |
| `Real.Extension.sign_eq_zero_iff` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/LiouvilleTests.lean:179](../../HexOrderedFnMathlib/LiouvilleTests.lean#L179) |
| `Real.Extension.compare_eq` | retain: public characterizing API | [HexOrderedFnMathlib/Extension.lean:185](../../HexOrderedFnMathlib/Extension.lean#L185) |
| `Real.Extension.sign_pos_iff` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/LiouvilleTests.lean:198](../../HexOrderedFnMathlib/LiouvilleTests.lean#L198) |
| `Real.Extension.sign_neg_iff` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/LiouvilleTests.lean:199](../../HexOrderedFnMathlib/LiouvilleTests.lean#L199) |
| `Real.Extension.C_lt` | retain: public characterizing API | [HexOrderedFnMathlib/Extension.lean:229](../../HexOrderedFnMathlib/Extension.lean#L229) |
| `Real.Extension.eval_strictMono` | retain: public characterizing API | [HexOrderedFnMathlib/Extension.lean:264](../../HexOrderedFnMathlib/Extension.lean#L264) |
| `Real.Extension.OrderValid.strictOrderedRing` | retain: existing anonymous compiled example | [HexManual/Chapters/HexOrderedFn.lean:253](../../HexManual/Chapters/HexOrderedFn.lean#L253) |
| `Real.Extension.OrderValid.orderedRing` | retain: existing anonymous compiled example | [HexManual/Chapters/HexOrderedFn.lean:254](../../HexManual/Chapters/HexOrderedFn.lean#L254) |
| `Real.Extension.transport_lt` | retain: public characterizing API | [HexOrderedFnMathlib/Extension.lean:333](../../HexOrderedFnMathlib/Extension.lean#L333) |
| `Real.Extension.sign_transport` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/LiouvilleTests.lean:288](../../HexOrderedFnMathlib/LiouvilleTests.lean#L288) |
| `Real.Valid.orderValid` | retain: existing anonymous compiled example | [HexManual/Chapters/HexOrderedFn.lean:243](../../HexManual/Chapters/HexOrderedFn.lean#L243) |
| `Hahn.map_support` | retain: public characterizing API | [HexOrderedFnMathlib/Hahn.lean:33](../../HexOrderedFnMathlib/Hahn.lean#L33) |
| `Hahn.map_leadingCoeff` | retain: public characterizing API | [HexOrderedFnMathlib/Hahn.lean:51](../../HexOrderedFnMathlib/Hahn.lean#L51) |
| `Hahn.map_le` | retain: public characterizing API | [HexOrderedFnMathlib/Hahn.lean:80](../../HexOrderedFnMathlib/Hahn.lean#L80) |
| `Infinitesimal.embed_leadingCoeff` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:146](../../HexOrderedFnMathlib/Infinitesimal.lean#L146) |
| `Infinitesimal.embed_order` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:162](../../HexOrderedFnMathlib/Infinitesimal.lean#L162) |
| `Infinitesimal.sign_normalize` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:293](../../HexOrderedFnMathlib/Infinitesimal.lean#L293) |
| `Infinitesimal.sign_neg` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:299](../../HexOrderedFnMathlib/Infinitesimal.lean#L299) |
| `Infinitesimal.sign_mul` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:303](../../HexOrderedFnMathlib/Infinitesimal.lean#L303) |
| `Infinitesimal.sign_eq_zero_iff` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:309](../../HexOrderedFnMathlib/Infinitesimal.lean#L309) |
| `Infinitesimal.compare_eq` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:319](../../HexOrderedFnMathlib/Infinitesimal.lean#L319) |
| `Infinitesimal.orderedRing` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:361](../../HexOrderedFnMathlib/Infinitesimal.lean#L361) |
| `Infinitesimal.sign_of_neg` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:368](../../HexOrderedFnMathlib/Infinitesimal.lean#L368) |
| `Infinitesimal.sign_of_pos` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:374](../../HexOrderedFnMathlib/Infinitesimal.lean#L374) |
| `Infinitesimal.X_lt_pow` | retain: existing anonymous compiled example | [HexManual/Chapters/HexOrderedFn.lean:116](../../HexManual/Chapters/HexOrderedFn.lean#L116) |
| `Infinitesimal.towerEmbed_lt` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:443](../../HexOrderedFnMathlib/Infinitesimal.lean#L443) |
| `Infinitesimal.towerEmbed_C` | retain: public characterizing API | [HexOrderedFnMathlib/Infinitesimal.lean:449](../../HexOrderedFnMathlib/Infinitesimal.lean#L449) |
| `Oracle.Contains.ofDyadic` | retain: public characterizing API | [HexOrderedFnMathlib/Oracle.lean:71](../../HexOrderedFnMathlib/Oracle.lean#L71) |
| `Oracle.Contains.neg` | retain: public characterizing API | [HexOrderedFnMathlib/Oracle.lean:74](../../HexOrderedFnMathlib/Oracle.lean#L74) |
| `Oracle.Contains.inter_isSome` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/Tests.lean:35](../../HexOrderedFnMathlib/Tests.lean#L35) |
| `Oracle.Contains.inter` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/Tests.lean:38](../../HexOrderedFnMathlib/Tests.lean#L38) |
| `Real.sign?_sound` | retain: existing anonymous compiled example | [HexOrderedFnMathlib/Tests.lean:92](../../HexOrderedFnMathlib/Tests.lean#L92) |
