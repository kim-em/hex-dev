One small public API boundary surfaced while #10358 replaces the old fixture `mkDecideProof` sign-packet list with original-reader quotation. This is a request to the existing owner, not a new issue or dispatch.

The generic original `ScalarPacket.read` quotation and its coefficient interpretation already pass a fresh79-theorem/11-definition kernel audit without the old Records list. In a separate ordinary `module` consumer, `ScalarPacket.read` reaches `Tower.Signature.codec.decode` while parsing a producer's frozen graph. `Signature.codec` in `HexRealClosure/TowerContext.lean:97` is not exposed; the public client cannot unfold it. Quotation correctly stops at `Except.rec`. The existing `Signature.codec_lawful` gives `decode (encode s) = .ok s`, but the client also needs the public encoding identity to connect the frozen literal to that encoded signature.

Concrete reduced public-module reproducer (with the existing public cubic fixture):
```lean
module
public import HexRCF.RootQuoteCases
public section
open Hex Hex.RealClosure Hex.SignDet
example : Tower.Signature.codec.encode Hex.RCF.RootQuoteTests.base.signature =
    (.array (.cons (.array .nil) (.cons (.number 0)
      (.cons (.array .nil) .nil))) : Codec.Json) := by
  rfl
```
`lake build` fails: the left side is not definitionally equal to the displayed literal. Supplying `Signature.codec_lawful` directly for the demanded literal also fails ordinary kernel type checking, rather than silently accepting the wrong reader equation.

Is there an existing public encoding equation I should consume? I found `Signature.codec_lawful` and `Signature.ofLiteral_literal`, but no equation exposing the encoding projection. A public owner lemma of the shape
```lean
theorem Signature.codec_encode (s : Signature) :
    Signature.codec.encode s = s.literal.toJson := by rfl
```
would let the adapter compose lawful roundtrip with an explicitly checked literal identity, without copying the owner's codec proof or changing its representation. Please keep any owner change in the existing work. I have not edited your library files or relaxed the native-producer/kernel guard. The existing inverse-normalization and strict compiled missing-inventory requests remain separate. Independent adapter work and the already-running10975 CI continue;10331 retains dispatch.

A fresh read-only review confirms this visibility diagnosis and suggests the more direct public decoder equation, consistent with the existing `contextCodec_self` API:
```lean
theorem Signature.codec_literal (s : Signature) :
    Signature.codec.decode s.literal.toJson = .ok s := by
  exact Signature.codec_lawful s
```
Inside the owner module the encoded literal is definitionally the same, so this consumes the current law. Either this direct literal equation or the encoding projection equation above would address the first concrete gap without exposing private parser internals. Subsequent public replay still needs validation; I am not treating this as evidence that all public-module obstacles are already resolved. The full failed public fixture and attempted encoded-context variants remain retained separately; no passing-public-quotation claim is made.
