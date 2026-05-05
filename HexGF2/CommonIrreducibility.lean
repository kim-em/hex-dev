import HexGF2.RabinSoundness

/-!
Project-side irreducibility witnesses for committed packed `GF(2)` moduli.

The witnesses are produced by the Rabin certificate checker introduced in
`HexGF2/Irreducibility.lean` and bridged to `GF2Poly.Irreducible` through
`checkIrreducibilityCertificate_imp_irreducible`. The pow chain and Bezout
data are constructed by the executable functions `xpow2kMod` and `xgcd`, so
each witness is a single `decide` reduction of the certificate-checker.
-/
namespace Hex
namespace GF2Poly

/-- The AES Rijndael modulus over `GF(2)`: `X^8 + X^4 + X^3 + X + 1`. -/
private def aesModulus : GF2Poly := ofUInt64Monic 0x1B 8

/-- Rabin certificate for the AES modulus. The pow chain stores
`X^(2^k) mod aesModulus` for `k = 0..8`; the single Bezout witness covers
the unique maximal proper divisor `d = 4` of `n = 8`.

Both the pow chain and the Bezout witness data are produced from the
executable `xpow2kMod` and `xgcd` so the certificate doubles as a
mechanical recipe. The chain is given as an explicit array literal so
kernel reduction (used by `decide` below) can normalize each entry
without going through the well-founded `Array.map`. -/
private def aesCert : IrreducibilityCertificate :=
  { n := 8
    powChain :=
      #[xpow2kMod aesModulus 0, xpow2kMod aesModulus 1, xpow2kMod aesModulus 2,
        xpow2kMod aesModulus 3, xpow2kMod aesModulus 4, xpow2kMod aesModulus 5,
        xpow2kMod aesModulus 6, xpow2kMod aesModulus 7, xpow2kMod aesModulus 8]
    bezout :=
      let diff := frobeniusDiffMod aesModulus 4
      let xg := xgcd aesModulus diff
      #[{ left := xg.left, right := xg.right }] }

set_option maxRecDepth 4096 in
private theorem aesCert_check :
    checkIrreducibilityCertificate aesModulus aesCert = true := by
  decide

/-- The AES Rijndael modulus `X^8 + X^4 + X^3 + X + 1` is irreducible over
`GF(2)`. -/
theorem aes_modulus_irreducible :
    Irreducible (ofUInt64Monic 0x1B 8) :=
  checkIrreducibilityCertificate_imp_irreducible aesModulus aesCert aesCert_check


end GF2Poly
end Hex
