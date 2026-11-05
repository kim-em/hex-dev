/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.PolynomialBounds
public import HexRCF.RealCoefficients.SignData
public section

namespace Hex.RCF.RealCoefficients.PolynomialSigns
open Hex.OrderedFn.Oracle PolynomialBounds LiteralSign

/-- Routing compares stored monomials and rational coefficients. The actual
key equality is checked independently on every index hit. -/
@[expose] def keyOrder (p q : Poly n) : Ordering :=
  List.compareLex (fun (left right : Mono n × Rat) =>
    match Mono.lex left.1 right.1 with
    | .eq => if left.2 < right.2 then .lt else if right.2 < left.2 then .gt else .eq
    | other => other) p.termsList q.termsList

/-- Authenticate every retained sign once against fixed bounds. Rational-root
query evidence is not part of this enclosure interface and is rejected. -/
@[expose] def check (bounds : Fin n → Bounds) (entries : Array (Entry (Poly n))) : Bool :=
  entries.all fun entry => entry.evidence.isNone &&
    decide (PolynomialBounds.sign? bounds entry.key = some entry.value)

/-- A malformed route can lose a hit, but cannot supply a different key's sign.
The enclosing query checker separately requires every actual read to hit. -/
@[expose] def lookup (entries : Array (Entry (Poly n))) (index : Index)
    (key : Poly n) : Option Int := index.lookup entries keyOrder key

/-- Share equal stored sign keys and build an untrusted positional index.
Source atom and original-divisor inventories are not modified. Replay neither
deduplicates keys nor rebuilds the index. -/
def build? (bounds : Fin n → Bounds) (keys : List (Poly n)) :
    Option (Array (Entry (Poly n)) × Index) := do
  let entries ← keys.eraseDups.toArray.mapM fun key => do
    let value ← PolynomialBounds.sign? bounds key
    pure (⟨key, value, none⟩ : Entry (Poly n))
  let index := Index.build entries keyOrder
  if check bounds entries && keys.all (fun key => (lookup entries index key).isSome) then
    some (entries, index)
  else none

end Hex.RCF.RealCoefficients.PolynomialSigns
