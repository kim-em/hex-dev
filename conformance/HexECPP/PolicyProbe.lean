/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Search
public import HexECPP.Fixture256

public meta import HexECPP.Fixture256
public meta import HexPrimality.Search

public section

/-! The 256-bit ECPP fixture has a complete checked certificate while the
settled bounded Pocklington search policy exhausts on the same subject. -/

private def subject : Nat := Hex.ECPP.Fixture256.cert.subject

#guard Hex.ECPP.checkAt subject Hex.ECPP.Fixture256.cert

#guard match Hex.Nat.Internal.primeCertCountedWith? ⟨2, 32768, .off⟩ subject
    (Hex.Rand.ofSeed subject) (min (Hex.Nat.defaultPrimeFuel subject) 512) with
  | .error failure =>
      match failure.stop with
      | .exhausted => true
      | _ => false
  | .ok _ => false
