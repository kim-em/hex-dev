/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseCatalog
public meta import HexRealClosure.BaseCatalog

public section

namespace Hex.RealClosure.BaseContext.CatalogTests

private def registry : Registry := fun _ => none
private abbrev base := rational registry
private abbrev first := base.infinitesimal
private abbrev second := first.infinitesimal
private def epsilon : Element first := Element.infinitesimal base
private def delta : Element second := Element.infinitesimal first
private def a : Element second := 1 / epsilon.embed - delta
private def catalog := Catalog.empty registry

#guard (catalog.read base.signature).isSome
#guard (catalog.read second.signature).map PackedContext.signature = some second.signature
#guard (catalog.readElement a.write).map PackedElement.sign = some 1
#guard (catalog.readElement (a - a).write).map PackedElement.sign = some 0
#guard (catalog.insert (.pack (.rational registry))).isNone

private def missing : Signature := ⟨[⟨"missing", 1⟩], 2⟩
#guard (catalog.read missing).isNone
#guard (catalog.readElement { a.write with binding := missing }).isNone
#guard (catalog.readElement { a.write with binding := base.signature }).isNone
#guard (catalog.readElement { a.write with value := .fraction [] [] }).isNone

private abbrev packed := PackedContext.pack base
private abbrev reconstructed := packed.extend 2
private def value : PackedElement registry := ⟨reconstructed, a⟩
private def polynomial : Polynomial second := Polynomial.ofCoeffs #[a, delta, 2]
private def packedPolynomial : PackedPolynomial registry := ⟨reconstructed, polynomial⟩

#guard (catalog.readPolynomial polynomial.write).isSome
#guard (catalog.readPolynomial { polynomial.write with binding := missing }).isNone
#guard (catalog.readPolynomial { polynomial.write with coefficients := [.rational 1] }).isNone

private theorem read_reconstructed :
    catalog.read reconstructed.signature = some reconstructed := by
  have hs : packed.signature = ⟨[], 0⟩ := by
    simpa only [packed, PackedContext.signature, base, rational, RealContext.keys_rational] using
      Context.signature_real (.rational registry)
  simp only [PackedContext.extend_signature, hs, Nat.zero_add]
  simpa only [RealPrefix.keys_rational, RealPrefix.finish, reconstructed, packed, base, rational] using
    Catalog.read_prefix catalog (.pack (.rational registry)) 2
      (by simpa only [RealPrefix.keys_rational] using Catalog.lookup_rational catalog)

example : catalog.readElement value.write = some value :=
  Catalog.read_write catalog value read_reconstructed

example : catalog.readPolynomial packedPolynomial.write = some packedPolynomial :=
  Catalog.readPolynomial_write catalog packedPolynomial read_reconstructed

example (raw : Signature) (context : PackedContext registry)
    (h : catalog.read raw = some context) : context.signature = raw :=
  Catalog.read_signature catalog raw context h

end Hex.RealClosure.BaseContext.CatalogTests
