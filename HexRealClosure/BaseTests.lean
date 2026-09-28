/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseCodec
public meta import HexRealClosure.BaseCodec

public section

namespace Hex.RealClosure.BaseContext.Tests

private def registry : Registry := fun _ => none
private def otherRegistry : Registry := fun _ => some (fun _ => OrderedFn.Oracle.Bounds.singleton 0)
private abbrev q := rational registry
private abbrev first := q.infinitesimal
private abbrev second := first.infinitesimal
private def epsilon : Element first := Element.infinitesimal q
private def delta : Element second := Element.infinitesimal first

#guard epsilon.sign = 1
#guard (epsilon - 1).sign = -1
#guard (epsilon - epsilon).sign = 0
#guard (1 / epsilon - 1000000).sign = 1
#guard (delta - epsilon.embed).sign = -1
#guard (epsilon.embed / delta - 1000000).sign = 1
#guard ((1 / epsilon).embed * epsilon.embed - 1).sign = 0

private def value : Element second :=
  (epsilon.embed + delta) / (2 * delta + 3)
#guard (Element.read second value.write).map Element.stored = some value.stored
#guard (Element.read first epsilon.write).map Element.stored = some epsilon.stored
#guard (Element.read q (0 : Element q).write).map Element.stored = some 0
#guard (Element.read second epsilon.write).isNone
#guard (Element.read first value.write).isNone

-- Same carrier and sign, different immutable registry/context: no implicit move.
#check_failure (fun (a : Element q) => (a : Element (rational otherRegistry)))
#check_failure (fun (a : Element first) => (a : Element (rational otherRegistry).infinitesimal))
#check_failure (fun (a : Element first) => a + delta)
#check_failure Context.real first
#check_failure Context.mk
#check_failure RealContext.mk

private def fraction (num den : List Syntax) : Serialized :=
  ⟨first.signature, .fraction num den⟩
#guard (Element.read first (fraction [.rational 1] [])).isNone
#guard (Element.read first (fraction [.rational 0] [.rational 0])).isNone
#guard (Element.read first (fraction [.fraction [] []] [.rational 1])).isNone
#guard (Element.read first ⟨first.signature, .rational 2⟩).isNone
#guard (Element.read q ⟨q.signature, .fraction [.rational 2] [.rational 1]⟩).isNone
#guard (Element.read first ⟨⟨[⟨"unknown", 1⟩], 1⟩, epsilon.write.value⟩).isNone

-- Noncanonical input is normalized only after all coefficients and the denominator pass.
#guard (Element.read first (fraction [.rational 2, .rational 2] [.rational 2])).map
  Element.stored = some (epsilon + 1).stored

example (a : Element second) : Element.read second a.write = some a :=
  Element.read_write a

end Hex.RealClosure.BaseContext.Tests
