/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePolynomial
public meta import HexRealClosure.BasePolynomial

public section

namespace Hex.RealClosure.BaseContext.PolynomialTests

private def registry : Registry := fun _ => none
private def otherRegistry : Registry := fun _ =>
  some (fun _ => OrderedFn.Oracle.Bounds.singleton 0)
private abbrev base := rational registry
private abbrev first := base.infinitesimal
private abbrev second := first.infinitesimal
private def epsilon : Element first := Element.infinitesimal base
private def delta : Element second := Element.infinitesimal first
private def p : Polynomial first := Polynomial.ofCoeffs #[epsilon, 1 / epsilon, 2]
private def a : Element first := epsilon + 1

#guard p.stored.natDegree = 2
#guard (p.coeff 0).equal epsilon
#guard (p.coeff 4).equal 0
#guard (p.embed.coeff 0).equal epsilon.embed
#guard (p.embed.eval a.embed).equal (p.eval a).embed
#guard ((p * p).embed.eval a.embed).equal ((p.eval a) * (p.eval a)).embed
#guard (p.embed.eval delta).sign = 1
#guard (Polynomial.read first p.write).map Polynomial.stored = some p.stored
#guard (Polynomial.read second p.write).isNone
#guard (Polynomial.read first p.embed.write).isNone
#guard (Polynomial.read second p.embed.write).map Polynomial.stored = some p.embed.stored

#check_failure (fun (q : Polynomial first) => (q : Polynomial second))
#check_failure (fun (q : Polynomial first) => q + p.embed)
#check_failure (fun (q : Polynomial first) => q.eval delta)
#check_failure (fun (b : Element first) => Polynomial.ofCoeffs #[b, delta])
#check_failure (fun (q : Polynomial base) => (q : Polynomial (rational otherRegistry)))
#check_failure (fun (q : Polynomial base) (r : Polynomial (rational otherRegistry)) => q + r)
#check_failure (fun (q : Polynomial first) =>
  (q : Polynomial (rational otherRegistry).infinitesimal))

private def square : Element first := (epsilon + 1) * (epsilon + 1)
private def expanded : Element first := epsilon * epsilon + 2 * epsilon + 1
private def high : Polynomial first := Polynomial.ofCoeffs #[1, epsilon, square]
private def equivalent : Polynomial first := Polynomial.ofCoeffs #[0, epsilon, expanded]
#guard (high - equivalent).stored.natDegree = 0
#guard (high - equivalent).stored.size = 1
#guard (high - high).stored.size = 0
#guard (high.embed - equivalent.embed).stored.natDegree = 0
#guard (high.embed - high.embed).stored.size = 0

private def malformed : Polynomial.Serialized :=
  ⟨first.signature, [.fraction [.rational 1] [.rational 0]]⟩
#guard (Polynomial.read first malformed).isNone
#guard (Polynomial.read first ⟨first.signature, [.rational 1]⟩).isNone
#guard (Polynomial.read base ⟨base.signature, [.fraction [] []]⟩).isNone

-- Trailing zero coefficients are normalized after every coefficient is checked.
private def padded : Polynomial.Serialized :=
  ⟨first.signature, p.write.coefficients ++ [(0 : Element first).write.value]⟩
#guard (Polynomial.read first padded).map Polynomial.stored = some p.stored

example (q : Polynomial second) : Polynomial.read second q.write = some q :=
  Polynomial.read_write q

example : p.embed.stored.size = p.stored.size := Polynomial.embed_size p
example : p.embed.stored.natDegree = p.stored.natDegree := Polynomial.embed_degree p

end Hex.RealClosure.BaseContext.PolynomialTests
