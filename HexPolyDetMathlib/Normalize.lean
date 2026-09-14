/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib.Scaling
public meta import HexPolyDetMathlib.Scaling
public meta import HexMatrixMathlib.Literal

public meta section

namespace HexMatrixMathlib.DetPoly.Normalize

open Lean Meta HexMatrixMathlib.Literal

abbrev NormalizeM := ExceptT MessageData MetaM

def literalNat? (e : Expr) : Option Nat :=
  e.rawNatLit? <|> if e.isAppOfArity ``OfNat.ofNat 3 then e.getAppArgs[1]!.rawNatLit? else none

/-- Bound closed scalar arithmetic before asking `norm_num` to evaluate it.
Opaque operations remain atoms. Numerator and denominator bits are bounded
 together, so nested closed powers cannot expand before the budget check. -/
partial def scalarBound (a : Expr) (fuel : Nat := 8) : NormalizeM (Option Nat) := do
  if a.hasFVar || a.hasMVar then return none
  let bounded (n : Nat) : NormalizeM (Option Nat) := do
    if n > 4096 then throwThe MessageData m!"coefficient bit budget exhausted (limit 4096)"
    return some n
  if let some n := a.rawNatLit? then return ← bounded (n.log2 + 1)
  let args := a.getAppArgs
  if (a.isAppOf ``Nat.cast || a.isAppOf ``Int.cast) && args.size == 3 then
    return ← scalarBound args[2]! fuel
  if (a.isAppOf ``Int.ofNat || a.isAppOf ``Int.negSucc) && args.size == 1 then
    if let some n := literalNat? args[0]! then return ← bounded ((n + 1).log2 + 1)
  if a.isAppOf ``OfNat.ofNat && args.size == 3 then
    if let some n := args[1]!.rawNatLit? then return ← bounded (n.log2 + 1)
  if a.isAppOf ``Neg.neg && args.size == 3 then return ← scalarBound args[2]! fuel
  if (a.isAppOf ``HAdd.hAdd || a.isAppOf ``HSub.hSub || a.isAppOf ``HMul.hMul ||
      a.isAppOf ``HDiv.hDiv) && args.size == 6 then
    let some x ← scalarBound args[4]! fuel | return none
    let some y ← scalarBound args[5]! fuel | return none
    return ← bounded (x + y + 1)
  if a.isAppOf ``HPow.hPow && args.size == 6 then
    let some n := literalNat? args[5]! | return none
    if n > 64 then throwThe MessageData m!"exponent budget exhausted (limit 64)"
    let some x ← scalarBound args[4]! fuel | return none
    return ← bounded (x * n + 1)
  if fuel > 0 then
    if let some b ← unfoldDefinition? a then return ← scalarBound b (fuel - 1)
  return none

/-- An integer-coefficient expression and a proof of its positive scaling. -/
structure Result where
  term : Expr
  scale : Nat
  proof : Expr
  deriving Inhabited

/-- Integer coefficients are quoted as ring numerals, without division. -/
def integer (z : Int) : MetaM Expr := do
  let e ← mkNumeral (mkConst ``Rat) z.natAbs
  if z < 0 then mkAppM ``Neg.neg #[e] else pure e

def natural (n : Nat) : MetaM Expr := mkNumeral (mkConst ``Rat) n

def scaled (s : Nat) (e : Expr) : MetaM Expr := do mkAppM ``HMul.hMul #[← natural s, e]

/-- Assert only the computed natural scale, leaving its reduction to the kernel. -/
def result (a term : Expr) (s : Nat) (proof : Expr) : NormalizeM Result := do
  if s.log2 + 1 > 4096 then throwThe MessageData m!"coefficient bit budget exhausted (limit 4096)"
  return ⟨term, s, ← mkExpectedTypeHint proof (← mkEq term (← scaled s a))⟩

def unchanged (a : Expr) : NormalizeM Result := do
  result a a 1 (← mkEqSymm (← mkAppM ``one_mul #[a]))

/-- Raise an entry to a common positive scale. The closed multiplication in
the expected type verifies that the computed quotient is exact. -/
def rescale (a : Expr) (p : Result) (s : Nat) : NormalizeM Result := do
  if s == p.scale then return p
  let t := s / p.scale
  unless p.scale > 0 && t * p.scale == s do
    throwThe MessageData m!"invalid rational common scale"
  let term ← scaled t p.term
  result a term s (← mkAppM ``Scaling.row #[a, p.term, toExpr p.scale, toExpr t, p.proof])

/-- Clear closed rational coefficients through ring operations. Division by
an open term remains one atom; no division of symbolic polynomials occurs. -/
partial def expression (a : Expr) : NormalizeM Result := do
  if (← scalarBound a).isSome then
    if let some q ← ((try some <$> evalEntry a catch _ => pure none) : MetaM (Option Rat)) then
      if q.num.natAbs.log2 + 1 > 4096 then throwThe MessageData m!"coefficient bit budget exhausted (limit 4096)"
      let p ← integer q.num
      return ← result a p q.den (← decideProof (← mkEq p (← scaled q.den a)))
  let args := a.getAppArgs
  let name := a.getAppFn.constName?
  if (name == some ``HAdd.hAdd || name == some ``HSub.hSub || name == some ``HMul.hMul)
      && args.size == 6 then
    let x := args[4]!
    let y := args[5]!
    let p ← expression x
    let q ← expression y
    if name == some ``HMul.hMul then
      let term ← mkAppM ``HMul.hMul #[p.term, q.term]
      let h ← mkAppM ``Scaling.mul #[x, y, p.term, q.term, toExpr p.scale, toExpr q.scale, p.proof, q.proof]
      return ← result a term (p.scale * q.scale) h
    let s := p.scale.lcm q.scale
    let p ← rescale x p s
    let q ← rescale y q s
    let term ← mkAppM name.get! #[p.term, q.term]
    let theoremName := if name == some ``HAdd.hAdd then ``Scaling.add else ``Scaling.sub
    let h ← mkAppM theoremName #[x, y, p.term, q.term, toExpr s, p.proof, q.proof]
    return ← result a term s h
  if name == some ``Neg.neg && args.size == 3 then
    let x := args[2]!
    let p ← expression x
    let term ← mkAppM ``Neg.neg #[p.term]
    return ← result a term p.scale (← mkAppM ``Scaling.neg #[x, p.term, toExpr p.scale, p.proof])
  if name == some ``HPow.hPow && args.size == 6 then
    if let some n ← (Meta.evalNat args[5]!).run then
      if n > 64 then throwThe MessageData m!"exponent budget exhausted (limit 64)"
      let x := args[4]!
      let p ← expression x
      let term ← mkAppM ``HPow.hPow #[p.term, toExpr n]
      return ← result a term (p.scale ^ n)
        (← mkAppM ``Scaling.pow #[x, p.term, toExpr p.scale, toExpr n, p.proof])
  if name == some ``HDiv.hDiv && args.size == 6 then
    let x := args[4]!
    let b := args[5]!
    if (← scalarBound b).isSome then
      if let some q ← ((try some <$> evalEntry b catch _ => pure none) : MetaM (Option Rat)) then
        let inv := 1 / q
        let p ← expression x
        let z ← integer inv.num
        let term ← mkAppM ``HMul.hMul #[z, p.term]
        let hb ← decideProof (← mkEq z (← mkAppM ``HDiv.hDiv #[← natural inv.den, b]))
        return ← result a term (p.scale * inv.den)
          (← mkAppM ``Scaling.div #[x, b, p.term, toExpr p.scale, toExpr inv.num,
            toExpr inv.den, p.proof, hb])
  unchanged a

/-- Scale a row by the least common multiple of its positive entry scales. -/
def row (es : Array Expr) : NormalizeM (Nat × Array Result) := do
  let rs ← es.mapM expression
  let scale := rs.foldl (fun n r => n.lcm r.scale) 1
  let mut out := #[]
  for i in [:rs.size] do
    out := out.push (← rescale es[i]! rs[i]! scale)
  return (scale, out)

end HexMatrixMathlib.DetPoly.Normalize
