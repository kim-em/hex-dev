/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareissMathlib.Scaling
public meta import HexBareissMathlib.Scaling
public meta import HexMatrixMathlib.Literal

public meta section

namespace HexMatrixMathlib.DetPoly.Normalize

open Lean Meta HexMatrixMathlib.Literal

abbrev NormalizeM := ExceptT MessageData MetaM

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

/-- Clear closed rational coefficients through ring operations. Division by
an open term remains one atom; no division of symbolic polynomials occurs. -/
partial def expression (a : Expr) : NormalizeM Result := do
  if !a.hasFVar && !a.hasMVar then
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
    let isMul := name == some ``HMul.hMul
    let term ← if isMul then mkAppM ``HMul.hMul #[p.term, q.term]
      else mkAppM name.get! #[← scaled q.scale p.term, ← scaled p.scale q.term]
    let theoremName := if isMul then ``Scaling.mul else if name == some ``HAdd.hAdd then ``Scaling.add else ``Scaling.sub
    let h ← mkAppM theoremName #[x, y, p.term, q.term, toExpr p.scale, toExpr q.scale, p.proof, q.proof]
    return ← result a term (p.scale * q.scale) h
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
    if !b.hasFVar && !b.hasMVar then
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

/-- Scale a row by the product of its positive entry scales. -/
def row (es : Array Expr) : NormalizeM (Nat × Array Result) := do
  let rs ← es.mapM expression
  let scale := rs.foldl (fun n r => n * r.scale) 1
  let mut out := #[]
  for i in [:rs.size] do
    let p := rs[i]!
    let t := (rs.zipIdx).foldl (fun n (r, j) => if i == j then n else n * r.scale) 1
    let term ← scaled t p.term
    let proof ← mkAppM ``Scaling.row #[es[i]!, p.term, toExpr p.scale, toExpr t, p.proof]
    out := out.push (← result es[i]! term scale proof)
  return (scale, out)

end HexMatrixMathlib.DetPoly.Normalize
