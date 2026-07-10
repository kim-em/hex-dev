/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith
public import HexHensel.Basic
public import HexPoly

public section

/-!
Word-sized (Montgomery) computation of the CLD quotient for the
Berlekamp-Zassenhaus lattice tier (issue #8691, Phase 1b).

`cldQuotientModWord?` mirrors `Hex.cldQuotientMod` but runs all mod-`p^a`
polynomial arithmetic over `Hex.WordMod` (residue arrays with single-reduction
Montgomery multiplication) instead of `Int`/bignum, whenever `p^a` fits an odd
machine word. It is byte-identical to `cldQuotientMod` on a monic divisor `g`;
the correspondence proof is Phase 2, after which it is wired via `@[csimp]`.
-/

namespace Hex

/-- Accumulating helper for `powLtWord?`: multiply `acc` by `p`, `n` times, with
early exit if any partial product reaches `2^64`. -/
@[expose]
def powLtWordAux (p : Nat) : Nat → Nat → Option Nat
  | 0, acc => some acc
  | n + 1, acc =>
      let next := acc * p
      if next < UInt64.word then powLtWordAux p n next else none

/-- `some (p^a)` if `p^a < 2^64`, computed with early exit so a huge exponent
never materialises a bignum. -/
@[expose]
def powLtWord? (p a : Nat) : Option Nat :=
  powLtWordAux p a 1

/--
Word-sized CLD quotient `(f · g') / g mod p^a` for monic `g`, computed over
`WordMod` when the guard `Odd (p^a) ∧ p^a < 2^64` holds (`p` odd prime ⇒ `p^a`
odd). Returns `none` when the guard fails, so the caller keeps the bignum path.
-/
@[expose]
def cldQuotientModWord? (f g : ZPoly) (p a : Nat) : Option ZPoly :=
  match powLtWord? p a with
  | none => none
  | some m =>
      let mU : UInt64 := UInt64.ofNat m
      if h : mU % 2 = 1 then
        let ctx := _root_.MontCtx.mk mU h
        let toW : Int → WordMod ctx := fun c => WordMod.ofNat (ZPoly.intModNat c m)
        let fW : DensePoly (WordMod ctx) := DensePoly.ofCoeffs (f.toArray.map toW)
        let gW : DensePoly (WordMod ctx) := DensePoly.ofCoeffs (g.toArray.map toW)
        let qW := (DensePoly.divMod (fW * DensePoly.derivative gW) gW).1
        some (DensePoly.ofCoeffs (qW.toArray.map (fun w => Int.ofNat w.toNat)))
      else
        none

end Hex
