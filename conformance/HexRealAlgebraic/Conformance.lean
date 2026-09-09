/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealAlgebraic

/-! Compiled checks of the executable real algebraic API, without Mathlib. -/

open Hex
open Hex.RealAlgebraicNumber (ofRat ofAlgebraic? sqrt?)

#guard
  let z : RealAlgebraicNumber := 0
  compare z z == .eq && !(decide (z < z)) && decide (z ≤ z) &&
    min z z == z && max z z == z && z.sign == 0 && z.abs == z &&
    z.toRat? == some 0 && z.floor == 0 && z.ceil == 0 && z⁻¹ == z && z / z == z

#guard
  let q := ofRat (-3 / 2)
  compare q 0 == .lt && compare 0 q == .gt && decide (q < 0) &&
    !(decide (0 < q)) && decide (q ≤ 0) && !(decide (0 ≤ q)) &&
    min q 0 == q && max q 0 == 0 && q.sign == -1 && q.abs == ofRat (3 / 2) &&
    q.toRat? == some (-3 / 2) && q.floor == -2 && q.ceil == -1 &&
    q + q == -3 && q - q == 0 && q * q == ofRat (9 / 4) &&
    q / q == 1 && q⁻¹ == ofRat (-2 / 3) && q ^ (2 : Nat) == q * q &&
    q ^ (-1 : Int) == q⁻¹ && (2 : Nat) • q == -3 && (-2 : Int) • q == 3 &&
    (2 : Rat) • q == -3

#guard
  match ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] (3 / 2)),
      ofAlgebraic? (ZPoly.rootNear #p[-8, 0, 1] 3) with
  | some s, some t =>
    let e := t / 2
    compare (-s) s == .lt && compare s (-s) == .gt &&
      compare s (ofRat (7071 / 5000)) == .gt &&
      compare s (ofRat (14143 / 10000)) == .lt &&
      s == e && compare s e == .eq && decide (s ≤ e) && decide (e ≤ s) &&
      !(decide (s < e)) && !(decide (e < s)) && min s e == s && max s e == s &&
      s * s == 2 && (s + 1) - s == 1 && s.sign == 1 && s.abs == s &&
      s.toRat?.isNone && s.floor == 1 && s.ceil == 2 && (-s).floor == -2 &&
      (-s).ceil == -1 && s.conj == s
  | _, _ => false

#guard
  let roots := ZPoly.algebraicRoots #p[1, 0, 1]
  roots.size == 2 && roots.all (fun a => (ofAlgebraic? a).isNone) &&
    (RealAlgebraicPoly.ofAlgebraic?
      (AlgebraicPoly.ofArray #[AlgebraicNumber.I])).isNone

#guard
  match (RealAlgebraicPoly.ofArray #[]).roots,
      (RealAlgebraicPoly.ofArray #[1]).roots,
      (RealAlgebraicPoly.ofArray #[1, 0, 1]).roots with
  | .all, .finite constant, .finite imaginary => constant.isEmpty && imaginary.isEmpty
  | _, _, _ => false

#guard
  (sqrt? (-1)).isNone && sqrt? 0 == some 0 &&
    sqrt? (ofRat (9 / 4)) == some (ofRat (3 / 2))
