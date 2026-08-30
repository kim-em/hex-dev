/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-! Expensive null control for the negative-result fresh-module sweep. -/

open Hex.PrimalityTactic

use_hex_primality_norm_num

example : ¬ Nat.Prime 18446739529634157713 := by norm_num
example : ¬ Nat.Prime 18446739452324759123 := by norm_num
example : ¬ Nat.Prime 18446739220396576361 := by norm_num
example : ¬ Nat.Prime 18446739014238183749 := by norm_num
example : ¬ Nat.Prime 18446738851029438343 := by norm_num
example : ¬ Nat.Prime 18446738687820713497 := by norm_num
example : ¬ Nat.Prime 18446738550381782309 := by norm_num
example : ¬ Nat.Prime 18446738369993193983 := by norm_num

-- Repeated goals deliberately raise this calibration module above the import
-- floor without changing the measured policy surface.
example : ¬ Nat.Prime 18446739529634157713 := by norm_num
example : ¬ Nat.Prime 18446739452324759123 := by norm_num
example : ¬ Nat.Prime 18446739220396576361 := by norm_num
example : ¬ Nat.Prime 18446739014238183749 := by norm_num
example : ¬ Nat.Prime 18446738851029438343 := by norm_num
example : ¬ Nat.Prime 18446738687820713497 := by norm_num
example : ¬ Nat.Prime 18446738550381782309 := by norm_num
example : ¬ Nat.Prime 18446738369993193983 := by norm_num
example : ¬ Nat.Prime 18446739529634157713 := by norm_num
example : ¬ Nat.Prime 18446739452324759123 := by norm_num
example : ¬ Nat.Prime 18446739220396576361 := by norm_num
example : ¬ Nat.Prime 18446739014238183749 := by norm_num
example : ¬ Nat.Prime 18446738851029438343 := by norm_num
example : ¬ Nat.Prime 18446738687820713497 := by norm_num
example : ¬ Nat.Prime 18446738550381782309 := by norm_num
example : ¬ Nat.Prime 18446738369993193983 := by norm_num
example : ¬ Nat.Prime 18446739529634157713 := by norm_num
example : ¬ Nat.Prime 18446739452324759123 := by norm_num
example : ¬ Nat.Prime 18446739220396576361 := by norm_num
example : ¬ Nat.Prime 18446739014238183749 := by norm_num
example : ¬ Nat.Prime 18446738851029438343 := by norm_num
example : ¬ Nat.Prime 18446738687820713497 := by norm_num
example : ¬ Nat.Prime 18446738550381782309 := by norm_num
example : ¬ Nat.Prime 18446738369993193983 := by norm_num
