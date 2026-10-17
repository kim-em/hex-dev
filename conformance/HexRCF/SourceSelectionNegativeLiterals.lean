/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
/-! Shared constructor data from `conformance-fixtures/HexRCF/source-selection-negative.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.SourceSelectionNegativeLiterals
open Hex.SignDet
@[expose] def j0 : Codec.Json := .array (.cons (.number (-2)) (.cons (.number (1)) .nil))
@[expose] def j1 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (1)) .nil))
@[expose] def j2 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) .nil))
@[expose] def j3 : Codec.Json := .array (.cons (j0) (.cons (j1) (.cons (j2) .nil)))
@[expose] def j4 : Codec.Json := .array (.cons (.number (-3)) (.cons (.number (2)) .nil))
@[expose] def j5 : Codec.Json := .array (.cons (.number (1)) (.cons (j4) .nil))
@[expose] def j6 : Codec.Json := .array (.cons (.number (-7)) (.cons (.number (5)) .nil))
@[expose] def j7 : Codec.Json := .array (.cons (.number (1)) (.cons (j6) .nil))
@[expose] def j8 : Codec.Json := .array .nil
@[expose] def j9 : Codec.Json := .array (.cons (.number (8)) (.cons (j3) (.cons (j5) (.cons (j7) (.cons (j8) (.cons (j8) .nil))))))
@[expose] def subject : Codec.Json := j9
@[expose] def j10 : Codec.Json := .array (.cons (j8) .nil)
@[expose] def j11 : Codec.Json := .array (.cons (.number (1)) .nil)
@[expose] def j12 : Codec.Json := .array (.cons (j11) .nil)
@[expose] def j13 : Codec.Json := .array (.cons (j10) (.cons (j10) (.cons (j11) (.cons (j11) (.cons (j12) (.cons (.number (1)) .nil))))))
@[expose] def j14 : Codec.Json := .array (.cons (j2) .nil)
@[expose] def j15 : Codec.Json := .array (.cons (j1) (.cons (j2) .nil))
@[expose] def j16 : Codec.Json := .array (.cons (j3) (.cons (j15) (.cons (j14) .nil)))
@[expose] def j17 : Codec.Json := .array (.cons (.number (2)) (.cons (.number (1)) (.cons (.number (0)) .nil)))
@[expose] def j18 : Codec.Json := .array (.cons (.number (2)) (.cons (.number (1)) .nil))
@[expose] def j19 : Codec.Json := .array (.cons (j2) (.cons (j8) (.cons (j18) .nil)))
@[expose] def j20 : Codec.Json := .array (.cons (j2) (.cons (j15) (.cons (j18) .nil)))
@[expose] def j21 : Codec.Json := .array (.cons (j20) .nil)
@[expose] def j22 : Codec.Json := .array (.cons (j2) (.cons (j15) .nil))
@[expose] def j23 : Codec.Json := .array (.cons (j22) .nil)
@[expose] def j24 : Codec.Json := .array (.cons (j16) (.cons (j17) (.cons (j19) (.cons (j21) (.cons (j23) .nil)))))
@[expose] def j25 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (-1)) (.cons (.number (1)) .nil)))
@[expose] def j26 : Codec.Json := .array (.cons (.number (-1)) (.cons (.number (-1)) (.cons (.number (1)) .nil)))
@[expose] def j27 : Codec.Json := .array (.cons (.number (8)) (.cons (j3) (.cons (j14) (.cons (j5) (.cons (j7) (.cons (j24) (.cons (j24) (.cons (j25) (.cons (j26) (.cons (.number (2)) (.cons (.number (1)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j28 : Codec.Json := .array (.cons (j27) .nil)
@[expose] def j29 : Codec.Json := .array (.cons (j8) (.cons (j14) .nil))
@[expose] def j30 : Codec.Json := .array (.cons (j29) .nil)
@[expose] def j31 : Codec.Json := .array (.cons (j30) .nil)
@[expose] def j32 : Codec.Json := .array (.cons (.number (0)) .nil)
@[expose] def j33 : Codec.Json := .array (.cons (.number (1)) (.cons (j32) (.cons (j32) (.cons (.number (1)) (.cons (j12) .nil)))))
@[expose] def j34 : Codec.Json := .array (.cons (.number (8)) (.cons (j3) (.cons (j5) (.cons (j7) (.cons (j8) (.cons (.number (1)) (.cons (j13) (.cons (j28) (.cons (j31) (.cons (j10) (.cons (j33) .nil)))))))))))
@[expose] def j35 : Codec.Json := .array (.cons (j34) (.cons (j8) .nil))
@[expose] def j36 : Codec.Json := .array (.cons (j35) .nil)
@[expose] def j37 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j36) .nil)))
@[expose] def graph : Codec.Json := j37
end Hex.RCF.RealCoefficients.SourceSelectionNegativeLiterals
