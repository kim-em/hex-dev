/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
/-! Shared constructor data from `conformance-fixtures/HexRCF/cell-zero.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.CellReplayTests.ZeroLiterals
open Hex.SignDet
@[expose] def j0 : Codec.Json := .array .nil
@[expose] def sections : Codec.Json := j0
@[expose] def j1 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (1)) .nil)))
@[expose] def j2 : Codec.Json := .array (.cons (j0) (.cons (.number (0)) (.cons (j0) .nil)))
@[expose] def j3 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (1)) (.cons (.number (1)) .nil)))
@[expose] def j4 : Codec.Json := .array (.cons (j1) (.cons (j3) .nil))
@[expose] def j5 : Codec.Json := .array (.cons (.number (0)) .nil)
@[expose] def j6 : Codec.Json := .array (.cons (.number (2)) .nil)
@[expose] def j7 : Codec.Json := .array (.cons (j2) (.cons (j4) (.cons (j5) (.cons (j6) (.cons (j0) (.cons (j0) .nil))))))
@[expose] def j8 : Codec.Json := .array (.cons (j0) .nil)
@[expose] def j9 : Codec.Json := .array (.cons (.number (1)) .nil)
@[expose] def j10 : Codec.Json := .array (.cons (j9) .nil)
@[expose] def j11 : Codec.Json := .array (.cons (j8) (.cons (j8) (.cons (j9) (.cons (j9) (.cons (j10) (.cons (.number (1)) .nil))))))
@[expose] def j12 : Codec.Json := .array (.cons (j3) .nil)
@[expose] def j13 : Codec.Json := .array (.cons (j4) (.cons (j12) .nil))
@[expose] def j14 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) .nil))
@[expose] def j15 : Codec.Json := .array (.cons (j3) (.cons (j0) (.cons (j3) .nil)))
@[expose] def j16 : Codec.Json := .array (.cons (j3) (.cons (j4) .nil))
@[expose] def j17 : Codec.Json := .array (.cons (j16) .nil)
@[expose] def j18 : Codec.Json := .array (.cons (j13) (.cons (j14) (.cons (j15) (.cons (j0) (.cons (j17) .nil)))))
@[expose] def j19 : Codec.Json := .array (.cons (.number (-1)) (.cons (.number (1)) .nil))
@[expose] def j20 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) .nil))
@[expose] def j21 : Codec.Json := .array (.cons (j2) (.cons (j4) (.cons (j12) (.cons (j5) (.cons (j6) (.cons (j18) (.cons (j18) (.cons (j19) (.cons (j20) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j22 : Codec.Json := .array (.cons (j21) .nil)
@[expose] def j23 : Codec.Json := .array (.cons (j0) (.cons (j12) .nil))
@[expose] def j24 : Codec.Json := .array (.cons (j23) .nil)
@[expose] def j25 : Codec.Json := .array (.cons (j24) .nil)
@[expose] def j26 : Codec.Json := .array (.cons (.number (1)) (.cons (j5) (.cons (j5) (.cons (.number (1)) (.cons (j10) .nil)))))
@[expose] def j27 : Codec.Json := .array (.cons (j2) (.cons (j4) (.cons (j5) (.cons (j6) (.cons (j0) (.cons (.number (1)) (.cons (j11) (.cons (j22) (.cons (j25) (.cons (j8) (.cons (j26) .nil)))))))))))
@[expose] def j28 : Codec.Json := .array (.cons (j27) (.cons (j0) .nil))
@[expose] def j29 : Codec.Json := .array (.cons (j28) .nil)
@[expose] def j30 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j29) .nil)))
@[expose] def j31 : Codec.Json := .array (.cons (j5) (.cons (j9) (.cons (j6) .nil)))
@[expose] def j32 : Codec.Json := .array (.cons (.number (-1)) .nil)
@[expose] def j33 : Codec.Json := .array (.cons (j32) (.cons (j5) (.cons (j9) .nil)))
@[expose] def j34 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (1)) (.cons (.number (0)) .nil)))
@[expose] def j35 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (0)) .nil)))
@[expose] def j36 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-1)) (.cons (.number (1)) .nil)))
@[expose] def j37 : Codec.Json := .array (.cons (.number (2)) (.cons (.number (0)) (.cons (.number (-2)) .nil)))
@[expose] def j38 : Codec.Json := .array (.cons (j36) (.cons (j37) (.cons (j3) .nil)))
@[expose] def j39 : Codec.Json := .array (.cons (j31) (.cons (j33) (.cons (j34) (.cons (j35) (.cons (j38) (.cons (.number (2)) .nil))))))
@[expose] def j40 : Codec.Json := .array (.cons (j4) .nil)
@[expose] def j41 : Codec.Json := .array (.cons (j40) (.cons (j9) (.cons (j15) (.cons (j0) (.cons (j0) .nil)))))
@[expose] def j42 : Codec.Json := .array (.cons (j2) (.cons (j4) (.cons (j0) (.cons (j5) (.cons (j6) (.cons (j18) (.cons (j41) (.cons (j32) (.cons (j9) (.cons (.number (0)) (.cons (.number (0)) (.cons (.number (0)) .nil))))))))))))
@[expose] def j43 : Codec.Json := .array (.cons (j21) (.cons (j42) (.cons (j42) .nil)))
@[expose] def j44 : Codec.Json := .array (.cons (.number (0)) (.cons (j0) (.cons (j15) .nil)))
@[expose] def j45 : Codec.Json := .array (.cons (j44) .nil)
@[expose] def j46 : Codec.Json := .array (.cons (j45) (.cons (j0) .nil))
@[expose] def j47 : Codec.Json := .array (.cons (j46) .nil)
@[expose] def j48 : Codec.Json := .array (.cons (j44) (.cons (j44) .nil))
@[expose] def j49 : Codec.Json := .array (.cons (j48) (.cons (j0) .nil))
@[expose] def j50 : Codec.Json := .array (.cons (j49) .nil)
@[expose] def j51 : Codec.Json := .array (.cons (j24) (.cons (j47) (.cons (j50) .nil)))
@[expose] def j52 : Codec.Json := .array (.cons (j45) .nil)
@[expose] def j53 : Codec.Json := .array (.cons (j2) (.cons (j4) (.cons (j5) (.cons (j6) (.cons (j8) (.cons (.number (3)) (.cons (j39) (.cons (j43) (.cons (j51) (.cons (j52) (.cons (j26) .nil)))))))))))
@[expose] def j54 : Codec.Json := .array (.cons (j53) (.cons (j0) .nil))
@[expose] def j55 : Codec.Json := .array (.cons (j54) .nil)
@[expose] def j56 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j55) .nil)))
@[expose] def j57 : Codec.Json := .array (.cons (.number (1)) (.cons (j7) (.cons (j8) (.cons (j5) (.cons (j56) .nil)))))
@[expose] def j58 : Codec.Json := .array (.cons (j1) (.cons (Codec.Json.Value.null) (.cons (Codec.Json.Value.null) (.cons (j7) (.cons (j30) (.cons (j57) .nil))))))
@[expose] def j59 : Codec.Json := .array (.cons (j58) .nil)
@[expose] def sectors : Codec.Json := j59
end Hex.RCF.RealCoefficients.CellReplayTests.ZeroLiterals
