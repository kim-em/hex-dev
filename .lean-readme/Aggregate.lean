/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Lean
public meta import HexLLL

public section

private def loadReadmeDynlib (dir stem : String) : IO Unit := do
  let ext := if System.Platform.isOSX then "dylib" else "so"
  Lean.loadDynlib s!".lake/build/lib/{dir}{stem}.{ext}"

run_cmd loadReadmeDynlib "" "libhexarithffi"
run_cmd loadReadmeDynlib "" "libHex_HexArith"
run_cmd loadReadmeDynlib "" "libhexmodarithffi"
run_cmd loadReadmeDynlib "" "libHex_HexModArith"
run_cmd loadReadmeDynlib "lean/" "Hex_HexHensel_WordMul"
run_cmd loadReadmeDynlib "" "libHex_HexBasic"
run_cmd loadReadmeDynlib "" "libHex_HexMatrix"
run_cmd loadReadmeDynlib "" "libHex_HexBareiss"
