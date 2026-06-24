import Lake

open System Lake DSL

package Hex where

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.30.0-rc2"

require «lean-bench» from git
  "https://github.com/kim-em/lean-bench.git" @ "master"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

require HexMatrix from git
  "https://github.com/kim-em/hex-matrix.git" @ "20e4c73f958cf7996199972a45e538d06121f91f"
require HexMatrixMathlib from git
  "https://github.com/kim-em/hex-matrix-mathlib.git" @ "7e2eed8ae6d962d11e65d5763ce93439ce3fcb72"
require HexGramSchmidt from git
  "https://github.com/kim-em/hex-gram-schmidt.git" @ "d9ffab41cd4b400bc05eb69eb1724484d43017e3"
require HexGramSchmidtMathlib from git
  "https://github.com/kim-em/hex-gram-schmidt-mathlib.git" @ "29404cfe535ec3dc53a6a174235e69fbf0c3c7e8"
require HexLLL from git
  "https://github.com/kim-em/hex-lll.git" @ "ff9729a08b65fda89f391eca5ce5b4497711f815"
require HexLLLMathlib from git
  "https://github.com/kim-em/hex-lll-mathlib.git" @ "e4554e109e1cd93547572819499c33db769300af"

private def clmulOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexGF2" / "ffi" / "clmul.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexGF2" / "ffi" / "clmul.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO oFile srcFile flags

private def zmod64MulOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexModArith" / "ffi" / "zmod64_mul.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexModArith" / "ffi" / "zmod64_mul.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO oFile srcFile flags

extern_lib hexgf2ffi (pkg) := do
  let name := nameToStaticLib "hexgf2ffi"
  let oTarget ← clmulOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) #[oTarget]

private def hexArithOTarget (pkg : Package) (src : String) : FetchM (Job FilePath) := do
  let stem := (src.dropEnd 2).toString
  let oFile := pkg.dir / defaultBuildDir / "HexArith" / "ffi" / s!"{stem}.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexArith" / "ffi" / src
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO oFile srcFile flags

extern_lib hexarithffi (pkg) := do
  let name := nameToStaticLib "hexarithffi"
  let oTargets ← #[ "wide_arith.c", "mpz_gcdext.c" ].mapM (hexArithOTarget pkg)
  buildStaticLib (pkg.staticLibDir / name) oTargets

extern_lib hexmodarithffi (pkg) := do
  let name := nameToStaticLib "hexmodarithffi"
  let oTarget ← zmod64MulOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) #[oTarget]

lean_lib Hex where

lean_lib HexArith where
  precompileModules := true
  moreLinkArgs := #[
    s!"{(defaultBuildDir / "lib" / nameToStaticLib "hexarithffi").toString}",
    "-lgmp"
  ]

lean_lib HexPoly where

lean_lib HexModArith where
  precompileModules := true
  moreLinkArgs := #[
    s!"{(defaultBuildDir / "lib" / nameToStaticLib "hexmodarithffi").toString}",
    "-lgmp"
  ]

lean_lib HexGF2 where
  precompileModules := true

lean_lib HexPolyZ where

lean_lib HexPolyFp where

lean_lib HexGFqRing where

lean_lib HexGFqField where

lean_lib HexBerlekamp where

lean_lib HexHensel where

lean_lib HexConway where

lean_lib HexGFq where

lean_lib HexBerlekampZassenhaus where

lean_lib HexPolyMathlib where

lean_lib HexModArithMathlib where

lean_lib HexPolyZMathlib where

lean_lib HexBerlekampMathlib where

lean_lib HexHenselMathlib where

lean_lib HexGF2Mathlib where

lean_lib HexGFqMathlib where

lean_lib HexBerlekampZassenhausMathlib where

lean_exe hexarith_bench where
  root := `HexArith.Bench

lean_exe hexpoly_bench where
  root := `HexPoly.Bench

lean_exe hexpoly_emit_fixtures where
  root := `HexPoly.EmitFixtures

lean_exe hexpolyfp_emit_fixtures where
  root := `HexPolyFp.EmitFixtures

lean_exe hexberlekamp_emit_fixtures where
  root := `HexBerlekamp.EmitFixtures

lean_exe hexbz_emit_fixtures where
  root := `HexBerlekampZassenhaus.EmitFixtures

lean_exe hexbz_bench where
  root := `HexBerlekampZassenhaus.Bench

lean_exe hexgfq_emit_fixtures where
  root := `HexGFq.EmitFixtures

lean_exe hexgf2_emit_fixtures where
  root := `HexGF2.EmitFixtures

lean_exe hexhensel_emit_fixtures where
  root := `HexHensel.EmitFixtures

lean_exe hexconway_emit_fixtures where
  root := `HexConway.EmitFixtures

lean_exe hexgfqring_emit_fixtures where
  root := `HexGFqRing.EmitFixtures

lean_exe hexgfqfield_emit_fixtures where
  root := `HexGFqField.EmitFixtures

lean_exe hexpolyz_bench where
  root := `HexPolyZ.Bench

lean_exe hexpolyz_emit_fixtures where
  root := `HexPolyZ.EmitFixtures

lean_exe hexmodarith_bench where
  root := `HexModArith.Bench

lean_exe hexgf2_bench where
  root := `HexGF2Bench

-- No bench exes for `Hex*Mathlib` libraries — see
-- SPEC/benchmarking.md §Mathlib-free benches. The Mathlib-side libraries
-- are proof-only; there is no computational kernel to benchmark.

lean_exe hexpolyfp_bench where
  root := `HexPolyFp.Bench

lean_exe hexgfqring_bench where
  root := `HexGFqRing.Bench

lean_exe hexgfqfield_bench where
  root := `HexGFqField.Bench

lean_exe hexgfq_bench where
  root := `HexGFq.Bench

lean_exe hexhensel_bench where
  root := `HexHensel.Bench

lean_exe hexberlekamp_bench where
  root := `HexBerlekamp.Bench

lean_exe hexconway_bench where
  root := `HexConway.Bench

@[default_target]
lean_lib HexManual where
