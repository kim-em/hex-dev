module

public import Lake

public section

open System Lake DSL

package Hex where

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.30.0-rc2"

require «lean-bench» from git
  "https://github.com/kim-em/lean-bench.git" @ "master"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

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

private def hexlllProviderOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexLLL" / "ffi" / "lean_hexlll_provider.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexLLL" / "ffi" / "lean_hexlll_provider.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
    compileO oFile srcFile flags

extern_lib hexlllffi (pkg) := do
  let name := nameToStaticLib "hexlllffi"
  let oTarget ← hexlllProviderOTarget pkg
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

lean_lib HexMatrix where
  precompileModules := true

lean_lib HexRowReduce where
  precompileModules := true

lean_lib HexDeterminant where
  precompileModules := true

lean_lib HexBareiss where
  precompileModules := true

lean_lib HexGramSchmidt where

lean_lib HexLLL where
  precompileModules := true
  extraDepTargets := #[`hexlllffi]
  moreLinkArgs :=
    if System.Platform.isOSX then
      #[]
    else
      #["-ldl"]

lean_lib HexMatrixMathlib where

lean_lib HexGramSchmidtMathlib where

lean_lib HexLLLMathlib where

lean_exe hexlll_provider_probe where
  root := `HexLLL.ProviderProbe

-- Multi-file bench drivers: their modules live under `bench/` and are owned by
-- a precompiled lean_lib (mirroring the released bench sub-project), so the bench
-- exes can root into them. Single-file bench drivers instead carry
-- `srcDir := "bench"` on their own `lean_exe`.
lean_lib HexLLLBenchSupport where
  srcDir := "bench"
  globs := #[`HexLLLBench, `HexLLLBench.Inputs, `HexLLLBench.Targets]

lean_lib HexGF2BenchSupport where
  srcDir := "bench"
  globs := #[`HexGF2.Bench]

-- Conformance #guard drivers live under `conformance/` and are built by this
-- library (mirroring the released conformance sub-projects). EmitFixtures drivers
-- are the `*_emit_fixtures` exes below, carrying `srcDir := "conformance"`.
lean_lib HexConformance where
  srcDir := "conformance"
  globs := #[`HexArith.Conformance, `HexBerlekamp.Conformance, `HexBerlekampZassenhaus.Conformance, `HexConway.Conformance, `HexGF2.Conformance, `HexGFq.Conformance, `HexGFqField.Conformance, `HexGFqRing.Conformance, `HexGramSchmidt.Conformance, `HexHensel.Conformance, `HexLLL.Conformance, `HexMatrix.Conformance, `HexModArith.Conformance, `HexPoly.Conformance, `HexPolyFp.Conformance, `HexPolyZ.Conformance]

lean_exe hexmatrix_emit_fixtures where
  srcDir := "conformance"
  root := `HexMatrix.EmitFixtures

lean_exe hexgramschmidt_emit_fixtures where
  srcDir := "conformance"
  root := `HexGramSchmidt.EmitFixtures

lean_exe hexlll_emit_fixtures where
  srcDir := "conformance"
  root := `HexLLL.EmitFixtures

lean_exe hexmatrix_bench where
  srcDir := "bench"
  root := `HexMatrix.Bench

lean_exe hexgramschmidt_bench where
  srcDir := "bench"
  root := `HexGramSchmidt.Bench

lean_exe hexlll_bench where
  srcDir := "bench"
  supportInterpreter := true
  root := `HexLLLBench.Main

lean_exe hex_arith_floor where
  srcDir := "bench"
  root := `HexBench.ArithFloor

lean_exe hex_classical_spike where
  srcDir := "bench"
  root := `HexBench.ClassicalSpike

lean_exe hexarith_bench where
  srcDir := "bench"
  root := `HexArith.Bench

lean_exe hexpoly_bench where
  srcDir := "bench"
  root := `HexPoly.Bench

lean_exe hexpoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexPoly.EmitFixtures

lean_exe hexpolyfp_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolyFp.EmitFixtures

lean_exe hexberlekamp_emit_fixtures where
  srcDir := "conformance"
  root := `HexBerlekamp.EmitFixtures

lean_exe hexbz_emit_fixtures where
  srcDir := "conformance"
  root := `HexBerlekampZassenhaus.EmitFixtures

lean_exe hexbz_bench where
  srcDir := "bench"
  root := `HexBerlekampZassenhaus.Bench

lean_exe hexgfq_emit_fixtures where
  srcDir := "conformance"
  root := `HexGFq.EmitFixtures

lean_exe hexgf2_emit_fixtures where
  srcDir := "conformance"
  root := `HexGF2.EmitFixtures

lean_exe hexhensel_emit_fixtures where
  srcDir := "conformance"
  root := `HexHensel.EmitFixtures

lean_exe hexconway_emit_fixtures where
  srcDir := "conformance"
  root := `HexConway.EmitFixtures

lean_exe hexgfqring_emit_fixtures where
  srcDir := "conformance"
  root := `HexGFqRing.EmitFixtures

lean_exe hexgfqfield_emit_fixtures where
  srcDir := "conformance"
  root := `HexGFqField.EmitFixtures

lean_exe hexpolyz_bench where
  srcDir := "bench"
  root := `HexPolyZ.Bench

lean_exe hexpolyz_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolyZ.EmitFixtures

lean_exe hexmodarith_bench where
  srcDir := "bench"
  root := `HexModArith.Bench

lean_exe hexgf2_bench where
  srcDir := "bench"
  root := `HexGF2Bench

-- No bench exes for `Hex*Mathlib` libraries — see
-- SPEC/benchmarking.md §Mathlib-free benches. The Mathlib-side libraries
-- are proof-only; there is no computational kernel to benchmark.

lean_exe hexpolyfp_bench where
  srcDir := "bench"
  root := `HexPolyFp.Bench

lean_exe hexgfqring_bench where
  srcDir := "bench"
  root := `HexGFqRing.Bench

lean_exe hexgfqfield_bench where
  srcDir := "bench"
  root := `HexGFqField.Bench

lean_exe hexgfq_bench where
  srcDir := "bench"
  root := `HexGFq.Bench

lean_exe hexhensel_bench where
  srcDir := "bench"
  root := `HexHensel.Bench

lean_exe hexberlekamp_bench where
  srcDir := "bench"
  root := `HexBerlekamp.Bench

lean_exe hexconway_bench where
  srcDir := "bench"
  root := `HexConway.Bench

@[default_target]
lean_lib HexManual where
