module

public import Lake

public section

open System Lake DSL

package Hex where
  -- Parse docstrings as Verso markup. Suggestions remain opt-in because they
  -- attempt to elaborate ordinary code spans, including local expressions.
  leanOptions := #[⟨`doc.verso, true⟩, ⟨`doc.verso.suggestions, false⟩]

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.35.0-rc3"

-- Test-only native oracle. Released Hex libraries do not depend on it.
require NautyFFI from git
  "https://github.com/leanprover/nauty-ffi.git" @
    "ec8597014d0ae82490a616b855d59a35e6bfa21f"

require «lean-bench» from git
  "https://github.com/kim-em/lean-bench.git" @ "master"

-- Hasse's theorem is imported from the axiom-clean formalization in AINTLIB.
require AINTLIB from git
  "https://github.com/CBirkbeck/AINTLIB.git" @
    "ab1451487da02cd4483d0e2cdb2cc9e44bbbac17"

-- Abstract Sturm–Tarski semantics for the development query adapters.
require TauCeti from git
  "https://github.com/TauCetiProject/TauCeti.git" @
    "0dbbe255a4f418084b30a3ffe6763d824a6b4250"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d870b9068518a0870842d15a0cd42637ec30b587"

private def clmulOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexGF2" / "ffi" / "clmul.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexGF2" / "ffi" / "clmul.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3"]
    compileO oFile srcFile flags

private def zmod64MulOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexModArith" / "ffi" / "zmod64_mul.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexModArith" / "ffi" / "zmod64_mul.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    -- `LEAN_EXPORTING` makes `LEAN_EXPORT` a dllexport on Windows, as Lake
    -- does for Lean's own C; a carrier DLL otherwise hides these symbols.
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3",
      "-DLEAN_EXPORTING"]
    -- Mathlib's sandbox permits writes in the build directory, but not /tmp.
    -- Set TMPDIR for this compiler process only, including compiler wrappers.
    createParentDirs oFile
    proc {
      cmd := "cc"
      args := #["-c", "-o", oFile.toString, srcFile.toString] ++ flags
      env := #[("TMPDIR", some (← IO.FS.realPath (oFile.parent.getD ".")).toString)]
    }

extern_lib hexgf2ffi (pkg) := do
  let name := nameToStaticLib "hexgf2ffi"
  let oTarget ← clmulOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) #[oTarget]

private def hexArithOTarget (pkg : Package) (src : String) : FetchM (Job FilePath) := do
  let stem := (src.dropEnd 2).toString
  let oFile := pkg.dir / defaultBuildDir / "HexArith" / "ffi" / s!"{stem}.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexArith" / "ffi" / src
  buildFileAfterDep oFile srcTarget fun srcFile => do
    -- `LEAN_EXPORTING` makes `LEAN_EXPORT` a dllexport on Windows, as Lake
    -- does for Lean's own C; a carrier DLL otherwise hides these symbols.
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3",
      "-DLEAN_EXPORTING"]
    -- Mathlib's sandbox permits writes in the build directory, but not /tmp.
    -- Set TMPDIR for this compiler process only, including compiler wrappers.
    createParentDirs oFile
    proc {
      cmd := "cc"
      args := #["-c", "-o", oFile.toString, srcFile.toString] ++ flags
      env := #[("TMPDIR", some (← IO.FS.realPath (oFile.parent.getD ".")).toString)]
    }

-- Object files rather than an archive: a library's shared form keeps every
-- object it is given, while an archive contributes only referenced members.
target hexarithWideO pkg : FilePath := hexArithOTarget pkg "wide_arith.c"

-- TODO(lean4#15160): remove extended_gcd.c after the pinned toolchain provides
-- Nat.extendedGcd: https://github.com/leanprover/lean4/pull/15160
target hexarithGcdO pkg : FilePath := hexArithOTarget pkg "extended_gcd.c"

target hexmodarithO pkg : FilePath := zmod64MulOTarget pkg

target hexecpppariio pkg : FilePath := do
  let oFile := pkg.dir / defaultBuildDir / "HexECPPTheory" / "ffi" / "pari_pipe.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexECPPTheory" / "ffi" / "pari_pipe.c"
  let oTarget ← buildFileAfterDep oFile srcTarget fun srcFile => do
    createParentDirs oFile
    proc {
      cmd := "cc"
      args := #["-c", "-o", oFile.toString, srcFile.toString,
        "-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2", "-std=c11"]
      env := #[("TMPDIR", some (← IO.FS.realPath (oFile.parent.getD ".")).toString)]
    }
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "hexecpppariio") #[oTarget]

private def hexlllProviderOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "HexLLL" / "ffi" / "lean_hexlll_provider.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexLLL" / "ffi" / "lean_hexlll_provider.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3"]
    compileO oFile srcFile flags

extern_lib hexlllffi (pkg) := do
  let name := nameToStaticLib "hexlllffi"
  let oTarget ← hexlllProviderOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) #[oTarget]

private def nautyVendorOTarget (pkg : Package) (src : String) : FetchM (Job FilePath) := do
  let stem := (src.dropEnd 2).toString
  let oFile := pkg.dir / defaultBuildDir / "vendor" / "nauty-2.9.3" / s!"{stem}.o"
  let srcTarget ← inputTextFile <| pkg.dir / "vendor" / "nauty-2.9.3" / src
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (pkg.dir / "vendor" / "nauty-2.9.3").toString,
      "-fPIC", "-O2", "-std=c11", "-DUSE_TLS"]
    compileO oFile srcFile flags

private def nautyCanonOTarget (pkg : Package) : FetchM (Job FilePath) := do
  let oFile := pkg.dir / defaultBuildDir / "Hex" / "BenchOracle" / "ffi" /
    "nauty_canon.o"
  let srcTarget ← inputTextFile <| pkg.dir / "Hex" / "BenchOracle" / "ffi" /
    "nauty_canon.c"
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let flags := #["-I", (← getLeanIncludeDir).toString,
      "-I", (pkg.dir / "vendor" / "nauty-2.9.3").toString,
      "-fPIC", "-O2", "-std=c11", "-DUSE_TLS"]
    compileO oFile srcFile flags

extern_lib hexnautyffi (pkg) := do
  let name := nameToStaticLib "hexnautyffi"
  let vendorTargets ← #["nauty.c", "nautil.c", "naugraph.c", "schreier.c",
    "naurng.c"].mapM (nautyVendorOTarget pkg)
  let shimTarget ← nautyCanonOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) (vendorTargets.push shimTarget)

lean_lib Hex where

-- Mathlib-free dependencies and producers called during elaboration.
lean_lib HexBasic

lean_lib HexTruncatedSeries where

@[default_target]
lean_lib HexTruncatedSeriesTheory where

lean_lib HexArith where
  precompileModules := true

-- The C objects ride on a separate library that owns the modules binding them.
-- Lake links a module's native library against the whole shared library of any
-- *other* library it imports, objects included, but never adds its own
-- library's `moreLinkObjs`; Windows resolves every symbol at link time, so the
-- objects must sit in a different library from the modules that import them.
-- Declared after `HexArith`, because Lake gives a module to the last library
-- that claims it. These modules import nothing from `HexArith`, and
-- `extended_gcd.c` calls back into `HexArith.Nat.ExtendedGcd`, so both sides
-- of that callback live in one shared library. The single root named after the
-- library makes Lake load it as a plugin; Lean loads every plain dynlib before
-- any plugin, so a carrier that is not a plugin cannot depend on one.
lean_lib HexArithNative where
  roots := #[`HexArithNative]
  globs := #[.one `HexArithNative, .one `HexArith.UInt64.Wide,
    .one `HexArith.Nat.ExtendedGcd]
  precompileModules := true
  moreLinkObjs := #[hexarithWideO, hexarithGcdO]
  -- TODO(lean4#15160): remove -lgmp with the local extended_gcd.c adapter.
  moreLinkArgs := #["-lgmp"]

lean_lib HexPoly where

lean_lib HexPolyFast where

@[default_target]
lean_lib HexOrderedFn where

@[default_target]
lean_lib HexOrderedFnTheory where

@[default_target]
lean_lib HexOrderedFnTests where
  globs := #[.one `HexOrderedFn.Tests, .one `HexOrderedFnTheory.Tests,
    .one `HexOrderedFn.InfinitesimalTests, .one `HexOrderedFnTheory.InfinitesimalTests,
    .one `HexOrderedFn.ExtensionTests, .one `HexOrderedFnTheory.LiouvilleTests,
    .one `HexOrderedFnTheory.LintTests]

lean_lib HexMvPoly where

@[default_target]
lean_lib HexRealFormula where

@[default_target]
lean_lib HexRealFormulaTheory where

lean_lib HexMvGcd where

@[default_target]
lean_lib HexGenericRank where

@[default_target]
lean_lib HexGenericRankTheory where

lean_lib HexReflect where

@[default_target]
lean_lib HexReflectTheory where

@[default_target]
lean_lib HexKronecker where

@[default_target]
lean_lib HexKroneckerTheory where

@[default_target]
lean_lib HexKroneckerTests where
  globs := #[.one `HexKroneckerTheory.Tests]

lean_lib HexSparsePoly where

lean_lib HexModArith where
  precompileModules := true

-- Carries `zmod64_mul.c` for the modules that bind it; see `HexArithNative`.
lean_lib HexModArithNative where
  roots := #[`HexModArithNative]
  globs := #[.one `HexModArithNative, .one `HexModArith.WordMod,
    .one `HexModArith.Residue]
  precompileModules := true
  moreLinkObjs := #[hexmodarithO]

lean_lib HexModular where

@[default_target]
lean_lib HexModularMatrix where

@[default_target]
lean_lib HexModularMatrixTheory where

lean_lib HexGF2 where
  precompileModules := true

lean_lib HexPolyZ where

lean_lib HexPolyZGcd where

@[default_target]
lean_lib HexRationalFn where

@[default_target]
lean_lib HexRationalFnTheory where

lean_lib HexRoots where

lean_lib HexResultant where

lean_lib HexNumberField where

lean_lib HexRealAlgebraic where

@[default_target]
lean_lib HexRealAlgebraicTheory where

@[default_target]
lean_lib HexRealAlgebraicTheoryTests where
  globs := #[.one `HexRealAlgebraicTheory.Tests]

lean_lib HexNumberFieldTower where

lean_lib HexPolyFp where
  precompileModules := true

lean_lib HexGFqRing where

lean_lib HexGFqField where

lean_lib HexBerlekamp where

lean_lib HexHensel where
  -- `WordPoly.mul` has a native convolution extern used by downstream
  -- interpreter-time guards, so its module dynlib must export the stub.
  precompileModules := true

lean_lib HexMvHensel where

lean_lib HexMvFactor where

lean_lib HexConway where

lean_lib HexGFq where

lean_lib HexPrimality

lean_lib HexECPP

lean_lib HexIntFactor where
  globs := #[`HexIntFactor, `HexIntFactor.Pari, `HexIntFactor.Export,
    `HexIntFactor.Replay, `HexIntFactor.Mixed.Replay, `HexIntFactor.Mixed.Import,
    `HexIntFactor.Mixed.Pari, `HexIntFactor.Mixed.Export,
    `HexIntFactor.Mixed.Frozen.Small].map Glob.one
  -- The registered construction provider must also execute natively.
  precompileModules := true

-- Large frozen ECPP endpoints have measured finite replay allocations.
lean_lib HexIntFactorMixedFrozen where
  roots := #[`HexIntFactor.Mixed.Frozen.CaseA, `HexIntFactor.Mixed.Frozen.CaseB,
    `HexIntFactor.Mixed.Frozen.Partial]

lean_lib HexIntFactorTests where
  globs := #[`HexIntFactor.ImportTests, `HexIntFactor.PariTests,
    `HexIntFactor.ExportTests, `HexIntFactor.Mixed.ImportTests,
    `HexIntFactor.Mixed.ExportTests,
    `HexIntFactor.Frozen.Case0,
    `HexIntFactor.Frozen.Case1,
    `HexIntFactor.Frozen.Case2,
    `HexIntFactor.Frozen.Case3,
    `HexIntFactor.Frozen.Case4,
    `HexIntFactor.Frozen.Case5,
    `HexIntFactor.Frozen.Case6, `HexIntFactor.Frozen.Partial12
    ].map Glob.one

lean_lib HexBerlekampZassenhaus where

lean_lib HexRealRoots where

@[default_target]
lean_lib HexSturm where

@[default_target]
lean_lib HexSignDet where

@[default_target]
lean_lib HexSignDetTheory where

lean_lib HexRealClosure where
  -- The runnable selected-root tests use `#eval` across the library boundary.
  precompileModules := true

@[default_target]
lean_lib HexRealClosureTests where
  globs := #[.one `HexRealClosure.Tests, .one `HexRealClosure.PackingTests, .one `HexRealClosure.InversePackingTests, .one `HexRealClosure.RootOrderTests,
    .one `HexRealClosure.RootPolicyTests, .one `HexRealClosure.RootFactorsTests, .one `HexRealClosure.TowerRootsTests,
    .one `HexRealClosure.RootCollectionTests, .one `HexRealClosure.TowerPresentationTests,
    .one `HexRealClosure.LocalSampleTests, .one `HexRealClosure.LiveContextTests,
    .one `HexRealClosure.LiveRequestTests,
    .one `HexRealClosure.TrivialTests, .one `HexRealClosure.TrivialTowerTests,
    .one `HexRealClosure.TowerEnlargeOrderTests,
    .one `HexRealClosure.TowerTransportTests, .one `HexRealClosure.BaseInclusionTests]

-- Native CI capacity probes for the actual certificate/context codecs.
lean_exe hexrealclosure_codec_bytes where
  srcDir := "conformance"
  root := `HexRealClosure.CodecBytesDriver

-- The deep fixture is type-checked above; only its execution is outside routine CI.
lean_exe hexrealclosure_transport_tests where
  root := `HexRealClosure.TowerTransportTests

@[default_target]
lean_lib HexRealClosureTheory where

@[default_target]
lean_lib HexRealClosureTheoryTests where
  globs := #[.one `HexRealClosureTheory.BaseTests,
    .one `HexRealClosureTheory.BaseSubsequenceTests]

@[default_target]
lean_lib HexSturmTheory where

@[default_target]
lean_lib HexSturmTheoryTests where
  globs := #[.one `HexSturmTheory.Tests,
    .one `HexSturmTheory.Tests.Replay.Accepted,
    .one `HexSturmTheory.Tests.Replay.Rejected,
    .one `HexSturmTheory.Tests.Replay.Baseline]

lean_lib HexInterval where

@[default_target]
lean_lib HexPolyTheory where

@[default_target]
lean_lib HexMvPolyTheory where

@[default_target]
lean_lib HexSparsePolyTheory where

@[default_target]
lean_lib HexModArithTheory where

@[default_target]
lean_lib HexPolyZTheory where

@[default_target]
lean_lib HexPolyZGcdTheory where

@[default_target]
lean_lib HexRootsTheory where

@[default_target]
lean_lib HexResultantTheory where

@[default_target]
lean_lib HexNumberFieldTheory where

@[default_target]
lean_lib HexNumberFieldTowerTheory where

@[default_target]
lean_lib HexPolyFpTheory where

lean_lib HexBerlekampTheory where

@[default_target]
lean_lib HexHenselTheory where

@[default_target]
lean_lib HexGF2Theory where

@[default_target]
lean_lib HexGFqTheory where

@[default_target]
lean_lib HexBerlekampZassenhausTheory where

@[default_target]
lean_lib HexPrimalityTheory where

lean_lib HexECPPTheory where
  roots := #[`HexECPPTheory, `HexECPPTheory.Native, `HexECPPTheory.Pari]

-- Lake selects the last matching library. Keep the Mathlib-free IO sidecar
-- after the bridge so only this module needs a shared native library.
lean_lib HexECPPTheoryPariIO where
  roots := #[`HexECPPTheory.Pari.IO]
  globs := #[.one `HexECPPTheory.Pari.IO]
  precompileModules := true
  moreLinkObjs := #[hexecpppariio]

-- The release aggregate also builds these modules. Its manifest equality
-- check requires that registration; all owners use the same Lean settings.
lean_lib HexECPPTheoryTests where
  globs := #[.one `HexECPPTheory.Tests, .one `HexECPPTheory.LintTests]

@[default_target]
lean_lib HexIntFactorTheory where
  roots := #[`HexIntFactorTheory, `HexIntFactorTheory.Mixed]

lean_lib HexMatrix

-- `perm_group` runs the HexPermGroup producer (Schreier-Sims and certificate
-- construction) during elaboration, so it needs native code.
@[default_target]
lean_lib HexPermGroup where
  precompileModules := true

@[default_target]
lean_lib HexPermGroupTheory where

@[default_target]
lean_lib HexPermGroupTests where
  globs := #[.one `HexPermGroup.Tests, .one `HexPermGroup.CertificateTests,
    .one `HexPermGroup.ImportTests,
    .one `HexPermGroupTheory.Tests, .one `HexPermGroupTheory.CertificateTests,
    .one `HexPermGroupTheory.TacticTests]

lean_lib HexGraph where

lean_lib HexGraphIso

@[default_target]
lean_lib HexGraphIsoTheory where

lean_lib HexCharPoly where
  precompileModules := true

lean_lib HexMinPoly where

lean_lib HexPolySmith where

@[default_target]
lean_lib HexPolySmithTheory where

lean_lib HexRowReduce

lean_lib HexDeterminant

lean_lib HexBareiss

lean_lib HexDeterminantalIdeal where

lean_lib HexDet where

lean_lib HexRank where
  precompileModules := true

lean_lib HexHermite where
  precompileModules := true

lean_lib HexSmith where
  precompileModules := true

lean_lib HexHermiteTheory where

lean_lib HexSmithTheory where

lean_lib HexGramSchmidt where

lean_lib HexLatticeEnum where

@[default_target]
lean_lib HexLatticeEnumTheory where

@[default_target]
lean_lib HexLatticeEnumTests where
  globs := #[`HexLatticeEnumTheory.Tests, `HexLatticeEnumTheory.LintTests]

lean_lib HexLLL where
  precompileModules := true
  extraDepTargets := #[`hexlllffi]
  -- `dlopen` lives in libdl on Linux, in libc on macOS, and is absent on
  -- Windows, where the provider uses LoadLibrary instead.
  moreLinkArgs :=
    if System.Platform.isOSX || System.Platform.isWindows then
      #[]
    else
      #["-ldl"]

@[default_target]
lean_lib HexMatrixTheory where

@[default_target]
lean_lib HexCharPolyTheory where

@[default_target]
lean_lib HexMinPolyTheory where

@[default_target]
lean_lib HexRowReduceTheory where

@[default_target]
lean_lib HexDeterminantTheory where

@[default_target]
lean_lib HexDeterminantalIdealTheory where

@[default_target]
lean_lib HexDeterminantalIdealTests where
  globs := #[`HexDeterminantalIdealTheory.Tests]

@[default_target]
lean_lib HexPolyDet where

@[default_target]
lean_lib HexPolyDetTheory where

lean_lib HexPolyDetTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexPolyDetTheory.ProofProbe.Numeric2Hex,
    `HexPolyDetTheory.ProofProbe.Symbolic2Hex,
    `HexPolyDetTheory.ProofProbe.Quotient2Hex,
    `HexPolyDetTheory.ProofProbe.ResultNumeric2Hex,
    `HexPolyDetTheory.ProofProbe.ResultSymbolic2Hex,
    `HexPolyDetTheory.ProofProbe.OriginalQuadratic4,
    `HexPolyDetTheory.ProofProbe.RankOne10].map Glob.one

@[default_target]
lean_lib HexBareissTheory where

lean_lib HexBareissTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexBareissTheory.ProofProbe.Baseline,
    `HexBareissTheory.ProofProbe.MathlibBaseline,
    `HexBareissTheory.ProofProbe.Dense8Hex,
    `HexBareissTheory.ProofProbe.Dense8Mathlib,
    `HexBareissTheory.ProofProbe.Dense12Hex,
    `HexBareissTheory.ProofProbe.Dense12Mathlib,
    `HexBareissTheory.ProofProbe.Dense16Hex,
    `HexBareissTheory.ProofProbe.Dense16Mathlib,
    `HexBareissTheory.ProofProbe.Dense32Hex,
    `HexBareissTheory.ProofProbe.Tridiagonal16Hex,
    `HexBareissTheory.ProofProbe.Tridiagonal16Mathlib,
    `HexBareissTheory.ProofProbe.Vandermonde8Hex,
    `HexBareissTheory.ProofProbe.Vandermonde8Mathlib,
    `HexBareissTheory.ProofProbe.Singular16Hex,
    `HexBareissTheory.ProofProbe.Singular16Mathlib,
    `HexBareissTheory.ProofProbe.Large8Bits64Hex,
    `HexBareissTheory.ProofProbe.Large8Bits64Mathlib,
    `HexBareissTheory.ProofProbe.Large4Bits256Hex,
    `HexBareissTheory.ProofProbe.Large4Bits256Mathlib,
    `HexBareissTheory.ProofProbe.Rational8Hex,
    `HexBareissTheory.ProofProbe.Rational8Mathlib]

@[default_target]
lean_lib HexDetTheory where

lean_lib HexRankTheory where

@[default_target]
lean_lib HexRankTests where
  globs := #[`HexRankTheory.Tests, `HexRankTheory.NumberFieldTests]

@[default_target]
lean_lib HexGenericRankTests where
  globs := #[`HexGenericRankTheory.Tests]

lean_lib HexDeterminantalIdealTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexDeterminantalIdealTheory.ProofProbe.Full2R1,
    `HexDeterminantalIdealTheory.ProofProbe.Full2R2,
    `HexDeterminantalIdealTheory.ProofProbe.Low2R1].map Glob.one

lean_lib HexGenericRankTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexGenericRankTheory.ProofProbe.VariableGeneric,
    `HexGenericRankTheory.ProofProbe.VariableHypothesis,
    `HexGenericRankTheory.ProofProbe.VariableSideGoal,
    `HexGenericRankTheory.ProofProbe.FiniteGeneric].map Glob.one

lean_lib HexRankTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexRankTheory.ProofProbe.Dense8Hex,
    `HexRankTheory.ProofProbe.Deficient16Hex,
    `HexRankTheory.ProofProbe.Rational8Hex,
    `HexRankTheory.ProofProbe.Quadratic8Hex,
    `HexRankTheory.ProofProbe.Algebraic8Hex,
    `HexRankTheory.ProofProbe.NumberFieldSupport].map Glob.one

@[default_target]
lean_lib HexGramSchmidtTheory where

@[default_target]
lean_lib HexLLLTheory where

@[default_target]
lean_lib HexRealRootsTheory where

@[default_target]
lean_lib HexRCF where

-- Optional development adapter: its shared frontend is not yet published.
@[default_target]
lean_lib HexRCFRealFormula where
  srcDir := "adapters"
  globs := #[`HexRCF.RealFormula]

@[default_target]
lean_lib HexRCFRealCoefficients where
  srcDir := "adapters"
  globs := #[`HexRCF.RealCoefficients, `HexRCF.RealCoefficients.Reify,
    `HexRCF.RealCoefficients.Specialize, `HexRCF.RealCoefficients.Coefficients,
    `HexRCF.RealCoefficients.RootAliases, `HexRCF.RealCoefficients.Conversion,
    `HexRCF.RealCoefficients.Interpret,
    `HexRCF.RealCoefficients.Formula, `HexRCF.RealCoefficients.Field,
    `HexRCF.RealCoefficients.LiteralSign, `HexRCF.RealCoefficients.SignIndex,
    `HexRCF.RealCoefficients.FieldIndex,
    `HexRCF.RealCoefficients.IntervalSign, `HexRCF.RealCoefficients.SquareRoot,
    `HexRCF.RealCoefficients.CommonTactic,
    `HexRCF.RealCoefficients.CommonPresentation,
    `HexRCF.RealCoefficients.FieldSpecialize,
    `HexRCF.RealCoefficients.RepresentationSpecialize,
    `HexRCF.RealCoefficients.Samples, `HexRCF.RealCoefficients.Gather,
    `HexRCF.RealCoefficients.SelectedFormula,
    `HexRCF.RealCoefficients.SelectedBytes,
    `HexRCF.RealCoefficients.Realization,
    `HexRCF.RealCoefficients.NumberField,
    `HexRCF.RealCoefficients.SignInputs,
    `HexRCF.RealCoefficients.FieldCarrier, `HexRCF.RealCoefficients.Carrier,
    `HexRCF.RealCoefficients.IsolationCheck, `HexRCF.RealCoefficients.Isolations,
    `HexRCF.RealCoefficients.IsolationBuild, `HexRCF.RealCoefficients.IsolationSemantics,
    `HexRCF.RealCoefficients.IsolationAssembly, `HexRCF.RealCoefficients.IsolationProgress,
    `HexRCF.RealCoefficients.RadicalCheck, `HexRCF.RealCoefficients.Radical,
    `HexRCF.RealCoefficients.RadicalBuild, `HexRCF.RealCoefficients.RadicalProgress,
    `HexRCF.RealCoefficients.FieldDecision, `HexRCF.RealCoefficients.FieldIsolate,
    `HexRCF.RealCoefficients.FieldBuild, `HexRCF.RealCoefficients.FieldSignProgress,
    `HexRCF.RealCoefficients.FieldBuildProgress,
    `HexRCF.RealCoefficients.FieldRoots,
    `HexRCF.RealCoefficients.FieldDecisionProgress,
    `HexRCF.RealCoefficients.FieldBuildBudget,
    `HexRCF.RealCoefficients.FieldRootSigns, `HexRCF.RealCoefficients.FieldRootSignsProgress,
    `HexRCF.RealCoefficients.FieldReplay,
    `HexRCF.RealCoefficients.FieldRefinement,
    `HexRCF.RealCoefficients.FieldLiteral,
    `HexRCF.RealCoefficients.FieldRuntime,
    `HexRCF.RealCoefficients.Preparation,
    `HexRCF.RealCoefficients.FiniteReplay,
    `HexRCF.RealCoefficients.Replay, `HexRCF.RealCoefficients.FieldCompile,
    `HexRCF.RealCoefficients.SquareTwo,
    `HexRCF.RealCoefficients.CubeTwo,
    `HexRCF.RealCoefficients.Selected,
    `HexRCF.RealCoefficients.Tactic,
    `HexRCF.RealCoefficients.CellFormula,
    `HexRCF.RealCoefficients.Registration,
    `HexRCF.RealCoefficients.AlgebraicBounds,
    `HexRCF.RealCoefficients.RationalRoot,
    `HexRCF.RealCoefficients.AlgebraicRoot,
    `HexRCF.RealCoefficients.Finite].map Glob.one

-- Semantic results connecting accepted queries to roots and selected values.
@[default_target]
lean_lib HexQuerySemantics where
  srcDir := "adapters"
  globs := #[`HexSturmTheory.Tests.Replay.Semantics,
    `HexSturmTheory.Tests.Replay.SemanticsBaseline,
    `HexSignDetTheory.RootModel, `HexSignDetTheory.RootProducer,
    `HexSignDetTheory.SelectedRoot, `HexSignDetTheory.SelectedProducer,
    `HexSignDetTheory.CompletionProducer, `HexSignDetTheory.Convert,
    `HexSignDetTheory.DagSelectedSigns, `HexSignDetTheory.Embedding,
    `HexSignDetTheory.Naturality,
    `HexSignDetTheory.QueryHandle, `HexSignDetTheory.TableProducer,
    `HexSignDetTheory.ReencodingProducer, `HexSignDetTheory.RootList,
    `HexSignDetTheory.ReencodingRefinement, `HexSignDetTheory.Thom,
    `HexSignDetTheory.ThomReencoding, `HexSignDetTheory.ThomRoots,
    `HexSignDetTheory.ComparisonProducer,
    `HexRealClosureTheory.Specialize, `HexRealClosureTheory.SpecializeTests,
    `HexRealClosureTheory.SignFacts, `HexRealClosureTheory.SignRequests,
    `HexRealClosureTheory.SignEvidence, `HexRealClosureTheory.FactReplay,
    `HexRealClosureTheory.KernelReplay,
    `HexRealClosureTheory.Packing, `HexRealClosureTheory.InversePacking,
    `HexRealClosureTheory.TransportPolynomial, `HexRealClosureTheory.TransportProduct,
    `HexRealClosureTheory.TransportArithmetic, `HexRealClosureTheory.TransportQuery, `HexRealClosureTheory.TransportTests,
    `HexRealClosureTheory.TransportPower, `HexRealClosureTheory.TransportTarski,
    `HexRealClosureTheory.TransportRing,
    `HexRealClosureTheory.TransportClosed, `HexRealClosureTheory.TransportClosedQuery, `HexRealClosureTheory.TransportClosedReduction, `HexRealClosureTheory.TransportRegular,
    `HexRealClosureTheory.TransportReduction, `HexRealClosureTheory.TransportPreparation, `HexRealClosureTheory.TransportMoment, `HexRealClosureTheory.TransportReplay, `HexRealClosureTheory.TransportSample, `HexRealClosureTheory.TransportDescriptor, `HexRealClosureTheory.TransportInventory, `HexRealClosureTheory.TransportSelected, `HexRealClosureTheory.TransportFiniteTests,
    `HexRealClosureTheory.AlgebraicTransport, `HexRealClosureTheory.AlgebraicYun,
    `HexRealClosureTheory.AlgebraicReencode,
    `HexRealClosureTheory.AlgebraicRoots,
    `HexRealClosureTheory.SpecializePolynomial, `HexRealClosureTheory.SpecializeRegular, `HexRealClosureTheory.SpecializeQuery, `HexRealClosureTheory.SpecializeTarski,
    `HexRealClosureTheory.SpecializeReduction,
    `HexRealClosureTheory.SpecializeMoment,
    `HexRealClosureTheory.SpecializeReplay,
    `HexRealClosureTheory.SpecializeNested,
    `HexRealClosureTheory.SpecializeFractionRing,
    `HexRealClosureTheory.MonicEvaluation,
    `HexRealClosureTheory.RegularEvaluation,
    `HexRealClosureTheory.ModelEvaluation,
    `HexRealClosureTheory.AlgebraicEvaluation, `HexRealClosureTheory.ModelInventory,
    `HexRealClosureTheory.SuffixEvaluation,
    `HexRealClosureTheory.StagedEvaluation,
    `HexRealClosureTheory.BaseEvaluation,
    `HexRealClosureTheory.NativeRealization,
    `HexRealClosureTheory.SharedRealization,
    `HexRealClosureTheory.SharedRealizationTests,
    `HexRealClosureTheory.NativeRealizationTests,
    `HexRealClosureTheory.CoefficientMap, `HexRealClosureTheory.CoefficientComposition,
    `HexRealClosureTheory.CoefficientQuery,
    `HexRealClosureTheory.CoefficientTarski,
    `HexRealClosureTheory.CoefficientEmbeddingTests,
    `HexRealClosureTheory.CoefficientEmbedding,
    `HexRealClosureTheory.CoefficientSelected,
    `HexRealClosureTheory.CoefficientDescriptor,
    `HexRealClosureTheory.CoefficientReplay,
    `HexRealClosureTheory.CoefficientMoment,
    `HexRealClosureTheory.CoefficientReduction,
    `HexRealClosureTheory.SpecializeSample,
    `HexRealClosureTheory.SpecializeSelected,
    `HexRealClosureTheory.SpecializeDescriptor,
    `HexRealClosureTheory.Algebraic, `HexRealClosureTheory.AlgebraicClean,
    `HexRealClosureTheory.TowerModel, `HexRealClosureTheory.TowerModelTests,
    `HexRealClosureTheory.BaseModel,
    `HexRealClosureTheory.BaseOrder,
    `HexRealClosureTheory.BaseMapModel,
    `HexRealClosureTheory.BaseFactory,
    `HexRealClosureTheory.ContextModel,
    `HexRealClosureTheory.BaseFactoryTests, `HexRealClosureTheory.BaseGatherTests,
    `HexRealClosureTheory.CacheModels,
    `HexRealClosureTheory.CacheRebuild,
    `HexRealClosureTheory.CacheGather,
    `HexRealClosureTheory.GatherTests,
    `HexRealClosureTheory.SharedPresentation,
    `HexRealClosureTheory.SharedPresentationTests,
    `HexRealClosureTheory.TowerAlgebraic, `HexRealClosureTheory.TowerRefinement,
    `HexRealClosureTheory.TowerTransport, `HexRealClosureTheory.TowerTransportTests,
    `HexRealClosureTheory.TowerReuse,
    `HexRealClosureTheory.TowerInclusion, `HexRealClosureTheory.LiveContext,
    `HexRealClosureTheory.LiveRequest, `HexRealClosureTheory.LiveRequestTests,
    `HexRealClosureTheory.TowerYun,
    `HexRealClosureTheory.AlgebraicValue, `HexRealClosureTheory.BaseClean, `HexRealClosureTheory.AlgebraicTower,
    `HexRealClosureTheory.SelectedRoot,
    `HexRealClosureTheory.Canonical, `HexRealClosureTheory.Element, `HexRealClosureTheory.QAdjoin,
    `HexRealClosureTheory.NumberField, `HexRealClosureTheory.NumberFieldTower,
    `HexRealClosureTheory.Polynomial, `HexRealClosureTheory.Yun,
    `HexRealClosureTheory.YunInvariant, `HexRealClosureTheory.Bounds,
    `HexRealClosureTheory.Deflation, `HexRealClosureTheory.Bisection,
    `HexRealClosureTheory.BisectionRoots, `HexRealClosureTheory.BisectionFrontier,
    `HexRealClosureTheory.BisectionCounts, `HexRealClosureTheory.Isolation,
    `HexRealClosureTheory.BisectionFactor, `HexRealClosureTheory.IsolationFactor,
    `HexRealClosureTheory.TowerRootPolicy, `HexRealClosureTheory.RootPolicy, `HexRealClosureTheory.IsolationPolicy,
    `HexRealClosureTheory.ZeroFactor, `HexRealClosureTheory.IsolationRoots,
    `HexRealClosureTheory.IsolationTotal,
    `HexRealClosureTheory.RootOrder, `HexRealClosureTheory.RootFactors,
    `HexRealClosureTheory.Trivial, `HexRealClosureTheory.TrivialTower, `HexRealClosureTheory.TrivialTowerTests,
    `HexRealClosureTheory.RootTotal, `HexRealClosureTheory.TowerRoots,
    `HexRealClosureTheory.RootTransport,
    `HexRealClosureTheory.RootCollection, `HexRealClosureTheory.RootList,
    `HexRealClosureTheory.Sample, `HexRealClosureTheory.LocalSample,
    `HexRealClosureTheory.LocalSampleTests,
    `HexRealClosureTheory.SampleTests,
    `HexRealClosureTheory.TowerCoverage, `HexRealClosureTheory.Presentation,
    `HexRealClosureTheory.PresentationTests,
    `HexRealClosureTheory.TowerNaturality,
    `HexRealClosureTheory.Ambient, `HexRealClosureTheory.AmbientTests,
    `HexRealClosureTheory.BaseAlgebraicity, `HexRealClosureTheory.BaseBound,
    `HexRealClosureTheory.EnlargementTests,
    `HexRealClosureTheory.Union, `HexRealClosureTheory.TowerUnion,
    `HexRealClosureTheory.TowerRestriction, `HexRealClosureTheory.TowerEnlarge,
    `HexRealClosureTheory.TowerEnlargeOrder, `HexRealClosureTheory.TowerEnlargeOrderTests,
    `HexRealClosureTheory.UnionTests].map Glob.one

lean_exe hexrealclosure_root_order_tests where
  root := `HexRealClosure.RootOrderTests

-- Ordinary-import consumers of merged family APIs, also built as an isolated
-- local downstream project in experiments/RealClosureConsumer.
@[default_target]
lean_lib RealClosureConsumer where
  srcDir := "examples"
  globs := #[.submodules `RealClosureConsumer]

lean_exe hexlll_external_reduction where
  root := `HexLLL.ExternalReduction

-- Multi-file bench drivers: their modules live under `bench/` and are owned by
-- a precompiled lean_lib (mirroring the released bench sub-project), so the bench
-- exes can root into them. Single-file bench drivers instead carry
-- `srcDir := "bench"` on their own `lean_exe`.
lean_lib HexLLLBenchSupport where
  srcDir := "bench"
  globs := #[`HexLLLBench, `HexLLLBench.Inputs, `HexLLLBench.Targets]

lean_lib HexRankBenchSupport where
  srcDir := "bench"
  globs := #[`HexRank.Bench.Quotient]

lean_lib HexGF2BenchSupport where
  srcDir := "bench"
  globs := #[`HexGF2.Bench]

lean_lib HexBerlekampKernelProbe where
  srcDir := "bench"
  globs := #[`HexBench.BerlekampKernel]

lean_lib HexPrimalityKernelProbe where
  srcDir := "bench"
  globs := #[`HexPrimalityBench.Inputs, `HexBench.PrimalityKernel,
    `HexPrimality.PMinusOneFixtures, `HexIntFactor.PMinusOneFixtures,
    `HexPrimality.PMinusOneMeasure, `HexPrimality.PMinusOneParents].map Glob.one ++
    -- Computational diagnostics emit no proof and observe clocks/counters.
    #[.submodules `HexPrimality.EcmDiagnostics]

lean_lib HexPrimalityElabProbe where
  srcDir := "bench"
  globs := #[`HexPrimalityBench.Inputs, `HexPrimality.ProofProbe.Support,
    `HexPrimality.ProofProbe.CoreBaseline,
    `HexPrimality.ProofProbe.Core512,
    `HexPrimality.ProofProbe.CoreExhausted,
    `HexPrimality.ProofProbe.CoreOverBudget,
    `HexIntFactor.ProofProbe.PrimalityExhausted,
    `HexPrimalityTheory.ProofProbe.MathlibBaseline,
    `HexPrimalityTheory.ProofProbe.Mathlib512,
    `HexPrimalityTheory.ProofProbe.MathlibExhausted,
    `HexPrimalityTheory.ProofProbe.MathlibOverBudget,
    `HexPrimalityTheory.ProofProbe.Negative25,
    `HexPrimalityTheory.ProofProbe.Negative32,
    `HexPrimalityTheory.ProofProbe.Negative64,
    `HexPrimalityTheory.ProofProbe.Negative64Null,
    `HexPrimalityTheory.ProofProbe.Negative65,
    `HexPrimalityTheory.ProofProbe.Negative512,
    `HexPrimalityTheory.ProofProbe.Negative512Odd,
    `HexPrimalityTheory.ProofProbe.NegativeExhausted512]

lean_lib HexPrimalityTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexPrimalityTheory.ProofProbe.Support,
    `HexPrimalityTheory.ProofProbe.FactorExperiment,
    `HexPrimalityTheory.ProofProbe.Baseline,
    `HexPrimalityTheory.ProofProbe.Input31,
    `HexPrimalityTheory.ProofProbe.Literal31,
    `HexPrimalityTheory.ProofProbe.Reify31,
    `HexPrimalityTheory.ProofProbe.Replay31,
    `HexPrimalityTheory.ProofProbe.Primality31,
    `HexPrimalityTheory.ProofProbe.Input512,
    `HexPrimalityTheory.ProofProbe.Literal512,
    `HexPrimalityTheory.ProofProbe.Reify512,
    `HexPrimalityTheory.ProofProbe.Replay512,
    `HexPrimalityTheory.ProofProbe.Primality512,
    `HexPrimalityTheory.ProofProbe.NormNumTrial,
    `HexPrimalityTheory.ProofProbe.NormNumThreshold,
    `HexPrimalityTheory.ProofProbe.NormNum512,
    `HexPrimalityTheory.ProofProbe.MathlibBaseline,
    `HexPrimalityTheory.ProofProbe.Mathlib512,
    `HexPrimalityTheory.ProofProbe.MathlibExhausted,
    `HexPrimalityTheory.ProofProbe.MathlibOverBudget,
    `HexPrimalityTheory.ProofProbe.Negative25,
    `HexPrimalityTheory.ProofProbe.Negative32,
    `HexPrimalityTheory.ProofProbe.Negative64,
    `HexPrimalityTheory.ProofProbe.Negative64Null,
    `HexPrimalityTheory.ProofProbe.Negative65,
    `HexPrimalityTheory.ProofProbe.Negative512,
    `HexPrimalityTheory.ProofProbe.Negative512Odd,
    `HexPrimalityTheory.ProofProbe.Adoption,
    `HexPrimalityTheory.ProofProbe.NegativeExhausted512].map Glob.one ++
    #[.submodules `HexPrimalityTheory.ProofProbe.FactorCorpus]

lean_lib HexECPPTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexECPPTheory.ProofProbe.NativeGeneration,
    `HexECPPTheory.ProofProbe.Native512Baseline,
    `HexECPPTheory.ProofProbe.Native512Reify,
    `HexECPPTheory.ProofProbe.Native512Direct,
    `HexECPPTheory.ProofProbe.Native128_0,
    `HexECPPTheory.ProofProbe.NativeBaseline,
    `HexECPPTheory.ProofProbe.NativeReify,
    `HexECPPTheory.ProofProbe.NativeDirect,
    `HexECPPTheory.ProofProbe.NativeHoldout,
    `HexECPPTheory.ProofProbe.NativeValidation,
    `HexECPPTheory.ProofProbe.NativeUpdated,
    `HexECPPTheory.ProofProbe.Native256_0,
    `HexECPPTheory.ProofProbe.Native256_1,
    `HexECPPTheory.ProofProbe.Native256_2,
    `HexECPPTheory.ProofProbe.Support,
    `HexECPPTheory.ProofProbe.Support17,
    `HexECPPTheory.ProofProbe.Ecpp17,
    `HexECPPTheory.ProofProbe.Pock17,
    `HexECPPTheory.ProofProbe.Baseline65,
    `HexECPPTheory.ProofProbe.Reify65,
    `HexECPPTheory.ProofProbe.Direct65,
    `HexECPPTheory.ProofProbe.Replay65,
    `HexECPPTheory.ProofProbe.Replay256,
    `HexECPPTheory.ProofProbe.Replay512].map Glob.one

lean_lib HexPrimalityConstructionProbe where
  srcDir := "bench"
  globs := #[.submodules `HexPrimality.ProofProbe.Curve25519]

lean_lib HexPrimalityElabProbeScientific where
  srcDir := "bench"
  globs := #[`HexPrimalityBench.Inputs, `HexPrimality.ProofProbe.Support,
    `HexPrimality.ProofProbe.CoreBaseline,
    `HexPrimality.ProofProbe.Bit31.Input,
    `HexPrimality.ProofProbe.Bit31.Search,
    `HexPrimality.ProofProbe.Bit31.Literal,
    `HexPrimality.ProofProbe.Bit31.Replay,
    `HexPrimality.ProofProbe.Bit31.Tactic,
    `HexPrimality.ProofProbe.Bit61.Input,
    `HexPrimality.ProofProbe.Bit61.Search,
    `HexPrimality.ProofProbe.Bit61.Literal,
    `HexPrimality.ProofProbe.Bit61.Replay,
    `HexPrimality.ProofProbe.Bit61.Tactic,
    `HexPrimality.ProofProbe.Bit123.Input,
    `HexPrimality.ProofProbe.Bit123.Search,
    `HexPrimality.ProofProbe.Bit123.Literal,
    `HexPrimality.ProofProbe.Bit123.Replay,
    `HexPrimality.ProofProbe.Bit123.Tactic,
    `HexPrimality.ProofProbe.Bit256.Input,
    `HexPrimality.ProofProbe.Bit256.Search,
    `HexPrimality.ProofProbe.Bit256.Literal,
    `HexPrimality.ProofProbe.Bit256.Replay,
    `HexPrimality.ProofProbe.Bit256.Tactic,
    `HexPrimality.ProofProbe.Bit511.Input,
    `HexPrimality.ProofProbe.Bit511.Search,
    `HexPrimality.ProofProbe.Bit511.Literal,
    `HexPrimality.ProofProbe.Bit511.Replay,
    `HexPrimality.ProofProbe.Bit511.Tactic,
    `HexPrimality.ProofProbe.Bit512.Input,
    `HexPrimality.ProofProbe.Bit512.Search,
    `HexPrimality.ProofProbe.Bit512.Literal,
    `HexPrimality.ProofProbe.Bit512.Replay,
    `HexPrimality.ProofProbe.Bit512.Tactic].map Glob.one ++ #[.submodules `HexPrimality.ProofProbe.PMinusOne]

-- Explicit companion probes for large mixed frozen data.
lean_lib HexIntFactorTheoryProofProbe where
  srcDir := "bench"
  globs := #[Glob.one `HexIntFactorTheory.ProofProbe.Mixed]

lean_lib HexIntFactorTheoryTests where
  globs := #[Glob.one `HexIntFactorTheory.MixedTests]

lean_lib HexIntFactorKernelProbe where
  srcDir := "bench"
  globs := #[`HexBench.IntFactorKernel, `HexIntFactor.FieldBench,
    `HexIntFactor.ProofProbe.Support,
    `HexIntFactor.ProofProbe.Replay1,
    `HexIntFactor.ProofProbe.Replay10,
    `HexIntFactor.ProofProbe.PrimalityExhausted].map Glob.one

lean_lib HexMvGcdKernelProbe where
  srcDir := "bench"
  globs := #[`HexMvGcd.Kernel]

lean_lib HexMvGcdBenchSupport where
  srcDir := "bench"
  globs := #[`HexMvGcd.Families, `HexMvGcd.Matrix,
    `HexMvGcd.ComparatorCases, `HexMvGcd.Comparators,
    `HexMvGcd.Profile, `HexMvGcdFlint, `HexMvGcdSingular]

lean_lib HexMvPolyBenchSupport where
  srcDir := "bench"
  globs := #[`HexMvPolyCorpus, `HexMvPoly.Sorted, `HexMvPoly.SortedTests]

lean_lib HexModularBenchSupport where
  srcDir := "bench"
  globs := #[`HexModularBench.Comparator]

lean_lib HexMvPolyTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexMvPolyTheory.ProofProbe.Examples].map Glob.one

lean_lib HexIntervalExperiment where
  globs := #[`HexInterval.Experiment.Representation,
    `HexInterval.Experiment.Rational, `HexInterval.Experiment.Center,
    `HexInterval.Experiment.Scale, `HexInterval.Experiment.Propagator,
    `HexInterval.Experiment.Policy, `HexInterval.Experiment.PolicyFrontier,
    `HexInterval.Experiment.PolicyDriver,
    `HexInterval.Experiment.PackageRegistry,
    `HexInterval.Experiment.DyadicInterval,
    `HexInterval.Experiment.DyadicRules,
    `HexInterval.Experiment.StructuralMatcher,
    `HexInterval.Experiment.PayloadArena,
    `HexInterval.Experiment.PayloadSession,
    `HexInterval.Experiment.PolicySession,
    `HexInterval.Experiment.TargetRun,
    `HexInterval.Experiment.StagedPolicy,
    `HexInterval.Experiment.AdaptivePolicy,
    `HexInterval.Experiment.PolicyFeature,
    `HexInterval.Experiment.FeaturePolicy,
    `HexInterval.Experiment.BranchStart,
    `HexInterval.Experiment.BranchTree,
    `HexInterval.Experiment.BranchProof,
    `HexInterval.Experiment.SemanticReplay,
    `HexInterval.Experiment.ChronologicalReplay,
    `HexInterval.Experiment.GenericInstanceReconstruction,
    `HexInterval.Experiment.OperationSemantics,
    `HexInterval.Experiment.ProofEmitter,
    `HexInterval.Experiment.ProofRegistry,
    `HexInterval.Experiment.Frontend,
    `HexInterval.Experiment.FrontendEncoder,
    `HexInterval.Experiment.ProofFrontend,
    `HexInterval.Experiment.GoalFrontend,
    `HexInterval.Experiment.GoalClosure,
    `HexInterval.Experiment.TraceReplay,
    `HexInterval.Experiment.SineSign,
    `HexInterval.Experiment.ExpSign,
    `HexInterval.Experiment.PntLogTable,
    `HexInterval.Experiment.PntNestedLog,
    `HexInterval.Experiment.PntExpTail,
    `HexInterval.Experiment.PntTable12,
    `HexInterval.Experiment.PntTable12Ordinary,
    `HexInterval.Experiment.PntTable10Shard,
    `HexInterval.Experiment.PntTable10Convex,
    `HexInterval.Experiment.PntTable10Pointwise,
    `HexInterval.Experiment.PntTable10LargePointwise,
    `HexInterval.Experiment.PntTable10LogCoupled,
    `HexInterval.Experiment.PntTable10A2,
    `HexInterval.Experiment.PntTable12Log,
    `HexInterval.Experiment.PntFks2ShardData,
    `HexInterval.Experiment.PntFks2Shard,
    `HexInterval.Experiment.PntFks2FamilyData00,
    `HexInterval.Experiment.PntFks2FamilyData01,
    `HexInterval.Experiment.PntFks2FamilyData02,
    `HexInterval.Experiment.PntFks2FamilyData03,
    `HexInterval.Experiment.PntFks2FamilyData04,
    `HexInterval.Experiment.PntFks2FamilyData05,
    `HexInterval.Experiment.PntFks2FamilyData06,
    `HexInterval.Experiment.PntFks2FamilyData07,
    `HexInterval.Experiment.PntFks2FamilyData08,
    `HexInterval.Experiment.PntFks2FamilyData09,
    `HexInterval.Experiment.PntFks2FamilyData10,
    `HexInterval.Experiment.PntFks2FamilyData12,
    `HexInterval.Experiment.PntFks2FamilyData13,
    `HexInterval.Experiment.PntFks2FamilyData,
    `HexInterval.Experiment.PntFks2Family,
    `HexInterval.Experiment.PntFks2Structure,
    `HexInterval.Experiment.PntFks2Xpow,
    `HexInterval.Experiment.CosBillion,
    `HexInterval.Experiment.LogTablePrecision,
    `HexInterval.Experiment.PntLogNatural,
    `HexInterval.Experiment.PntFks2Nested,
    `HexInterval.Experiment.PntLogRational,
    `HexInterval.Experiment.PntExpNegative,
    `HexInterval.Experiment.PntExpPoint,
    `HexInterval.Experiment.PntNestedLogTwo,
    `HexInterval.Experiment.PntPiPoint,
    `HexInterval.Experiment.IntegralCanary,
    `HexInterval.Experiment.PntBKLNWExp,
    `HexInterval.Experiment.PntBKLNWPow,
    `HexInterval.Experiment.PntDusartExp,
    `HexInterval.Experiment.PntFks2Mu,
    `HexInterval.Experiment.PntExpUpper,
    `HexInterval.Experiment.PntRamanujanTheta,
    `HexInterval.Experiment.SinTen,
    `HexInterval.Experiment.SinTenInterval,
    `HexInterval.Experiment.MixedFunctions,
    `HexInterval.Experiment.MixedInstantiation].map Glob.one

lean_lib HexIntervalTheoryExperiment where
  globs := #[`HexIntervalTheory.Experiment.Arithmetic,
    `HexIntervalTheory.Experiment.Center,
    `HexIntervalTheory.Experiment.Centered,
    `HexIntervalTheory.Experiment.DyadicInterval,
    `HexIntervalTheory.Experiment.SineSign,
    `HexIntervalTheory.Experiment.ExpSign,
    `HexIntervalTheory.Experiment.PntLogTable,
    `HexIntervalTheory.Experiment.PntNestedLog,
    `HexIntervalTheory.Experiment.PntExpTail,
    `HexIntervalTheory.Experiment.PntTable12,
    `HexIntervalTheory.Experiment.PntTable12Ordinary,
    `HexIntervalTheory.Experiment.PntTable10Shard,
    `HexIntervalTheory.Experiment.PntTable10Convex,
    `HexIntervalTheory.Experiment.PntTable10Pointwise,
    `HexIntervalTheory.Experiment.PntTable10LargePointwise,
    `HexIntervalTheory.Experiment.PntTable10LogCoupled,
    `HexIntervalTheory.Experiment.PntTable10A2,
    `HexIntervalTheory.Experiment.PntTable10Exact,
    `HexIntervalTheory.Experiment.PntTable12Log,
    `HexIntervalTheory.Experiment.PntFks2Shard,
    `HexIntervalTheory.Experiment.PntFks2Xpow,
    `HexIntervalTheory.Experiment.CosBillion,
    `HexIntervalTheory.Experiment.LogTablePrecision,
    `HexIntervalTheory.Experiment.PntLogNatural,
    `HexIntervalTheory.Experiment.PntFks2Nested,
    `HexIntervalTheory.Experiment.PntLogRational,
    `HexIntervalTheory.Experiment.PntExpNegative,
    `HexIntervalTheory.Experiment.PntExpPoint,
    `HexIntervalTheory.Experiment.PntNestedLogTwo,
    `HexIntervalTheory.Experiment.PntPiPoint,
    `HexIntervalTheory.Experiment.IntegralCanary,
    `HexIntervalTheory.Experiment.PntBKLNWExp,
    `HexIntervalTheory.Experiment.PntBKLNWPow,
    `HexIntervalTheory.Experiment.PntDusartExp,
    `HexIntervalTheory.Experiment.PntFks2Mu,
    `HexIntervalTheory.Experiment.PntExpUpper,
    `HexIntervalTheory.Experiment.PntRamanujanTheta,
    `HexIntervalTheory.Experiment.PntPrimeLogSmall,
    `HexIntervalTheory.Experiment.PntChebyshev,
    `HexIntervalAlgebraic.Experiment.PolynomialDispatch,
    `HexIntervalAlgebraic.Experiment.PolynomialDispatchProof,
    `HexIntervalTheory.Experiment.SinTen,
    `HexIntervalTheory.Experiment.SinTenInterval,
    `HexIntervalTheory.Experiment.MixedFunctions,
    `HexIntervalTheory.Experiment.MixedInstantiation].map Glob.one

@[default_target]
lean_lib HexIntervalTheory where
  globs := #[`HexIntervalTheory, `HexIntervalTheory.Interval,
    `HexIntervalTheory.Addition, `HexIntervalTheory.Subtraction,
    `HexIntervalTheory.MinMax, `HexIntervalTheory.Absolute,
    `HexIntervalTheory.Multiplication,
    `HexIntervalTheory.Power, `HexIntervalTheory.Split,
    `HexIntervalTheory.Inverse, `HexIntervalTheory.Division,
    `HexIntervalTheory.Regularize, `HexIntervalTheory.Program,
    `HexIntervalTheory.Proof, `HexIntervalTheory.Rule,
    `HexIntervalTheory.Frontend,
    `HexIntervalTheory.Tactic].map Glob.one

lean_lib HexIntervalReplayProbe where
  srcDir := "bench"
  globs := #[`HexInterval.ReplayBaseline, `HexInterval.ReplayBundled,
    `HexInterval.ReplayChecked, `HexInterval.ReplayRationalBaseline,
    `HexInterval.ReplayRationalDirect, `HexInterval.ReplayRationalChecked,
    `HexInterval.ReplayRational, `HexInterval.ImportBundled,
    `HexInterval.ImportChecked, `HexInterval.WhnfBundled,
    `HexInterval.WhnfChecked, `HexInterval.WhnfBaseline,
    `HexInterval.WhnfRationalDirect, `HexInterval.WhnfRationalChecked,
    `HexInterval.WhnfRationalBaseline, `HexInterval.ReplayCenterBaseline,
    `HexInterval.ReplayCenterChecked, `HexInterval.WhnfCenterChecked,
    `HexInterval.WhnfCenterBaseline, `HexInterval.WhnfScaleChecked,
    `HexInterval.WhnfScaleBaseline, `HexInterval.ReplayScaleChecked,
    `HexInterval.ReplayScaleBaseline]

lean_lib HexIntervalTheoryReplayProbe where
  srcDir := "bench"
  globs := #[`HexIntervalTheory.CenterDirect,
    `HexIntervalTheory.CenterReflected].map Glob.one

lean_lib HexRealRootsTheoryReplayProbe where
  srcDir := "bench"
  globs := #[`HexRealRootsTheory.ProofProbe.Natural6,
    `HexRealRootsTheory.ProofProbe.Refined2,
    `HexRealRootsTheory.ProofProbe.RealClosed].map Glob.one

lean_lib HexBerlekampZassenhausTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexBerlekampZassenhausTheory.ProofProbe.Factor4,
    `HexBerlekampZassenhausTheory.ProofProbe.Irreducible4,
    `HexBerlekampZassenhausTheory.ProofProbe.Repeated8,
    `HexBerlekampZassenhausTheory.ProofProbe.Kernel4].map Glob.one

lean_lib HexBerlekampTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexBerlekampTheory.ProofProbe.Factor4,
    `HexBerlekampTheory.ProofProbe.Irreducible4,
    `HexBerlekampTheory.ProofProbe.Repeated8].map Glob.one

lean_lib HexSignDetTheoryProofProbe where
  srcDir := "bench"
  globs := #[.submodules `HexSignDetTheory.ProofProbe]

-- Correctness diagnostics remain CI-built outside the benchmark root.
lean_lib HexSignDetTheoryDiagnostics where
  srcDir := "conformance"
  globs := #[.submodules `HexSignDetTheory.Diagnostics]

-- Depth-three kernel reductions retain their separate manual target.
lean_lib HexSignDetTheoryDepthThree where
  srcDir := "conformance"
  globs := #[.submodules `HexSignDetTheory.DepthThree]

lean_lib HexRealFormulaProofProbe where
  srcDir := "bench"
  globs := #[`HexRealFormulaTheory.ProofProbe.Support,
    `HexRealFormulaTheory.ProofProbe.Parameterized,
    `HexRealFormulaTheory.ProofProbe.Alternation].map Glob.one

lean_lib HexRCFBenchSupport where
  srcDir := "bench"
  globs := #[`HexRCF.BenchHash].map Glob.one

lean_lib HexRCFProofProbe where
  srcDir := "bench"
  globs := #[`HexRCF.ProofProbe.Examples,
    `HexRCF.ProofProbe.Registered.Unused,
    `HexRCF.ProofProbe.Registered.Support,
    `HexRCF.ProofProbe.Registered.Tactic].map Glob.one

-- Conformance #guard drivers live under `conformance/` and are built by this
-- library (mirroring the released conformance sub-projects). Alongside each
-- library's `Conformance` core module, the heavier cross-check sweeps and
-- extern-path fast checks (`CrossCheck` / `FastCheck`) also live here so the
-- implementation-vs-testing boundary stays legible; they elaborate their
-- `#guard`s in the same `lake build`. EmitFixtures drivers are the
-- `*_emit_fixtures` exes below, carrying `srcDir := "conformance"`.
/-- Libraries whose conformance modules are not built while they are parked.
HexInterval is parked: none of its libraries, executables or conformance
modules are built in CI. Remove a prefix here to restore its conformance. -/
def parkedConformancePrefixes : List String := ["HexInterval"]

def isParkedGlob : Glob → Bool
  | .one n | .submodules n | .andSubmodules n =>
    parkedConformancePrefixes.any (n.getRoot.toString.startsWith ·)

lean_lib HexConformance where
  srcDir := "conformance"
  globs := Array.filter (fun g => !isParkedGlob g) <| #[
`HexArith.Conformance, `HexArith.CrossCheck, `HexBerlekamp.Conformance, `HexBerlekampZassenhaus.Conformance, `HexBerlekampZassenhaus.CrossCheck, `HexBerlekampZassenhausTheory.Conformance, `HexConway.Conformance, `HexGF2.Conformance, `HexGF2.CrossCheck, `HexGF2.FastCheck, `HexGFq.Conformance, `HexGFq.CrossCheck, `HexGFqField.Conformance, `HexGFqRing.Conformance, `HexGramSchmidt.Conformance, `HexGraphIso.Conformance, `HexHensel.Conformance, `HexHensel.CrossCheck, `HexInterval.Conformance, `HexIntervalTheory.IntervalConformance, `HexInterval.CenterConformance, `HexInterval.ScaleConformance, `HexInterval.PropagatorConformance, `HexInterval.ScopeConformance, `HexInterval.StructuralMatcherConformance, `HexInterval.MatcherSchedulerConformance, `HexInterval.NestedBranchConformance, `HexInterval.StructureViewConformance, `HexInterval.PolicyConformance, `HexInterval.PolicyFrontierConformance, `HexInterval.PolicyDriverConformance, `HexInterval.PackageRegistryConformance, `HexInterval.DyadicIntervalConformance, `HexInterval.DyadicRulesConformance, `HexInterval.PayloadArenaConformance, `HexInterval.PayloadSessionConformance, `HexInterval.PolicySessionConformance, `HexInterval.PolicyFunctionConformance, `HexInterval.SemanticReplayConformance, `HexInterval.ChronologicalReplayConformance, `HexInterval.GenericInstanceReconstructionConformance, `HexInterval.ProofEmitterConformance, `HexInterval.TraceReplayConformance, `HexInterval.SinTenIntervalConformance, `HexIntervalTheory.DyadicIntervalConformance, `HexIntervalTheory.CenteredConformance, `HexIntervalTheory.SineSignConformance, `HexIntervalTheory.SineProofConformance, `HexIntervalTheory.SineTacticConformance, `HexIntervalTheory.ProofRegistryConformance, `HexIntervalTheory.ExpSignConformance, `HexIntervalTheory.ReluConformance, `HexIntervalTheory.RefuteConformance, `HexIntervalTheory.PntLogTableConformance, `HexIntervalTheory.PntNestedLogConformance, `HexIntervalTheory.PntExpTailConformance, `HexIntervalTheory.PntTable12Conformance, `HexIntervalTheory.PntTable12OrdinaryConformance, `HexIntervalAlgebraic.PolynomialDispatchConformance, `HexIntervalTheory.PntTable12LogConformance, `HexIntervalTheory.PntFks2ShardConformance, `HexIntervalTheory.LogTablePrecisionConformance, `HexIntervalTheory.IntegralCanaryConformance, `HexIntervalTheory.PntBKLNWExpConformance, `HexIntervalTheory.PntBKLNWPowConformance, `HexIntervalTheory.PntPrimeLogSmallConformance, `HexIntervalTheory.PntDusartExpConformance, `HexIntervalTheory.SinTenConformance, `HexIntervalTheory.SinTenIntervalConformance, `HexIntervalTheory.CosBillionConformance, `HexHermite.Conformance, `HexLLL.Conformance, `HexMatrix.Conformance, `HexRealFormula.Conformance, `HexRealFormulaTheory.Conformance, `HexRealFormulaTheory.Arithmetic, `HexMvPolyFixtures, `HexMvPoly.Conformance, `HexMvPolyTheory.Conformance, `HexSparsePolyFixtures, `HexSparsePoly.Conformance, `HexRowReduce.Conformance, `HexDeterminant.Conformance, `HexDeterminantalIdealFixtures, `HexDeterminantalIdeal.Conformance, `HexDeterminant.Carriers, `HexBareiss.Fixtures, `HexBareiss.Conformance, `HexModularMatrix.Fixtures, `HexModularMatrix.Conformance, `HexDet.Conformance, `HexDet.Carriers, `HexCharPoly.Fixtures, `HexCharPoly.Carriers, `HexCharPoly.Conformance, `HexModArith.Conformance, `HexModArith.FastCheck, `HexModular.Conformance, `HexPolyZGcd.Conformance, `HexMvGcd.Conformance, `HexNumberField.Conformance, `HexNumberFieldTower.Conformance, `HexPoly.Conformance, `HexPrimality.CertificateProducer, `HexPrimality.ConstructionConformance, `HexPrimality.ConstructionRetry, `HexPrimality.ConstructionRegistration, `HexPrimality.Curve25519Replay, `HexPrimality.Curve448Replay, `HexPrimality.SqufofConformance, `HexPrimality.Conformance, `HexECPP.NativeConformance, `HexECPP.Conformance, `HexECPP.Fixture17, `HexECPP.PolicyProbe, `HexECPP.Fixture65, `HexECPP.Fixture256, `HexECPP.Fixture512, `HexECPP.PariFixtures, `HexECPP.ImportConformance, `HexECPPTheory.NativeConformance, `HexECPPTheory.NativeFixtures, `HexECPPTheory.Conformance, `HexECPPTheory.CompactFixtures, `HexECPPTheory.CompactReject, `HexECPPTheory.PariProcess, `HexECPPTheory.Reject, `HexECPPTheory.HasseAudit, `HexECPPTheory.SoundnessAudit, `HexPrimalityTheory.Conformance, `HexPrimalityTheoryConformance.OptIn, `HexPolyFp.Conformance, `HexPolyZ.Conformance, `HexRCF.Conformance, `HexRealRoots.Conformance, `HexRealRootsTheory.Conformance, `HexResultant.Conformance, `HexRoots.Conformance].map Glob.one ++
    #[`HexPolyDet.Conformance, `HexRank.Conformance, `HexGenericRank.Conformance, `HexGenericRank.Fixtures, `HexRowReduce.FieldFixtures, `HexRealFormulaTheory.ReifierConformance, `HexRCF.RealFormulaConformance, `HexRCF.RealCoefficientsConformance, `HexRCF.AlgebraicProgress, `HexRCF.IsolationProgress, `HexRCF.RadicalProgress, `HexRCF.ProductionProgress, `HexRCF.FieldRootsConformance, `HexRCF.CertificationInputs, `HexRCF.RationalSources, `HexRCF.ProofEvidence, `HexRCF.CheckedConversions, `HexRCF.ReplayModes, `HexRCF.CarrierModes, `HexRCF.SignIndex, `HexRCF.PreparedCoefficients, `HexRCF.FiniteReplay, `HexRCF.TowerSamples, `HexRCF.Samples, `HexRCF.RealizationData, `HexRCF.Realization, `HexRCF.NumberField, `HexRCF.Gather, `HexRCF.GeneratorWindowInputs, `HexRCF.GeneratorWindow, `HexRCF.CertificationProofs, `HexRCF.TotalAlgebraicProofs, `HexRCF.AlgebraicDivision, `HexRCF.NormalizedCoefficients, `HexRCF.NormalizedInputs, `HexRCF.RegisteredConstants, `HexRCF.NamedConstants, `HexRCF.MixedConstants, `HexRCF.CoarseConstants, `HexRCF.RealCoefficientTactic, `HexRCF.RealCoefficientCommonField, `HexRCF.CommonFieldPresentation, `HexRCF.RootAliasesConformance, `HexRCF.RationalRoots, `HexRCF.AlgebraicRoots, `HexRCF.FormulaConformance, `HexRCF.LiteralSignConformance, `HexRCF.FieldSpecializeConformance, `HexRCF.SignDetFieldProofs, `HexRCF.AdmissionConformance, `HexRCF.IsolationConformance].map Glob.one

    ++ #[
      `HexRCF.SelectedRoot.Packing, `HexRCF.SelectedRoot.PackingData,
      `HexRCF.SelectedRoot.PackingReplay, `HexRCF.SelectedRoot.PackingMissing, `HexRCF.SelectedRoot.PackingAudit,
      `HexRCF.SelectedRoot.ByteAudit, `HexRCF.SelectedRoot.ByteBounds, `HexRCF.SelectedRoot.ByteChecks,
      `HexRCF.SelectedRoot.ByteData, `HexRCF.SelectedRoot.ByteProofs,
      `HexRCF.SelectedRoot.Audit, `HexRCF.SelectedRoot.Checks, `HexRCF.SelectedRoot.Collect,
      `HexRCF.SelectedRoot.Controls, `HexRCF.SelectedRoot.Data, `HexRCF.SelectedRoot.Frozen,
      `HexRCF.SelectedRoot.FrozenCollect, `HexRCF.SelectedRoot.KernelCheck, `HexRCF.SelectedRoot.Intermediates, `HexRCF.SelectedRoot.Literals,
      `HexRCF.SelectedRoot.PacketFields, `HexRCF.SelectedRoot.Packets, `HexRCF.SelectedRoot.Proofs,
      `HexRCF.SelectedRoot.Read, `HexRCF.SelectedRoot.Refusals, `HexRCF.SelectedRoot.ReplayTools,
      `HexRCF.SelectedRoot.Row, `HexRCF.SelectedRoot.RowCollect, `HexRCF.SelectedRoot.RowIntermediates,
      `HexRCF.SelectedRoot.RowTools, `HexRCF.SelectedRoot.Source, `HexRCF.SelectedRoot.Upper].map Glob.one

    ++ #[`HexRealAlgebraic.Conformance, `HexRealAlgebraic.Checks,
      `HexRealAlgebraic.FieldSignConformance, `HexNumberField.ComplexChecks,
      `HexRealAlgebraic.ReprChecks, `HexRealClosure.ReprChecks, `HexRealAlgebraicTheory.FieldSignConformance].map Glob.one

    ++ #[`HexReflect.TestProviders, `HexReflect.Conformance, `HexReflect.ScopeConformance, `HexReflect.ResidueConformance].map Glob.one

    ++ #[`HexSignDet.CommonField, `HexSignDet.Conformance, `HexSignDet.CrossCheck, `HexSignDet.FastCheck, `HexSignDet.JsonBytes, `HexSignDet.DescriptorCodec, `HexSignDet.Infinitesimal].map Glob.one

    ++ #[`HexRealClosure.BisectionFrontierTests, `HexRealClosure.IsolationTests,
      `HexRealClosureTheory.CoefficientSignsConformance,
      `HexRealClosureTheory.DependenciesConformance,
      `HexRealClosureTheory.PackingConformance,
      `HexRealClosureTheory.ContextOperationsConformance,
      `HexRealClosureTheory.ContextOperationsPublic,
      `HexRealClosureTheory.NestedSignsConformance,
      `HexRealClosureTheory.SignCodecConformance,
      `HexRealClosureTheory.SignFactsConformance,
      `HexRealClosureTheory.SignRequestsConformance,
      `HexRealClosureTheory.SignEvidenceConformance].map Glob.one

    ++ #[`HexSturm.Fixtures, `HexSturm.Conformance].map Glob.one

    ++ #[`HexKronecker.Conformance].map Glob.one

    ++ #[`HexSmith.Conformance].map Glob.one

    ++ #[`HexMinPoly.Fixtures, `HexMinPoly.Conformance].map Glob.one

    ++ #[`HexTruncatedSeries.Conformance].map Glob.one

    ++ #[`HexPolyFast.Conformance, `HexPolyFast.Lint].map Glob.one

    ++ #[`HexRationalFn.Conformance, `HexRationalFn.Domains, `HexOrderedFn.Conformance].map Glob.one

    ++ #[`HexLatticeEnum.Conformance].map Glob.one

    ++ #[`HexMvHensel.Conformance, `HexMvFactor.Conformance].map Glob.one

    ++ #[`HexIntFactor.Conformance, `HexIntFactor.EcmTables,
      `HexIntFactor.FieldReplay,
      `HexIntFactor.PrimalityConformance].map Glob.one

    ++ #[`HexPolySmith.Conformance].map Glob.one

    ++ #[`HexIntervalTheory.PntLogNaturalConformance,
      `HexIntervalTheory.PntLogRationalConformance,
      `HexIntervalTheory.PntExpNegativeConformance,
      `HexIntervalTheory.PntExpPointConformance].map Glob.one

    ++ #[`HexIntervalTheory.PntNestedLogTwoConformance,
      `HexIntervalTheory.PntPiPointConformance].map Glob.one

    ++ #[`HexIntervalTheory.PntChebyshevConformance].map Glob.one

    ++ #[`HexIntervalTheory.PntFks2MuConformance,
      `HexIntervalTheory.PntExpUpperConformance,
      `HexIntervalTheory.PntRamanujanThetaConformance].map Glob.one

    ++ #[`HexIntervalTheory.PntFks2NestedConformance].map Glob.one

    ++ #[`HexIntervalTheory.PntFks2StructureConformance].map Glob.one

    ++ #[`HexIntervalTheory.PntTable10ShardConformance,
      `HexIntervalTheory.PntTable10ConvexConformance,
      `HexIntervalTheory.PntTable10PointwiseConformance,
      `HexIntervalTheory.PntTable10LargePointwiseConformance,
      `HexIntervalTheory.PntTable10LogCoupledConformance,
      `HexIntervalTheory.PntTable10A2Conformance,
      `HexIntervalTheory.PntTable10ExactConformance].map Glob.one

    ++ #[`HexInterval.StagedPolicyConformance].map Glob.one

    ++ #[`HexIntervalTheory.ArithmeticConformance].map Glob.one

    ++ #[`HexInterval.MinMaxConformance,
      `HexIntervalTheory.MinMaxConformance].map Glob.one

    ++ #[`HexGraphIso.Cases, `HexGraphIso.SparseCases, `HexPermGroup.Conformance,
      `HexPermGroup.KernelConformance, `HexPermGroup.Limits].map Glob.one

    ++ #[`HexInterval.PolicyFeatureConformance,
      `HexInterval.FeaturePolicyConformance,
      `HexInterval.SearchConformance,
      `HexInterval.ExecutableConformance,
      `HexInterval.RuntimeConformance,
      `HexIntervalTheory.RuntimeProofConformance,
      `HexIntervalTheory.RuntimeTerminalConformance,
      `HexIntervalTheory.RuntimeRuleConformance,
      `HexIntervalTheory.RuntimeEmitConformance,
      `HexIntervalTheory.ProgramProofConformance,
      `HexIntervalTheory.DriverConformance,
      `HexIntervalTheory.ControllerConformance,
      `HexIntervalTheory.ExecutableControllerConformance,
      `HexIntervalTheory.RuleConformance,
      `HexIntervalTheory.FrontendConformance,
      `HexIntervalTheory.TacticConformance,
      `HexIntervalTheory.MixedFunctionsConformance,
      `HexIntervalTheory.MixedInstantiationConformance,
      `HexIntervalTheory.ExactBranchConformance].map Glob.one

    ++ #[`HexECPPTheory.CompositeDivisors, `HexECPPTheory.NodeBudget,
      `HexECPPTheory.ModuleImports].map Glob.one

-- The expensive complete-family Mathlib proofs are owned only by this
-- non-default library. They are excluded from both merge-gating
-- `HexIntervalTheoryExperiment` and `HexConformance`.
lean_lib HexIntervalPntFks2Local where
  globs := #[`HexIntervalTheory.Experiment.PntFks2XpowProof00,
    `HexIntervalTheory.Experiment.PntFks2XpowProof01,
    `HexIntervalTheory.Experiment.PntFks2XpowProof02,
    `HexIntervalTheory.Experiment.PntFks2XpowProof03,
    `HexIntervalTheory.Experiment.PntFks2XpowProof04,
    `HexIntervalTheory.Experiment.PntFks2XpowProof05,
    `HexIntervalTheory.Experiment.PntFks2XpowResults,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof00,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof01,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof02,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof03,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof04,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof05,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof06,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof07,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof08,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof09,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof10,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof12,
    `HexIntervalTheory.Experiment.PntFks2FamilyProof13,
    `HexIntervalTheory.Experiment.PntFks2Family].map Glob.one

lean_lib HexIntervalPntFks2ConformanceLocal where
  srcDir := "conformance"
  globs := #[`HexIntervalTheory.PntFks2XpowConformance].map Glob.one

-- The local executable owns the complete runtime and guarded-axiom driver.
lean_exe hex_interval_pnt_fks2_local where
  srcDir := "conformance"
  root := `HexIntervalTheory.PntFks2FamilyConformance

-- Public umbrellas intentionally contain only the supported API. Executable
-- examples and regression tests are compiled through this separate target so
-- removing them from an umbrella cannot silently remove them from CI.
lean_lib HexReleaseTests where
  globs := #[`HexArith.ExtendedGcdTests, `HexECPPTheory.Tests, `HexPoly.InterpretTests, `HexPoly.PseudoTests,
    `HexPolyTheory.InterpretTests, `HexPolyTheory.PseudoTests,
    `HexMatrixTheory.Tests,
    `HexPolyTheory.LiteralTests,
    `HexBareissTheory.Tests,
    `HexRowReduceTheory.Tests,
    `HexBerlekamp.FactorTacticTests,
    `HexBerlekampTheory.FactorPolyTests,
    `HexBerlekampZassenhaus.FactorTacticTests,
    `HexBerlekampZassenhausTheory.FactorPolyTests,
    `HexBerlekampZassenhausTheory.PublicReplayTests,
    `HexBerlekampZassenhausTheory.QuotationTests,
    `HexBerlekampZassenhausTheory.IrreducibilityTests,
    `HexRealRoots.ReplayTest,
    `HexRealRoots.TarskiTests,
    `HexRealRootsTheory.IsolateRootsTests,
    `HexRealRootsTheory.IsolateRootsElabTests,
    `HexRealRootsTheory.SturmTests,
    `HexRealRootsTheory.RealRootCountTests,
    `HexRealRootsTheory.TarskiTests,
    `HexRootsTheory.Examples,
    `HexPrimality.Examples.Curve25519,
    `HexModular.KernelTests, `HexModular.LoopTests,
    `HexMvPoly.KernelTests,
    `HexMvPoly.KernelResidueTests,
    `HexMvPolyTheory.KernelResidueTests,
    `HexSparsePoly.KernelTests,
    `HexGraphIso.TestGraphs,
    `HexGraphIso.SparseTests,
    `HexGraphIso.TacticTests,
    `HexGraphIso.ModuleBoundaryTests,
    `HexBasic.ModuleBoundaryTests,
    `HexGraphIsoTheory.TacticTests,
    `HexGraphIsoTheory.SparseTacticTests,
    `HexPermGroup.Tests,
    `HexPermGroup.CertificateTests,
    `HexPermGroup.ImportTests,
    `HexPermGroupTheory.Tests,
    `HexPermGroupTheory.CertificateTests,
    `HexPermGroupTheory.TacticTests,
    `HexNumberFieldTower.Embed,
    `HexRCF.LanguageTests,
    `HexRCF.SturmBuilderTests,
    `HexRCF.CarrierTests,
    `HexRCF.IsolationsTests,
    `HexRCF.SeparationTests,
    `HexRCF.CellsTests,
    `HexRCF.CommonRootTests,
    `HexRCF.SignMatrixTests,
    `HexRCF.BuilderTests,
    `HexRCF.CertificateTests,
    `HexRCF.DecisionTests,
    `HexRCF.ReifyTests,
    `HexRCF.HandlerTests.Support, `HexRCF.HandlerTests.Async,
    `HexRCF.HandlerTests,
    `HexRCF.LintTests]
    -- a name array mapped through Glob.one: an array literal this long is
    -- elaborated in chunks, on which the name-to-glob coercion fails
    |>.map Glob.one

-- TODO(lean4#15160): after removing the backport, keep the Hex signed API
-- regression coverage and remove copied upstream primitive cases.
lean_exe hexarith_extgcd_tests where
  root := `HexArith.ExtendedGcdTests

-- Build-only regression roots for the structural matrix frontends.
@[default_target]
lean_lib HexStructuralTacticTests where
  globs := #[`HexPolyDetTheory.Tests, `HexMinPolyTheory.Tests, `HexSmithTheory.Tests, `HexHermiteTheory.Tests, `HexRowReduceTheory.Tests]

lean_lib HexStructuralTacticProofProbe where
  srcDir := "bench"
  globs := #[.submodules `HexMinPolyTheory.ProofProbe,
    .submodules `HexSmithTheory.ProofProbe, .submodules `HexHermiteTheory.ProofProbe,
    .submodules `HexRowReduceTheory.ProofProbe]

-- Verification-only modules for the incubating multivariate factorization
-- stack. Keep this separate from the released-test target, whose module list
-- must exactly mirror the repositories already present in the release manifest.
lean_lib HexMvFactorizationTests where
  globs := #[`HexPolyZGcd.Kernel,
    `HexMvGcd.KernelTests,
    `HexMvGcd.CertTests,
    `HexMvGcd.Eval,
    `HexMvGcd.SquarefreeTests,
    `HexMvHensel.KernelTests,
    `HexMvHensel.ShiftTests,
    `HexMvHensel.UniTests,
    `HexMvHensel.DiophantineTests,
    `HexMvHensel.SeedTests,
    `HexMvHensel.CertTests,
    `HexMvHensel.LiftTests,
    `HexMvHensel.CompleteTests,
    `HexMvFactor.KernelTests,
    `HexMvFactor.KroneckerTests,
    `HexMvFactor.LeadingTests,
    `HexMvFactor.PointTests,
    `HexMvFactor.InputTests,
    `HexMvFactor.EezTests,
    `HexMvFactor.FactorTests,
    `HexMvFactor.CompleteTests]

-- Complete development imports for the two factorization packages. Their
-- ordinary umbrellas deliberately expose only the supported release API.
lean_lib HexFactorizationModules where
  globs := #[`HexECPPTheory.Native, `HexECPPTheory.Pari,
    `HexBerlekampZassenhaus.All,
    `HexBerlekampZassenhausTheory.All]

-- Monorepo-only lint regression for the sparse-poly pair; the kernel
-- probes live in HexReleaseTests alongside the release manifest's
-- test_modules entry.
@[default_target]
lean_lib HexSparsePolyTests where
  globs := #[`HexSparsePolyTheory.LintTests]

-- Declaration linting runs in monorepo CI. The lint source is copied to the
-- mirror with its bridge library; mirror CI builds the published API.
@[default_target]
lean_lib HexTruncatedSeriesTests where
  globs := #[`HexTruncatedSeriesTheory.LintTests]

-- Monorepo-only lint regression for the integer Smith pair. It moves into the
-- release-manifest-backed test target when the pair is published.
@[default_target]
lean_lib HexSmithTests where
  globs := #[`HexSmith.QuickstartTests,
    `HexSmithTheory.LintTests,
    `HexSmithTheory.QuickstartTests]

-- HexCharPoly is not yet a published split repository (its released.yml
-- entries were withdrawn until the phase pipeline completes), so its
-- verification-only elaborator regressions stay separate from the
-- release-manifest-backed target above; they rejoin HexReleaseTests (and
-- the manifest's test_modules) at publication.
@[default_target]
lean_lib HexCharPolyTests where
  globs := #[`HexCharPoly.CharPolyElabTests,
    `HexCharPolyTheory.CharPolyElabTests]

-- Mirrors the released aggregate's module-system umbrella, so a library that
-- never adopted the module system fails here instead of after the publish-out
-- sync. `check_released_manifest.py` keeps the import list equal to the
-- `leanprover/hex` pins in `scripts/release/released.yml`.
@[default_target]
lean_lib HexAggregateCheck where

-- Canonical end-to-end examples are release artifacts rather than public API.
-- Keep their target separate for the same reason as the regression tests.
lean_lib HexReleaseExamples where
  globs := #[`Examples.Release1, `Examples.Release3, `Examples.Release4, `Examples.Release5,
    `Examples.FiniteFields, `Examples.DeterminantKernelProof, `Examples.RowReduce]

lean_exe hexrowreduce_emit_fixtures where
  srcDir := "conformance"
  root := `HexRowReduce.EmitFixtures

lean_exe hexdeterminant_emit_fixtures where
  srcDir := "conformance"
  root := `HexDeterminant.EmitFixtures

lean_exe hexdeterminant_emit_carrier_fixtures where
  srcDir := "conformance"
  root := `HexDeterminant.EmitCarrierFixtures

lean_exe hexpolydet_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolyDet.EmitFixtures

lean_exe hexbareiss_emit_carrier_fixtures where
  srcDir := "conformance"
  root := `HexBareiss.EmitCarrierFixtures

lean_exe hexmodularmatrix_emit_fixtures where
  srcDir := "conformance"
  root := `HexModularMatrix.EmitFixtures

lean_exe hexbareiss_emit_fixtures where
  srcDir := "conformance"
  root := `HexBareiss.EmitFixtures

lean_exe hexdet_emit_fixtures where
  srcDir := "conformance"
  root := `HexDet.EmitFixtures

lean_exe hexdet_emit_carrier_fixtures where
  srcDir := "conformance"
  root := `HexDet.EmitCarrierFixtures

lean_exe hexgenericrank_emit_fixtures where
  srcDir := "conformance"
  root := `HexGenericRank.EmitFixtures

lean_exe hexrank_emit_fixtures where
  srcDir := "conformance"
  root := `HexRank.EmitFixtures

lean_exe hexhermite_emit_fixtures where
  srcDir := "conformance"
  root := `HexHermite.EmitFixtures

lean_exe hexsmith_emit_fixtures where
  srcDir := "conformance"
  root := `HexSmith.EmitFixtures

lean_exe hexcharpoly_emit_carrier_fixtures where
  srcDir := "conformance"
  root := `HexCharPoly.EmitCarrierFixtures

lean_exe hexcharpoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexCharPoly.EmitFixtures

lean_exe hexminpoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexMinPoly.EmitFixtures

lean_exe hexgramschmidt_emit_fixtures where
  srcDir := "conformance"
  root := `HexGramSchmidt.EmitFixtures

lean_exe hexlll_emit_fixtures where
  srcDir := "conformance"
  root := `HexLLL.EmitFixtures

lean_exe hexlatticeenum_emit_fixtures where
  srcDir := "conformance"
  root := `HexLatticeEnum.EmitFixtures

lean_exe hexrealroots_emit_fixtures where
  srcDir := "conformance"
  root := `HexRealRoots.EmitFixtures

lean_exe hexsigndet_emit_fixtures where
  srcDir := "conformance"
  root := `HexSignDet.EmitFixtures

lean_exe hexsigndet_emit_field_signs where
  srcDir := "conformance"
  root := `HexSignDet.EmitFieldSigns

lean_exe hexsigndet_emit_common_fields where
  srcDir := "conformance"
  root := `HexSignDet.EmitCommonFields

lean_exe hexsigndet_json_bytes where
  srcDir := "conformance"
  root := `HexSignDet.JsonBytesDriver

lean_exe hexsigndet_emit_nested_fields where
  srcDir := "conformance"
  root := `HexSignDet.EmitNestedFields

lean_exe hexsigndet_emit_infinitesimal where
  srcDir := "conformance"
  root := `HexSignDet.EmitInfinitesimal

-- Compiled sign-determination checks over genuine number fields. Mathlib-free.
lean_exe hexsigndet_field_checks where
  srcDir := "conformance"
  root := `HexSignDet.FieldChecks

lean_exe hexrealformula_emit_fixtures where
  srcDir := "conformance"
  root := `HexRealFormula.EmitFixtures

lean_exe hexrcf_emit_fixtures where
  srcDir := "conformance"
  root := `HexRCF.EmitFixtures

lean_exe hexroots_emit_fixtures where
  srcDir := "conformance"
  root := `HexRoots.EmitFixtures

lean_exe hexrealalgebraic_emit_fixtures where
  srcDir := "conformance"
  root := `HexRealAlgebraic.EmitFixtures

lean_exe hexrealalgebraic_conformance where
  srcDir := "conformance"
  root := `HexRealAlgebraic.RunChecks

lean_exe hexnumberfield_emit_fixtures where
  srcDir := "conformance"
  root := `HexNumberField.EmitFixtures

lean_exe hexnumberfieldtower_emit_fixtures where
  srcDir := "conformance"
  root := `HexNumberFieldTower.EmitFixtures

lean_exe hexresultant_emit_fixtures where
  srcDir := "conformance"
  root := `HexResultant.EmitFixtures

lean_exe hexsparsepoly_bench where
  srcDir := "bench"
  root := `HexSparsePoly.Bench

lean_exe hexsparsepoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexSparsePoly.EmitFixtures

lean_exe hexmvpoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexMvPoly.EmitFixtures

lean_exe hexdeterminantalideal_emit_fixtures where
  srcDir := "conformance"
  root := `HexDeterminantalIdeal.EmitFixtures

lean_exe hextruncatedseries_emit_fixtures where
  srcDir := "conformance"
  root := `HexTruncatedSeries.EmitFixtures

lean_exe hexmodular_emit_fixtures where
  srcDir := "conformance"
  root := `HexModular.EmitFixtures

lean_exe hexgraphiso_emit_fixtures where
  srcDir := "conformance"
  root := `HexGraphIso.EmitFixtures

lean_exe hexgraphiso_sparse_probe where
  srcDir := "conformance"
  root := `HexGraphIso.SparseProbe

lean_exe hexgraphiso_emit_sparse where
  srcDir := "conformance"
  root := `HexGraphIso.EmitSparse

lean_exe hexgraphiso_sparse_bench where
  srcDir := "bench"
  root := `HexGraphIso.SparseBench

lean_exe hexpermgroup_emit_fixtures where
  srcDir := "conformance"
  root := `HexPermGroup.EmitFixtures

lean_exe hexgraphiso_emit_campaign where
  srcDir := "conformance"
  root := `HexGraphIso.EmitCampaign

lean_exe hexpolyzgcd_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolyZGcd.EmitFixtures

lean_exe hexpolysmith_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolySmith.EmitFixtures

lean_exe hexrationalfn_emit_fixtures where
  srcDir := "conformance"
  root := `HexRationalFn.EmitFixtures

lean_exe hexmodular_bench where
  srcDir := "bench"
  root := `HexModular.Bench
  extraDepTargets := #[`HexModularBenchSupport]

lean_exe hexmvgcd_emit_fixtures where
  srcDir := "conformance"
  root := `HexMvGcd.EmitFixtures

lean_exe hexmvhensel_emit_fixtures where
  srcDir := "conformance"
  root := `HexMvHensel.EmitFixtures

lean_exe hexmvfactor_emit_fixtures where
  srcDir := "conformance"
  root := `HexMvFactor.EmitFixtures

lean_exe hexroots_bench where
  srcDir := "bench"
  root := `HexRoots.Bench

lean_exe hexresultant_bench where
  srcDir := "bench"
  root := `HexResultant.Bench

lean_exe hexnumberfield_bench where
  srcDir := "bench"
  root := `HexNumberField.Bench

lean_exe hexrealclosure_bench where
  srcDir := "bench"
  root := `HexRealClosure.Bench

lean_exe hexrealclosure_phase4 where
  srcDir := "bench"
  root := `HexRealClosure.Phase4

lean_exe hexrealclosure_nested_normalization where
  srcDir := "bench"
  root := `HexRealClosure.NestedNormalization

lean_exe hexrealclosure_replay_size where
  srcDir := "conformance"
  root := `HexRealClosure.ReplaySize

lean_exe hexrealclosure_trivial_tests where
  root := `HexRealClosure.TrivialTowerTests

lean_exe hexrealclosure_trivial_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.TrivialConformance

lean_exe hexrealclosure_number_field_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.NumberFieldConformance

lean_exe hexrealclosure_number_field_samples where
  srcDir := "conformance"
  root := `HexRealClosure.NumberFieldSamples
lean_exe hexrealclosure_bytes_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.BytesConformance

lean_exe hexrealclosure_bounds_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.BoundsConformance

lean_lib HexRealClosureConformanceSupport where
  srcDir := "conformance"
  globs := #[.one `HexRealClosure.NestedReplay]

lean_exe hexrealclosure_sample_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.SampleConformance

lean_exe hexrealclosure_isolation_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.IsolationConformance

lean_exe hexrealclosure_deflation_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.DeflationConformance

lean_exe hexnumberfieldtower_bench where
  srcDir := "bench"
  root := `HexNumberFieldTower.Bench

lean_exe hexroots_demo where
  srcDir := "examples"
  root := `HexRootsDemo

lean_exe hexmatrix_bench where
  srcDir := "bench"
  root := `HexMatrix.Bench

-- The graph_iso fresh-module probes (SPEC/hex-graph-iso § Benchmarks and
-- SPEC/hex-graph-iso-theory § Tests): build-only structural checks of the
-- four release probe cases on each tactic route. The scheduled-only CFI
-- pair has its own target so the merge build stays inside its budget.
lean_lib HexGraphIsoProofProbe where
  srcDir := "bench"
  globs := #[`HexGraphIso.ProofProbe.Support,
    `HexGraphIso.ProofProbe.Positive12,
    `HexGraphIso.ProofProbe.Negative12,
    `HexGraphIso.ProofProbe.Coloured10Pos,
    `HexGraphIso.ProofProbe.Coloured10Neg].map Glob.one

lean_lib HexGraphIsoSparseProofProbe where
  srcDir := "bench"
  globs := #[`HexGraphIso.SparseProofProbe.Support,
    `HexGraphIso.SparseProofProbe.Positive12,
    `HexGraphIso.SparseProofProbe.Negative12,
    `HexGraphIso.SparseProofProbe.Coloured10Pos,
    `HexGraphIso.SparseProofProbe.Coloured10Neg]

lean_lib HexPermGroupTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexPermGroupTheory.ProofProbe.Kernel]

lean_lib HexGraphIsoTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexGraphIsoTheory.ProofProbe.Support,
    `HexGraphIsoTheory.ProofProbe.MathlibPositive12,
    `HexGraphIsoTheory.ProofProbe.MathlibNegative12].map Glob.one

lean_exe hexgraphiso_bench where
  srcDir := "bench"
  root := `HexGraphIso.Bench

lean_exe hexpermgroup_bench where
  srcDir := "bench"
  root := `HexPermGroup.Bench

-- Local/scheduled per-instance sweep for the cactus plots
-- (scripts/plots/hexgraphiso-cactus.py); not part of merge CI.
lean_exe hexgraphiso_cactus where
  srcDir := "bench"
  root := `HexGraphIso.Cactus

-- Stage-decomposition profiler for the canonicalization pipeline
-- (local tool; see bench/HexGraphIso/Profile.lean for methodology).
lean_exe hexgraphiso_profile where
  srcDir := "bench"
  root := `HexGraphIso.Profile

lean_exe hexrowreduce_bench where
  srcDir := "bench"
  root := `HexRowReduce.Bench

lean_exe hexdeterminant_bench where
  srcDir := "bench"
  root := `HexDeterminant.Bench

lean_exe hexdeterminantalideal_bench where
  srcDir := "bench"
  root := `HexDeterminantalIdeal.Bench

lean_exe hexmodularmatrix_bench where
  srcDir := "bench"
  root := `HexModularMatrix.Bench

lean_exe hexpolydet_bench where
  srcDir := "bench"
  root := `HexPolyDet.Bench

lean_exe hexbareiss_bench where
  srcDir := "bench"
  root := `HexBareiss.Bench

lean_exe hexdet_bench where
  srcDir := "bench"
  root := `HexDet.Bench

lean_exe hexgenericrank_bench where
  srcDir := "bench"
  root := `HexGenericRank.Bench

lean_exe hexrank_bench where
  srcDir := "bench"
  root := `HexRank.Bench

lean_exe hexhermite_bench where
  srcDir := "bench"
  root := `HexHermite.Bench

lean_exe hexsmith_bench where
  srcDir := "bench"
  root := `HexSmith.Bench

lean_exe hexcharpoly_bench where
  srcDir := "bench"
  root := `HexCharPoly.Bench

lean_exe hexminpoly_bench where
  srcDir := "bench"
  root := `HexMinPoly.Bench

lean_exe hexgramschmidt_bench where
  srcDir := "bench"
  root := `HexGramSchmidt.Bench

lean_exe hexsigndet_bench where
  srcDir := "bench"
  root := `HexSignDet.Bench

lean_lib HexSignDetBenchSupport where
  srcDir := "bench"
  globs := #[.one `HexSignDet.Input, .one `HexSignDet.Phases, .one `HexSignDet.Small,
    .one `HexSignDet.Paired, .one `HexSignDet.Maximal, .one `HexSignDet.Joint,
    .one `HexSignDet.MaximalMatrix, .one `HexSignDet.Height, .one `HexSignDet.NestedSigns,
    .one `HexSignDet.NestedTables, .one `HexSignDet.SharedRoots]

lean_exe hexrealalgebraic_bench where
  srcDir := "bench"
  root := `HexRealAlgebraic.Bench

lean_lib HexSturmBenchSupport where
  srcDir := "bench"
  globs := #[.one `HexSturm.Frontend]

lean_exe hexsturm_bench where
  srcDir := "bench"
  root := `HexSturm.Bench

lean_exe hexrealroots_bench where
  srcDir := "bench"
  root := `HexRealRoots.Bench

lean_exe hexrealformula_bench where
  srcDir := "bench"
  root := `HexRealFormula.Bench

lean_exe hexrcf_bench where
  srcDir := "bench"
  root := `HexRCF.Bench

lean_exe hexlll_bench where
  srcDir := "bench"
  supportInterpreter := true
  root := `HexLLLBench.Main

lean_exe hexlll_gram_bench where
  srcDir := "bench"
  root := `HexLLLBench.GramBench

lean_exe hex_arith_floor where
  srcDir := "bench"
  root := `HexBench.ArithFloor

lean_exe hex_interval_representation_spike where
  srcDir := "bench"
  root := `HexBench.IntervalRepresentationSpike

lean_exe hex_interval_center_spike where
  srcDir := "bench"
  root := `HexBench.IntervalCenterSpike

lean_exe hex_interval_scale_spike where
  srcDir := "bench"
  root := `HexBench.IntervalScaleSpike

lean_exe hex_interval_scheduler_spike where
  srcDir := "bench"
  root := `HexInterval.IntervalSchedulerSpike

lean_exe hex_interval_policy_frontier_spike where
  srcDir := "bench"
  root := `HexInterval.IntervalPolicyFrontierSpike

lean_exe hexinterval_decision_bench where
  srcDir := "bench"
  root := `HexInterval.DecisionBench

lean_exe hexbz_factor_service where
  srcDir := "bench"
  root := `HexBench.FactorService

lean_exe hexbz_root_split_probe where
  srcDir := "bench"
  root := `HexBench.RootSplitProbe

lean_exe hexarith_bench where
  srcDir := "bench"
  root := `HexArith.Bench

lean_exe hexpoly_bench where
  srcDir := "bench"
  root := `HexPoly.Bench

lean_exe hexpolysmith_bench where
  srcDir := "bench"
  root := `HexPolySmith.Bench

lean_exe hexmvpoly_bench where
  srcDir := "bench"
  root := `HexMvPoly.Bench

lean_exe hexreflect_bench where
  srcDir := "bench"
  root := `HexReflect.Bench

lean_exe hexmvgcd_bench where
  srcDir := "bench"
  root := `HexMvGcd.Bench

lean_exe hextruncatedseries_bench where
  srcDir := "bench"
  root := `HexTruncatedSeries.Bench

lean_exe hexpolyfast_bench where
  srcDir := "bench"
  root := `HexPolyFast.Bench

lean_exe hexrationalfn_bench where
  srcDir := "bench"
  root := `HexRationalFn.Bench

lean_exe hexorderedfn_liouville_test where
  root := `HexOrderedFnTheory.LiouvilleRun

lean_exe hexorderedfn_emit_real_fixtures where
  srcDir := "conformance"
  root := `HexOrderedFn.EmitRealFixtures

lean_exe hexorderedfn_emit_fixtures where
  srcDir := "conformance"
  root := `HexOrderedFn.EmitFixtures

lean_exe hexorderedfn_bench where
  srcDir := "bench"
  root := `HexOrderedFn.Bench

lean_lib HexRationalFnBenchSupport where
  srcDir := "bench"
  roots := #[`HexRationalFn.Scaling, `HexRationalFn.Families,
    `HexRationalFn.Workloads, `HexRationalFn.Fixtures]

lean_lib HexRationalFnKernelProbe where
  srcDir := "bench"
  globs := #[`HexRationalFn.ProofProbe.Support,
    `HexRationalFn.ProofProbe.Replay4,
    `HexRationalFn.ProofProbe.Reject64].map Glob.one

lean_exe hexpolyfast_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolyFast.EmitFixtures

lean_exe hexpoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexPoly.EmitFixtures

lean_exe hexkronecker_emit_fixtures where
  srcDir := "conformance"
  root := `HexKronecker.EmitFixtures

lean_exe hexkronecker_bench where
  srcDir := "bench"
  root := `HexKronecker.Bench

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

lean_exe hexprimality_emit_fixtures where
  srcDir := "conformance"
  root := `HexPrimality.EmitFixtures

lean_exe hexecpp_emit_fixtures where
  srcDir := "conformance"
  root := `HexECPP.EmitFixtures

lean_exe hexintfactor_emit_fixtures where
  srcDir := "conformance"
  root := `HexIntFactor.EmitFixtures

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

lean_exe hexpolyzgcd_bench where
  srcDir := "bench"
  root := `HexPolyZGcd.Bench

lean_exe hexpolyz_kronecker_crossover where
  srcDir := "bench"
  root := `HexPolyZ.KroneckerCrossover

lean_exe hexpolyz_emit_fixtures where
  srcDir := "conformance"
  root := `HexPolyZ.EmitFixtures

lean_exe hexmodarith_bench where
  srcDir := "bench"
  root := `HexModArith.Bench

lean_exe hexgf2_bench where
  srcDir := "bench"
  root := `HexGF2Bench

-- No bench exes for `Hex*Theory` libraries — see
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

lean_exe hexprimality_bench where
  srcDir := "bench"
  root := `HexPrimality.Bench

lean_exe hexprimality_squfof_measure where
  srcDir := "bench"
  root := `HexPrimality.SqufofMeasure
lean_exe hexecpp_bench where
  srcDir := "bench"
  root := `HexECPP.Bench

lean_exe hexprimality_policy_probe where
  srcDir := "bench"
  root := `HexPrimality.PolicyProbe

lean_exe hexprimality_field_probe where
  srcDir := "bench"
  root := `HexPrimality.FieldProbe

lean_exe hexprimality_factor_experiment where
  srcDir := "bench"
  root := `HexPrimality.FactorExperiment

lean_exe hexprimality_fuel_probe where
  srcDir := "bench"
  root := `HexPrimality.FuelProbe

-- Expensive exact construction guards run only for the owning library in CI.
lean_lib HexIntFactorFieldConformance where
  srcDir := "conformance"
  globs := #[`HexIntFactor.FieldConstruction, `HexIntFactor.FieldMathlib].map Glob.one

lean_exe hexintfactor_field_bench where
  srcDir := "bench"
  root := `HexIntFactor.FieldSearchBench

lean_exe hexintfactor_bench where
  srcDir := "bench"
  root := `HexIntFactor.Bench

lean_exe hexberlekamp_bench where
  srcDir := "bench"
  root := `HexBerlekamp.Bench

-- Local (non-CI, non-LeanBench) comparison driver for the Strassen base-kernel
-- measurement; emits JSON for `scripts/plots/strassen-base-kernel-comparison.py`.
lean_exe hexstrassen_compare where
  srcDir := "bench"
  root := `HexStrassen.Compare

lean_exe hexconway_replay where
  srcDir := "bench"
  root := `HexConway.Replay

lean_exe hexconway_bench where
  srcDir := "bench"
  root := `HexConway.Bench

@[default_target]
lean_lib HexManual where

lean_exe hexlatticeenum_bench where
  srcDir := "bench"
  root := `HexLatticeEnum.Bench

lean_exe tower_factor_diff where
  srcDir := "bench"
  root := `HexNumberFieldTower.FactorDiff

lean_exe hexgraphiso_emit_trace where
  srcDir := "conformance"
  root := `HexGraphIso.EmitTrace

lean_exe hexnumberfield_quadratic where
  srcDir := "bench"
  root := `HexNumberField.Quadratic

lean_lib HexCharPolyTheoryProofProbe where
  srcDir := "bench"
  globs := #[`HexCharPolyTheory.ProofProbe.Support,
    `HexCharPolyTheory.ProofProbe.BlockSupport,
    `HexCharPolyTheory.ProofProbe.ComputedSupport,
    `HexCharPolyTheory.ProofProbe.Examples].map Glob.one

-- Manual issue-10301 experiments; neither target belongs to the default build or CI.
lean_lib CadSampleCostsExperiment where
  srcDir := "experiments"
  globs := #[.submodules `CadSampleCosts]

lean_exe cad_sample_costs where
  srcDir := "experiments"
  root := `CadSampleCosts.Runtime

-- Serial native ECPP campaign driver; no Mathlib dependency.
lean_exe hexecpp_native where
  srcDir := "bench"
  root := `HexECPP.Native

-- Full current construction comparator, including the registered ECM retry.
lean_exe hexecpp_compare where
  srcDir := "bench"
  root := `HexECPP.Compare

-- Larger CFI correctness fixtures are optional manual builds.
lean_lib HexGraphIsoCfiDiagnostics where
  srcDir := "conformance"
  globs := #[`HexGraphIso.Diagnostics.DenseCfi,
    `HexGraphIso.Diagnostics.SparseCfi].map Glob.one

-- Focused larger symbolic determinant correctness fixtures.
lean_lib HexPolyDetTheoryDiagnostics where
  srcDir := "conformance"
  globs := #[.submodules `HexPolyDetTheory.Diagnostics]

-- Generated paired measurement arms, outside the representative CI target.
lean_lib HexCharPolyTheoryMeasurements where
  srcDir := "bench"
  globs := #[
    `HexCharPolyTheory.ProofProbe.Dense4Check,
    `HexCharPolyTheory.ProofProbe.Dense4Block,
    `HexCharPolyTheory.ProofProbe.Dense4Quoted,
    `HexCharPolyTheory.ProofProbe.Dense4Computed,
    `HexCharPolyTheory.ProofProbe.Dense4Rank,
    `HexCharPolyTheory.ProofProbe.Dense4Original,
    `HexCharPolyTheory.ProofProbe.Dense4Packed,
    `HexCharPolyTheory.ProofProbe.Dense8Check,
    `HexCharPolyTheory.ProofProbe.Dense8Block,
    `HexCharPolyTheory.ProofProbe.Dense8Quoted,
    `HexCharPolyTheory.ProofProbe.Dense8Computed,
    `HexCharPolyTheory.ProofProbe.Dense8Rank,
    `HexCharPolyTheory.ProofProbe.Dense8Original,
    `HexCharPolyTheory.ProofProbe.Dense8Packed,
    `HexCharPolyTheory.ProofProbe.Dense16Check,
    `HexCharPolyTheory.ProofProbe.Dense16Block,
    `HexCharPolyTheory.ProofProbe.Dense16Quoted,
    `HexCharPolyTheory.ProofProbe.Dense16Computed,
    `HexCharPolyTheory.ProofProbe.Dense16Rank,
    `HexCharPolyTheory.ProofProbe.Dense16Original,
    `HexCharPolyTheory.ProofProbe.Dense16Packed,
    `HexCharPolyTheory.ProofProbe.Dense32Check,
    `HexCharPolyTheory.ProofProbe.Dense32Block,
    `HexCharPolyTheory.ProofProbe.Dense32Quoted,
    `HexCharPolyTheory.ProofProbe.Dense32Computed,
    `HexCharPolyTheory.ProofProbe.Dense32Rank,
    `HexCharPolyTheory.ProofProbe.Dense32Original,
    `HexCharPolyTheory.ProofProbe.Dense32Packed,
    `HexCharPolyTheory.ProofProbe.Dense16Candidate,
    `HexCharPolyTheory.ProofProbe.Dense16Reference].map Glob.one

-- Fixed CM data and bounded roots for the independent analytic oracle.
lean_exe hexecpp_emit_class_polynomials where
  srcDir := "conformance"
  root := `HexECPP.EmitClassPolynomials

lean_lib KernelReplayExperiment where
  srcDir := "experiments"
  globs := #[.one `KernelReplay.Assemble, .one `KernelReplay.Json, .one `KernelReplay.Generated,
    .one `KernelReplay.Packing,
    .one `KernelReplay.PackingProbe, .one `KernelReplay.Inverse,
    .one `KernelReplay.Nested, .one `KernelReplay.NestedProbe,
    .one `KernelReplay.FactOperations, .one `KernelReplay.FactOperationsProbe,
    .one `KernelReplay.Root, .one `KernelReplay.RootProbe,
    .one `KernelReplay.ProofProbe,
    .one `KernelReplay.InProcessProbe, .one `KernelReplay.LowerProbe, .one `KernelReplay.LowerProof]

lean_exe hexsigndet_kernel_replay_probe where
  supportInterpreter := true
  srcDir := "experiments"
  root := `KernelReplay.Main

lean_exe hexsigndet_inprocess_replay_probe where
  srcDir := "experiments"
  root := `KernelReplay.InProcessMain

lean_exe hexrealclosure_policy_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.RootPolicyConformance

lean_exe hexrealclosure_normalization_bench where
  srcDir := "bench"
  root := `HexRealClosure.Normalization

lean_exe hexrealclosure_basic_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.BasicConformance

lean_exe hexrealclosure_root_format_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.RootFormatConformance

lean_exe hexrealclosure_repr_conformance where
  srcDir := "conformance"
  root := `HexRealClosure.ReprConformance
