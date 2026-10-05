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
  let oFile := pkg.dir / defaultBuildDir / "HexECPPMathlib" / "ffi" / "pari_pipe.o"
  let srcTarget ← inputTextFile <| pkg.dir / "HexECPPMathlib" / "ffi" / "pari_pipe.c"
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
lean_lib HexTruncatedSeriesMathlib where

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
lean_lib HexOrderedFnMathlib where

@[default_target]
lean_lib HexOrderedFnTests where
  globs := #[.one `HexOrderedFn.Tests, .one `HexOrderedFnMathlib.Tests,
    .one `HexOrderedFn.InfinitesimalTests, .one `HexOrderedFnMathlib.InfinitesimalTests,
    .one `HexOrderedFn.ExtensionTests, .one `HexOrderedFnMathlib.LiouvilleTests,
    .one `HexOrderedFnMathlib.LintTests]

lean_lib HexMvPoly where

@[default_target]
lean_lib HexRealFormula where

@[default_target]
lean_lib HexRealFormulaMathlib where

lean_lib HexMvGcd where

@[default_target]
lean_lib HexGenericRank where

@[default_target]
lean_lib HexGenericRankMathlib where

lean_lib HexReflect where

@[default_target]
lean_lib HexReflectMathlib where

@[default_target]
lean_lib HexKronecker where

@[default_target]
lean_lib HexKroneckerMathlib where

@[default_target]
lean_lib HexKroneckerTests where
  globs := #[.one `HexKroneckerMathlib.Tests]

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
lean_lib HexModularMatrixMathlib where

lean_lib HexGF2 where
  precompileModules := true

lean_lib HexPolyZ where

lean_lib HexPolyZGcd where

@[default_target]
lean_lib HexRationalFn where

@[default_target]
lean_lib HexRationalFnMathlib where

lean_lib HexRoots where

lean_lib HexResultant where

lean_lib HexNumberField where

lean_lib HexRealAlgebraic where

@[default_target]
lean_lib HexRealAlgebraicMathlib where

@[default_target]
lean_lib HexRealAlgebraicMathlibTests where
  globs := #[.one `HexRealAlgebraicMathlib.Tests]

lean_lib HexNumberFieldTower where

lean_lib HexPolyFp where
  precompileModules := true

-- Fast-multiplication kernels specified by HexPolyFast/SPEC/hex-poly-fast.md
-- §"Coefficient-owner file layouts". They import HexPolyFast and HexModular,
-- which must be published before the released umbrellas HexPolyZ.lean and
-- HexPolyFp.lean can export them. Restore the kernels after a successful real
-- sync publishes those dependencies (https://github.com/kim-em/hex-dev/issues/10739).
@[default_target]
lean_lib HexPolyFastKernels where
  globs := #[`HexPolyZ.KroneckerMulti, `HexPolyZ.NttMul, `HexPolyFp.NttMul]

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
lean_lib HexSignDetMathlib where

lean_lib HexRealClosure where
  -- The runnable selected-root tests use `#eval` across the library boundary.
  precompileModules := true

@[default_target]
lean_lib HexRealClosureTests where
  globs := #[.one `HexRealClosure.Tests, .one `HexRealClosure.RootOrderTests,
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
lean_lib HexRealClosureMathlib where

@[default_target]
lean_lib HexRealClosureMathlibTests where
  globs := #[.one `HexRealClosureMathlib.BaseTests,
    .one `HexRealClosureMathlib.BaseSubsequenceTests]

@[default_target]
lean_lib HexSturmMathlib where

@[default_target]
lean_lib HexSturmMathlibTests where
  globs := #[.one `HexSturmMathlib.Tests,
    .one `HexSturmMathlib.Tests.Replay.Accepted,
    .one `HexSturmMathlib.Tests.Replay.Rejected,
    .one `HexSturmMathlib.Tests.Replay.Baseline]

lean_lib HexInterval where

@[default_target]
lean_lib HexPolyMathlib where

@[default_target]
lean_lib HexMvPolyMathlib where

@[default_target]
lean_lib HexSparsePolyMathlib where

@[default_target]
lean_lib HexModArithMathlib where

@[default_target]
lean_lib HexPolyZMathlib where

@[default_target]
lean_lib HexPolyZGcdMathlib where

@[default_target]
lean_lib HexRootsMathlib where

@[default_target]
lean_lib HexResultantMathlib where

@[default_target]
lean_lib HexNumberFieldMathlib where

@[default_target]
lean_lib HexNumberFieldTowerMathlib where

@[default_target]
lean_lib HexPolyFpMathlib where

lean_lib HexBerlekampMathlib where

@[default_target]
lean_lib HexHenselMathlib where

@[default_target]
lean_lib HexGF2Mathlib where

@[default_target]
lean_lib HexGFqMathlib where

@[default_target]
lean_lib HexBerlekampZassenhausMathlib where

@[default_target]
lean_lib HexPrimalityMathlib where

lean_lib HexECPPMathlib where
  roots := #[`HexECPPMathlib, `HexECPPMathlib.Native, `HexECPPMathlib.Pari]

-- Lake selects the last matching library. Keep the Mathlib-free IO sidecar
-- after the bridge so only this module needs a shared native library.
lean_lib HexECPPMathlibPariIO where
  roots := #[`HexECPPMathlib.Pari.IO]
  globs := #[.one `HexECPPMathlib.Pari.IO]
  precompileModules := true
  moreLinkObjs := #[hexecpppariio]

-- The release aggregate also builds these modules. Its manifest equality
-- check requires that registration; all owners use the same Lean settings.
lean_lib HexECPPMathlibTests where
  globs := #[.one `HexECPPMathlib.Tests, .one `HexECPPMathlib.LintTests]

@[default_target]
lean_lib HexIntFactorMathlib where
  roots := #[`HexIntFactorMathlib, `HexIntFactorMathlib.Mixed]

lean_lib HexMatrix

@[default_target]
lean_lib HexPermGroup

@[default_target]
lean_lib HexPermGroupMathlib where

@[default_target]
lean_lib HexPermGroupTests where
  globs := #[.one `HexPermGroup.Tests, .one `HexPermGroup.CertificateTests,
    .one `HexPermGroupMathlib.Tests, .one `HexPermGroupMathlib.CertificateTests]

lean_lib HexGraph where

lean_lib HexGraphIso

@[default_target]
lean_lib HexGraphIsoMathlib where

lean_lib HexCharPoly where
  precompileModules := true

lean_lib HexMinPoly where

lean_lib HexPolySmith where

@[default_target]
lean_lib HexPolySmithMathlib where

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

lean_lib HexHermiteMathlib where

lean_lib HexSmithMathlib where

lean_lib HexGramSchmidt where

lean_lib HexLatticeEnum where

@[default_target]
lean_lib HexLatticeEnumMathlib where

@[default_target]
lean_lib HexLatticeEnumTests where
  globs := #[`HexLatticeEnumMathlib.Tests, `HexLatticeEnumMathlib.LintTests]

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
lean_lib HexMatrixMathlib where

@[default_target]
lean_lib HexCharPolyMathlib where

@[default_target]
lean_lib HexMinPolyMathlib where

@[default_target]
lean_lib HexRowReduceMathlib where

@[default_target]
lean_lib HexDeterminantMathlib where

@[default_target]
lean_lib HexDeterminantalIdealMathlib where

@[default_target]
lean_lib HexDeterminantalIdealTests where
  globs := #[`HexDeterminantalIdealMathlib.Tests]

@[default_target]
lean_lib HexPolyDet where

@[default_target]
lean_lib HexPolyDetMathlib where

lean_lib HexPolyDetMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexPolyDetMathlib.ProofProbe.Numeric2Hex,
    `HexPolyDetMathlib.ProofProbe.Symbolic2Hex,
    `HexPolyDetMathlib.ProofProbe.Quotient2Hex,
    `HexPolyDetMathlib.ProofProbe.ResultNumeric2Hex,
    `HexPolyDetMathlib.ProofProbe.ResultSymbolic2Hex,
    `HexPolyDetMathlib.ProofProbe.OriginalQuadratic4,
    `HexPolyDetMathlib.ProofProbe.RankOne10].map Glob.one

@[default_target]
lean_lib HexBareissMathlib where

lean_lib HexBareissMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexBareissMathlib.ProofProbe.Baseline,
    `HexBareissMathlib.ProofProbe.MathlibBaseline,
    `HexBareissMathlib.ProofProbe.Dense8Hex,
    `HexBareissMathlib.ProofProbe.Dense8Mathlib,
    `HexBareissMathlib.ProofProbe.Dense12Hex,
    `HexBareissMathlib.ProofProbe.Dense12Mathlib,
    `HexBareissMathlib.ProofProbe.Dense16Hex,
    `HexBareissMathlib.ProofProbe.Dense16Mathlib,
    `HexBareissMathlib.ProofProbe.Dense32Hex,
    `HexBareissMathlib.ProofProbe.Tridiagonal16Hex,
    `HexBareissMathlib.ProofProbe.Tridiagonal16Mathlib,
    `HexBareissMathlib.ProofProbe.Vandermonde8Hex,
    `HexBareissMathlib.ProofProbe.Vandermonde8Mathlib,
    `HexBareissMathlib.ProofProbe.Singular16Hex,
    `HexBareissMathlib.ProofProbe.Singular16Mathlib,
    `HexBareissMathlib.ProofProbe.Large8Bits64Hex,
    `HexBareissMathlib.ProofProbe.Large8Bits64Mathlib,
    `HexBareissMathlib.ProofProbe.Large4Bits256Hex,
    `HexBareissMathlib.ProofProbe.Large4Bits256Mathlib,
    `HexBareissMathlib.ProofProbe.Rational8Hex,
    `HexBareissMathlib.ProofProbe.Rational8Mathlib]

@[default_target]
lean_lib HexDetMathlib where

lean_lib HexRankMathlib where

@[default_target]
lean_lib HexRankTests where
  globs := #[`HexRankMathlib.Tests, `HexRankMathlib.NumberFieldTests]

@[default_target]
lean_lib HexGenericRankTests where
  globs := #[`HexGenericRankMathlib.Tests]

lean_lib HexDeterminantalIdealMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexDeterminantalIdealMathlib.ProofProbe.Full2R1,
    `HexDeterminantalIdealMathlib.ProofProbe.Full2R2,
    `HexDeterminantalIdealMathlib.ProofProbe.Low2R1].map Glob.one

lean_lib HexGenericRankMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexGenericRankMathlib.ProofProbe.VariableGeneric,
    `HexGenericRankMathlib.ProofProbe.VariableHypothesis,
    `HexGenericRankMathlib.ProofProbe.VariableSideGoal,
    `HexGenericRankMathlib.ProofProbe.FiniteGeneric].map Glob.one

lean_lib HexRankMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexRankMathlib.ProofProbe.Dense8Hex,
    `HexRankMathlib.ProofProbe.Deficient16Hex,
    `HexRankMathlib.ProofProbe.Rational8Hex,
    `HexRankMathlib.ProofProbe.Quadratic8Hex,
    `HexRankMathlib.ProofProbe.Algebraic8Hex,
    `HexRankMathlib.ProofProbe.NumberFieldSupport].map Glob.one

@[default_target]
lean_lib HexGramSchmidtMathlib where

@[default_target]
lean_lib HexLLLMathlib where

@[default_target]
lean_lib HexRealRootsMathlib where

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
  globs := #[`HexSturmMathlib.Tests.Replay.Semantics,
    `HexSturmMathlib.Tests.Replay.SemanticsBaseline,
    `HexSignDetMathlib.RootModel, `HexSignDetMathlib.RootProducer,
    `HexSignDetMathlib.SelectedRoot, `HexSignDetMathlib.SelectedProducer,
    `HexSignDetMathlib.CompletionProducer, `HexSignDetMathlib.Convert,
    `HexSignDetMathlib.DagSelectedSigns, `HexSignDetMathlib.Embedding,
    `HexSignDetMathlib.QueryHandle, `HexSignDetMathlib.TableProducer,
    `HexSignDetMathlib.ReencodingProducer, `HexSignDetMathlib.RootList,
    `HexSignDetMathlib.ReencodingRefinement, `HexSignDetMathlib.Thom,
    `HexSignDetMathlib.ThomReencoding, `HexSignDetMathlib.ThomRoots,
    `HexSignDetMathlib.ComparisonProducer,
    `HexRealClosureMathlib.Specialize, `HexRealClosureMathlib.SpecializeTests,
    `HexRealClosureMathlib.SignFacts, `HexRealClosureMathlib.SignRequests,
    `HexRealClosureMathlib.SignEvidence,
    `HexRealClosureMathlib.TransportPolynomial, `HexRealClosureMathlib.TransportProduct,
    `HexRealClosureMathlib.TransportArithmetic, `HexRealClosureMathlib.TransportQuery, `HexRealClosureMathlib.TransportTests,
    `HexRealClosureMathlib.TransportPower, `HexRealClosureMathlib.TransportTarski,
    `HexRealClosureMathlib.TransportRing,
    `HexRealClosureMathlib.TransportClosed, `HexRealClosureMathlib.TransportClosedQuery, `HexRealClosureMathlib.TransportClosedReduction, `HexRealClosureMathlib.TransportRegular,
    `HexRealClosureMathlib.TransportReduction, `HexRealClosureMathlib.TransportPreparation, `HexRealClosureMathlib.TransportMoment, `HexRealClosureMathlib.TransportReplay, `HexRealClosureMathlib.TransportSample, `HexRealClosureMathlib.TransportDescriptor, `HexRealClosureMathlib.TransportInventory, `HexRealClosureMathlib.TransportSelected, `HexRealClosureMathlib.TransportFiniteTests,
    `HexRealClosureMathlib.AlgebraicTransport, `HexRealClosureMathlib.AlgebraicYun,
    `HexRealClosureMathlib.AlgebraicReencode,
    `HexRealClosureMathlib.AlgebraicRoots,
    `HexRealClosureMathlib.SpecializePolynomial, `HexRealClosureMathlib.SpecializeRegular, `HexRealClosureMathlib.SpecializeQuery, `HexRealClosureMathlib.SpecializeTarski,
    `HexRealClosureMathlib.SpecializeReduction,
    `HexRealClosureMathlib.SpecializeMoment,
    `HexRealClosureMathlib.SpecializeReplay,
    `HexRealClosureMathlib.SpecializeNested,
    `HexRealClosureMathlib.SpecializeFractionRing,
    `HexRealClosureMathlib.MonicEvaluation,
    `HexRealClosureMathlib.RegularEvaluation,
    `HexRealClosureMathlib.ModelEvaluation,
    `HexRealClosureMathlib.AlgebraicEvaluation, `HexRealClosureMathlib.ModelInventory,
    `HexRealClosureMathlib.SuffixEvaluation,
    `HexRealClosureMathlib.StagedEvaluation,
    `HexRealClosureMathlib.BaseEvaluation,
    `HexRealClosureMathlib.NativeRealization,
    `HexRealClosureMathlib.NativeRealizationTests,
    `HexRealClosureMathlib.CoefficientMap, `HexRealClosureMathlib.CoefficientComposition,
    `HexRealClosureMathlib.CoefficientQuery,
    `HexRealClosureMathlib.CoefficientTarski,
    `HexRealClosureMathlib.CoefficientEmbeddingTests,
    `HexRealClosureMathlib.CoefficientEmbedding,
    `HexRealClosureMathlib.CoefficientSelected,
    `HexRealClosureMathlib.CoefficientDescriptor,
    `HexRealClosureMathlib.CoefficientReplay,
    `HexRealClosureMathlib.CoefficientMoment,
    `HexRealClosureMathlib.CoefficientReduction,
    `HexRealClosureMathlib.SpecializeSample,
    `HexRealClosureMathlib.SpecializeSelected,
    `HexRealClosureMathlib.SpecializeDescriptor,
    `HexRealClosureMathlib.Algebraic, `HexRealClosureMathlib.AlgebraicClean,
    `HexRealClosureMathlib.TowerModel, `HexRealClosureMathlib.TowerModelTests,
    `HexRealClosureMathlib.BaseModel,
    `HexRealClosureMathlib.BaseOrder,
    `HexRealClosureMathlib.BaseMapModel,
    `HexRealClosureMathlib.BaseFactory,
    `HexRealClosureMathlib.ContextModel,
    `HexRealClosureMathlib.BaseFactoryTests, `HexRealClosureMathlib.BaseGatherTests,
    `HexRealClosureMathlib.CacheModels,
    `HexRealClosureMathlib.CacheRebuild,
    `HexRealClosureMathlib.CacheGather,
    `HexRealClosureMathlib.GatherTests,
    `HexRealClosureMathlib.SharedPresentation,
    `HexRealClosureMathlib.SharedPresentationTests,
    `HexRealClosureMathlib.TowerAlgebraic, `HexRealClosureMathlib.TowerRefinement,
    `HexRealClosureMathlib.TowerTransport, `HexRealClosureMathlib.TowerTransportTests,
    `HexRealClosureMathlib.TowerReuse,
    `HexRealClosureMathlib.TowerInclusion, `HexRealClosureMathlib.LiveContext,
    `HexRealClosureMathlib.LiveRequest, `HexRealClosureMathlib.LiveRequestTests,
    `HexRealClosureMathlib.TowerYun,
    `HexRealClosureMathlib.AlgebraicValue, `HexRealClosureMathlib.BaseClean, `HexRealClosureMathlib.AlgebraicTower,
    `HexRealClosureMathlib.SelectedRoot,
    `HexRealClosureMathlib.Canonical, `HexRealClosureMathlib.Element, `HexRealClosureMathlib.QAdjoin,
    `HexRealClosureMathlib.NumberField, `HexRealClosureMathlib.NumberFieldTower,
    `HexRealClosureMathlib.Polynomial, `HexRealClosureMathlib.Yun,
    `HexRealClosureMathlib.YunInvariant, `HexRealClosureMathlib.Bounds,
    `HexRealClosureMathlib.Deflation, `HexRealClosureMathlib.Bisection,
    `HexRealClosureMathlib.BisectionRoots, `HexRealClosureMathlib.BisectionFrontier,
    `HexRealClosureMathlib.BisectionCounts, `HexRealClosureMathlib.Isolation,
    `HexRealClosureMathlib.BisectionFactor, `HexRealClosureMathlib.IsolationFactor,
    `HexRealClosureMathlib.TowerRootPolicy, `HexRealClosureMathlib.RootPolicy, `HexRealClosureMathlib.IsolationPolicy,
    `HexRealClosureMathlib.ZeroFactor, `HexRealClosureMathlib.IsolationRoots,
    `HexRealClosureMathlib.IsolationTotal,
    `HexRealClosureMathlib.RootOrder, `HexRealClosureMathlib.RootFactors,
    `HexRealClosureMathlib.Trivial, `HexRealClosureMathlib.TrivialTower, `HexRealClosureMathlib.TrivialTowerTests,
    `HexRealClosureMathlib.RootTotal, `HexRealClosureMathlib.TowerRoots,
    `HexRealClosureMathlib.RootTransport,
    `HexRealClosureMathlib.RootCollection, `HexRealClosureMathlib.RootList,
    `HexRealClosureMathlib.Sample, `HexRealClosureMathlib.LocalSample,
    `HexRealClosureMathlib.LocalSampleTests,
    `HexRealClosureMathlib.SampleTests,
    `HexRealClosureMathlib.TowerCoverage, `HexRealClosureMathlib.Presentation,
    `HexRealClosureMathlib.PresentationTests,
    `HexRealClosureMathlib.TowerNaturality,
    `HexRealClosureMathlib.Ambient, `HexRealClosureMathlib.AmbientTests,
    `HexRealClosureMathlib.BaseAlgebraicity, `HexRealClosureMathlib.BaseBound,
    `HexRealClosureMathlib.EnlargementTests,
    `HexRealClosureMathlib.Union, `HexRealClosureMathlib.TowerUnion,
    `HexRealClosureMathlib.TowerRestriction, `HexRealClosureMathlib.TowerEnlarge,
    `HexRealClosureMathlib.TowerEnlargeOrder, `HexRealClosureMathlib.TowerEnlargeOrderTests,
    `HexRealClosureMathlib.UnionTests].map Glob.one

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
    `HexPrimalityMathlib.ProofProbe.MathlibBaseline,
    `HexPrimalityMathlib.ProofProbe.Mathlib512,
    `HexPrimalityMathlib.ProofProbe.MathlibExhausted,
    `HexPrimalityMathlib.ProofProbe.MathlibOverBudget,
    `HexPrimalityMathlib.ProofProbe.Negative25,
    `HexPrimalityMathlib.ProofProbe.Negative32,
    `HexPrimalityMathlib.ProofProbe.Negative64,
    `HexPrimalityMathlib.ProofProbe.Negative64Null,
    `HexPrimalityMathlib.ProofProbe.Negative65,
    `HexPrimalityMathlib.ProofProbe.Negative512,
    `HexPrimalityMathlib.ProofProbe.Negative512Odd,
    `HexPrimalityMathlib.ProofProbe.NegativeExhausted512]

lean_lib HexPrimalityMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexPrimalityMathlib.ProofProbe.Support,
    `HexPrimalityMathlib.ProofProbe.FactorExperiment,
    `HexPrimalityMathlib.ProofProbe.Baseline,
    `HexPrimalityMathlib.ProofProbe.Input31,
    `HexPrimalityMathlib.ProofProbe.Literal31,
    `HexPrimalityMathlib.ProofProbe.Reify31,
    `HexPrimalityMathlib.ProofProbe.Replay31,
    `HexPrimalityMathlib.ProofProbe.Primality31,
    `HexPrimalityMathlib.ProofProbe.Input512,
    `HexPrimalityMathlib.ProofProbe.Literal512,
    `HexPrimalityMathlib.ProofProbe.Reify512,
    `HexPrimalityMathlib.ProofProbe.Replay512,
    `HexPrimalityMathlib.ProofProbe.Primality512,
    `HexPrimalityMathlib.ProofProbe.NormNumTrial,
    `HexPrimalityMathlib.ProofProbe.NormNumThreshold,
    `HexPrimalityMathlib.ProofProbe.NormNum512,
    `HexPrimalityMathlib.ProofProbe.MathlibBaseline,
    `HexPrimalityMathlib.ProofProbe.Mathlib512,
    `HexPrimalityMathlib.ProofProbe.MathlibExhausted,
    `HexPrimalityMathlib.ProofProbe.MathlibOverBudget,
    `HexPrimalityMathlib.ProofProbe.Negative25,
    `HexPrimalityMathlib.ProofProbe.Negative32,
    `HexPrimalityMathlib.ProofProbe.Negative64,
    `HexPrimalityMathlib.ProofProbe.Negative64Null,
    `HexPrimalityMathlib.ProofProbe.Negative65,
    `HexPrimalityMathlib.ProofProbe.Negative512,
    `HexPrimalityMathlib.ProofProbe.Negative512Odd,
    `HexPrimalityMathlib.ProofProbe.Adoption,
    `HexPrimalityMathlib.ProofProbe.NegativeExhausted512].map Glob.one ++
    #[.submodules `HexPrimalityMathlib.ProofProbe.FactorCorpus]

lean_lib HexECPPMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexECPPMathlib.ProofProbe.NativeGeneration,
    `HexECPPMathlib.ProofProbe.Native512Baseline,
    `HexECPPMathlib.ProofProbe.Native512Reify,
    `HexECPPMathlib.ProofProbe.Native512Direct,
    `HexECPPMathlib.ProofProbe.Native128_0,
    `HexECPPMathlib.ProofProbe.NativeBaseline,
    `HexECPPMathlib.ProofProbe.NativeReify,
    `HexECPPMathlib.ProofProbe.NativeDirect,
    `HexECPPMathlib.ProofProbe.NativeHoldout,
    `HexECPPMathlib.ProofProbe.NativeValidation,
    `HexECPPMathlib.ProofProbe.NativeUpdated,
    `HexECPPMathlib.ProofProbe.Native256_0,
    `HexECPPMathlib.ProofProbe.Native256_1,
    `HexECPPMathlib.ProofProbe.Native256_2,
    `HexECPPMathlib.ProofProbe.Support,
    `HexECPPMathlib.ProofProbe.Support17,
    `HexECPPMathlib.ProofProbe.Ecpp17,
    `HexECPPMathlib.ProofProbe.Pock17,
    `HexECPPMathlib.ProofProbe.Baseline65,
    `HexECPPMathlib.ProofProbe.Reify65,
    `HexECPPMathlib.ProofProbe.Direct65,
    `HexECPPMathlib.ProofProbe.Replay65,
    `HexECPPMathlib.ProofProbe.Replay256,
    `HexECPPMathlib.ProofProbe.Replay512].map Glob.one

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
lean_lib HexIntFactorMathlibProofProbe where
  srcDir := "bench"
  globs := #[Glob.one `HexIntFactorMathlib.ProofProbe.Mixed]

lean_lib HexIntFactorMathlibTests where
  globs := #[Glob.one `HexIntFactorMathlib.MixedTests]

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

lean_lib HexMvPolyMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexMvPolyMathlib.ProofProbe.Examples].map Glob.one

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

lean_lib HexIntervalMathlibExperiment where
  globs := #[`HexIntervalMathlib.Experiment.Arithmetic,
    `HexIntervalMathlib.Experiment.Center,
    `HexIntervalMathlib.Experiment.Centered,
    `HexIntervalMathlib.Experiment.DyadicInterval,
    `HexIntervalMathlib.Experiment.SineSign,
    `HexIntervalMathlib.Experiment.ExpSign,
    `HexIntervalMathlib.Experiment.PntLogTable,
    `HexIntervalMathlib.Experiment.PntNestedLog,
    `HexIntervalMathlib.Experiment.PntExpTail,
    `HexIntervalMathlib.Experiment.PntTable12,
    `HexIntervalMathlib.Experiment.PntTable12Ordinary,
    `HexIntervalMathlib.Experiment.PntTable10Shard,
    `HexIntervalMathlib.Experiment.PntTable10Convex,
    `HexIntervalMathlib.Experiment.PntTable10Pointwise,
    `HexIntervalMathlib.Experiment.PntTable10LargePointwise,
    `HexIntervalMathlib.Experiment.PntTable10LogCoupled,
    `HexIntervalMathlib.Experiment.PntTable10A2,
    `HexIntervalMathlib.Experiment.PntTable10Exact,
    `HexIntervalMathlib.Experiment.PntTable12Log,
    `HexIntervalMathlib.Experiment.PntFks2Shard,
    `HexIntervalMathlib.Experiment.PntFks2Xpow,
    `HexIntervalMathlib.Experiment.CosBillion,
    `HexIntervalMathlib.Experiment.LogTablePrecision,
    `HexIntervalMathlib.Experiment.PntLogNatural,
    `HexIntervalMathlib.Experiment.PntFks2Nested,
    `HexIntervalMathlib.Experiment.PntLogRational,
    `HexIntervalMathlib.Experiment.PntExpNegative,
    `HexIntervalMathlib.Experiment.PntExpPoint,
    `HexIntervalMathlib.Experiment.PntNestedLogTwo,
    `HexIntervalMathlib.Experiment.PntPiPoint,
    `HexIntervalMathlib.Experiment.IntegralCanary,
    `HexIntervalMathlib.Experiment.PntBKLNWExp,
    `HexIntervalMathlib.Experiment.PntBKLNWPow,
    `HexIntervalMathlib.Experiment.PntDusartExp,
    `HexIntervalMathlib.Experiment.PntFks2Mu,
    `HexIntervalMathlib.Experiment.PntExpUpper,
    `HexIntervalMathlib.Experiment.PntRamanujanTheta,
    `HexIntervalMathlib.Experiment.PntPrimeLogSmall,
    `HexIntervalMathlib.Experiment.PntChebyshev,
    `HexIntervalAlgebraic.Experiment.PolynomialDispatch,
    `HexIntervalAlgebraic.Experiment.PolynomialDispatchProof,
    `HexIntervalMathlib.Experiment.SinTen,
    `HexIntervalMathlib.Experiment.SinTenInterval,
    `HexIntervalMathlib.Experiment.MixedFunctions,
    `HexIntervalMathlib.Experiment.MixedInstantiation].map Glob.one

@[default_target]
lean_lib HexIntervalMathlib where
  globs := #[`HexIntervalMathlib, `HexIntervalMathlib.Interval,
    `HexIntervalMathlib.Addition, `HexIntervalMathlib.Subtraction,
    `HexIntervalMathlib.MinMax, `HexIntervalMathlib.Absolute,
    `HexIntervalMathlib.Multiplication,
    `HexIntervalMathlib.Power, `HexIntervalMathlib.Split,
    `HexIntervalMathlib.Inverse, `HexIntervalMathlib.Division,
    `HexIntervalMathlib.Regularize, `HexIntervalMathlib.Program,
    `HexIntervalMathlib.Proof, `HexIntervalMathlib.Rule,
    `HexIntervalMathlib.Frontend,
    `HexIntervalMathlib.Tactic].map Glob.one

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

lean_lib HexIntervalMathlibReplayProbe where
  srcDir := "bench"
  globs := #[`HexIntervalMathlib.CenterDirect,
    `HexIntervalMathlib.CenterReflected].map Glob.one

lean_lib HexRealRootsMathlibReplayProbe where
  srcDir := "bench"
  globs := #[`HexRealRootsMathlib.ProofProbe.Natural6,
    `HexRealRootsMathlib.ProofProbe.Refined2,
    `HexRealRootsMathlib.ProofProbe.RealClosed].map Glob.one

lean_lib HexBerlekampZassenhausMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexBerlekampZassenhausMathlib.ProofProbe.Factor4,
    `HexBerlekampZassenhausMathlib.ProofProbe.Irreducible4,
    `HexBerlekampZassenhausMathlib.ProofProbe.Repeated8,
    `HexBerlekampZassenhausMathlib.ProofProbe.Kernel4].map Glob.one

lean_lib HexBerlekampMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexBerlekampMathlib.ProofProbe.Factor4,
    `HexBerlekampMathlib.ProofProbe.Irreducible4,
    `HexBerlekampMathlib.ProofProbe.Repeated8].map Glob.one

lean_lib HexSignDetMathlibProofProbe where
  srcDir := "bench"
  globs := #[.submodules `HexSignDetMathlib.ProofProbe]

-- Correctness diagnostics remain CI-built outside the benchmark root.
lean_lib HexSignDetMathlibDiagnostics where
  srcDir := "conformance"
  globs := #[.submodules `HexSignDetMathlib.Diagnostics]

-- Depth-three kernel reductions retain their separate manual target.
lean_lib HexSignDetMathlibDepthThree where
  srcDir := "conformance"
  globs := #[.submodules `HexSignDetMathlib.DepthThree]

lean_lib HexRealFormulaProofProbe where
  srcDir := "bench"
  globs := #[`HexRealFormulaMathlib.ProofProbe.Support,
    `HexRealFormulaMathlib.ProofProbe.Parameterized,
    `HexRealFormulaMathlib.ProofProbe.Alternation].map Glob.one

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
`HexArith.Conformance, `HexArith.CrossCheck, `HexBerlekamp.Conformance, `HexBerlekampZassenhaus.Conformance, `HexBerlekampZassenhaus.CrossCheck, `HexBerlekampZassenhausMathlib.Conformance, `HexConway.Conformance, `HexGF2.Conformance, `HexGF2.CrossCheck, `HexGF2.FastCheck, `HexGFq.Conformance, `HexGFq.CrossCheck, `HexGFqField.Conformance, `HexGFqRing.Conformance, `HexGramSchmidt.Conformance, `HexGraphIso.Conformance, `HexHensel.Conformance, `HexHensel.CrossCheck, `HexInterval.Conformance, `HexIntervalMathlib.IntervalConformance, `HexInterval.CenterConformance, `HexInterval.ScaleConformance, `HexInterval.PropagatorConformance, `HexInterval.ScopeConformance, `HexInterval.StructuralMatcherConformance, `HexInterval.MatcherSchedulerConformance, `HexInterval.NestedBranchConformance, `HexInterval.StructureViewConformance, `HexInterval.PolicyConformance, `HexInterval.PolicyFrontierConformance, `HexInterval.PolicyDriverConformance, `HexInterval.PackageRegistryConformance, `HexInterval.DyadicIntervalConformance, `HexInterval.DyadicRulesConformance, `HexInterval.PayloadArenaConformance, `HexInterval.PayloadSessionConformance, `HexInterval.PolicySessionConformance, `HexInterval.PolicyFunctionConformance, `HexInterval.SemanticReplayConformance, `HexInterval.ChronologicalReplayConformance, `HexInterval.GenericInstanceReconstructionConformance, `HexInterval.ProofEmitterConformance, `HexInterval.TraceReplayConformance, `HexInterval.SinTenIntervalConformance, `HexIntervalMathlib.DyadicIntervalConformance, `HexIntervalMathlib.CenteredConformance, `HexIntervalMathlib.SineSignConformance, `HexIntervalMathlib.SineProofConformance, `HexIntervalMathlib.SineTacticConformance, `HexIntervalMathlib.ProofRegistryConformance, `HexIntervalMathlib.ExpSignConformance, `HexIntervalMathlib.ReluConformance, `HexIntervalMathlib.RefuteConformance, `HexIntervalMathlib.PntLogTableConformance, `HexIntervalMathlib.PntNestedLogConformance, `HexIntervalMathlib.PntExpTailConformance, `HexIntervalMathlib.PntTable12Conformance, `HexIntervalMathlib.PntTable12OrdinaryConformance, `HexIntervalAlgebraic.PolynomialDispatchConformance, `HexIntervalMathlib.PntTable12LogConformance, `HexIntervalMathlib.PntFks2ShardConformance, `HexIntervalMathlib.LogTablePrecisionConformance, `HexIntervalMathlib.IntegralCanaryConformance, `HexIntervalMathlib.PntBKLNWExpConformance, `HexIntervalMathlib.PntBKLNWPowConformance, `HexIntervalMathlib.PntPrimeLogSmallConformance, `HexIntervalMathlib.PntDusartExpConformance, `HexIntervalMathlib.SinTenConformance, `HexIntervalMathlib.SinTenIntervalConformance, `HexIntervalMathlib.CosBillionConformance, `HexHermite.Conformance, `HexLLL.Conformance, `HexMatrix.Conformance, `HexRealFormula.Conformance, `HexRealFormulaMathlib.Conformance, `HexRealFormulaMathlib.Arithmetic, `HexMvPolyFixtures, `HexMvPoly.Conformance, `HexMvPolyMathlib.Conformance, `HexSparsePolyFixtures, `HexSparsePoly.Conformance, `HexRowReduce.Conformance, `HexDeterminant.Conformance, `HexDeterminantalIdealFixtures, `HexDeterminantalIdeal.Conformance, `HexDeterminant.Carriers, `HexBareiss.Fixtures, `HexBareiss.Conformance, `HexModularMatrix.Fixtures, `HexModularMatrix.Conformance, `HexDet.Conformance, `HexDet.Carriers, `HexCharPoly.Fixtures, `HexCharPoly.Carriers, `HexCharPoly.Conformance, `HexModArith.Conformance, `HexModArith.FastCheck, `HexModular.Conformance, `HexPolyZGcd.Conformance, `HexMvGcd.Conformance, `HexNumberField.Conformance, `HexNumberFieldTower.Conformance, `HexPoly.Conformance, `HexPrimality.CertificateProducer, `HexPrimality.ConstructionConformance, `HexPrimality.ConstructionRetry, `HexPrimality.ConstructionRegistration, `HexPrimality.Curve25519Replay, `HexPrimality.Curve448Replay, `HexPrimality.SqufofConformance, `HexPrimality.Conformance, `HexECPP.NativeConformance, `HexECPP.Conformance, `HexECPP.Fixture17, `HexECPP.PolicyProbe, `HexECPP.Fixture65, `HexECPP.Fixture256, `HexECPP.Fixture512, `HexECPP.PariFixtures, `HexECPP.ImportConformance, `HexECPPMathlib.NativeConformance, `HexECPPMathlib.NativeFixtures, `HexECPPMathlib.Conformance, `HexECPPMathlib.CompactFixtures, `HexECPPMathlib.CompactReject, `HexECPPMathlib.PariProcess, `HexECPPMathlib.Reject, `HexECPPMathlib.HasseAudit, `HexECPPMathlib.SoundnessAudit, `HexPrimalityMathlib.Conformance, `HexPrimalityMathlibConformance.OptIn, `HexPolyFp.Conformance, `HexPolyZ.Conformance, `HexRCF.Conformance, `HexRealRoots.Conformance, `HexRealRootsMathlib.Conformance, `HexResultant.Conformance, `HexRoots.Conformance].map Glob.one ++
    #[`HexPolyDet.Conformance, `HexRank.Conformance, `HexGenericRank.Conformance, `HexGenericRank.Fixtures, `HexRowReduce.FieldFixtures, `HexRealFormulaMathlib.ReifierConformance, `HexRCF.RealFormulaConformance, `HexRCF.RealCoefficientsConformance, `HexRCF.AlgebraicProgress, `HexRCF.IsolationProgress, `HexRCF.RadicalProgress, `HexRCF.ProductionProgress, `HexRCF.FieldRootsConformance, `HexRCF.CertificationInputs, `HexRCF.RationalSources, `HexRCF.ProofEvidence, `HexRCF.CheckedConversions, `HexRCF.ReplayModes, `HexRCF.CarrierModes, `HexRCF.SignIndex, `HexRCF.PreparedCoefficients, `HexRCF.FiniteReplay, `HexRCF.TowerSamples, `HexRCF.Samples, `HexRCF.Gather, `HexRCF.GeneratorWindowInputs, `HexRCF.GeneratorWindow, `HexRCF.CertificationProofs, `HexRCF.TotalAlgebraicProofs, `HexRCF.AlgebraicDivision, `HexRCF.NormalizedCoefficients, `HexRCF.NormalizedInputs, `HexRCF.RegisteredConstants, `HexRCF.NamedConstants, `HexRCF.MixedConstants, `HexRCF.CoarseConstants, `HexRCF.RealCoefficientTactic, `HexRCF.RealCoefficientCommonField, `HexRCF.CommonFieldPresentation, `HexRCF.RootAliasesConformance, `HexRCF.RationalRoots, `HexRCF.AlgebraicRoots, `HexRCF.FormulaConformance, `HexRCF.LiteralSignConformance, `HexRCF.FieldSpecializeConformance, `HexRCF.AdmissionConformance, `HexRCF.IsolationConformance].map Glob.one

    ++ #[`HexRealAlgebraic.Conformance, `HexRealAlgebraic.Checks,
      `HexRealAlgebraic.FieldSignConformance, `HexNumberField.ComplexChecks,
      `HexRealAlgebraic.ReprChecks, `HexRealAlgebraicMathlib.FieldSignConformance].map Glob.one

    ++ #[`HexReflect.TestProviders, `HexReflect.Conformance, `HexReflect.ScopeConformance, `HexReflect.ResidueConformance].map Glob.one

    ++ #[`HexSignDet.CommonField, `HexSignDet.Conformance, `HexSignDet.CrossCheck, `HexSignDet.FastCheck, `HexSignDet.JsonBytes, `HexSignDet.Infinitesimal, `HexSignDetMathlib.Conformance, `HexSignDetMathlib.RootSemantics,
      `HexSignDetMathlib.FieldConformance].map Glob.one

    ++ #[`HexRealClosure.BisectionFrontierTests, `HexRealClosure.IsolationTests,
      `HexRealClosureMathlib.CoefficientSignsConformance,
      `HexRealClosureMathlib.DependenciesConformance,
      `HexRealClosureMathlib.PackingConformance,
      `HexRealClosureMathlib.ContextOperationsConformance,
      `HexRealClosureMathlib.ContextOperationsPublic,
      `HexRealClosureMathlib.NestedSignsConformance,
      `HexRealClosureMathlib.SignCodecConformance,
      `HexRealClosureMathlib.SignFactsConformance,
      `HexRealClosureMathlib.SignRequestsConformance,
      `HexRealClosureMathlib.SignEvidenceConformance].map Glob.one

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

    ++ #[`HexIntervalMathlib.PntLogNaturalConformance,
      `HexIntervalMathlib.PntLogRationalConformance,
      `HexIntervalMathlib.PntExpNegativeConformance,
      `HexIntervalMathlib.PntExpPointConformance].map Glob.one

    ++ #[`HexIntervalMathlib.PntNestedLogTwoConformance,
      `HexIntervalMathlib.PntPiPointConformance].map Glob.one

    ++ #[`HexIntervalMathlib.PntChebyshevConformance].map Glob.one

    ++ #[`HexIntervalMathlib.PntFks2MuConformance,
      `HexIntervalMathlib.PntExpUpperConformance,
      `HexIntervalMathlib.PntRamanujanThetaConformance].map Glob.one

    ++ #[`HexIntervalMathlib.PntFks2NestedConformance].map Glob.one

    ++ #[`HexIntervalMathlib.PntFks2StructureConformance].map Glob.one

    ++ #[`HexIntervalMathlib.PntTable10ShardConformance,
      `HexIntervalMathlib.PntTable10ConvexConformance,
      `HexIntervalMathlib.PntTable10PointwiseConformance,
      `HexIntervalMathlib.PntTable10LargePointwiseConformance,
      `HexIntervalMathlib.PntTable10LogCoupledConformance,
      `HexIntervalMathlib.PntTable10A2Conformance,
      `HexIntervalMathlib.PntTable10ExactConformance].map Glob.one

    ++ #[`HexInterval.StagedPolicyConformance].map Glob.one

    ++ #[`HexIntervalMathlib.ArithmeticConformance].map Glob.one

    ++ #[`HexInterval.MinMaxConformance,
      `HexIntervalMathlib.MinMaxConformance].map Glob.one

    ++ #[`HexGraphIso.Cases, `HexGraphIso.SparseCases, `HexPermGroup.Conformance,
      `HexPermGroup.KernelConformance, `HexPermGroup.Limits].map Glob.one

    ++ #[`HexInterval.PolicyFeatureConformance,
      `HexInterval.FeaturePolicyConformance,
      `HexInterval.SearchConformance,
      `HexInterval.ExecutableConformance,
      `HexInterval.RuntimeConformance,
      `HexIntervalMathlib.RuntimeProofConformance,
      `HexIntervalMathlib.RuntimeTerminalConformance,
      `HexIntervalMathlib.RuntimeRuleConformance,
      `HexIntervalMathlib.RuntimeEmitConformance,
      `HexIntervalMathlib.ProgramProofConformance,
      `HexIntervalMathlib.DriverConformance,
      `HexIntervalMathlib.ControllerConformance,
      `HexIntervalMathlib.ExecutableControllerConformance,
      `HexIntervalMathlib.RuleConformance,
      `HexIntervalMathlib.FrontendConformance,
      `HexIntervalMathlib.TacticConformance,
      `HexIntervalMathlib.MixedFunctionsConformance,
      `HexIntervalMathlib.MixedInstantiationConformance,
      `HexIntervalMathlib.ExactBranchConformance].map Glob.one

    ++ #[`HexECPPMathlib.CompositeDivisors, `HexECPPMathlib.NodeBudget,
      `HexECPPMathlib.ModuleImports].map Glob.one

-- The expensive complete-family Mathlib proofs are owned only by this
-- non-default library. They are excluded from both merge-gating
-- `HexIntervalMathlibExperiment` and `HexConformance`.
lean_lib HexIntervalPntFks2Local where
  globs := #[`HexIntervalMathlib.Experiment.PntFks2XpowProof00,
    `HexIntervalMathlib.Experiment.PntFks2XpowProof01,
    `HexIntervalMathlib.Experiment.PntFks2XpowProof02,
    `HexIntervalMathlib.Experiment.PntFks2XpowProof03,
    `HexIntervalMathlib.Experiment.PntFks2XpowProof04,
    `HexIntervalMathlib.Experiment.PntFks2XpowProof05,
    `HexIntervalMathlib.Experiment.PntFks2XpowResults,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof00,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof01,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof02,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof03,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof04,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof05,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof06,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof07,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof08,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof09,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof10,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof12,
    `HexIntervalMathlib.Experiment.PntFks2FamilyProof13,
    `HexIntervalMathlib.Experiment.PntFks2Family].map Glob.one

lean_lib HexIntervalPntFks2ConformanceLocal where
  srcDir := "conformance"
  globs := #[`HexIntervalMathlib.PntFks2XpowConformance].map Glob.one

-- The local executable owns the complete runtime and guarded-axiom driver.
lean_exe hex_interval_pnt_fks2_local where
  srcDir := "conformance"
  root := `HexIntervalMathlib.PntFks2FamilyConformance

-- Public umbrellas intentionally contain only the supported API. Executable
-- examples and regression tests are compiled through this separate target so
-- removing them from an umbrella cannot silently remove them from CI.
lean_lib HexReleaseTests where
  globs := #[`HexArith.ExtendedGcdTests, `HexECPPMathlib.Tests, `HexPoly.InterpretTests, `HexPoly.PseudoTests,
    `HexPolyMathlib.InterpretTests, `HexPolyMathlib.PseudoTests,
    `HexMatrixMathlib.Tests,
    `HexPolyMathlib.LiteralTests,
    `HexBareissMathlib.Tests,
    `HexRowReduceMathlib.Tests,
    `HexBerlekamp.FactorTacticTests,
    `HexBerlekampMathlib.FactorPolyTests,
    `HexBerlekampZassenhaus.FactorTacticTests,
    `HexBerlekampZassenhausMathlib.FactorPolyTests,
    `HexBerlekampZassenhausMathlib.PublicReplayTests,
    `HexBerlekampZassenhausMathlib.QuotationTests,
    `HexBerlekampZassenhausMathlib.IrreducibilityTests,
    `HexRealRoots.ReplayTest,
    `HexRealRoots.TarskiTests,
    `HexRealRootsMathlib.IsolateRootsTests,
    `HexRealRootsMathlib.IsolateRootsElabTests,
    `HexRealRootsMathlib.SturmTests,
    `HexRealRootsMathlib.RealRootCountTests,
    `HexRealRootsMathlib.TarskiTests,
    `HexRootsMathlib.Examples,
    `HexPrimality.Examples.Curve25519,
    `HexModular.KernelTests, `HexModular.LoopTests,
    `HexMvPoly.KernelTests,
    `HexMvPoly.KernelResidueTests,
    `HexMvPolyMathlib.KernelResidueTests,
    `HexSparsePoly.KernelTests,
    `HexGraphIso.TestGraphs,
    `HexGraphIso.SparseTests,
    `HexGraphIso.TacticTests,
    `HexGraphIso.ModuleBoundaryTests,
    `HexGraphIsoMathlib.TacticTests,
    `HexGraphIsoMathlib.SparseTacticTests,
    `HexPermGroup.Tests,
    `HexPermGroup.CertificateTests,
    `HexPermGroupMathlib.Tests,
    `HexPermGroupMathlib.CertificateTests,
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
  globs := #[`HexPolyDetMathlib.Tests, `HexMinPolyMathlib.Tests, `HexSmithMathlib.Tests, `HexHermiteMathlib.Tests, `HexRowReduceMathlib.Tests]

lean_lib HexStructuralTacticProofProbe where
  srcDir := "bench"
  globs := #[.submodules `HexMinPolyMathlib.ProofProbe,
    .submodules `HexSmithMathlib.ProofProbe, .submodules `HexHermiteMathlib.ProofProbe,
    .submodules `HexRowReduceMathlib.ProofProbe]

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
  globs := #[`HexECPPMathlib.Native, `HexECPPMathlib.Pari,
    `HexBerlekampZassenhaus.All,
    `HexBerlekampZassenhausMathlib.All]

-- Monorepo-only lint regression for the sparse-poly pair; the kernel
-- probes live in HexReleaseTests alongside the release manifest's
-- test_modules entry.
@[default_target]
lean_lib HexSparsePolyTests where
  globs := #[`HexSparsePolyMathlib.LintTests]

-- Declaration linting runs in monorepo CI. The lint source is copied to the
-- mirror with its bridge library; mirror CI builds the published API.
@[default_target]
lean_lib HexTruncatedSeriesTests where
  globs := #[`HexTruncatedSeriesMathlib.LintTests]

-- Monorepo-only lint regression for the integer Smith pair. It moves into the
-- release-manifest-backed test target when the pair is published.
@[default_target]
lean_lib HexSmithTests where
  globs := #[`HexSmith.QuickstartTests,
    `HexSmithMathlib.LintTests,
    `HexSmithMathlib.QuickstartTests]

-- HexCharPoly is not yet a published split repository (its released.yml
-- entries were withdrawn until the phase pipeline completes), so its
-- verification-only elaborator regressions stay separate from the
-- release-manifest-backed target above; they rejoin HexReleaseTests (and
-- the manifest's test_modules) at publication.
@[default_target]
lean_lib HexCharPolyTests where
  globs := #[`HexCharPoly.CharPolyElabTests,
    `HexCharPolyMathlib.CharPolyElabTests]

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
-- SPEC/hex-graph-iso-mathlib § Tests): build-only structural checks of the
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

lean_lib HexPermGroupMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexPermGroupMathlib.ProofProbe.Kernel]

lean_lib HexGraphIsoMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexGraphIsoMathlib.ProofProbe.Support,
    `HexGraphIsoMathlib.ProofProbe.MathlibPositive12,
    `HexGraphIsoMathlib.ProofProbe.MathlibNegative12].map Glob.one

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
    .one `HexSignDet.MaximalMatrix, .one `HexSignDet.Height]

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
  root := `HexOrderedFnMathlib.LiouvilleRun

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

lean_lib HexCharPolyMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexCharPolyMathlib.ProofProbe.Support,
    `HexCharPolyMathlib.ProofProbe.BlockSupport,
    `HexCharPolyMathlib.ProofProbe.ComputedSupport,
    `HexCharPolyMathlib.ProofProbe.Examples].map Glob.one

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
lean_lib HexPolyDetMathlibDiagnostics where
  srcDir := "conformance"
  globs := #[.submodules `HexPolyDetMathlib.Diagnostics]

-- Generated paired measurement arms, outside the representative CI target.
lean_lib HexCharPolyMathlibMeasurements where
  srcDir := "bench"
  globs := #[
    `HexCharPolyMathlib.ProofProbe.Dense4Check,
    `HexCharPolyMathlib.ProofProbe.Dense4Block,
    `HexCharPolyMathlib.ProofProbe.Dense4Quoted,
    `HexCharPolyMathlib.ProofProbe.Dense4Computed,
    `HexCharPolyMathlib.ProofProbe.Dense4Rank,
    `HexCharPolyMathlib.ProofProbe.Dense4Original,
    `HexCharPolyMathlib.ProofProbe.Dense4Packed,
    `HexCharPolyMathlib.ProofProbe.Dense8Check,
    `HexCharPolyMathlib.ProofProbe.Dense8Block,
    `HexCharPolyMathlib.ProofProbe.Dense8Quoted,
    `HexCharPolyMathlib.ProofProbe.Dense8Computed,
    `HexCharPolyMathlib.ProofProbe.Dense8Rank,
    `HexCharPolyMathlib.ProofProbe.Dense8Original,
    `HexCharPolyMathlib.ProofProbe.Dense8Packed,
    `HexCharPolyMathlib.ProofProbe.Dense16Check,
    `HexCharPolyMathlib.ProofProbe.Dense16Block,
    `HexCharPolyMathlib.ProofProbe.Dense16Quoted,
    `HexCharPolyMathlib.ProofProbe.Dense16Computed,
    `HexCharPolyMathlib.ProofProbe.Dense16Rank,
    `HexCharPolyMathlib.ProofProbe.Dense16Original,
    `HexCharPolyMathlib.ProofProbe.Dense16Packed,
    `HexCharPolyMathlib.ProofProbe.Dense32Check,
    `HexCharPolyMathlib.ProofProbe.Dense32Block,
    `HexCharPolyMathlib.ProofProbe.Dense32Quoted,
    `HexCharPolyMathlib.ProofProbe.Dense32Computed,
    `HexCharPolyMathlib.ProofProbe.Dense32Rank,
    `HexCharPolyMathlib.ProofProbe.Dense32Original,
    `HexCharPolyMathlib.ProofProbe.Dense32Packed,
    `HexCharPolyMathlib.ProofProbe.Dense16Candidate,
    `HexCharPolyMathlib.ProofProbe.Dense16Reference].map Glob.one

-- Fixed CM data and bounded roots for the independent analytic oracle.
lean_exe hexecpp_emit_class_polynomials where
  srcDir := "conformance"
  root := `HexECPP.EmitClassPolynomials

lean_lib KernelReplayExperiment where
  srcDir := "experiments"
  globs := #[.one `KernelReplay.Assemble, .one `KernelReplay.Json, .one `KernelReplay.Generated,
    .one `KernelReplay.Nested, .one `KernelReplay.NestedProbe,
    .one `KernelReplay.FactOperations, .one `KernelReplay.FactOperationsProbe,
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
