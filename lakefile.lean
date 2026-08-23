module

public import Lake

public section

open System Lake DSL

package Hex where
  -- Parse docstrings as Verso markup. Suggestions remain opt-in because they
  -- attempt to elaborate ordinary code spans, including local expressions.
  leanOptions := #[⟨`doc.verso, true⟩, ⟨`doc.verso.suggestions, false⟩]

require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.33.0-rc1"

require «lean-bench» from git
  "https://github.com/kim-em/lean-bench.git" @ "master"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0-rc1"

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
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3"]
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
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3"]
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
    let flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O3"]
    compileO oFile srcFile flags

extern_lib hexlllffi (pkg) := do
  let name := nameToStaticLib "hexlllffi"
  let oTarget ← hexlllProviderOTarget pkg
  buildStaticLib (pkg.staticLibDir / name) #[oTarget]

lean_lib Hex where

lean_lib HexBasic where

lean_lib HexArith where
  precompileModules := true
  -- The `hexarithffi` extern_lib is linked into this precompiled library's
  -- dynlib automatically (as with `hexgf2ffi` and `HexGF2`); we only need to
  -- add the system GMP library. Passing the static lib by an explicit path
  -- broke consumers: that path was relative to the *root* package's build dir,
  -- so when hex is a dependency it resolved against the wrong project and the
  -- dynlink failed.
  moreLinkArgs := #["-lgmp"]

lean_lib HexPoly where

lean_lib HexMvPoly where

lean_lib HexMvGcd where

lean_lib HexSparsePoly where

lean_lib HexModArith where
  precompileModules := true
  -- See `HexArith`: the `hexmodarithffi` extern_lib links in automatically, so
  -- we pass only the system GMP library rather than an explicit static-lib path.
  moreLinkArgs := #["-lgmp"]

lean_lib HexModular where

lean_lib HexGF2 where
  precompileModules := true

lean_lib HexPolyZ where

lean_lib HexPolyZGcd where

lean_lib HexRoots where

lean_lib HexResultant where

lean_lib HexNumberField where

lean_lib HexNumberFieldTower where

lean_lib HexPolyFp where

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

lean_lib HexBerlekampZassenhaus where

lean_lib HexRealRoots where

lean_lib HexInterval where

@[default_target]
lean_lib HexPolyMathlib where

@[default_target]
lean_lib HexMvPolyMathlib where

@[default_target]
lean_lib HexModArithMathlib where

@[default_target]
lean_lib HexPolyZMathlib where

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

lean_lib HexMatrix where
  precompileModules := true

lean_lib HexCharPoly where

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

@[default_target]
lean_lib HexMatrixMathlib where

@[default_target]
lean_lib HexCharPolyMathlib where

@[default_target]
lean_lib HexRowReduceMathlib where

@[default_target]
lean_lib HexDeterminantMathlib where

@[default_target]
lean_lib HexBareissMathlib where

@[default_target]
lean_lib HexGramSchmidtMathlib where

@[default_target]
lean_lib HexLLLMathlib where

@[default_target]
lean_lib HexRealRootsMathlib where

@[default_target]
lean_lib HexRCF where

lean_exe hexlll_external_reduction where
  root := `HexLLL.ExternalReduction

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

lean_lib HexBerlekampKernelProbe where
  srcDir := "bench"
  globs := #[`HexBench.BerlekampKernel]

lean_lib HexMvPolyBenchSupport where
  srcDir := "bench"
  globs := #[`HexMvPolyCorpus]

lean_lib HexMvPolyMathlibProofProbe where
  srcDir := "bench"
  globs := #[`HexMvPolyMathlib.ProofProbe.Support,
    `HexMvPolyMathlib.ProofProbe.Baseline,
    `HexMvPolyMathlib.ProofProbe.HexAdditionInputs32,
    `HexMvPolyMathlib.ProofProbe.SortedAdditionInputs32,
    `HexMvPolyMathlib.ProofProbe.HexAddition32,
    `HexMvPolyMathlib.ProofProbe.SortedAddition32,
    `HexMvPolyMathlib.ProofProbe.HexAdditionInputs64,
    `HexMvPolyMathlib.ProofProbe.SortedAdditionInputs64,
    `HexMvPolyMathlib.ProofProbe.HexAddition64,
    `HexMvPolyMathlib.ProofProbe.SortedAddition64,
    `HexMvPolyMathlib.ProofProbe.HexMulSparse6,
    `HexMvPolyMathlib.ProofProbe.SortedMulSparse6,
    `HexMvPolyMathlib.ProofProbe.HexMulCollideInputs8,
    `HexMvPolyMathlib.ProofProbe.SortedMulCollideInputs8,
    `HexMvPolyMathlib.ProofProbe.HexMulCollide8,
    `HexMvPolyMathlib.ProofProbe.SortedMulCollide8,
    `HexMvPolyMathlib.ProofProbe.HexMulCollideInputs12,
    `HexMvPolyMathlib.ProofProbe.SortedMulCollideInputs12,
    `HexMvPolyMathlib.ProofProbe.HexMulCollide12,
    `HexMvPolyMathlib.ProofProbe.SortedMulCollide12,
    `HexMvPolyMathlib.ProofProbe.HexCancellation4,
    `HexMvPolyMathlib.ProofProbe.SortedCancellation4,
    `HexMvPolyMathlib.ProofProbe.HexCancellation6,
    `HexMvPolyMathlib.ProofProbe.SortedCancellation6,
    `HexMvPolyMathlib.ProofProbe.HexCancellationInputs8,
    `HexMvPolyMathlib.ProofProbe.SortedCancellationInputs8,
    `HexMvPolyMathlib.ProofProbe.HexCancellation8,
    `HexMvPolyMathlib.ProofProbe.SortedCancellation8,
    `HexMvPolyMathlib.ProofProbe.HexCancellationInputs10,
    `HexMvPolyMathlib.ProofProbe.SortedCancellationInputs10,
    `HexMvPolyMathlib.ProofProbe.HexCancellation10,
    `HexMvPolyMathlib.ProofProbe.SortedCancellation10,
    `HexMvPolyMathlib.ProofProbe.HexSos3,
    `HexMvPolyMathlib.ProofProbe.SortedSos3,
    `HexMvPolyMathlib.ProofProbe.HexSos4,
    `HexMvPolyMathlib.ProofProbe.SortedSos4,
    `HexMvPolyMathlib.ProofProbe.HexSosInputs6,
    `HexMvPolyMathlib.ProofProbe.SortedSosInputs6,
    `HexMvPolyMathlib.ProofProbe.HexSos6,
    `HexMvPolyMathlib.ProofProbe.SortedSos6,
    `HexMvPolyMathlib.ProofProbe.HexSosInputs8,
    `HexMvPolyMathlib.ProofProbe.SortedSosInputs8,
    `HexMvPolyMathlib.ProofProbe.HexSos8,
    `HexMvPolyMathlib.ProofProbe.SortedSos8,
    `HexMvPolyMathlib.ProofProbe.HexStructuralInputs8,
    `HexMvPolyMathlib.ProofProbe.SortedStructuralInputs8,
    `HexMvPolyMathlib.ProofProbe.HexStructural8,
    `HexMvPolyMathlib.ProofProbe.SortedStructural8,
    `HexMvPolyMathlib.ProofProbe.HexStructuralInputs32,
    `HexMvPolyMathlib.ProofProbe.SortedStructuralInputs32,
    `HexMvPolyMathlib.ProofProbe.HexStructural32,
    `HexMvPolyMathlib.ProofProbe.SortedStructural32].map Glob.one

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
  globs := #[`HexIntervalMathlib.CenterBaseline,
    `HexIntervalMathlib.CenterReflected, `HexIntervalMathlib.CenterDirect]

lean_lib HexRealRootsMathlibReplayProbe where
  srcDir := "bench"
  globs := #[`HexRealRootsMathlib.ProofProbe.Baseline,
    `HexRealRootsMathlib.ProofProbe.Natural6,
    `HexRealRootsMathlib.ProofProbe.Refined2]

lean_lib HexRealRootsMathlibReplayProbeScientific where
  srcDir := "bench"
  globs := #[`HexRealRootsMathlib.ProofProbe.Natural8,
    `HexRealRootsMathlib.ProofProbe.Natural10,
    `HexRealRootsMathlib.ProofProbe.Refined4,
    `HexRealRootsMathlib.ProofProbe.Refined6]

lean_lib HexRCFProofProbe where
  srcDir := "bench"
  globs := #[`HexRCF.BenchHash, `HexRCF.ProofProbe.Support,
    `HexRCF.ProofProbe.Generated,
    `HexRCF.ProofProbe.Validate, `HexRCF.ProofProbe.Baseline,
    `HexRCF.ProofProbe.Quadratic.Reify, `HexRCF.ProofProbe.Quadratic.Input,
    `HexRCF.ProofProbe.Quadratic.Search, `HexRCF.ProofProbe.Quadratic.Literal,
    `HexRCF.ProofProbe.Quadratic.Replay, `HexRCF.ProofProbe.Quadratic.Tactic]

lean_lib HexRCFProofProbeScientific where
  srcDir := "bench"
  globs := #[`HexRCF.ProofProbe.Degree10.Reify,
    `HexRCF.ProofProbe.Degree10.Input, `HexRCF.ProofProbe.Degree10.Search,
    `HexRCF.ProofProbe.Degree10.Literal, `HexRCF.ProofProbe.Degree10.Replay,
    `HexRCF.ProofProbe.Degree10.Tactic, `HexRCF.ProofProbe.Degree50.Reify,
    `HexRCF.ProofProbe.Degree50.Input, `HexRCF.ProofProbe.Degree50.Search,
    `HexRCF.ProofProbe.Degree50.Literal, `HexRCF.ProofProbe.Degree50.Replay,
    `HexRCF.ProofProbe.Degree50.Tactic,
    `HexRCF.ProofProbe.DoubleDegree50]

-- Conformance #guard drivers live under `conformance/` and are built by this
-- library (mirroring the released conformance sub-projects). Alongside each
-- library's `Conformance` core module, the heavier cross-check sweeps and
-- extern-path fast checks (`CrossCheck` / `FastCheck`) also live here so the
-- implementation-vs-testing boundary stays legible; they elaborate their
-- `#guard`s in the same `lake build`. EmitFixtures drivers are the
-- `*_emit_fixtures` exes below, carrying `srcDir := "conformance"`.
lean_lib HexConformance where
  srcDir := "conformance"
  globs := #[`HexArith.Conformance, `HexArith.CrossCheck, `HexBerlekamp.Conformance, `HexBerlekampZassenhaus.Conformance, `HexBerlekampZassenhaus.CrossCheck, `HexConway.Conformance, `HexGF2.Conformance, `HexGF2.CrossCheck, `HexGF2.FastCheck, `HexGFq.Conformance, `HexGFq.CrossCheck, `HexGFqField.Conformance, `HexGFqRing.Conformance, `HexGramSchmidt.Conformance, `HexHensel.Conformance, `HexHensel.CrossCheck, `HexInterval.Conformance, `HexIntervalMathlib.IntervalConformance, `HexInterval.CenterConformance, `HexInterval.ScaleConformance, `HexInterval.PropagatorConformance, `HexInterval.ScopeConformance, `HexInterval.StructuralMatcherConformance, `HexInterval.MatcherSchedulerConformance, `HexInterval.NestedBranchConformance, `HexInterval.StructureViewConformance, `HexInterval.PolicyConformance, `HexInterval.PolicyFrontierConformance, `HexInterval.PolicyDriverConformance, `HexInterval.PackageRegistryConformance, `HexInterval.DyadicIntervalConformance, `HexInterval.DyadicRulesConformance, `HexInterval.PayloadArenaConformance, `HexInterval.PayloadSessionConformance, `HexInterval.PolicySessionConformance, `HexInterval.PolicyFunctionConformance, `HexInterval.SemanticReplayConformance, `HexInterval.ChronologicalReplayConformance, `HexInterval.GenericInstanceReconstructionConformance, `HexInterval.ProofEmitterConformance, `HexInterval.TraceReplayConformance, `HexInterval.SinTenIntervalConformance, `HexIntervalMathlib.DyadicIntervalConformance, `HexIntervalMathlib.CenteredConformance, `HexIntervalMathlib.SineSignConformance, `HexIntervalMathlib.SineProofConformance, `HexIntervalMathlib.SineTacticConformance, `HexIntervalMathlib.ProofRegistryConformance, `HexIntervalMathlib.ExpSignConformance, `HexIntervalMathlib.ReluConformance, `HexIntervalMathlib.RefuteConformance, `HexIntervalMathlib.PntLogTableConformance, `HexIntervalMathlib.PntNestedLogConformance, `HexIntervalMathlib.PntExpTailConformance, `HexIntervalMathlib.PntTable12Conformance, `HexIntervalMathlib.PntTable12OrdinaryConformance, `HexIntervalAlgebraic.PolynomialDispatchConformance, `HexIntervalMathlib.PntTable12LogConformance, `HexIntervalMathlib.PntFks2ShardConformance, `HexIntervalMathlib.LogTablePrecisionConformance, `HexIntervalMathlib.IntegralCanaryConformance, `HexIntervalMathlib.PntBKLNWExpConformance, `HexIntervalMathlib.PntBKLNWPowConformance, `HexIntervalMathlib.PntPrimeLogSmallConformance, `HexIntervalMathlib.PntDusartExpConformance, `HexIntervalMathlib.SinTenConformance, `HexIntervalMathlib.SinTenIntervalConformance, `HexIntervalMathlib.CosBillionConformance, `HexLLL.Conformance, `HexMatrix.Conformance, `HexMvPolyFixtures, `HexMvPoly.Conformance, `HexMvPolyMathlib.Conformance, `HexSparsePolyFixtures, `HexSparsePoly.Conformance, `HexRowReduce.Conformance, `HexDeterminant.Conformance, `HexBareiss.Conformance, `HexCharPoly.Fixtures, `HexCharPoly.Conformance, `HexModArith.Conformance, `HexModArith.FastCheck, `HexNumberField.Conformance, `HexNumberFieldTower.Conformance, `HexPoly.Conformance, `HexPolyFp.Conformance, `HexPolyZ.Conformance, `HexRCF.Conformance, `HexRealRoots.Conformance, `HexRealRootsMathlib.Conformance, `HexResultant.Conformance, `HexRoots.Conformance].map Glob.one

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

    ++ #[`HexInterval.PolicyFeatureConformance,
      `HexInterval.FeaturePolicyConformance,
      `HexInterval.SearchConformance,
      `HexInterval.ExecutableConformance,
      `HexInterval.RuntimeConformance,
      `HexIntervalMathlib.RuntimeProofConformance,
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
  globs := #[`HexBerlekamp.FactorTacticTests,
    `HexBerlekampMathlib.FactorPolyTests,
    `HexBerlekampZassenhaus.FactorTacticTests,
    `HexBerlekampZassenhausMathlib.FactorPolyTests,
    `HexBerlekampZassenhausMathlib.IrreducibilityTests,
    `HexCharPoly.CharPolyElabTests,
    `HexCharPolyMathlib.CharPolyElabTests,
    `HexRealRoots.ReplayTest,
    `HexRealRootsMathlib.IsolateRootsTests,
    `HexRealRootsMathlib.IsolateRootsElabTests,
    `HexRootsMathlib.Examples,
    `HexMvPoly.KernelTests]

-- Complete development imports for the two factorization packages. Their
-- ordinary umbrellas deliberately expose only the supported release API.
lean_lib HexFactorizationModules where
  globs := #[`HexBerlekampZassenhaus.All,
    `HexBerlekampZassenhausMathlib.All]

-- HexSparsePoly is not yet a published split repository, so its
-- verification-only kernel probes stay separate from the
-- release-manifest-backed target above; they join HexReleaseTests (and the
-- release manifest's test_modules) when the split repository is published.
@[default_target]
lean_lib HexSparsePolyTests where
  globs := #[`HexSparsePoly.KernelTests]

-- HexRCF is not yet a published split repository, so its verification-only
-- modules stay separate from the release-manifest-backed target above.
@[default_target]
lean_lib HexRCFTests where
  globs := #[`HexRCF.LanguageTests,
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
    `HexRCF.LintTests]

-- Mirrors the released aggregate's module-system umbrella, so a library that
-- never adopted the module system fails here instead of after the publish-out
-- sync. `check_released_manifest.py` keeps the import list equal to the
-- `leanprover/hex` pins in `scripts/release/released.yml`.
@[default_target]
lean_lib HexAggregateCheck where

-- Canonical end-to-end examples are release artifacts rather than public API.
-- Keep their target separate for the same reason as the regression tests.
lean_lib HexReleaseExamples where
  globs := #[`Examples.Release3, `Examples.Release4, `Examples.Release5, `Examples.FiniteFields]

lean_exe hexrowreduce_emit_fixtures where
  srcDir := "conformance"
  root := `HexRowReduce.EmitFixtures

lean_exe hexdeterminant_emit_fixtures where
  srcDir := "conformance"
  root := `HexDeterminant.EmitFixtures

lean_exe hexbareiss_emit_fixtures where
  srcDir := "conformance"
  root := `HexBareiss.EmitFixtures

lean_exe hexcharpoly_emit_fixtures where
  srcDir := "conformance"
  root := `HexCharPoly.EmitFixtures

lean_exe hexgramschmidt_emit_fixtures where
  srcDir := "conformance"
  root := `HexGramSchmidt.EmitFixtures

lean_exe hexlll_emit_fixtures where
  srcDir := "conformance"
  root := `HexLLL.EmitFixtures

lean_exe hexrealroots_emit_fixtures where
  srcDir := "conformance"
  root := `HexRealRoots.EmitFixtures

lean_exe hexrcf_emit_fixtures where
  srcDir := "conformance"
  root := `HexRCF.EmitFixtures

lean_exe hexroots_emit_fixtures where
  srcDir := "conformance"
  root := `HexRoots.EmitFixtures

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

lean_exe hexroots_bench where
  srcDir := "bench"
  root := `HexRoots.Bench

lean_exe hexresultant_bench where
  srcDir := "bench"
  root := `HexResultant.Bench

lean_exe hexnumberfield_bench where
  srcDir := "bench"
  root := `HexNumberField.Bench

lean_exe hexnumberfieldtower_bench where
  srcDir := "bench"
  root := `HexNumberFieldTower.Bench

lean_exe hexroots_demo where
  srcDir := "examples"
  root := `HexRootsDemo

lean_exe hexmatrix_bench where
  srcDir := "bench"
  root := `HexMatrix.Bench

lean_exe hexdeterminant_bench where
  srcDir := "bench"
  root := `HexDeterminant.Bench

lean_exe hexbareiss_bench where
  srcDir := "bench"
  root := `HexBareiss.Bench

lean_exe hexcharpoly_bench where
  srcDir := "bench"
  root := `HexCharPoly.Bench

lean_exe hexgramschmidt_bench where
  srcDir := "bench"
  root := `HexGramSchmidt.Bench

lean_exe hexrealroots_bench where
  srcDir := "bench"
  root := `HexRealRoots.Bench

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

lean_exe hexmvpoly_bench where
  srcDir := "bench"
  root := `HexMvPoly.Bench

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

lean_exe hexberlekamp_bench where
  srcDir := "bench"
  root := `HexBerlekamp.Bench

-- Local (non-CI, non-LeanBench) comparison driver for the Strassen base-kernel
-- measurement; emits JSON for `scripts/plots/strassen-base-kernel-comparison.py`.
lean_exe hexstrassen_compare where
  srcDir := "bench"
  root := `HexStrassen.Compare

lean_exe hexconway_bench where
  srcDir := "bench"
  root := `HexConway.Bench

@[default_target]
lean_lib HexManual where

-- Renders `HexManual` to static HTML (see `Main.lean`). Not a
-- `default_target`: the site is built explicitly by the Pages workflow
-- (`.github/workflows/pages.yml`) and on demand via `lake exe hexmanual`.
lean_exe hexmanual where
  root := `Main
