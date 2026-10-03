import Lake
open Lake DSL System

package HexECPPMathlib where
  leanOptions := #[⟨`doc.verso, true⟩, ⟨`doc.verso.suggestions, false⟩]

require HexBasic from git
  "https://github.com/leanprover/hex-basic.git" @ "a7de08cb8ff56c86e43ddb909e16df78e672a303"

require HexArith from git
  "https://github.com/leanprover/hex-arith.git" @ "4976aa3805cdbc1cbbb3853bcdb784467a754249"

require HexPrimality from git
  "https://github.com/leanprover/hex-primality.git" @ "4717a54f0e128cc041df82a4274ab0db914cbdde"

require HexECPP from git
  "https://github.com/leanprover/hex-ecpp.git" @ "ae0f33d6747b4469d50c2ee21d766791ce7ce855"

require HexPrimalityMathlib from git
  "https://github.com/leanprover/hex-primality-mathlib.git" @ "3de013793db15f7d0f390360334006bc6fbfda13"

-- Temporary module-system branch; switch to pinned upstream main after
-- https://github.com/CBirkbeck/AINTLIB/pull/8598 merges.
require AINTLIB from git
  "https://github.com/CBirkbeck/AINTLIB.git" @
    "a5c3affa17bb17d13bbfd2e6c828dc978af65657"

-- Keep Mathlib last so its compatible transitive pins win over AINTLIB
-- when resolving a fresh lockfile.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d870b9068518a0870842d15a0cd42637ec30b587"

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

@[default_target]
lean_lib HexECPPMathlib where
  roots := #[`HexECPPMathlib, `HexECPPMathlib.Native, `HexECPPMathlib.Pari]

lean_lib HexECPPMathlibPariIO where
  roots := #[`HexECPPMathlib.Pari.IO]
  globs := #[.one `HexECPPMathlib.Pari.IO]
  precompileModules := true
  moreLinkObjs := #[hexecpppariio]

lean_lib HexECPPMathlibTests where
  globs := #[.one `HexECPPMathlib.Tests]
