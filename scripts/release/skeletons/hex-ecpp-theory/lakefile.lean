import Lake
open Lake DSL System

package HexECPPTheory where
  leanOptions := #[⟨`doc.verso, true⟩, ⟨`doc.verso.suggestions, false⟩]

require HexBasic from git
  "https://github.com/leanprover/hex-basic.git" @ "a7de08cb8ff56c86e43ddb909e16df78e672a303"

require HexArith from git
  "https://github.com/leanprover/hex-arith.git" @ "4976aa3805cdbc1cbbb3853bcdb784467a754249"

require HexPrimality from git
  "https://github.com/leanprover/hex-primality.git" @ "4717a54f0e128cc041df82a4274ab0db914cbdde"

require HexECPP from git
  "https://github.com/leanprover/hex-ecpp.git" @ "ae0f33d6747b4469d50c2ee21d766791ce7ce855"

require HexPrimalityTheory from git
  "https://github.com/leanprover/hex-primality-theory.git" @ "3de013793db15f7d0f390360334006bc6fbfda13"

-- AINTLIB supplies Hasse's theorem and supports module clients.
require AINTLIB from git
  "https://github.com/CBirkbeck/AINTLIB.git" @
    "ab1451487da02cd4483d0e2cdb2cc9e44bbbac17"

-- Keep Mathlib last so its compatible transitive pins win over AINTLIB
-- when resolving a fresh lockfile.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d870b9068518a0870842d15a0cd42637ec30b587"

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

@[default_target]
lean_lib HexECPPTheory where
  roots := #[`HexECPPTheory, `HexECPPTheory.Native, `HexECPPTheory.Pari]

lean_lib HexECPPTheoryPariIO where
  roots := #[`HexECPPTheory.Pari.IO]
  globs := #[.one `HexECPPTheory.Pari.IO]
  precompileModules := true
  moreLinkObjs := #[hexecpppariio]

lean_lib HexECPPTheoryTests where
  globs := #[.one `HexECPPTheory.Tests]
