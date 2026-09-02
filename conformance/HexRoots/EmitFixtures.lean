/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexRoots

/-!
JSONL emit driver for the `hex-roots` oracle.

`lake exe hexroots_emit_fixtures` writes one `poly` fixture record per
input case followed by one `isolateAll32` `result` record carrying the
outcome of `Hex.isolateAll?` at target precision `32`. The companion
oracle `scripts/oracle/roots_flint.py` re-runs each polynomial through
python-flint's `fmpz_poly.complex_roots()` (certified Arb balls with
multiplicities) and cross-checks that the Lean certification discs
cover the flint roots with matching multiplicities.

The driver uses `isolateAll?` at target `32` rather than `isolate`: the oracle
needs root *locations*, not the separation precision `isolate` forces.

**Fixture set.** The CI tier contains 50 degree-20 dense
polynomials from the seed-`0xC0FFEE` LCG, plus the small curated rational and
Gaussian-rational cases that exercise simple atoms and real/complex
multiple-root clusters. The all-atoms local finisher makes fresh degree-20
emission practical (the soft front end is deliberately size-gated above this
tier); rounded Newton recentring keeps the exact rational centre representation compact.
Every run regenerates the full deterministic set before python-flint checks the
committed JSONL, so a kernel change cannot leave stale certificates unnoticed.

Each `result.value` serialises the isolation outcome. On success it is
a JSON array with one object per certification result, canonically sorted by
its object encoding so semantically irrelevant component traversal order does
not churn the committed fixture. Each object carries
`kind` (`"atom"` | `"cluster"`), `k` (root count, `1` for atoms), the
disc centre as an exact rational (`re_num` / `re_den` / `im_num` /
`im_den`, from `DyadicSquare.re`/`im` via `Dyadic.toRat`), and `prec`
(the stored square's precision). A `none` outcome from the driver
serialises as the JSON string `"none"` and is reported to stderr with its case
id.

The local JSON builders below (`certValue`, `noneValue`) exist because
the shared `Hex.Conformance.Emit` helpers only cover flat records; the
per-result object here is nested, so the driver hand-builds the array
payload and passes it to `emitResult` as a raw JSON fragment.
-/

namespace Hex.RootsEmit

open Hex.Conformance.Emit
open Hex Hex.DensePoly

private def lib : String := "HexRoots"

/-- The isolation target precision for the ci-tier fixtures. -/
private def target : Int := 32

/-- One ci-tier fixture: a case id and the polynomial's coefficients
    (ascending, constant term first). -/
private structure Case where
  id     : String
  coeffs : List Int
deriving Inhabited

/-- One step of the deterministic seed-`0xC0FFEE` coefficient stream. -/
private def lcgNext (s : UInt64) : UInt64 :=
  6364136223846793005 * s + 1442695040888963407

/-- Generate `count` consecutive dense degree-`degree` cases from one LCG
state, forcing a zero leading draw to one. -/
private def randomCases (degree count : Nat) (seed : UInt64) : List Case := Id.run do
  let mut s := seed
  let mut out : Array Case := #[]
  for i in [0:count] do
    let mut coeffs : Array Int := #[]
    for _ in [0:degree + 1] do
      s := lcgNext s
      coeffs := coeffs.push (Int.ofNat (s.toNat % 21) - 10)
    if coeffs[degree]! = 0 then
      coeffs := coeffs.set! degree 1
    out := out.push { id := s!"random/deg{degree}_{i}", coeffs := coeffs.toList }
  return out.toList

/-- Curated atom/cluster cases followed by the full seeded degree-20
ci tier. -/
private def cases : List Case := [
  -- Real simple roots.
  { id := "rational/deg3", coeffs := [6, -7, 0, 1] },            -- (x−1)(x−2)(x+3)
  { id := "rational/x3_minus_x", coeffs := [0, -1, 0, 1] },      -- x(x−1)(x+1)
  -- Complex and real simple roots together.
  { id := "gaussian/x2p4_xm1_xp3", coeffs := [-12, 8, 1, 2, 1] }, -- (x²+4)(x−1)(x+3)
  -- Multiple root: the k = 2 cluster around 5 must not atomize.
  { id := "cluster/x2p1_x5sq", coeffs := [25, -10, 26, -10, 1] }, -- (x²+1)(x−5)²
  -- Real multiple root: the k = 2 cluster around 1 must not atomize.
  { id := "cluster/xm1sq_xm4", coeffs := [-4, 9, -6, 1] },        -- (x−1)²(x−4)
  -- Complex multiple roots: two k = 2 clusters at ±i.
  { id := "cluster/x2p1sq", coeffs := [1, 0, 2, 0, 1] }           -- (x²+1)²
] ++ randomCases 20 50 0xC0FFEE

/-! # Result serialisation. -/

/-- Serialise one certification result as a JSON object. -/
private def certObject {p : ZPoly} (c : Certified p) : String :=
  let s := c.square
  let kind := match c with | .atom _ => "atom" | .cluster _ => "cluster"
  let k : Int := match c with | .atom _ => 1 | .cluster cl => (cl.k : Int)
  let re := s.re.toRat
  let im := s.im.toRat
  "{\"kind\":\"" ++ kind ++ "\",\"k\":" ++ toString k ++
    ",\"re_num\":" ++ toString re.num ++ ",\"re_den\":" ++ toString (re.den : Int) ++
    ",\"im_num\":" ++ toString im.num ++ ",\"im_den\":" ++ toString (im.den : Int) ++
    ",\"prec\":" ++ toString s.prec ++ "}"

/-- Serialise the certification results as a JSON array. -/
private def certValue {p : ZPoly} (rs : Array (Certified p)) : String :=
  let objects := (rs.toList.map certObject).mergeSort (· ≤ ·)
  "[" ++ String.intercalate "," objects ++ "]"

/-- The `result.value` for a driver give-up. -/
private def noneValue : String := "\"none\""

/-- The expensive half of one case: the serialised `isolateAll32`
outcome and the gave-up flag. Pure, so cases parallelise as tasks
with the record stream still written in order by `main`. -/
private def caseValue (c : Case) : String × Bool :=
  let p : ZPoly := DensePoly.ofCoeffs c.coeffs.toArray
  if h : 0 < p.degree?.getD 0 then
    match isolateAll? p target #[Component.cauchy p h] with
    | some rs => (certValue rs, false)
    | none    => (noneValue, true)
  else
    (noneValue, true)

end Hex.RootsEmit

open Hex.RootsEmit Hex.Conformance.Emit in
def main : IO Unit := do
  -- The per-case isolation dominates the run (seconds per degree-20
  -- case), so it is computed in parallel tasks while the records are
  -- written strictly in case order, keeping the stream byte-identical
  -- to sequential emission. The runtime's task pool bounds
  -- concurrency at the hardware thread count; `HEX_EMIT_JOBS` caps
  -- the number of outstanding tasks below that when set.
  let jobs? := (← IO.getEnv "HEX_EMIT_JOBS").bind (·.toNat?)
  let arr := (cases : List Case).toArray
  let n := arr.size
  let window := match jobs? with
    | some j => min (max 1 j) n
    | none => n
  let mut tasks : Array (Option (Task (String × Bool))) := .replicate n none
  let mut spawned := 0
  while spawned < window do
    let j := spawned
    tasks := tasks.set! j (some (Task.spawn fun _ => caseValue arr[j]!))
    spawned := spawned + 1
  for i in [0:n] do
    let c := arr[i]!
    emitPolyFixture lib c.id c.coeffs
    let (value, gaveUp) := (tasks[i]!.getD (Task.pure (noneValue, true))).get
    emitResult lib c.id "isolateAll32" value
    if gaveUp then
      IO.eprintln s!"hexroots_emit_fixtures: isolateAll? returned none for case {c.id}; \
        this is SPEC-noteworthy"
    if spawned < n then
      let j := spawned
      tasks := tasks.set! j (some (Task.spawn fun _ => caseValue arr[j]!))
      spawned := spawned + 1
