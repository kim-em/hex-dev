import HexBerlekampZassenhaus.Basic

/-!
# Empirical probe: does the fast path ever emit a COARSE (reducible) factor?

Codex's "tight CLD bound" review argued that a below-cap recovery success could
be *coarse*: the projected lattice at low precision might merge two true-factor
supports into one class, so `bhksRecoverClassified` returns a candidate that
exactly divides `f` and multiplies to `f` yet is reducible. If that happened,
`factor_irreducible_of_nonUnit` would be false against the executable and the
fast early-exit would need a soundness guard.

This file tests the claim. Each input is built from KNOWN irreducible factors,
so its true factor-degree multiset is hardcoded; any non-`none` fast result with
a different degree multiset is a coarse/wrong below-cap success.

Findings (every input, every bound tested): the fast path returns ONLY the
correct fine factorisation or a clean `none` (slow-path fallback). Never coarse.
The Swinnerton-Dyer worst case `SD2·(x²+1)` returns `none` at every small bound
rather than emitting a merged class. The trusted exhaustive `factorSlowTrial` is
NOT used as an oracle here because it lifts to the astronomically loose
`defaultFactorCoeffBound` and does not terminate in reasonable time on these
inputs; the known construction supplies the ground truth instead.

`#eval!` output prints during `lake build HexBerlekampZassenhaus.CoarseCheck`.
Diagnostic only; not imported by the proof corpus.
-/

namespace Hex.CoarseCheck
open Hex

def linear (k : Int) : ZPoly := DensePoly.ofCoeffs #[-k, 1]
def q (a : Int) : ZPoly := DensePoly.ofCoeffs #[a, 0, 1]        -- x² + a (irreducible for a > 0)
def qlin (b c : Int) : ZPoly := DensePoly.ofCoeffs #[c, b, 1]   -- x² + b x + c
def prod (fs : List ZPoly) : ZPoly := Array.polyProduct fs.toArray
def sd2 : ZPoly := DensePoly.ofCoeffs #[1, 0, -10, 0, 1]        -- x⁴-10x²+1 (Swinnerton-Dyer)

def splitFamily (n : Nat) : ZPoly :=
  Array.polyProduct (((List.range n).map (fun i => linear (Int.ofNat (i + 1)))).toArray)

def sortedDegs (fs : Array ZPoly) : List Nat :=
  (fs.toList.map (fun g => g.degree?.getD 0)).mergeSort (fun a b => decide (a ≤ b))

/-- Full-cap `factorFast`: any emitted factor of degree > 1 on the all-linear
split family is coarse. -/
def reportFast (label : String) (f : ZPoly) : IO Unit := do
  match factorFast f with
  | none => IO.println s!"{label}: factorFast = none"
  | some φ =>
    let dm := φ.factors.toList.map (fun e => (e.1.degree?.getD 0, e.2))
    let coarse := dm.any (fun p => p.1 > 1)
    let mark := if coarse then "<<<<<< COARSE" else "fine"
    IO.println s!"{label}: factorFast deg×mult = {dm}  {mark}"

/-- Bounded fast calls at small B (precision capped, no astronomical-cap hang)
compared against the KNOWN true factor-degree multiset. -/
def knownProbe (label : String) (f : ZPoly) (trueDegs : List Nat) : IO Unit := do
  let truth := trueDegs.mergeSort (fun a b => decide (a ≤ b))
  IO.println s!"{label}: TRUE degs = {truth}"
  for B in [(2 : Nat), 4, 8, 16, 32] do
    match factorFastFactorsWithBound f B with
    | none => IO.println s!"   B={B}: none"
    | some fs =>
      let ds := sortedDegs fs
      let mark := if ds == truth then "fine (== truth)" else "<<<<<< COARSE/WRONG"
      IO.println s!"   B={B}: degs={ds}  {mark}"

/-- Window-engineering probe: small factors (cheap product recovery) embedded
among large factors (CLD domination ⇒ high separation precision). Extended B
range to reach recovery precision for the large factors. If the lattice ever
emits the small pair merged, we get COARSE/WRONG. -/
def windowProbe (label : String) (f : ZPoly) (trueDegs : List Nat) : IO Unit := do
  let truth := trueDegs.mergeSort (fun a b => decide (a ≤ b))
  IO.println s!"{label}: TRUE degs = {truth}"
  for B in [(4 : Nat), 16, 64, 128, 256, 512] do
    match factorFastFactorsWithBound f B with
    | none => IO.println s!"   B={B}: none"
    | some fs =>
      let ds := sortedDegs fs
      let mark := if ds == truth then "fine (== truth)" else "<<<<<< COARSE/WRONG"
      IO.println s!"   B={B}: degs={ds}  {mark}"

-- A. Full-cap factorFast on the deterministic split family.
#eval! do
  IO.println "== A. factorFast (full cap) on split family (all-linear truth) =="
  for n in [(4 : Nat), 6, 8, 10, 12] do
    reportFast s!"(x-1)..(x-{n})" (splitFamily n)

-- B. Lattice-adversarial inputs (products of irreducible quadratics, plus
-- Swinnerton-Dyer), bounded fast calls vs known truth.
#eval! knownProbe "(x-1)(x-2)(x²+1)(x²+2)"    (prod [linear 1, linear 2, q 1, q 2]) [1, 1, 2, 2]
#eval! knownProbe "(x²+1)(x²+2)(x²+x+1)"       (prod [q 1, q 2, qlin 1 1]) [2, 2, 2]
#eval! knownProbe "(x²+x+1)(x²+x+2)(x²+x+3)"   (prod [qlin 1 1, qlin 1 2, qlin 1 3]) [2, 2, 2]
#eval! knownProbe "(x²+1)(x²+2)(x²+3)(x²+5)"   (prod [q 1, q 2, q 3, q 5]) [2, 2, 2, 2]
#eval! knownProbe "SD2·(x²+1)"                 (prod [sd2, q 1]) [2, 4]

-- C. Window-engineering: small pair (x-1)(x-2) [product x²-3x+2, tiny, cheap to
-- recover] embedded among LARGE-coefficient factors that dominate the CLD
-- vectors and force high separation precision. If the precision window opens,
-- the fast path emits the merged x²-3x+2 (degree 2) → COARSE.
#eval! windowProbe "(x-1)(x-2)(x²+100)"            (prod [linear 1, linear 2, q 100]) [1, 1, 2]
#eval! windowProbe "(x-1)(x-2)(x²+100)(x²+200)"    (prod [linear 1, linear 2, q 100, q 200]) [1, 1, 2, 2]
#eval! windowProbe "(x-1)(x-2)(x²+999)"            (prod [linear 1, linear 2, q 999]) [1, 1, 2]
#eval! windowProbe "(x-1)(x+1)(x²+500)"            (prod [linear 1, linear (-1), q 500]) [1, 1, 2]
#eval! windowProbe "(x-10)(x-11)(x²+777)"          (prod [linear 10, linear 11, q 777]) [1, 1, 2]

end Hex.CoarseCheck
