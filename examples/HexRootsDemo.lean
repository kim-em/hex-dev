/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots

public section

/-!
# Certified complex-root isolation demo

Run from the repository root with:

```text
lake exe hexroots_demo
```

The polynomial is `p(x) = x³ - x - 1`. The executable first decides that all
roots are simple, isolates all three roots in pairwise-disjoint dyadic squares,
then finds the positive-real isolation and refines it to at least 80 bits of
square precision.

The proof-facing companion `HexRootsMathlib.Examples.pisot` denotes the same
polynomial by an algebraic expression. It gives explicit bounds for all three
roots and proves that the two nonreal roots lie in the open unit disc. Its real
root is the plastic constant, commonly known as the smallest Pisot number; the
companion formalizes its Pisot property, not the global minimality theorem.
-/

namespace HexRootsDemo

open Hex

/-- `p(x) = x³ - x - 1`, with coefficients stored constant-term first. -/
def p : ZPoly := DensePoly.ofCoeffs #[-1, -1, 0, 1]

/-- A display-only conversion. Certification itself uses exact dyadic
arithmetic; floats appear only in the human-readable output. -/
def dyadicToFloat (x : Dyadic) : Float :=
  let q := x.toRat
  Float.ofInt q.num / Float.ofNat q.den

def showSquare {q : ZPoly} (label : String)
    (iso : DyadicRootIsolation q) : IO Unit := do
  let s := iso.square
  IO.println s!"{label}:"
  IO.println s!"  centre ≈ {dyadicToFloat s.re} {if s.im < 0 then "-" else "+"} \
    {dyadicToFloat (Hex.Dyadic.abs s.im)} i"
  IO.println s!"  certified square: |Δre|, |Δim| ≤ 2^(-{s.prec})"

def showAtoms {q : ZPoly}
    (atoms : Array (DyadicRootIsolation q)) : IO Unit := do
  let mut index := 1
  for iso in atoms do
    showSquare s!"root {index}" iso
    index := index + 1

def main : IO Unit := do
  IO.println "Certified isolation for p(x) = x^3 - x - 1"
  if h : HasOnlySimpleRoots p then
    match isolate p h 32 .nk with
    | none =>
        IO.eprintln "isolation unexpectedly exhausted its certified fuel"
    | some atoms =>
        IO.println s!"\nFound {atoms.size} pairwise-disjoint certified roots:\n"
        showAtoms atoms
        IO.println "\nThe accompanying Lean theorems prove:"
        IO.println "  1.32471795 < β < 1.32471796"
        IO.println "  -0.66235899 < Re(conjugates) < -0.66235897"
        IO.println "  0.56227950 < |Im(conjugates)| < 0.56227953"
        IO.println "  |conjugate roots| < 1"
        match atoms.toList.find? (fun iso => decide (0 < iso.square.re)) with
        | none => pure ()
        | some realIso =>
            match realIso.refineTo? 80 with
            | none => IO.eprintln "refinement unexpectedly failed"
            | some refined =>
                IO.println "\nThe real root refined to at least 80 bits:"
                showSquare "refined real root" refined
  else
    IO.eprintln "the polynomial has a repeated root"

end HexRootsDemo

def main : IO Unit := HexRootsDemo.main
