/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
`#m[...]` literal notation and grid pretty-printing for `Hex.Matrix`.

`#m[a, b; c, d]` builds the matrix with rows `[a, b]` and `[c, d]`: rows are
separated by `;` and entries by `,`, mirroring Mathlib's `!![...]` but with a
distinct opening token, so the two notations coexist in the Mathlib bridge
libraries (Mathlib owns `![` and `!![`).

```
#m[1, 2;
   3, 4]   -- : Hex.Matrix Int 2 2
```

A literal collects its rows into nested `#v[...]` vectors and feeds them to
`Hex.Matrix.ofFn`, so the construction goes through the public matrix API. Row
lengths are checked by the elaborator: a ragged literal fails to typecheck
rather than silently building a malformed matrix.

The `Repr` instance renders a matrix back in `#m[...]` notation under `#eval`,
column-aligned and copy-pasteable as input.
-/

namespace Hex.Matrix

open Lean

/-- `#m[a, b; c, d]` is the `Hex.Matrix` with rows `[a, b]` and `[c, d]`.
Rows are `;`-separated and entries `,`-separated. -/
syntax (name := matrixLiteral)
  "#m[" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term

macro_rules
  | `(#m[$[$[$rows],*];*]) => do
    let nRows := rows.size
    let nCols := if h : 0 < nRows then rows[0].size else 0
    let rowVecs ← rows.zipIdx.mapM fun (row, i) => do
      unless row.size = nCols do
        Macro.throwErrorAt (mkNullNode (row.map (·.raw)))
          s!"ragged matrix literal: row {i + 1} has {row.size} entries, but row 1 has {nCols}"
      let elems : Syntax.TSepArray `term "," := .ofElems row
      `(#v[$elems,*])
    let rowsSep : Syntax.TSepArray `term "," := .ofElems rowVecs
    `(let d := #v[$rowsSep,*];
      Hex.Matrix.ofFn (n := $(quote nRows)) (m := $(quote nCols)) fun i j => d[i][j])

/-- Render `M` in `#m[...]` notation, with entries right-justified per column so
the columns line up. The output is copy-pasteable as input. For example,
```
#m[ 0, 2,  1;
   -6, 0, -8;
    5, 6,  0]
```
This is what the `Repr` instance shows under `#eval`. -/
def render [Repr R] (M : Matrix R n m) : Std.Format :=
  let cells : List (List String) :=
    (List.finRange n).map fun i => (M.row i).toList.map fun x => (repr x).pretty
  let widths : List Nat :=
    (List.range m).map fun j => cells.foldl (fun w r => max w (r.getD j "").length) 0
  let pad : String → Nat → String := fun s w => String.ofList (List.replicate (w - s.length) ' ') ++ s
  let rowText : List String → String := fun r =>
    ", ".intercalate (((List.range m).zip widths).map fun (j, w) => pad (r.getD j "") w)
  -- Continuation rows are indented by three spaces to sit under the first entry
  -- (just past the `#m[` opener), keeping the columns aligned.
  Std.Format.text ("#m[" ++ ";\n   ".intercalate (cells.map rowText) ++ "]")

/-- Show matrices in copy-pasteable `#m[...]` notation under `#eval`/`Repr`.
Higher priority than the `#v[...]` vector instance below so a matrix renders as
a grid rather than as a nested vector of vectors. -/
instance (priority := high) [Repr R] : Repr (Matrix R n m) where
  reprPrec M _ := M.render

/-- The `#m[...]` rendering as a `String`. -/
instance [Repr R] : ToString (Matrix R n m) where
  toString M := M.render.pretty

/-- Render a vector in copy-pasteable `#v[...]` notation under `#eval`/`Repr`,
mirroring the `#m[...]` matrix rendering. Higher priority than the core
`deriving Repr` instance, so a bare vector (for example a matrix row or an LLL
short vector) prints as `#v[...]` and can be pasted straight back as input. -/
instance (priority := high) reprVector [Repr R] : Repr (Vector R n) where
  reprPrec v _ :=
    Std.Format.text ("#v[" ++ ", ".intercalate (v.toList.map fun x => (repr x).pretty) ++ "]")

end Hex.Matrix
