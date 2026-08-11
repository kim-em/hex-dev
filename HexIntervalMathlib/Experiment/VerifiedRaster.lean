/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.DyadicInterval

@[expose] public section

/-!
# Proof objects for conservative raster graphs

This module states what a verified rasterizer must prove.  It does not know
which functions the interval engine supports, how search chooses subdivisions,
or how a bitmap is encoded.  A function package supplies interval theorems; a
raster assembly proves that every graph point over the horizontal viewport is
inside a marked pixel and that every blank pixel is disjoint from the graph.

Marked pixels are deliberately allowed to be conservative: `Correct` does not
claim that every marked pixel is hit.  A PNG or other image is an untrusted
rendering of the finite `Raster.cells` mask, not part of the proof boundary.
-/

namespace Hex.Interval.Experiment.VerifiedRaster

open DyadicInterval

/-- One rectangular pixel, with exact open or closed boundaries inherited
from its dyadic interval facts. -/
structure Pixel where
  x : Fact
  y : Fact
  marked : Bool
  deriving DecidableEq

/-- Exact membership in one pixel rectangle. -/
def Pixel.Contains (pixel : Pixel) (x y : ℝ) : Prop :=
  pixel.x.Contains x ∧ pixel.y.Contains y

/-- A finite row-major mask and its exact mathematical viewport.  `shape`
binds only the flat-list length to the declared dimensions.  Rendering must
preserve the list order, `marked` bits, and every cell's exact rectangle; a
future checked layout will bind those rectangles to uniform pixel indices. -/
structure Raster where
  width : Nat
  height : Nat
  xViewport : Fact
  yViewport : Fact
  cells : List Pixel
  shape : cells.length = width * height

/-- Every graph point over the horizontal viewport is enclosed by at least one
marked pixel.  This stronger form also proves that the graph stays inside the
vertical viewport whenever all listed pixels do. -/
def Covers (raster : Raster) (f : ℝ → ℝ) : Prop :=
  ∀ x, raster.xViewport.Contains x →
    ∃ pixel, pixel ∈ raster.cells ∧ pixel.marked = true ∧
      pixel.Contains x (f x)

/-- Every pixel rendered blank is disjoint from the graph.  The horizontal
premise is local to the pixel, so this property remains useful even when a
raster covers only part of a larger function domain. -/
def Excludes (raster : Raster) (f : ℝ → ℝ) : Prop :=
  ∀ pixel, pixel ∈ raster.cells → pixel.marked = false →
    ∀ x, pixel.x.Contains x → ¬pixel.y.Contains (f x)

/-- Every rendered cell lies within the declared viewport.  This prevents the
finite mask from proving a graph enclosure over one rectangle while labelling
it as an unrelated viewport. -/
def Contained (raster : Raster) : Prop :=
  ∀ pixel, pixel ∈ raster.cells → ∀ x y, pixel.Contains x y →
    raster.xViewport.Contains x ∧ raster.yViewport.Contains y

/-- Sound conservative graph rendering.  It intentionally omits the stronger
and usually false assertion that every marked pixel contains a graph point.
An empty horizontal viewport may satisfy this contract vacuously; clients
claiming a visible graph should separately prove that viewport nonempty. -/
structure Correct (raster : Raster) (f : ℝ → ℝ) : Prop where
  contained : Contained raster
  covers : Covers raster f
  excludes : Excludes raster f

end Hex.Interval.Experiment.VerifiedRaster
