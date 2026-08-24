/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexIntervalMathlib.Experiment.PntFks2XpowProof00
public import HexIntervalMathlib.Experiment.PntFks2XpowProof01
public import HexIntervalMathlib.Experiment.PntFks2XpowProof02
public import HexIntervalMathlib.Experiment.PntFks2XpowProof03
public import HexIntervalMathlib.Experiment.PntFks2XpowProof04
public import HexIntervalMathlib.Experiment.PntFks2XpowProof05

@[expose] public section

/-!
# Source-shaped FKS2 inverse-power results

The disjoint bands are authenticated once, at the strongest denominator that
holds on each band.  Monotonicity then reconstructs the six nested source
prefixes without repeating rational work.
-/

namespace Hex.Interval.Experiment.PntFks2Xpow

open PntFks2Family (allCells)
open PntFks2Shard

private def covered00 : List Cell := bands[0].cells
private def covered01 : List Cell := bands[0].cells ++ bands[1].cells
private def covered02 : List Cell := covered01 ++ bands[2].cells
private def covered03 : List Cell := covered02 ++ bands[3].cells
private def covered04 : List Cell := covered03 ++ bands[4].cells
private def covered05 : List Cell := covered04 ++ bands[5].cells

private theorem covered00_cells : covered00 = allCells.take prefixes[0].cells := by rfl
private theorem covered01_cells : covered01 = allCells.take prefixes[1].cells := by rfl
private theorem covered02_cells : covered02 = allCells.take prefixes[2].cells := by rfl
set_option maxRecDepth 100000 in
private theorem covered03_cells : covered03 = allCells.take prefixes[3].cells := by rfl
set_option maxRecDepth 100000 in
private theorem covered04_cells : covered04 = allCells.take prefixes[4].cells := by rfl
set_option maxRecDepth 100000 in
private theorem covered05_cells : covered05 = allCells.take prefixes[5].cells := by rfl

private theorem promote (source target : Prefix) (cell : Cell)
    (valid : UpperValid source cell)
    (sourcePositive : 0 < source.n) (targetPositive : 0 < target.n)
    (ordered : source.n ≤ target.n) : XpowHolds target cell :=
  xpowHolds_mono_of_upperValid source target cell sourcePositive targetPositive ordered valid

theorem row6_prefix (cell : Cell) (member : cell ∈ allCells.take prefixes[0].cells) :
    XpowHolds prefixes[0] cell := by
  rw [← covered00_cells] at member
  exact promote prefixes[0] prefixes[0] cell (band00_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes]) (by norm_num)

theorem row7_prefix (cell : Cell) (member : cell ∈ allCells.take prefixes[1].cells) :
    XpowHolds prefixes[1] cell := by
  rw [← covered01_cells] at member
  rcases List.mem_append.mp member with member | member
  · exact promote prefixes[0] prefixes[1] cell (band00_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
      (by norm_num [prefixes])
  · exact promote prefixes[1] prefixes[1] cell (band01_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
      (by norm_num)

theorem row8_prefix (cell : Cell) (member : cell ∈ allCells.take prefixes[2].cells) :
    XpowHolds prefixes[2] cell := by
  rw [← covered02_cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact promote prefixes[0] prefixes[2] cell (band00_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
        (by norm_num [prefixes])
    · exact promote prefixes[1] prefixes[2] cell (band01_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
        (by norm_num [prefixes])
  · exact promote prefixes[2] prefixes[2] cell (band02_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
      (by norm_num)

theorem row9_prefix (cell : Cell) (member : cell ∈ allCells.take prefixes[3].cells) :
    XpowHolds prefixes[3] cell := by
  rw [← covered03_cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact promote prefixes[0] prefixes[3] cell (band00_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
          (by norm_num [prefixes])
      · exact promote prefixes[1] prefixes[3] cell (band01_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
          (by norm_num [prefixes])
    · exact promote prefixes[2] prefixes[3] cell (band02_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
        (by norm_num [prefixes])
  · exact promote prefixes[3] prefixes[3] cell (band03_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
      (by norm_num)

theorem row10_prefix (cell : Cell) (member : cell ∈ allCells.take prefixes[4].cells) :
    XpowHolds prefixes[4] cell := by
  rw [← covered04_cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact promote prefixes[0] prefixes[4] cell (band00_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
            (by norm_num [prefixes])
        · exact promote prefixes[1] prefixes[4] cell (band01_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
            (by norm_num [prefixes])
      · exact promote prefixes[2] prefixes[4] cell (band02_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
          (by norm_num [prefixes])
    · exact promote prefixes[3] prefixes[4] cell (band03_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
        (by norm_num [prefixes])
  · exact promote prefixes[4] prefixes[4] cell (band04_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
      (by norm_num)

set_option maxRecDepth 100000 in
theorem row11_prefix (cell : Cell) (member : cell ∈ allCells.take prefixes[5].cells) :
    XpowHolds prefixes[5] cell := by
  rw [← covered05_cells] at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · rcases List.mem_append.mp member with member | member
          · exact promote prefixes[0] prefixes[5] cell (band00_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
              (by norm_num [prefixes])
          · exact promote prefixes[1] prefixes[5] cell (band01_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
              (by norm_num [prefixes])
        · exact promote prefixes[2] prefixes[5] cell (band02_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
            (by norm_num [prefixes])
      · exact promote prefixes[3] prefixes[5] cell (band03_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
          (by norm_num [prefixes])
    · exact promote prefixes[4] prefixes[5] cell (band04_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
        (by norm_num [prefixes])
  · exact promote prefixes[5] prefixes[5] cell (band05_upperValid cell member) (by norm_num [prefixes]) (by norm_num [prefixes])
      (by norm_num)

/-- The `found` hypotheses on the six boundary theorems are exact lookups in
the copied source list, not analytic assumptions. Conformance separately
checks that every lookup is populated. -/
theorem row6_boundary (cell : Cell) (found : allCells[prefixes[0].cells]? = some cell) :
    ¬ XpowHolds prefixes[0] cell := by
  apply not_xpowHolds_of_lowerValid _ _ (by norm_num [prefixes])
  apply boundary00_lowerValid cell
  rw [← proofBoundary00_cell]
  simpa [prefixes] using found

theorem row7_boundary (cell : Cell) (found : allCells[prefixes[1].cells]? = some cell) :
    ¬ XpowHolds prefixes[1] cell := by
  apply not_xpowHolds_of_lowerValid _ _ (by norm_num [prefixes])
  apply boundary01_lowerValid cell
  rw [← proofBoundary01_cell]
  simpa [prefixes] using found

theorem row8_boundary (cell : Cell) (found : allCells[prefixes[2].cells]? = some cell) :
    ¬ XpowHolds prefixes[2] cell := by
  apply not_xpowHolds_of_lowerValid _ _ (by norm_num [prefixes])
  apply boundary02_lowerValid cell
  rw [← proofBoundary02_cell]
  simpa [prefixes] using found

theorem row9_boundary (cell : Cell) (found : allCells[prefixes[3].cells]? = some cell) :
    ¬ XpowHolds prefixes[3] cell := by
  apply not_xpowHolds_of_lowerValid _ _ (by norm_num [prefixes])
  apply boundary03_lowerValid cell
  rw [← proofBoundary03_cell]
  simpa [prefixes] using found

theorem row10_boundary (cell : Cell) (found : allCells[prefixes[4].cells]? = some cell) :
    ¬ XpowHolds prefixes[4] cell := by
  apply not_xpowHolds_of_lowerValid _ _ (by norm_num [prefixes])
  apply boundary04_lowerValid cell
  rw [← proofBoundary04_cell]
  simpa [prefixes] using found

theorem row11_boundary (cell : Cell) (found : allCells[prefixes[5].cells]? = some cell) :
    ¬ XpowHolds prefixes[5] cell := by
  apply not_xpowHolds_of_lowerValid _ _ (by norm_num [prefixes])
  apply boundary05_lowerValid cell
  rw [← proofBoundary05_cell]
  simpa [prefixes] using found

def sampleCells : List Cell :=
  allCells.take 20 ++ (allCells.drop 3726).take 20

private theorem sample_first : allCells.take 20 = bands[0].cells.take 20 := by rfl
set_option maxRecDepth 100000 in
private theorem sample_last :
    (allCells.drop 3726).take 20 = (bands[5].cells.drop 2378).take 20 := by rfl

set_option maxRecDepth 100000 in
theorem row11_sample (cell : Cell) (member : cell ∈ sampleCells) :
    XpowHolds prefixes[5] cell := by
  rcases List.mem_append.mp member with member | member
  · rw [sample_first] at member
    exact promote prefixes[0] prefixes[5] cell (band00_upperValid cell (List.mem_of_mem_take member))
      (by norm_num [prefixes]) (by norm_num [prefixes]) (by norm_num [prefixes])
  · rw [sample_last] at member
    exact promote prefixes[5] prefixes[5] cell
      (band05_upperValid cell (List.mem_of_mem_drop (List.mem_of_mem_take member)))
      (by norm_num [prefixes]) (by norm_num [prefixes]) (by norm_num)

end Hex.Interval.Experiment.PntFks2Xpow

end
