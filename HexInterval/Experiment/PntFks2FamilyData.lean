/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntFks2FamilyData00
public import HexInterval.Experiment.PntFks2FamilyData01
public import HexInterval.Experiment.PntFks2FamilyData02
public import HexInterval.Experiment.PntFks2FamilyData03
public import HexInterval.Experiment.PntFks2FamilyData04
public import HexInterval.Experiment.PntFks2FamilyData05
public import HexInterval.Experiment.PntFks2FamilyData06
public import HexInterval.Experiment.PntFks2FamilyData07
public import HexInterval.Experiment.PntFks2FamilyData08
public import HexInterval.Experiment.PntFks2FamilyData09
public import HexInterval.Experiment.PntFks2FamilyData10
public import HexInterval.Experiment.PntFks2FamilyData12
public import HexInterval.Experiment.PntFks2FamilyData13

@[expose] public section

/-! # Source-correlated full pinned PNT+ FKS2 family data -/

namespace Hex.Interval.Experiment.PntFks2Family

open PntFks2Shard

structure ShardRecord where
  shard : Nat
  cells : Nat
  digest : String
  deriving DecidableEq, Repr

/-- SHA-256 digests of the normalized tuples in each exact source shard. -/
def shardRecords : List ShardRecord := [
  ⟨0, 1000, "72410beb590803bda4a870007e612fb21ea00729cae78f15239a06a56f059f40"⟩,
  ⟨1, 1000, "fe6cf8535a902fb47e0ec7b0a5bdc1c9802eb367feb1fa048de5438a25614351"⟩,
  ⟨2, 1000, "9935742d58da928ea124bb29bdb920fd01a1349cfb2dde73743725281a74df9d"⟩,
  ⟨3, 1000, "8f5ad79f7f84264c51a9e149dee4174da1e36042e8764d3fb1a0e6de4a933aec"⟩,
  ⟨4, 1000, "f1a7b4212a11f4a78795094bbecf9637c936b99c1dbeb34aadffc5d6bc54cd74"⟩,
  ⟨5, 1000, "9df000935789249aa7fe7ca04aa1ef40d39156790bf7ab1625cea835140493b8"⟩,
  ⟨6, 1000, "58909e8345f801f4f5d6b8e07837c9d4701c096084ad46dd1c3127c8b337dfa4"⟩,
  ⟨7, 1000, "b62af7b1b56fa51fc1e9a5dd9b1428e94c2063c9bca6eb7b3f6af9914e3eb765"⟩,
  ⟨8, 1000, "1373f2c939e56b0336a0846ca85647590169fa3da7438ecd619101aa6b450612"⟩,
  ⟨9, 1000, "661471e770cd5084e2327df0ca13046ef0e58d2b7360874a0176bbe6a24d777d"⟩,
  ⟨10, 1000, "918997b176bbc7e5df59c6a1046cb8f4db4db13ab0a1499c4e4b6bd3205930d4"⟩,
  ⟨11, 1000, "f0c1460c72711de70ea677eb350bc89031f098965ff48d416d29f8d20a7a5b31"⟩,
  ⟨12, 1000, "524d873ff7a72dd0a51be4a79920cd87c5f0dd59a205e0c7980ef7410d4dbf57"⟩,
  ⟨13, 590, "3c3420a0630120c005febfaf9eb607a01bc8126b3d4b03fc30a852f4da002b0e"⟩
]

def shardCount : Nat := 14
def familyCellCount : Nat := 13590
def runtimeChunkSize : Nat := 20
def familyChunkCount : Nat := 680

def shardCells : Nat → List Cell
  | 0 => cells00
  | 1 => cells01
  | 2 => cells02
  | 3 => cells03
  | 4 => cells04
  | 5 => cells05
  | 6 => cells06
  | 7 => cells07
  | 8 => cells08
  | 9 => cells09
  | 10 => cells10
  | 11 => PntFks2Shard.cells11
  | 12 => cells12
  | 13 => cells13
  | _ => []

/-- All source cells in exact shard and declaration order. -/
def allCells : List Cell := (List.range shardCount).flatMap shardCells

def chunkShard (index : Nat) : Nat := index / 50
def chunkLocal (index : Nat) : Nat := index % 50

/-- Runtime chunks are twenty cells, except the final ten-cell chunk. -/
def familyChunk (index : Nat) : List Cell :=
  (shardCells (chunkShard index)).drop (chunkLocal index * runtimeChunkSize)
    |>.take runtimeChunkSize

end Hex.Interval.Experiment.PntFks2Family
