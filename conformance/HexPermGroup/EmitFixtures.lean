/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPermGroup

/-! Reproducible, presentation-preserving inputs for the GAP oracle. -/

open Lean

private def perm (xs : List Nat) : Json := toJson xs

private def record (id operation : String) (degree : Nat) (generators : List (List Nat))
    (fields : List (String × Json)) : Json :=
  Json.mkObj <| [("schema_version", toJson (1 : Nat)), ("id", toJson id),
    ("operation", toJson operation), ("degree", toJson degree),
    ("generators", toJson generators), ("status", toJson "complete")] ++ fields

private def s3 : List (List Nat) := [[1, 0, 2], [1, 2, 0]]
private def d4 : List (List Nat) := [[1, 2, 3, 0], [0, 3, 2, 1]]

private def largeGenerators : List (List Nat) :=
  (List.range 65).map fun k =>
    (List.range 130).map fun i =>
      if i = 2 * k then i + 1 else if i = 2 * k + 1 then i - 1 else i

private def cases : List Json :=
  [ record "s3-chain" "chain-cosets" 3 s3
      [("order", toJson (6 : Nat)), ("query", perm [2, 1, 0]),
       ("member", toJson true), ("orbits", toJson [[0, 1, 2]]),
       ("stabilizer_order", toJson (2 : Nat)),
       ("subgroup_generators", toJson [[1, 0, 2]]),
       ("subgroup_index", toJson (3 : Nat))]
  , record "s3-elementary" "elementary" 3 s3
      [("left", perm [1, 0, 2]), ("right", perm [1, 2, 0]),
       ("hex_product", perm [0, 2, 1]), ("sign", toJson (-1 : Int)),
       ("cycle_type", toJson [2, 1]), ("transitive", toJson true),
       ("abelian", toJson false)]
  , record "s3-action" "actions-kernel" 3 s3
      [("domain", toJson [0, 1, 2]), ("domain_identification", toJson [0, 1, 2]),
       ("image_order", toJson (6 : Nat)), ("kernel_order", toJson (1 : Nat))]
  , record "s3-search" "subgroup-search" 3 s3
      [("subgroup_generators", toJson [[1, 0, 2]]),
       ("subset", toJson [0, 1]), ("target", toJson [1, 2]),
       ("set_stabilizer_order", toJson (2 : Nat)),
       ("intersection_order", toJson (2 : Nat)),
       ("centralizer_order", toJson (2 : Nat)),
       ("normalizer_order", toJson (2 : Nat)), ("transporter_exists", toJson true)]
  , record "d4-blocks" "blocks" 4 d4
      [("domain", toJson [0, 1, 2, 3]), ("seed", toJson [0, 2]),
       ("blocks", toJson [[0, 2], [1, 3]]), ("primitive", toJson false)]
  , record "s3-normal" "normal-structure" 3 s3
      [("subgroup_generators", toJson [[1, 0, 2]]),
       ("normal_closure_order", toJson (6 : Nat)), ("core_order", toJson (1 : Nat)),
       ("derived_order", toJson (3 : Nat)), ("derived_series_orders", toJson [6, 3, 1]),
       ("solvable", toJson true), ("normal", toJson false)]
  , record "c2-products" "products" 2 [[1, 0]]
      [("right_degree", toJson (2 : Nat)), ("right_generators", toJson [[1, 0]]),
       ("direct_degree", toJson (4 : Nat)), ("direct_generator_count", toJson (2 : Nat)),
       ("direct_order", toJson (4 : Nat)), ("wreath_degree", toJson (4 : Nat)),
       ("wreath_generator_count", toJson (3 : Nat)), ("wreath_order", toJson (8 : Nat)),
       ("domain_identification", toJson [[0, 0], [0, 1], [1, 0], [1, 1]])]
  , record "s3-rank" "rank-unrank-sampling" 3 s3
      [("indices", toJson [0, 1, 2, 3, 4, 5]), ("element_count", toJson (6 : Nat)),
       ("sampling_status", toJson "complete")]
  , record "limits-corruption" "limits-corruption" 3 s3
      [("producer_status", toJson "limited"), ("replay_status", toJson "rejected"),
       ("raw_input_retained", toJson true)]
  , record "order-over-u64" "large-order" 130 largeGenerators
      [("order_decimal", toJson "36893488147419103232"),
       ("fixed_points", toJson ([] : List Nat))] ]

def main (_args : List String) : IO Unit :=
  for fixture in cases do IO.println fixture.compress
