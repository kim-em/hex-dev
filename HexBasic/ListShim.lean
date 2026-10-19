/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.List.Nodup

public section

/-!
Compatibility imports for Hex list helpers. New consumers should import
`HexBasic.List.Nodup` and use the declaration in `Hex.List`.
-/

namespace List

export Hex.List (nodup_subset_length_le)

end List
