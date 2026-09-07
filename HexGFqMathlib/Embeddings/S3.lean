/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

/-- The canonical embedding of GF(419^1) into GF(419^4). -/
noncomputable def embed_419_1_4 :
    Hex.GFq 419 1 Hex.Conway.supportedEntry_419_1 →+*
      Hex.GFq 419 4 Hex.Conway.supportedEntry_419_4 :=
  conwayEmbed 419 1 4 _ _ Hex.Conway.compat_419_1_4

/-- The canonical embedding of GF(419^2) into GF(419^4). -/
noncomputable def embed_419_2_4 :
    Hex.GFq 419 2 Hex.Conway.supportedEntry_419_2 →+*
      Hex.GFq 419 4 Hex.Conway.supportedEntry_419_4 :=
  conwayEmbed 419 2 4 _ _ Hex.Conway.compat_419_2_4

/-- The canonical embedding of GF(421^1) into GF(421^2). -/
noncomputable def embed_421_1_2 :
    Hex.GFq 421 1 Hex.Conway.supportedEntry_421_1 →+*
      Hex.GFq 421 2 Hex.Conway.supportedEntry_421_2 :=
  conwayEmbed 421 1 2 _ _ Hex.Conway.compat_421_1_2

/-- The canonical embedding of GF(421^1) into GF(421^3). -/
noncomputable def embed_421_1_3 :
    Hex.GFq 421 1 Hex.Conway.supportedEntry_421_1 →+*
      Hex.GFq 421 3 Hex.Conway.supportedEntry_421_3 :=
  conwayEmbed 421 1 3 _ _ Hex.Conway.compat_421_1_3

/-- The canonical embedding of GF(421^1) into GF(421^4). -/
noncomputable def embed_421_1_4 :
    Hex.GFq 421 1 Hex.Conway.supportedEntry_421_1 →+*
      Hex.GFq 421 4 Hex.Conway.supportedEntry_421_4 :=
  conwayEmbed 421 1 4 _ _ Hex.Conway.compat_421_1_4

/-- The canonical embedding of GF(421^2) into GF(421^4). -/
noncomputable def embed_421_2_4 :
    Hex.GFq 421 2 Hex.Conway.supportedEntry_421_2 →+*
      Hex.GFq 421 4 Hex.Conway.supportedEntry_421_4 :=
  conwayEmbed 421 2 4 _ _ Hex.Conway.compat_421_2_4

/-- The canonical embedding of GF(431^1) into GF(431^2). -/
noncomputable def embed_431_1_2 :
    Hex.GFq 431 1 Hex.Conway.supportedEntry_431_1 →+*
      Hex.GFq 431 2 Hex.Conway.supportedEntry_431_2 :=
  conwayEmbed 431 1 2 _ _ Hex.Conway.compat_431_1_2

/-- The canonical embedding of GF(431^1) into GF(431^3). -/
noncomputable def embed_431_1_3 :
    Hex.GFq 431 1 Hex.Conway.supportedEntry_431_1 →+*
      Hex.GFq 431 3 Hex.Conway.supportedEntry_431_3 :=
  conwayEmbed 431 1 3 _ _ Hex.Conway.compat_431_1_3

/-- The canonical embedding of GF(431^1) into GF(431^4). -/
noncomputable def embed_431_1_4 :
    Hex.GFq 431 1 Hex.Conway.supportedEntry_431_1 →+*
      Hex.GFq 431 4 Hex.Conway.supportedEntry_431_4 :=
  conwayEmbed 431 1 4 _ _ Hex.Conway.compat_431_1_4

/-- The canonical embedding of GF(431^2) into GF(431^4). -/
noncomputable def embed_431_2_4 :
    Hex.GFq 431 2 Hex.Conway.supportedEntry_431_2 →+*
      Hex.GFq 431 4 Hex.Conway.supportedEntry_431_4 :=
  conwayEmbed 431 2 4 _ _ Hex.Conway.compat_431_2_4

/-- The canonical embedding of GF(433^1) into GF(433^2). -/
noncomputable def embed_433_1_2 :
    Hex.GFq 433 1 Hex.Conway.supportedEntry_433_1 →+*
      Hex.GFq 433 2 Hex.Conway.supportedEntry_433_2 :=
  conwayEmbed 433 1 2 _ _ Hex.Conway.compat_433_1_2

/-- The canonical embedding of GF(433^1) into GF(433^3). -/
noncomputable def embed_433_1_3 :
    Hex.GFq 433 1 Hex.Conway.supportedEntry_433_1 →+*
      Hex.GFq 433 3 Hex.Conway.supportedEntry_433_3 :=
  conwayEmbed 433 1 3 _ _ Hex.Conway.compat_433_1_3

/-- The canonical embedding of GF(433^1) into GF(433^4). -/
noncomputable def embed_433_1_4 :
    Hex.GFq 433 1 Hex.Conway.supportedEntry_433_1 →+*
      Hex.GFq 433 4 Hex.Conway.supportedEntry_433_4 :=
  conwayEmbed 433 1 4 _ _ Hex.Conway.compat_433_1_4

/-- The canonical embedding of GF(433^2) into GF(433^4). -/
noncomputable def embed_433_2_4 :
    Hex.GFq 433 2 Hex.Conway.supportedEntry_433_2 →+*
      Hex.GFq 433 4 Hex.Conway.supportedEntry_433_4 :=
  conwayEmbed 433 2 4 _ _ Hex.Conway.compat_433_2_4

/-- The canonical embedding of GF(439^1) into GF(439^2). -/
noncomputable def embed_439_1_2 :
    Hex.GFq 439 1 Hex.Conway.supportedEntry_439_1 →+*
      Hex.GFq 439 2 Hex.Conway.supportedEntry_439_2 :=
  conwayEmbed 439 1 2 _ _ Hex.Conway.compat_439_1_2

/-- The canonical embedding of GF(439^1) into GF(439^3). -/
noncomputable def embed_439_1_3 :
    Hex.GFq 439 1 Hex.Conway.supportedEntry_439_1 →+*
      Hex.GFq 439 3 Hex.Conway.supportedEntry_439_3 :=
  conwayEmbed 439 1 3 _ _ Hex.Conway.compat_439_1_3

/-- The canonical embedding of GF(439^1) into GF(439^4). -/
noncomputable def embed_439_1_4 :
    Hex.GFq 439 1 Hex.Conway.supportedEntry_439_1 →+*
      Hex.GFq 439 4 Hex.Conway.supportedEntry_439_4 :=
  conwayEmbed 439 1 4 _ _ Hex.Conway.compat_439_1_4

/-- The canonical embedding of GF(439^2) into GF(439^4). -/
noncomputable def embed_439_2_4 :
    Hex.GFq 439 2 Hex.Conway.supportedEntry_439_2 →+*
      Hex.GFq 439 4 Hex.Conway.supportedEntry_439_4 :=
  conwayEmbed 439 2 4 _ _ Hex.Conway.compat_439_2_4

/-- The canonical embedding of GF(443^1) into GF(443^2). -/
noncomputable def embed_443_1_2 :
    Hex.GFq 443 1 Hex.Conway.supportedEntry_443_1 →+*
      Hex.GFq 443 2 Hex.Conway.supportedEntry_443_2 :=
  conwayEmbed 443 1 2 _ _ Hex.Conway.compat_443_1_2

/-- The canonical embedding of GF(443^1) into GF(443^3). -/
noncomputable def embed_443_1_3 :
    Hex.GFq 443 1 Hex.Conway.supportedEntry_443_1 →+*
      Hex.GFq 443 3 Hex.Conway.supportedEntry_443_3 :=
  conwayEmbed 443 1 3 _ _ Hex.Conway.compat_443_1_3

/-- The canonical embedding of GF(443^1) into GF(443^4). -/
noncomputable def embed_443_1_4 :
    Hex.GFq 443 1 Hex.Conway.supportedEntry_443_1 →+*
      Hex.GFq 443 4 Hex.Conway.supportedEntry_443_4 :=
  conwayEmbed 443 1 4 _ _ Hex.Conway.compat_443_1_4

/-- The canonical embedding of GF(443^2) into GF(443^4). -/
noncomputable def embed_443_2_4 :
    Hex.GFq 443 2 Hex.Conway.supportedEntry_443_2 →+*
      Hex.GFq 443 4 Hex.Conway.supportedEntry_443_4 :=
  conwayEmbed 443 2 4 _ _ Hex.Conway.compat_443_2_4

/-- The canonical embedding of GF(449^1) into GF(449^2). -/
noncomputable def embed_449_1_2 :
    Hex.GFq 449 1 Hex.Conway.supportedEntry_449_1 →+*
      Hex.GFq 449 2 Hex.Conway.supportedEntry_449_2 :=
  conwayEmbed 449 1 2 _ _ Hex.Conway.compat_449_1_2

/-- The canonical embedding of GF(449^1) into GF(449^3). -/
noncomputable def embed_449_1_3 :
    Hex.GFq 449 1 Hex.Conway.supportedEntry_449_1 →+*
      Hex.GFq 449 3 Hex.Conway.supportedEntry_449_3 :=
  conwayEmbed 449 1 3 _ _ Hex.Conway.compat_449_1_3

/-- The canonical embedding of GF(449^1) into GF(449^4). -/
noncomputable def embed_449_1_4 :
    Hex.GFq 449 1 Hex.Conway.supportedEntry_449_1 →+*
      Hex.GFq 449 4 Hex.Conway.supportedEntry_449_4 :=
  conwayEmbed 449 1 4 _ _ Hex.Conway.compat_449_1_4

/-- The canonical embedding of GF(449^2) into GF(449^4). -/
noncomputable def embed_449_2_4 :
    Hex.GFq 449 2 Hex.Conway.supportedEntry_449_2 →+*
      Hex.GFq 449 4 Hex.Conway.supportedEntry_449_4 :=
  conwayEmbed 449 2 4 _ _ Hex.Conway.compat_449_2_4

/-- The canonical embedding of GF(457^1) into GF(457^2). -/
noncomputable def embed_457_1_2 :
    Hex.GFq 457 1 Hex.Conway.supportedEntry_457_1 →+*
      Hex.GFq 457 2 Hex.Conway.supportedEntry_457_2 :=
  conwayEmbed 457 1 2 _ _ Hex.Conway.compat_457_1_2

/-- The canonical embedding of GF(457^1) into GF(457^3). -/
noncomputable def embed_457_1_3 :
    Hex.GFq 457 1 Hex.Conway.supportedEntry_457_1 →+*
      Hex.GFq 457 3 Hex.Conway.supportedEntry_457_3 :=
  conwayEmbed 457 1 3 _ _ Hex.Conway.compat_457_1_3

/-- The canonical embedding of GF(457^1) into GF(457^4). -/
noncomputable def embed_457_1_4 :
    Hex.GFq 457 1 Hex.Conway.supportedEntry_457_1 →+*
      Hex.GFq 457 4 Hex.Conway.supportedEntry_457_4 :=
  conwayEmbed 457 1 4 _ _ Hex.Conway.compat_457_1_4

/-- The canonical embedding of GF(457^2) into GF(457^4). -/
noncomputable def embed_457_2_4 :
    Hex.GFq 457 2 Hex.Conway.supportedEntry_457_2 →+*
      Hex.GFq 457 4 Hex.Conway.supportedEntry_457_4 :=
  conwayEmbed 457 2 4 _ _ Hex.Conway.compat_457_2_4

/-- The canonical embedding of GF(461^1) into GF(461^2). -/
noncomputable def embed_461_1_2 :
    Hex.GFq 461 1 Hex.Conway.supportedEntry_461_1 →+*
      Hex.GFq 461 2 Hex.Conway.supportedEntry_461_2 :=
  conwayEmbed 461 1 2 _ _ Hex.Conway.compat_461_1_2

/-- The canonical embedding of GF(461^1) into GF(461^3). -/
noncomputable def embed_461_1_3 :
    Hex.GFq 461 1 Hex.Conway.supportedEntry_461_1 →+*
      Hex.GFq 461 3 Hex.Conway.supportedEntry_461_3 :=
  conwayEmbed 461 1 3 _ _ Hex.Conway.compat_461_1_3

/-- The canonical embedding of GF(461^1) into GF(461^4). -/
noncomputable def embed_461_1_4 :
    Hex.GFq 461 1 Hex.Conway.supportedEntry_461_1 →+*
      Hex.GFq 461 4 Hex.Conway.supportedEntry_461_4 :=
  conwayEmbed 461 1 4 _ _ Hex.Conway.compat_461_1_4

/-- The canonical embedding of GF(461^2) into GF(461^4). -/
noncomputable def embed_461_2_4 :
    Hex.GFq 461 2 Hex.Conway.supportedEntry_461_2 →+*
      Hex.GFq 461 4 Hex.Conway.supportedEntry_461_4 :=
  conwayEmbed 461 2 4 _ _ Hex.Conway.compat_461_2_4

/-- The canonical embedding of GF(463^1) into GF(463^2). -/
noncomputable def embed_463_1_2 :
    Hex.GFq 463 1 Hex.Conway.supportedEntry_463_1 →+*
      Hex.GFq 463 2 Hex.Conway.supportedEntry_463_2 :=
  conwayEmbed 463 1 2 _ _ Hex.Conway.compat_463_1_2

/-- The canonical embedding of GF(463^1) into GF(463^3). -/
noncomputable def embed_463_1_3 :
    Hex.GFq 463 1 Hex.Conway.supportedEntry_463_1 →+*
      Hex.GFq 463 3 Hex.Conway.supportedEntry_463_3 :=
  conwayEmbed 463 1 3 _ _ Hex.Conway.compat_463_1_3

/-- The canonical embedding of GF(463^1) into GF(463^4). -/
noncomputable def embed_463_1_4 :
    Hex.GFq 463 1 Hex.Conway.supportedEntry_463_1 →+*
      Hex.GFq 463 4 Hex.Conway.supportedEntry_463_4 :=
  conwayEmbed 463 1 4 _ _ Hex.Conway.compat_463_1_4

/-- The canonical embedding of GF(463^2) into GF(463^4). -/
noncomputable def embed_463_2_4 :
    Hex.GFq 463 2 Hex.Conway.supportedEntry_463_2 →+*
      Hex.GFq 463 4 Hex.Conway.supportedEntry_463_4 :=
  conwayEmbed 463 2 4 _ _ Hex.Conway.compat_463_2_4

/-- The canonical embedding of GF(467^1) into GF(467^2). -/
noncomputable def embed_467_1_2 :
    Hex.GFq 467 1 Hex.Conway.supportedEntry_467_1 →+*
      Hex.GFq 467 2 Hex.Conway.supportedEntry_467_2 :=
  conwayEmbed 467 1 2 _ _ Hex.Conway.compat_467_1_2

/-- The canonical embedding of GF(467^1) into GF(467^3). -/
noncomputable def embed_467_1_3 :
    Hex.GFq 467 1 Hex.Conway.supportedEntry_467_1 →+*
      Hex.GFq 467 3 Hex.Conway.supportedEntry_467_3 :=
  conwayEmbed 467 1 3 _ _ Hex.Conway.compat_467_1_3

/-- The canonical embedding of GF(467^1) into GF(467^4). -/
noncomputable def embed_467_1_4 :
    Hex.GFq 467 1 Hex.Conway.supportedEntry_467_1 →+*
      Hex.GFq 467 4 Hex.Conway.supportedEntry_467_4 :=
  conwayEmbed 467 1 4 _ _ Hex.Conway.compat_467_1_4

/-- The canonical embedding of GF(467^2) into GF(467^4). -/
noncomputable def embed_467_2_4 :
    Hex.GFq 467 2 Hex.Conway.supportedEntry_467_2 →+*
      Hex.GFq 467 4 Hex.Conway.supportedEntry_467_4 :=
  conwayEmbed 467 2 4 _ _ Hex.Conway.compat_467_2_4

/-- The canonical embedding of GF(479^1) into GF(479^2). -/
noncomputable def embed_479_1_2 :
    Hex.GFq 479 1 Hex.Conway.supportedEntry_479_1 →+*
      Hex.GFq 479 2 Hex.Conway.supportedEntry_479_2 :=
  conwayEmbed 479 1 2 _ _ Hex.Conway.compat_479_1_2

/-- The canonical embedding of GF(479^1) into GF(479^3). -/
noncomputable def embed_479_1_3 :
    Hex.GFq 479 1 Hex.Conway.supportedEntry_479_1 →+*
      Hex.GFq 479 3 Hex.Conway.supportedEntry_479_3 :=
  conwayEmbed 479 1 3 _ _ Hex.Conway.compat_479_1_3

/-- The canonical embedding of GF(479^1) into GF(479^4). -/
noncomputable def embed_479_1_4 :
    Hex.GFq 479 1 Hex.Conway.supportedEntry_479_1 →+*
      Hex.GFq 479 4 Hex.Conway.supportedEntry_479_4 :=
  conwayEmbed 479 1 4 _ _ Hex.Conway.compat_479_1_4

/-- The canonical embedding of GF(479^2) into GF(479^4). -/
noncomputable def embed_479_2_4 :
    Hex.GFq 479 2 Hex.Conway.supportedEntry_479_2 →+*
      Hex.GFq 479 4 Hex.Conway.supportedEntry_479_4 :=
  conwayEmbed 479 2 4 _ _ Hex.Conway.compat_479_2_4

/-- The canonical embedding of GF(487^1) into GF(487^2). -/
noncomputable def embed_487_1_2 :
    Hex.GFq 487 1 Hex.Conway.supportedEntry_487_1 →+*
      Hex.GFq 487 2 Hex.Conway.supportedEntry_487_2 :=
  conwayEmbed 487 1 2 _ _ Hex.Conway.compat_487_1_2

/-- The canonical embedding of GF(487^1) into GF(487^3). -/
noncomputable def embed_487_1_3 :
    Hex.GFq 487 1 Hex.Conway.supportedEntry_487_1 →+*
      Hex.GFq 487 3 Hex.Conway.supportedEntry_487_3 :=
  conwayEmbed 487 1 3 _ _ Hex.Conway.compat_487_1_3

/-- The canonical embedding of GF(487^1) into GF(487^4). -/
noncomputable def embed_487_1_4 :
    Hex.GFq 487 1 Hex.Conway.supportedEntry_487_1 →+*
      Hex.GFq 487 4 Hex.Conway.supportedEntry_487_4 :=
  conwayEmbed 487 1 4 _ _ Hex.Conway.compat_487_1_4

/-- The canonical embedding of GF(487^2) into GF(487^4). -/
noncomputable def embed_487_2_4 :
    Hex.GFq 487 2 Hex.Conway.supportedEntry_487_2 →+*
      Hex.GFq 487 4 Hex.Conway.supportedEntry_487_4 :=
  conwayEmbed 487 2 4 _ _ Hex.Conway.compat_487_2_4

/-- The canonical embedding of GF(491^1) into GF(491^2). -/
noncomputable def embed_491_1_2 :
    Hex.GFq 491 1 Hex.Conway.supportedEntry_491_1 →+*
      Hex.GFq 491 2 Hex.Conway.supportedEntry_491_2 :=
  conwayEmbed 491 1 2 _ _ Hex.Conway.compat_491_1_2

/-- The canonical embedding of GF(491^1) into GF(491^3). -/
noncomputable def embed_491_1_3 :
    Hex.GFq 491 1 Hex.Conway.supportedEntry_491_1 →+*
      Hex.GFq 491 3 Hex.Conway.supportedEntry_491_3 :=
  conwayEmbed 491 1 3 _ _ Hex.Conway.compat_491_1_3

/-- The canonical embedding of GF(491^1) into GF(491^4). -/
noncomputable def embed_491_1_4 :
    Hex.GFq 491 1 Hex.Conway.supportedEntry_491_1 →+*
      Hex.GFq 491 4 Hex.Conway.supportedEntry_491_4 :=
  conwayEmbed 491 1 4 _ _ Hex.Conway.compat_491_1_4

/-- The canonical embedding of GF(491^2) into GF(491^4). -/
noncomputable def embed_491_2_4 :
    Hex.GFq 491 2 Hex.Conway.supportedEntry_491_2 →+*
      Hex.GFq 491 4 Hex.Conway.supportedEntry_491_4 :=
  conwayEmbed 491 2 4 _ _ Hex.Conway.compat_491_2_4

/-- The canonical embedding of GF(499^1) into GF(499^2). -/
noncomputable def embed_499_1_2 :
    Hex.GFq 499 1 Hex.Conway.supportedEntry_499_1 →+*
      Hex.GFq 499 2 Hex.Conway.supportedEntry_499_2 :=
  conwayEmbed 499 1 2 _ _ Hex.Conway.compat_499_1_2

/-- The canonical embedding of GF(499^1) into GF(499^3). -/
noncomputable def embed_499_1_3 :
    Hex.GFq 499 1 Hex.Conway.supportedEntry_499_1 →+*
      Hex.GFq 499 3 Hex.Conway.supportedEntry_499_3 :=
  conwayEmbed 499 1 3 _ _ Hex.Conway.compat_499_1_3

/-- The canonical embedding of GF(499^1) into GF(499^4). -/
noncomputable def embed_499_1_4 :
    Hex.GFq 499 1 Hex.Conway.supportedEntry_499_1 →+*
      Hex.GFq 499 4 Hex.Conway.supportedEntry_499_4 :=
  conwayEmbed 499 1 4 _ _ Hex.Conway.compat_499_1_4

/-- The canonical embedding of GF(499^2) into GF(499^4). -/
noncomputable def embed_499_2_4 :
    Hex.GFq 499 2 Hex.Conway.supportedEntry_499_2 →+*
      Hex.GFq 499 4 Hex.Conway.supportedEntry_499_4 :=
  conwayEmbed 499 2 4 _ _ Hex.Conway.compat_499_2_4

/-- The canonical embedding of GF(503^1) into GF(503^2). -/
noncomputable def embed_503_1_2 :
    Hex.GFq 503 1 Hex.Conway.supportedEntry_503_1 →+*
      Hex.GFq 503 2 Hex.Conway.supportedEntry_503_2 :=
  conwayEmbed 503 1 2 _ _ Hex.Conway.compat_503_1_2

/-- The canonical embedding of GF(503^1) into GF(503^3). -/
noncomputable def embed_503_1_3 :
    Hex.GFq 503 1 Hex.Conway.supportedEntry_503_1 →+*
      Hex.GFq 503 3 Hex.Conway.supportedEntry_503_3 :=
  conwayEmbed 503 1 3 _ _ Hex.Conway.compat_503_1_3

/-- The canonical embedding of GF(509^1) into GF(509^2). -/
noncomputable def embed_509_1_2 :
    Hex.GFq 509 1 Hex.Conway.supportedEntry_509_1 →+*
      Hex.GFq 509 2 Hex.Conway.supportedEntry_509_2 :=
  conwayEmbed 509 1 2 _ _ Hex.Conway.compat_509_1_2

/-- The canonical embedding of GF(509^1) into GF(509^3). -/
noncomputable def embed_509_1_3 :
    Hex.GFq 509 1 Hex.Conway.supportedEntry_509_1 →+*
      Hex.GFq 509 3 Hex.Conway.supportedEntry_509_3 :=
  conwayEmbed 509 1 3 _ _ Hex.Conway.compat_509_1_3

/-- The canonical embedding of GF(521^1) into GF(521^2). -/
noncomputable def embed_521_1_2 :
    Hex.GFq 521 1 Hex.Conway.supportedEntry_521_1 →+*
      Hex.GFq 521 2 Hex.Conway.supportedEntry_521_2 :=
  conwayEmbed 521 1 2 _ _ Hex.Conway.compat_521_1_2

/-- The canonical embedding of GF(521^1) into GF(521^3). -/
noncomputable def embed_521_1_3 :
    Hex.GFq 521 1 Hex.Conway.supportedEntry_521_1 →+*
      Hex.GFq 521 3 Hex.Conway.supportedEntry_521_3 :=
  conwayEmbed 521 1 3 _ _ Hex.Conway.compat_521_1_3

/-- The canonical embedding of GF(523^1) into GF(523^2). -/
noncomputable def embed_523_1_2 :
    Hex.GFq 523 1 Hex.Conway.supportedEntry_523_1 →+*
      Hex.GFq 523 2 Hex.Conway.supportedEntry_523_2 :=
  conwayEmbed 523 1 2 _ _ Hex.Conway.compat_523_1_2

/-- The canonical embedding of GF(523^1) into GF(523^3). -/
noncomputable def embed_523_1_3 :
    Hex.GFq 523 1 Hex.Conway.supportedEntry_523_1 →+*
      Hex.GFq 523 3 Hex.Conway.supportedEntry_523_3 :=
  conwayEmbed 523 1 3 _ _ Hex.Conway.compat_523_1_3

/-- The canonical embedding of GF(541^1) into GF(541^2). -/
noncomputable def embed_541_1_2 :
    Hex.GFq 541 1 Hex.Conway.supportedEntry_541_1 →+*
      Hex.GFq 541 2 Hex.Conway.supportedEntry_541_2 :=
  conwayEmbed 541 1 2 _ _ Hex.Conway.compat_541_1_2

/-- The canonical embedding of GF(541^1) into GF(541^3). -/
noncomputable def embed_541_1_3 :
    Hex.GFq 541 1 Hex.Conway.supportedEntry_541_1 →+*
      Hex.GFq 541 3 Hex.Conway.supportedEntry_541_3 :=
  conwayEmbed 541 1 3 _ _ Hex.Conway.compat_541_1_3

/-- The canonical embedding of GF(547^1) into GF(547^2). -/
noncomputable def embed_547_1_2 :
    Hex.GFq 547 1 Hex.Conway.supportedEntry_547_1 →+*
      Hex.GFq 547 2 Hex.Conway.supportedEntry_547_2 :=
  conwayEmbed 547 1 2 _ _ Hex.Conway.compat_547_1_2

/-- The canonical embedding of GF(547^1) into GF(547^3). -/
noncomputable def embed_547_1_3 :
    Hex.GFq 547 1 Hex.Conway.supportedEntry_547_1 →+*
      Hex.GFq 547 3 Hex.Conway.supportedEntry_547_3 :=
  conwayEmbed 547 1 3 _ _ Hex.Conway.compat_547_1_3

/-- The canonical embedding of GF(557^1) into GF(557^2). -/
noncomputable def embed_557_1_2 :
    Hex.GFq 557 1 Hex.Conway.supportedEntry_557_1 →+*
      Hex.GFq 557 2 Hex.Conway.supportedEntry_557_2 :=
  conwayEmbed 557 1 2 _ _ Hex.Conway.compat_557_1_2

/-- The canonical embedding of GF(557^1) into GF(557^3). -/
noncomputable def embed_557_1_3 :
    Hex.GFq 557 1 Hex.Conway.supportedEntry_557_1 →+*
      Hex.GFq 557 3 Hex.Conway.supportedEntry_557_3 :=
  conwayEmbed 557 1 3 _ _ Hex.Conway.compat_557_1_3

/-- The canonical embedding of GF(563^1) into GF(563^2). -/
noncomputable def embed_563_1_2 :
    Hex.GFq 563 1 Hex.Conway.supportedEntry_563_1 →+*
      Hex.GFq 563 2 Hex.Conway.supportedEntry_563_2 :=
  conwayEmbed 563 1 2 _ _ Hex.Conway.compat_563_1_2

/-- The canonical embedding of GF(563^1) into GF(563^3). -/
noncomputable def embed_563_1_3 :
    Hex.GFq 563 1 Hex.Conway.supportedEntry_563_1 →+*
      Hex.GFq 563 3 Hex.Conway.supportedEntry_563_3 :=
  conwayEmbed 563 1 3 _ _ Hex.Conway.compat_563_1_3

/-- The canonical embedding of GF(569^1) into GF(569^2). -/
noncomputable def embed_569_1_2 :
    Hex.GFq 569 1 Hex.Conway.supportedEntry_569_1 →+*
      Hex.GFq 569 2 Hex.Conway.supportedEntry_569_2 :=
  conwayEmbed 569 1 2 _ _ Hex.Conway.compat_569_1_2

/-- The canonical embedding of GF(569^1) into GF(569^3). -/
noncomputable def embed_569_1_3 :
    Hex.GFq 569 1 Hex.Conway.supportedEntry_569_1 →+*
      Hex.GFq 569 3 Hex.Conway.supportedEntry_569_3 :=
  conwayEmbed 569 1 3 _ _ Hex.Conway.compat_569_1_3

/-- The canonical embedding of GF(571^1) into GF(571^2). -/
noncomputable def embed_571_1_2 :
    Hex.GFq 571 1 Hex.Conway.supportedEntry_571_1 →+*
      Hex.GFq 571 2 Hex.Conway.supportedEntry_571_2 :=
  conwayEmbed 571 1 2 _ _ Hex.Conway.compat_571_1_2

/-- The canonical embedding of GF(571^1) into GF(571^3). -/
noncomputable def embed_571_1_3 :
    Hex.GFq 571 1 Hex.Conway.supportedEntry_571_1 →+*
      Hex.GFq 571 3 Hex.Conway.supportedEntry_571_3 :=
  conwayEmbed 571 1 3 _ _ Hex.Conway.compat_571_1_3

/-- The canonical embedding of GF(577^1) into GF(577^2). -/
noncomputable def embed_577_1_2 :
    Hex.GFq 577 1 Hex.Conway.supportedEntry_577_1 →+*
      Hex.GFq 577 2 Hex.Conway.supportedEntry_577_2 :=
  conwayEmbed 577 1 2 _ _ Hex.Conway.compat_577_1_2

/-- The canonical embedding of GF(577^1) into GF(577^3). -/
noncomputable def embed_577_1_3 :
    Hex.GFq 577 1 Hex.Conway.supportedEntry_577_1 →+*
      Hex.GFq 577 3 Hex.Conway.supportedEntry_577_3 :=
  conwayEmbed 577 1 3 _ _ Hex.Conway.compat_577_1_3

/-- The canonical embedding of GF(587^1) into GF(587^2). -/
noncomputable def embed_587_1_2 :
    Hex.GFq 587 1 Hex.Conway.supportedEntry_587_1 →+*
      Hex.GFq 587 2 Hex.Conway.supportedEntry_587_2 :=
  conwayEmbed 587 1 2 _ _ Hex.Conway.compat_587_1_2

/-- The canonical embedding of GF(587^1) into GF(587^3). -/
noncomputable def embed_587_1_3 :
    Hex.GFq 587 1 Hex.Conway.supportedEntry_587_1 →+*
      Hex.GFq 587 3 Hex.Conway.supportedEntry_587_3 :=
  conwayEmbed 587 1 3 _ _ Hex.Conway.compat_587_1_3

/-- The canonical embedding of GF(593^1) into GF(593^2). -/
noncomputable def embed_593_1_2 :
    Hex.GFq 593 1 Hex.Conway.supportedEntry_593_1 →+*
      Hex.GFq 593 2 Hex.Conway.supportedEntry_593_2 :=
  conwayEmbed 593 1 2 _ _ Hex.Conway.compat_593_1_2

/-- The canonical embedding of GF(593^1) into GF(593^3). -/
noncomputable def embed_593_1_3 :
    Hex.GFq 593 1 Hex.Conway.supportedEntry_593_1 →+*
      Hex.GFq 593 3 Hex.Conway.supportedEntry_593_3 :=
  conwayEmbed 593 1 3 _ _ Hex.Conway.compat_593_1_3

/-- The canonical embedding of GF(599^1) into GF(599^2). -/
noncomputable def embed_599_1_2 :
    Hex.GFq 599 1 Hex.Conway.supportedEntry_599_1 →+*
      Hex.GFq 599 2 Hex.Conway.supportedEntry_599_2 :=
  conwayEmbed 599 1 2 _ _ Hex.Conway.compat_599_1_2

/-- The canonical embedding of GF(599^1) into GF(599^3). -/
noncomputable def embed_599_1_3 :
    Hex.GFq 599 1 Hex.Conway.supportedEntry_599_1 →+*
      Hex.GFq 599 3 Hex.Conway.supportedEntry_599_3 :=
  conwayEmbed 599 1 3 _ _ Hex.Conway.compat_599_1_3

/-- The canonical embedding of GF(601^1) into GF(601^2). -/
noncomputable def embed_601_1_2 :
    Hex.GFq 601 1 Hex.Conway.supportedEntry_601_1 →+*
      Hex.GFq 601 2 Hex.Conway.supportedEntry_601_2 :=
  conwayEmbed 601 1 2 _ _ Hex.Conway.compat_601_1_2

/-- The canonical embedding of GF(601^1) into GF(601^3). -/
noncomputable def embed_601_1_3 :
    Hex.GFq 601 1 Hex.Conway.supportedEntry_601_1 →+*
      Hex.GFq 601 3 Hex.Conway.supportedEntry_601_3 :=
  conwayEmbed 601 1 3 _ _ Hex.Conway.compat_601_1_3

/-- The canonical embedding of GF(607^1) into GF(607^2). -/
noncomputable def embed_607_1_2 :
    Hex.GFq 607 1 Hex.Conway.supportedEntry_607_1 →+*
      Hex.GFq 607 2 Hex.Conway.supportedEntry_607_2 :=
  conwayEmbed 607 1 2 _ _ Hex.Conway.compat_607_1_2

/-- The canonical embedding of GF(607^1) into GF(607^3). -/
noncomputable def embed_607_1_3 :
    Hex.GFq 607 1 Hex.Conway.supportedEntry_607_1 →+*
      Hex.GFq 607 3 Hex.Conway.supportedEntry_607_3 :=
  conwayEmbed 607 1 3 _ _ Hex.Conway.compat_607_1_3

/-- The canonical embedding of GF(613^1) into GF(613^2). -/
noncomputable def embed_613_1_2 :
    Hex.GFq 613 1 Hex.Conway.supportedEntry_613_1 →+*
      Hex.GFq 613 2 Hex.Conway.supportedEntry_613_2 :=
  conwayEmbed 613 1 2 _ _ Hex.Conway.compat_613_1_2

/-- The canonical embedding of GF(613^1) into GF(613^3). -/
noncomputable def embed_613_1_3 :
    Hex.GFq 613 1 Hex.Conway.supportedEntry_613_1 →+*
      Hex.GFq 613 3 Hex.Conway.supportedEntry_613_3 :=
  conwayEmbed 613 1 3 _ _ Hex.Conway.compat_613_1_3

/-- The canonical embedding of GF(617^1) into GF(617^2). -/
noncomputable def embed_617_1_2 :
    Hex.GFq 617 1 Hex.Conway.supportedEntry_617_1 →+*
      Hex.GFq 617 2 Hex.Conway.supportedEntry_617_2 :=
  conwayEmbed 617 1 2 _ _ Hex.Conway.compat_617_1_2

/-- The canonical embedding of GF(617^1) into GF(617^3). -/
noncomputable def embed_617_1_3 :
    Hex.GFq 617 1 Hex.Conway.supportedEntry_617_1 →+*
      Hex.GFq 617 3 Hex.Conway.supportedEntry_617_3 :=
  conwayEmbed 617 1 3 _ _ Hex.Conway.compat_617_1_3

/-- The canonical embedding of GF(619^1) into GF(619^2). -/
noncomputable def embed_619_1_2 :
    Hex.GFq 619 1 Hex.Conway.supportedEntry_619_1 →+*
      Hex.GFq 619 2 Hex.Conway.supportedEntry_619_2 :=
  conwayEmbed 619 1 2 _ _ Hex.Conway.compat_619_1_2

/-- The canonical embedding of GF(619^1) into GF(619^3). -/
noncomputable def embed_619_1_3 :
    Hex.GFq 619 1 Hex.Conway.supportedEntry_619_1 →+*
      Hex.GFq 619 3 Hex.Conway.supportedEntry_619_3 :=
  conwayEmbed 619 1 3 _ _ Hex.Conway.compat_619_1_3

/-- The canonical embedding of GF(631^1) into GF(631^2). -/
noncomputable def embed_631_1_2 :
    Hex.GFq 631 1 Hex.Conway.supportedEntry_631_1 →+*
      Hex.GFq 631 2 Hex.Conway.supportedEntry_631_2 :=
  conwayEmbed 631 1 2 _ _ Hex.Conway.compat_631_1_2

/-- The canonical embedding of GF(631^1) into GF(631^3). -/
noncomputable def embed_631_1_3 :
    Hex.GFq 631 1 Hex.Conway.supportedEntry_631_1 →+*
      Hex.GFq 631 3 Hex.Conway.supportedEntry_631_3 :=
  conwayEmbed 631 1 3 _ _ Hex.Conway.compat_631_1_3

/-- The canonical embedding of GF(641^1) into GF(641^2). -/
noncomputable def embed_641_1_2 :
    Hex.GFq 641 1 Hex.Conway.supportedEntry_641_1 →+*
      Hex.GFq 641 2 Hex.Conway.supportedEntry_641_2 :=
  conwayEmbed 641 1 2 _ _ Hex.Conway.compat_641_1_2

/-- The canonical embedding of GF(641^1) into GF(641^3). -/
noncomputable def embed_641_1_3 :
    Hex.GFq 641 1 Hex.Conway.supportedEntry_641_1 →+*
      Hex.GFq 641 3 Hex.Conway.supportedEntry_641_3 :=
  conwayEmbed 641 1 3 _ _ Hex.Conway.compat_641_1_3

/-- The canonical embedding of GF(643^1) into GF(643^2). -/
noncomputable def embed_643_1_2 :
    Hex.GFq 643 1 Hex.Conway.supportedEntry_643_1 →+*
      Hex.GFq 643 2 Hex.Conway.supportedEntry_643_2 :=
  conwayEmbed 643 1 2 _ _ Hex.Conway.compat_643_1_2

/-- The canonical embedding of GF(643^1) into GF(643^3). -/
noncomputable def embed_643_1_3 :
    Hex.GFq 643 1 Hex.Conway.supportedEntry_643_1 →+*
      Hex.GFq 643 3 Hex.Conway.supportedEntry_643_3 :=
  conwayEmbed 643 1 3 _ _ Hex.Conway.compat_643_1_3

/-- The canonical embedding of GF(647^1) into GF(647^2). -/
noncomputable def embed_647_1_2 :
    Hex.GFq 647 1 Hex.Conway.supportedEntry_647_1 →+*
      Hex.GFq 647 2 Hex.Conway.supportedEntry_647_2 :=
  conwayEmbed 647 1 2 _ _ Hex.Conway.compat_647_1_2

/-- The canonical embedding of GF(647^1) into GF(647^3). -/
noncomputable def embed_647_1_3 :
    Hex.GFq 647 1 Hex.Conway.supportedEntry_647_1 →+*
      Hex.GFq 647 3 Hex.Conway.supportedEntry_647_3 :=
  conwayEmbed 647 1 3 _ _ Hex.Conway.compat_647_1_3

/-- The canonical embedding of GF(653^1) into GF(653^2). -/
noncomputable def embed_653_1_2 :
    Hex.GFq 653 1 Hex.Conway.supportedEntry_653_1 →+*
      Hex.GFq 653 2 Hex.Conway.supportedEntry_653_2 :=
  conwayEmbed 653 1 2 _ _ Hex.Conway.compat_653_1_2

/-- The canonical embedding of GF(653^1) into GF(653^3). -/
noncomputable def embed_653_1_3 :
    Hex.GFq 653 1 Hex.Conway.supportedEntry_653_1 →+*
      Hex.GFq 653 3 Hex.Conway.supportedEntry_653_3 :=
  conwayEmbed 653 1 3 _ _ Hex.Conway.compat_653_1_3

/-- The canonical embedding of GF(659^1) into GF(659^2). -/
noncomputable def embed_659_1_2 :
    Hex.GFq 659 1 Hex.Conway.supportedEntry_659_1 →+*
      Hex.GFq 659 2 Hex.Conway.supportedEntry_659_2 :=
  conwayEmbed 659 1 2 _ _ Hex.Conway.compat_659_1_2

/-- The canonical embedding of GF(659^1) into GF(659^3). -/
noncomputable def embed_659_1_3 :
    Hex.GFq 659 1 Hex.Conway.supportedEntry_659_1 →+*
      Hex.GFq 659 3 Hex.Conway.supportedEntry_659_3 :=
  conwayEmbed 659 1 3 _ _ Hex.Conway.compat_659_1_3

/-- The canonical embedding of GF(661^1) into GF(661^2). -/
noncomputable def embed_661_1_2 :
    Hex.GFq 661 1 Hex.Conway.supportedEntry_661_1 →+*
      Hex.GFq 661 2 Hex.Conway.supportedEntry_661_2 :=
  conwayEmbed 661 1 2 _ _ Hex.Conway.compat_661_1_2

/-- The canonical embedding of GF(661^1) into GF(661^3). -/
noncomputable def embed_661_1_3 :
    Hex.GFq 661 1 Hex.Conway.supportedEntry_661_1 →+*
      Hex.GFq 661 3 Hex.Conway.supportedEntry_661_3 :=
  conwayEmbed 661 1 3 _ _ Hex.Conway.compat_661_1_3

/-- The canonical embedding of GF(673^1) into GF(673^2). -/
noncomputable def embed_673_1_2 :
    Hex.GFq 673 1 Hex.Conway.supportedEntry_673_1 →+*
      Hex.GFq 673 2 Hex.Conway.supportedEntry_673_2 :=
  conwayEmbed 673 1 2 _ _ Hex.Conway.compat_673_1_2

/-- The canonical embedding of GF(673^1) into GF(673^3). -/
noncomputable def embed_673_1_3 :
    Hex.GFq 673 1 Hex.Conway.supportedEntry_673_1 →+*
      Hex.GFq 673 3 Hex.Conway.supportedEntry_673_3 :=
  conwayEmbed 673 1 3 _ _ Hex.Conway.compat_673_1_3

/-- The canonical embedding of GF(677^1) into GF(677^2). -/
noncomputable def embed_677_1_2 :
    Hex.GFq 677 1 Hex.Conway.supportedEntry_677_1 →+*
      Hex.GFq 677 2 Hex.Conway.supportedEntry_677_2 :=
  conwayEmbed 677 1 2 _ _ Hex.Conway.compat_677_1_2

/-- The canonical embedding of GF(677^1) into GF(677^3). -/
noncomputable def embed_677_1_3 :
    Hex.GFq 677 1 Hex.Conway.supportedEntry_677_1 →+*
      Hex.GFq 677 3 Hex.Conway.supportedEntry_677_3 :=
  conwayEmbed 677 1 3 _ _ Hex.Conway.compat_677_1_3

/-- The canonical embedding of GF(683^1) into GF(683^2). -/
noncomputable def embed_683_1_2 :
    Hex.GFq 683 1 Hex.Conway.supportedEntry_683_1 →+*
      Hex.GFq 683 2 Hex.Conway.supportedEntry_683_2 :=
  conwayEmbed 683 1 2 _ _ Hex.Conway.compat_683_1_2

/-- The canonical embedding of GF(683^1) into GF(683^3). -/
noncomputable def embed_683_1_3 :
    Hex.GFq 683 1 Hex.Conway.supportedEntry_683_1 →+*
      Hex.GFq 683 3 Hex.Conway.supportedEntry_683_3 :=
  conwayEmbed 683 1 3 _ _ Hex.Conway.compat_683_1_3

/-- The canonical embedding of GF(691^1) into GF(691^2). -/
noncomputable def embed_691_1_2 :
    Hex.GFq 691 1 Hex.Conway.supportedEntry_691_1 →+*
      Hex.GFq 691 2 Hex.Conway.supportedEntry_691_2 :=
  conwayEmbed 691 1 2 _ _ Hex.Conway.compat_691_1_2

/-- The canonical embedding of GF(691^1) into GF(691^3). -/
noncomputable def embed_691_1_3 :
    Hex.GFq 691 1 Hex.Conway.supportedEntry_691_1 →+*
      Hex.GFq 691 3 Hex.Conway.supportedEntry_691_3 :=
  conwayEmbed 691 1 3 _ _ Hex.Conway.compat_691_1_3

/-- The canonical embedding of GF(701^1) into GF(701^2). -/
noncomputable def embed_701_1_2 :
    Hex.GFq 701 1 Hex.Conway.supportedEntry_701_1 →+*
      Hex.GFq 701 2 Hex.Conway.supportedEntry_701_2 :=
  conwayEmbed 701 1 2 _ _ Hex.Conway.compat_701_1_2

/-- The canonical embedding of GF(701^1) into GF(701^3). -/
noncomputable def embed_701_1_3 :
    Hex.GFq 701 1 Hex.Conway.supportedEntry_701_1 →+*
      Hex.GFq 701 3 Hex.Conway.supportedEntry_701_3 :=
  conwayEmbed 701 1 3 _ _ Hex.Conway.compat_701_1_3

/-- The canonical embedding of GF(709^1) into GF(709^2). -/
noncomputable def embed_709_1_2 :
    Hex.GFq 709 1 Hex.Conway.supportedEntry_709_1 →+*
      Hex.GFq 709 2 Hex.Conway.supportedEntry_709_2 :=
  conwayEmbed 709 1 2 _ _ Hex.Conway.compat_709_1_2

/-- The canonical embedding of GF(709^1) into GF(709^3). -/
noncomputable def embed_709_1_3 :
    Hex.GFq 709 1 Hex.Conway.supportedEntry_709_1 →+*
      Hex.GFq 709 3 Hex.Conway.supportedEntry_709_3 :=
  conwayEmbed 709 1 3 _ _ Hex.Conway.compat_709_1_3

/-- The canonical embedding of GF(719^1) into GF(719^2). -/
noncomputable def embed_719_1_2 :
    Hex.GFq 719 1 Hex.Conway.supportedEntry_719_1 →+*
      Hex.GFq 719 2 Hex.Conway.supportedEntry_719_2 :=
  conwayEmbed 719 1 2 _ _ Hex.Conway.compat_719_1_2

/-- The canonical embedding of GF(719^1) into GF(719^3). -/
noncomputable def embed_719_1_3 :
    Hex.GFq 719 1 Hex.Conway.supportedEntry_719_1 →+*
      Hex.GFq 719 3 Hex.Conway.supportedEntry_719_3 :=
  conwayEmbed 719 1 3 _ _ Hex.Conway.compat_719_1_3

/-- The canonical embedding of GF(727^1) into GF(727^2). -/
noncomputable def embed_727_1_2 :
    Hex.GFq 727 1 Hex.Conway.supportedEntry_727_1 →+*
      Hex.GFq 727 2 Hex.Conway.supportedEntry_727_2 :=
  conwayEmbed 727 1 2 _ _ Hex.Conway.compat_727_1_2

/-- The canonical embedding of GF(727^1) into GF(727^3). -/
noncomputable def embed_727_1_3 :
    Hex.GFq 727 1 Hex.Conway.supportedEntry_727_1 →+*
      Hex.GFq 727 3 Hex.Conway.supportedEntry_727_3 :=
  conwayEmbed 727 1 3 _ _ Hex.Conway.compat_727_1_3

/-- The canonical embedding of GF(733^1) into GF(733^2). -/
noncomputable def embed_733_1_2 :
    Hex.GFq 733 1 Hex.Conway.supportedEntry_733_1 →+*
      Hex.GFq 733 2 Hex.Conway.supportedEntry_733_2 :=
  conwayEmbed 733 1 2 _ _ Hex.Conway.compat_733_1_2

/-- The canonical embedding of GF(733^1) into GF(733^3). -/
noncomputable def embed_733_1_3 :
    Hex.GFq 733 1 Hex.Conway.supportedEntry_733_1 →+*
      Hex.GFq 733 3 Hex.Conway.supportedEntry_733_3 :=
  conwayEmbed 733 1 3 _ _ Hex.Conway.compat_733_1_3

end HexGFqMathlib.Conway
