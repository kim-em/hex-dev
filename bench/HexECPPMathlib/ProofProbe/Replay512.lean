/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.CompactFixtures
-- Serialize the two large kernel probes in Lake's build graph.
import HexECPPMathlib.ProofProbe.Replay256

theorem result512 : Nat.Prime 6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503096753 := by
  ecpp using Hex.ECPP.CompactFixtures.cert512

#print axioms result512
