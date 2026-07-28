/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.ProofProbe.Generated
public meta import HexRCF.ProofProbe.Generated

public section

/-!
Structural premise checks for the committed proof-probe literals. This module
is not measured; it makes malformed or stale generated certificates fail the
ordinary build.
-/

namespace Hex.RCF.ProofProbe.Validate

def quadraticCertificate : Certificate := rcfQuadraticCertificate
def degree10Certificate : Certificate := rcfDegree10Certificate
def degree50Certificate : Certificate := rcfDegree50Certificate

rcf_reify_probe quadratic : rcfQuadraticGoal
rcf_reify_probe degree10 : rcfDegree10Goal
rcf_reify_probe degree50 : rcfDegree50Goal

#guard quadraticCertificate.check quadraticSentence
#guard degree10Certificate.check degree10Sentence
#guard degree50Certificate.check degree50Sentence

rcf_literal_probe quadratic : rcfQuadraticCertificate
rcf_literal_probe degree10 : rcfDegree10Certificate
rcf_literal_probe degree50 : rcfDegree50Certificate

end Hex.RCF.ProofProbe.Validate
