/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Mixed.Import
public import HexIntFactor.Pari

public section

/-! Explicit process adapter for mixed factor proposals. Discovery supplies
arithmetic hints; only mixed replay accepts evidence and complete/partial data. -/

namespace Hex.Nat.Mixed

/-- Lift legacy proposal evidence while preserving signed arithmetic hints. -/
def FactorProposal.ofLegacy (p : Hex.Nat.FactorProposal) : FactorProposal :=
  ⟨p.subject, p.entries.map fun (base, exponent, cert) =>
    (base, exponent, cert.map Evidence.legacy)⟩

namespace Pari

/-- A producer failure can coexist with checked empty-factor partial progress. -/
structure Result (n : Nat) where
  value : Option (ImportResult n)
  producer : Option Hex.Nat.Pari.ProducerError
  importer : Option Hex.Nat.ImportError

/-- Explicit bounded PARI discovery followed by the pure mixed importer.
Failure preserves the admitted whole subject as an unclaimed residual;
there is no additional discovery or external primality-certificate producer. -/
def factor (n : Nat) (r : Hex.Rand) (budget : ImportBudget := {})
    (process : Hex.Nat.Pari.ProcessBudget := {}) (parser : Hex.Nat.Pari.ParseBudget := {})
    (executable : String := "gp") (cancel : Option IO.CancelToken := none) : IO (Result n) := do
  let produced ← Hex.Nat.Pari.produce n process parser executable cancel
  let (proposal, error) := match produced with
    | .ok p => (FactorProposal.ofLegacy p, none)
    | .error e => (⟨(n : Int), []⟩, some e)
  match importFactors budget n proposal r with
  | .ok value => return ⟨some value, error, none⟩
  | .error e => return ⟨none, error, some e⟩

end Pari
end Hex.Nat.Mixed
