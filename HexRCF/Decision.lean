/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Builder
public import HexRCF.Soundness
public import HexRealRoots.Isolate

public section

/-!
# Compiled RCF certificate assembly

This module runs root search, strict separation, endpoint classification, and
arithmetic witness construction outside kernel replay. It retains a candidate
only when the small certificate replay produces a well-formed verdict. A true
verdict is checked once more before the public decision wrapper returns it.
-/

namespace Hex.RCF

/-- Erase the proof fields tied to the executable Sturm chain, retaining only
the raw intervals that the generalized replay checker will validate. -/
private def rawIsolations {p : ZPoly} (roots : Hex.RealRootIsolations p) :
    IsolationCert :=
  ⟨roots.isolations.map (fun isolation => isolation.interval)⟩

/-- Run executable isolation, validate the raw intervals against the carrier's
literal replay, and refine touching intervals to strict separation. -/
def buildIsolations? (carrier : CarrierCert) : Option IsolationCert :=
  match Hex.isolate? carrier.carrier with
  | none => none
  | some roots =>
      let raw := rawIsolations roots
      if raw.check carrier.replay then
        Separation.separate? carrier.carrier carrier.replay raw
      else none

/-- Every emitted isolation array passes the generalized strict checker. -/
theorem check_buildIsolations {carrier : CarrierCert}
    {isolations : IsolationCert}
    (h : buildIsolations? carrier = some isolations) :
    isolations.checkStrict carrier.replay = true := by
  unfold buildIsolations? at h
  split at h <;> rename_i hroots
  · simp at h
  · dsimp only at h
    split at h
    · exact Separation.check_of_separate_eq_some h
    · simp at h

/-- Classify every isolated carrier root against one exact endpoint. -/
def buildRootCmps? (carrier : CarrierCert) (isolations : IsolationCert)
    (endpoint : Dyadic) :
    Option (Vector Separation.RootCmp isolations.intervals.size) :=
  Vector.ofFnM fun i =>
    Separation.classify? carrier.carrier carrier.replay
      isolations.intervals[i] endpoint

/-- Build both size-indexed endpoint-comparison vectors and retain them only
after the endpoint checker accepts every position. -/
def buildIocCmps? (carrier : CarrierCert) (isolations : IsolationCert)
    (a b : Dyadic) : Option (IocCmps isolations.intervals.size) := do
  let lower ← buildRootCmps? carrier isolations a
  let upper ← buildRootCmps? carrier isolations b
  let cmps : IocCmps isolations.intervals.size := { lower, upper }
  if cmps.check carrier.carrier carrier.replay isolations a b then
    some cmps
  else none

/-- Every emitted endpoint package passes its positional checker. -/
theorem check_buildIocCmps {carrier : CarrierCert}
    {isolations : IsolationCert} {a b : Dyadic}
    {cmps : IocCmps isolations.intervals.size}
    (h : buildIocCmps? carrier isolations a b = some cmps) :
    cmps.check carrier.carrier carrier.replay isolations a b = true := by
  unfold buildIocCmps? at h
  obtain ⟨lower, _hlower, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨upper, _hupper, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h <;> rename_i hcheck
  · cases Option.some.inj h
    exact hcheck
  · simp at h

/-- Wrap the aligned common-root list as a sign-matrix certificate, retaining
it only after the sign-matrix alignment checker accepts it. -/
def buildSignMatrix? (s : Sentence) (carrier : CarrierCert) :
    Option SignMatrixCert := do
  let commons ← buildCommonRoots? s carrier.carrier
  let cert : SignMatrixCert := { commonRoots := commons }
  if cert.check s carrier then some cert else none

/-- Every emitted sign-matrix package passes its alignment checker. -/
theorem check_buildSignMatrix {s : Sentence} {carrier : CarrierCert}
    {signs : SignMatrixCert}
    (h : buildSignMatrix? s carrier = some signs) :
    signs.check s carrier = true := by
  unfold buildSignMatrix? at h
  obtain ⟨commons, _hcommons, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h <;> rename_i hcheck
  · cases Option.some.inj h
    exact hcheck
  · simp at h

/-- Assemble the constant or carrier decomposition for a domain already known
not to be empty. Common-root work is skipped for root-free carriers. -/
private def buildDecomposition? (s : Sentence) : Option Certificate :=
  if s.polys.isEmpty then some .constants
  else do
    let carrier ← buildCarrier? s
    let isolations ← buildIsolations? carrier
    if isolations.intervals.isEmpty then
      some (.noRoots { carrier, isolations })
    else do
      let signs ← buildSignMatrix? s carrier
      match s with
      | .forallReal _ | .existsReal _ =>
          some (.cells { carrier, isolations, signs, iocCmps := none })
      | .forallIoc a b _ | .existsIoc a b _ => do
          let cmps ← buildIocCmps? carrier isolations a b
          some (.cells { carrier, isolations, signs, iocCmps := some cmps })

/-- Choose the empty-domain branch before performing any arithmetic work. -/
private def buildCandidate? (s : Sentence) : Option Certificate :=
  match s with
  | .forallIoc a b _ | .existsIoc a b _ =>
      if a < b then buildDecomposition? s else some .emptyIoc
  | .forallReal _ | .existsReal _ => buildDecomposition? s

/-- A compiled build result retains the certificate that produced its
diagnostic or proof-producing verdict. -/
structure BuildResult where
  certificate : Certificate
  verdict : Bool

/-- Assemble a certificate and reject it if replay finds malformed evidence. -/
def build? (s : Sentence) : Option BuildResult := do
  let certificate ← buildCandidate? s
  match certificate.replay? s with
  | none => none
  | some verdict => some { certificate, verdict }

/-- A retained build result records exactly the certificate's replay verdict. -/
theorem replay_build {s : Sentence} {result : BuildResult}
    (h : build? s = some result) :
    result.certificate.replay? s = some result.verdict := by
  unfold build? at h
  obtain ⟨certificate, _hcandidate, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> rename_i hreplay
  · simp at h
  · cases Option.some.inj h
    exact hreplay

/-- Compiled convenience decision. False is diagnostic; true is returned only
after the kernel-facing Boolean checker accepts the retained certificate. -/
def decide (s : Sentence) : Option Bool :=
  match build? s with
  | none => none
  | some result =>
      if result.verdict then
        if result.certificate.check s then some true else none
      else some false

/-- A true compiled verdict exposes a certificate accepted by the checker. -/
theorem decide_eq_some_true_imp_exists_cert {s : Sentence}
    (h : decide s = some true) :
    ∃ cert, Certificate.check s cert = true := by
  unfold decide at h
  split at h
  · simp at h
  · rename_i result hresult
    split at h
    · split at h
      · rename_i hcheck
        exact ⟨result.certificate, hcheck⟩
      · simp at h
    · simp at h

/-- Every true compiled verdict proves the reflected sentence. -/
theorem decide_sound (s : Sentence) (h : decide s = some true) : s.toProp := by
  obtain ⟨cert, hcert⟩ := decide_eq_some_true_imp_exists_cert h
  exact check_sound s cert hcert

end Hex.RCF
