/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Checker

public section

/-!
The optional external LLL provider. `lll` probes an `@[extern]` hook for
an independent native reducer, marshals the basis, and certifies the
returned candidate with `certCheck`; absence or rejection falls through
to the steered/native path. The provider is acceleration only.
-/

namespace Hex

/-! ## External LLL provider

Optional runtime hook for an external reducer (e.g. fpLLL) loaded through the
C FFI shim in `HexLLL/ffi/`. `providerAvailable` reports whether a provider is
registered (driven by the `HEX_FPLLL_FFI_LIB` environment variable); when none
is present, or a returned candidate fails validation, callers fall back to the
verified native reducer `lllNative`. The provider is acceleration only and is
never part of the trusted path — every candidate it returns is checked before
use. See `SPEC/hex-lll.md` for the dispatch and certification details. -/
namespace Internal.LLLProvider

@[extern "lean_hexlll_provider_available"]
opaque providerAvailable : Unit → Bool

@[extern "lean_hexlll_provider_reduce"]
opaque providerReduce (rows cols : USize) (entries : @& Array String)
    (delta eta : Float) (method : UInt8) (withInverse : Bool) :
    Except String (Array Int)

/-- Decoded result returned by the external LLL provider.

`reduced` is the row-major reduced basis, `transform` is the row-major
unimodular transformation matrix with `transform * input = reduced`, and
`inverse?` is the optional row-major inverse transformation when the caller
requested it. -/
structure Candidate where
  reduced : Array Int
  transform : Array Int
  inverse? : Option (Array Int)
deriving Repr, BEq

/-- Diagnostic counters for attempts to use the external LLL provider.

`absent` counts calls made when the provider is unavailable, `providerError`
counts provider-level failures, `rejected` counts structurally invalid provider
responses, and `accepted` counts responses decoded into a `Candidate`. -/
structure Diagnostics where
  absent : Nat := 0
  providerError : Nat := 0
  rejected : Nat := 0
  accepted : Nat := 0
deriving Repr, BEq, Inhabited

/-- Classification of one external-provider attempt: unavailable provider,
provider error, rejected response, or accepted candidate. -/
inductive Outcome where
  | absent
  | providerError
  | rejected
  | accepted
deriving Repr, BEq

/-- Increment the diagnostic counter matching `outcome`. -/
@[expose]
def bump (d : Diagnostics) : Outcome → Diagnostics
  | .absent => { d with absent := d.absent + 1 }
  | .providerError => { d with providerError := d.providerError + 1 }
  | .rejected => { d with rejected := d.rejected + 1 }
  | .accepted => { d with accepted := d.accepted + 1 }

initialize diagnosticsRef : IO.Ref Diagnostics ← IO.mkRef {}

/-- Reset the external-provider diagnostics counters to zero. Test and bench
harnesses use this to isolate one run's provider availability, rejection, and
acceptance counts. -/
@[expose]
def resetDiagnostics : IO Unit :=
  diagnosticsRef.set {}

/-- Read the external-provider diagnostics accumulated since the last
`resetDiagnostics`. The snapshot is the observability hook for deciding whether
the external reducer was absent, failed, returned malformed data, or supplied a
candidate accepted by the decoder. -/
@[expose]
def diagnostics : IO Diagnostics :=
  diagnosticsRef.get

/-- Increment the external-provider diagnostic counter for `outcome`. This is
the `IO` entry point used by provider calls; pure LLL code uses
`withRecordOutcome` to record the same classifications without changing its
surface type. -/
@[expose]
def recordOutcome (outcome : Outcome) : IO Unit :=
  diagnosticsRef.modify (fun d => bump d outcome)

/-- Decode the external reducer's flat integer response into a structured
`Candidate`. The decoder checks the status word, row/column headers, inverse
flag, and total payload length before slicing out the reduced basis,
transformation, and optional inverse; any mismatch returns `none`, so malformed
provider output cannot enter the certified path. -/
@[expose]
def validateFlat (rows cols : Nat) (withInverse : Bool) (flat : Array Int) :
    Option Candidate := do
  let status ← flat[0]?
  let rowsHeader ← flat[1]?
  let colsHeader ← flat[2]?
  let inverseHeader ← flat[3]?
  if status != 0 then
    none
  let rowsSeen ← rowsHeader.toNat?
  let colsSeen ← colsHeader.toNat?
  let inverseSeen ← inverseHeader.toNat?
  if rowsSeen != rows || colsSeen != cols then
    none
  let hasInverse ←
    match inverseSeen with
    | 0 => some false
    | 1 => some true
    | _ => none
  if hasInverse != withInverse then
    none
  let basisLen := rows * cols
  let transformLen := rows * rows
  let inverseLen := if hasInverse then transformLen else 0
  let expectedLen := 4 + basisLen + transformLen + inverseLen
  if flat.size != expectedLen then
    none
  let reduced := flat.extract 4 (4 + basisLen)
  let transform := flat.extract (4 + basisLen) (4 + basisLen + transformLen)
  let inverse? :=
    if hasInverse then
      some (flat.extract (4 + basisLen + transformLen)
        (4 + basisLen + transformLen + transformLen))
    else
      none
  some { reduced, transform, inverse? }

/-- Try to obtain an LLL candidate from the external provider. The call records
why no candidate was used (`absent`, provider error, or rejected flat payload)
and returns `some candidate` only after `validateFlat` accepts the provider's
response shape. -/
@[expose]
def tryReduce (rows cols : USize) (entries : Array String)
    (delta eta : Float) (method : UInt8) (withInverse : Bool) :
    IO (Option Candidate) := do
  if !providerAvailable () then
    recordOutcome .absent
    return none
  match providerReduce rows cols entries delta eta method withInverse with
  | .error _ =>
      recordOutcome .providerError
      return none
  | .ok flat =>
      match validateFlat rows.toNat cols.toNat withInverse flat with
      | some candidate =>
          recordOutcome .accepted
          return some candidate
      | none =>
          recordOutcome .rejected
          return none

#guard validateFlat 2 3 false #[0, 2, 3, 0, 1, 2, 3, 4, 5, 6, 1, 0, 0, 1] ==
  some { reduced := #[1, 2, 3, 4, 5, 6], transform := #[1, 0, 0, 1], inverse? := none }
#guard validateFlat 2 3 true #[0, 2, 3, 1, 1, 2, 3, 4, 5, 6, 1, 0, 0, 1, 1, 0, 0, 1] ==
  some
    { reduced := #[1, 2, 3, 4, 5, 6]
      transform := #[1, 0, 0, 1]
      inverse? := some #[1, 0, 0, 1] }
#guard validateFlat 2 3 false #[1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 1, 0, 0, 1] == none
#guard validateFlat 2 3 false #[0, 2, 4, 0, 1, 2, 3, 4, 5, 6, 1, 0, 0, 1] == none
#guard validateFlat 2 3 false #[0, 2, 3, 1, 1, 2, 3, 4, 5, 6, 1, 0, 0, 1] == none
#guard validateFlat 2 3 false #[0, 2, 3, 0, 1, 2, 3, 4, 5, 6, 1, 0, 0] == none

/-- Side-effecting companion of `recordOutcome` callable from pure code.

Definitionally `k`, so kernel reduction and proofs treat it as identity on the
continuation. The `@[implemented_by]` attribute redirects compiled code to a
side-effecting implementation that bumps `diagnosticsRef` via `unsafeBaseIO`
before returning `k`, giving us the diagnostic tally that the SPEC requires
without forcing `lll` into `IO`. The pattern mirrors `Init.Util.withPtrEq`. -/
unsafe def withRecordOutcomeImpl {α : Sort u} (o : Outcome) (k : α) : α :=
  match unsafeBaseIO (diagnosticsRef.modify (fun d => bump d o)) with
  | () => k

/-- Pure-facing wrapper that records one external-provider outcome in compiled
code and otherwise returns `k`. This lets the public reducer stay pure while
compiled runs still populate `diagnosticsRef` for provider observability. -/
@[expose, implemented_by withRecordOutcomeImpl]
def withRecordOutcome {α : Sort u} (_o : Outcome) (k : α) : α := k

/-- Approximate `Rat → Float` conversion used to forward the requested `δ` to
the external reducer. Precision of the forwarded value is not part of
correctness: the candidate is certified by integer arithmetic against the
exact `δ`. -/
@[expose]
def ratToFloat (r : Rat) : Float :=
  Float.ofInt r.num / Float.ofNat r.den

/-- Size-reduction bound *requested* from the external reducer, strictly
stronger than the `η = 11/20` the checker certifies.

The dispatch asks the reducer for a `(requestedDelta δ, requestedEta)`-reduced
basis but certifies it against the public `(δ, 11/20)`. The two differ on
purpose. `certCheck`'s reducedness clause is decided by a fixed-precision
enclosure pass that resolves open inequalities only by *margin*; a candidate
whose `|μ|` sits arbitrarily close to `11/20` would leave the enclosure
straddling its threshold and force the exact fallback. Requesting
`requestedEta < 11/20` instead guarantees a correctly-functioning reducer
lands every size-reduction inequality a macroscopic `11/20 − requestedEta`
clear of the certified bound, so the enclosure decides it.

`requestedEta` must stay `> 1/2` (the reducer's hard floor) and `< 11/20`.
Its exact value is untrusted: certification is against the exact `(δ, 11/20)`,
so the requested bound is outside the trusted story entirely (the
"reliability is empirical, soundness is not" clause). Varying it within
`(1/2, 11/20)` only trades reducer work against enclosure margin; it cannot
make a non-reduced basis certify. The value `107/200` sits a gap of `3/200`
below `11/20` and `7/200` above `1/2`: a narrow gap from the certified bound
keeps the small amount of extra work the stronger request costs the reducer
inside measurement noise, while still clearing the bound by a margin the
enclosure resolves. It is a `Rat`, forwarded to the reducer through
`ratToFloat` like `requestedDelta`, so the design constant and the certified
bound are comparable rationals. -/
@[expose]
def requestedEta : Rat := 107 / 200

/-- Lovász parameter *requested* from the external reducer: a fixed `1/100`
margin above the caller's `δ`, but never past the midpoint `(δ + 1)/2`
between `δ` and `1`.

Mirrors `requestedEta`: the dispatch certifies the candidate against the
caller's exact `δ` but asks the reducer for the stronger `requestedDelta δ`,
so a correctly-functioning reducer clears every Lovász inequality by a
positive margin `(requestedDelta δ − δ)·d[i+1]²` and the enclosure decides it
rather than straddling.

The midpoint cap is what keeps the request strictly between `δ` and `1` over
the whole public surface `δ ≤ 1`. For `δ ≤ 49/50` the `1/100` term wins and
the margin is the full `1/100`; for `49/50 < δ < 1` the midpoint wins and the
margin is `(1 − δ)/2`, still positive, so `δ < requestedDelta δ < 1` holds for
every `δ < 1`. At the boundary `δ = 1` the midpoint is `1`: no value is both
`> δ` and `< 1`, so the request equals the certified `δ` and the prophylactic
gap is unavoidably lost — a candidate the reducer cannot strengthen there
falls back through certification to the native path, which stays sound.

The Lovász condition governs how many swaps the reducer performs, so the
requested `δ` drives the extra work the stronger request costs; the small
`1/100` margin keeps that cost inside measurement noise while still giving the
enclosure a decisive gap.

Untrusted, exactly as `requestedEta`: the certificate is checked against the
exact `δ`, never against this value, so the margin may vary without touching
soundness. -/
@[expose]
def requestedDelta (δ : Rat) : Rat := min (δ + 1 / 100) ((δ + 1) / 2)

/-- Row-major marshalling of an integer matrix into the `Array String` payload
the external provider expects. -/
@[expose]
def matrixToEntries (B : Hex.Matrix Int n m) : Array String :=
  B.rows.toArray.flatMap (fun row => row.toArray.map toString)

/-- Reshape a flat row-major `Array Int` of length `rows * cols` into a
`Matrix Int rows cols`. Returns `none` on length mismatch. -/
@[expose]
def matrixFromArray (rows cols : Nat) (a : Array Int) :
    Option (Hex.Matrix Int rows cols) :=
  if h : a.size = rows * cols then
    some (Hex.Matrix.ofRows (Vector.ofFn fun i =>
      Vector.ofFn fun j =>
        a[i.val * cols + j.val]'(by
          have hi : i.val + 1 ≤ rows := Nat.succ_le_of_lt i.isLt
          have h1 : (i.val + 1) * cols ≤ rows * cols :=
            Nat.mul_le_mul_right cols hi
          have hjlt : j.val < cols := j.isLt
          have h2 : i.val * cols + j.val < (i.val + 1) * cols := by
            rw [Nat.succ_mul]
            exact Nat.add_lt_add_left hjlt _
          have h3 : i.val * cols + j.val < rows * cols :=
            Nat.lt_of_lt_of_le h2 h1
          rw [h]; exact h3)))
  else
    none

/-- Bundled output of the shape/cert pipeline: the reduced basis `B'`,
the two integer transforms, and a proof that they pass `Hex.certCheck` at
`(δ, 11/20)`. Bundling the proof inside the option lets the extraction lemma
read it off as a projection. -/
@[expose]
def CertifiedTriple (B : Hex.Matrix Int n m) (δ : Rat) : Type :=
  Σ' (B' : Hex.Matrix Int n m) (U V : Hex.Matrix Int n n),
    Hex.certCheck B B' U V δ (11 / 20) = true

/-- Pure shape/cert pipeline run on a flat provider payload. Validates the
header, reshapes the reduced basis and the two transforms, and runs
`Hex.certCheck` at `η = 11/20`. Returns the bundled certified triple on
acceptance and `none` on any failure. -/
@[expose]
def certifyFlat (B : Hex.Matrix Int n m) (δ : Rat) (flat : Array Int) :
    Option (CertifiedTriple B δ) :=
  match validateFlat n m true flat with
  | none => none
  | some candidate =>
      match candidate.inverse? with
      | none => none
      | some invFlat =>
          match matrixFromArray n m candidate.reduced with
          | none => none
          | some B' =>
              match matrixFromArray n n candidate.transform with
              | none => none
              | some U =>
                  match matrixFromArray n n invFlat with
                  | none => none
                  | some V =>
                      match h : Hex.certCheck B B' U V δ (11 / 20) with
                      | true => some ⟨B', U, V, h⟩
                      | false => none

/-- Pure certified-dispatch core. Gates on `providerAvailable ()` first so the
native path pays only the cached probe; marshals input and certifies the
candidate when the provider is present; updates the diagnostic tally via
`withRecordOutcome` on each outcome.

Returns the certified reduced basis `B'` on acceptance and `none` on absent /
provider error / shape rejection / certificate rejection. The Mathlib-free
correctness hook is `dispatch_some_certCheck`. -/
@[expose]
def dispatch (B : Hex.Matrix Int n m) (δ : Rat) :
    Option (Hex.Matrix Int n m) :=
  if !providerAvailable () then
    withRecordOutcome .absent none
  else
    match providerReduce (USize.ofNat n) (USize.ofNat m) (matrixToEntries B)
        (ratToFloat (requestedDelta δ)) (ratToFloat requestedEta) 0 true with
    | .error _ => withRecordOutcome .providerError none
    | .ok flat =>
        match certifyFlat B δ flat with
        | none => withRecordOutcome .rejected none
        | some triple => withRecordOutcome .accepted (some triple.1)

/-- An accepted `dispatch` result exhibits the integer transforms witnessing
`certCheck B B' U V δ (11/20) = true`. The property-level extraction
(`(same lattice, B'.independent, isLLLReduced B' δ (11/20))`) is `certCheck`'s
soundness theorem in HexLLLMathlib. -/
theorem dispatch_some_certCheck {B : Hex.Matrix Int n m} {δ : Rat}
    {B' : Hex.Matrix Int n m} (h : dispatch B δ = some B') :
    ∃ U V : Hex.Matrix Int n n, Hex.certCheck B B' U V δ (11 / 20) = true := by
  unfold dispatch at h
  simp only [withRecordOutcome] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i triple _
  have heq : triple.1 = B' := Option.some.inj h
  refine ⟨triple.2.1, triple.2.2.1, ?_⟩
  rw [← heq]
  exact triple.2.2.2

end Internal.LLLProvider

end Hex
