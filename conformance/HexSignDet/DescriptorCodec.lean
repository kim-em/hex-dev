/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Descriptor
public meta import HexSignDet.Codec.Descriptor

/-! Public-import conformance for selected-root subject composition. These
checks test literal parsing and bindings, not mathematical root validity. -/
public section
namespace Hex.SignDet.DescriptorCodec
/-- Public composition uses exact contexts and every selected-root field. -/
def subject : RawDescriptor Rat Nat :=
  ⟨7, DensePoly.ofCoeffs #[-1, 0, 1], .negInf, .posInf, [1, 2], [1, 1]⟩

def encodedSubject : Codec.Json := Codec.descriptor ValueCodec.rat ValueCodec.nat subject

def acceptsSubject (raw : RawDescriptor Rat Nat) : Bool :=
  match Codec.readDescriptorBinding ValueCodec.rat ValueCodec.nat raw encodedSubject with
  | .ok () => true
  | .error _ => false

def parsedSubject : Bool :=
  match Codec.readDescriptor ValueCodec.rat ValueCodec.nat encodedSubject with
  | .ok raw => decide (raw = subject)
  | .error _ => false

#guard parsedSubject
#guard acceptsSubject subject
#guard !acceptsSubject {subject with context := 8}
#guard !acceptsSubject {subject with head := DensePoly.ofCoeffs #[-2, 0, 1]}
#guard !acceptsSubject {subject with indices := [2, 1]}
#guard !acceptsSubject {subject with signs := [-1, 1]}
#guard !acceptsSubject {subject with lower := .finite 0}

/-- An ordinary kernel proof using the public reader and encoder. -/
theorem subject_roundtrip :
    parsedSubject = true := by
  decide +kernel

/-- info: 'Hex.SignDet.DescriptorCodec.subject_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subject_roundtrip


def fields : Array Codec.Json :=
  match encodedSubject.getArr? with
  | .ok a => a
  | .error _ => #[]

def rejectsWire (j : Codec.Json) : Bool :=
  match Codec.readDescriptor ValueCodec.rat ValueCodec.nat j with
  | .error _ => true
  | .ok _ => false

def wireError (j : Codec.Json) : String :=
  match Codec.readDescriptor ValueCodec.rat ValueCodec.nat j with
  | .error e => e
  | .ok _ => "accepted"

#guard wireError (.arr (fields.extract 0 5)) == "wrong field count"
#guard wireError (.arr (fields.push (Codec.Json.of (0 : Nat)))) == "wrong field count"
#guard rejectsWire (.arr (fields.set! 1 (.arr #[ValueCodec.rat.encode 1, ValueCodec.rat.encode 0])))
#guard rejectsWire (.arr (fields.set! 2 (.arr #[Codec.Json.of (3 : Nat)])))
#guard rejectsWire (.arr (fields.set! 4 (.arr #[Codec.Json.of (-1 : Int)])))
#guard (match Codec.readDescriptorBinding ValueCodec.rat ValueCodec.nat
    {subject with context := 8} encodedSubject with
  | .error e => e == "selected root binding mismatch"
  | .ok _ => false)

end Hex.SignDet.DescriptorCodec
