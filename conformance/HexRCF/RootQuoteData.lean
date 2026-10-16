/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.Data.Int.OfNat
public import HexRealClosure.NumberFieldTower
public import HexRealClosure.RootReplay
public section
open Hex Hex.RealClosure Hex.SignDet
namespace Hex.RCF.RootQuoteTests

/-! An independent cubic subject and complete finite replay. Every JSON field,
including rational scalar payloads, consists only of frozen constructors. -/

@[expose] def registry : BaseContext.Registry := fun _ => none
abbrev base := NumberField.base registry
@[expose] def contextToken : Codec.Json := .array (.cons (.number 0) .nil)
@[expose] def j0 : Codec.Json := .number (0)
@[expose] def j1 : Codec.Json := .array (.cons j0 .nil)
@[expose] def j2 : Codec.Json := .number (-3)
@[expose] def j3 : Codec.Json := .number (1)
@[expose] def j4 : Codec.Json := .array (.cons (.number 0) (.cons (.number (-3)) (.cons (.number 1) .nil)))
@[expose] def j5 : Codec.Json := .array (.cons (.number 0) (.cons (.number (0)) (.cons (.number 1) .nil)))
@[expose] def j6 : Codec.Json := .array (.cons (.number 0) (.cons (.number (1)) (.cons (.number 1) .nil)))
@[expose] def j7 : Codec.Json := .array (.cons j4 (.cons j5 (.cons j5 (.cons j6 .nil))))
@[expose] def j8 : Codec.Json := .number (-8)
@[expose] def j9 : Codec.Json := .array (.cons (.number 0) (.cons (.number (-8)) (.cons (.number 1) .nil)))
@[expose] def j10 : Codec.Json := .array (.cons j3 (.cons j9 .nil))
@[expose] def j11 : Codec.Json := .number (8)
@[expose] def j12 : Codec.Json := .array (.cons (.number 0) (.cons (.number (8)) (.cons (.number 1) .nil)))
@[expose] def j13 : Codec.Json := .array (.cons j3 (.cons j12 .nil))
@[expose] def j14 : Codec.Json := .array .nil
@[expose] def j15 : Codec.Json := .array (.cons contextToken (.cons j7 (.cons j10 (.cons j13 (.cons j14 (.cons j14 .nil))))))
@[expose] def j16 : Codec.Json := .array (.cons j14 .nil)
@[expose] def j17 : Codec.Json := .array (.cons j3 .nil)
@[expose] def j18 : Codec.Json := .array (.cons j17 .nil)
@[expose] def j19 : Codec.Json := .array (.cons j16 (.cons j16 (.cons j17 (.cons j17 (.cons j18 (.cons j3 .nil))))))
@[expose] def j20 : Codec.Json := .array (.cons j6 .nil)
@[expose] def j21 : Codec.Json := .array (.cons j5 (.cons j5 (.cons j6 .nil)))
@[expose] def j22 : Codec.Json := .array (.cons j7 (.cons j21 (.cons j20 .nil)))
@[expose] def j23 : Codec.Json := .number (3)
@[expose] def j24 : Codec.Json := .number (2)
@[expose] def j25 : Codec.Json := .array (.cons j23 (.cons j24 (.cons j0 .nil)))
@[expose] def j26 : Codec.Json := .array (.cons (.number 0) (.cons (.number (3)) (.cons (.number 1) .nil)))
@[expose] def j27 : Codec.Json := .array (.cons j6 (.cons j14 (.cons j26 .nil)))
@[expose] def j28 : Codec.Json := .array (.cons j5 (.cons j6 .nil))
@[expose] def j29 : Codec.Json := .array (.cons j6 (.cons j28 (.cons j26 .nil)))
@[expose] def j30 : Codec.Json := .array (.cons j29 .nil)
@[expose] def j31 : Codec.Json := .array (.cons j6 (.cons j21 .nil))
@[expose] def j32 : Codec.Json := .array (.cons j31 .nil)
@[expose] def j33 : Codec.Json := .array (.cons j22 (.cons j25 (.cons j27 (.cons j30 (.cons j32 .nil)))))
@[expose] def j34 : Codec.Json := .number (-1)
@[expose] def j35 : Codec.Json := .array (.cons j34 (.cons j3 (.cons j3 .nil)))
@[expose] def j36 : Codec.Json := .array (.cons j3 (.cons j3 (.cons j3 .nil)))
@[expose] def j37 : Codec.Json := .array (.cons contextToken (.cons j7 (.cons j20 (.cons j10 (.cons j13 (.cons j33 (.cons j33 (.cons j35 (.cons j36 (.cons j3 (.cons j0 (.cons j3 .nil))))))))))))
@[expose] def j38 : Codec.Json := .array (.cons j37 .nil)
@[expose] def j39 : Codec.Json := .array (.cons j14 (.cons j20 .nil))
@[expose] def j40 : Codec.Json := .array (.cons j39 .nil)
@[expose] def j41 : Codec.Json := .array (.cons j40 .nil)
@[expose] def j42 : Codec.Json := .array (.cons j3 (.cons j1 (.cons j1 (.cons j3 (.cons j18 .nil)))))
@[expose] def j43 : Codec.Json := .array (.cons contextToken (.cons j7 (.cons j10 (.cons j13 (.cons j14 (.cons j3 (.cons j19 (.cons j38 (.cons j41 (.cons j16 (.cons j42 .nil)))))))))))
@[expose] def j44 : Codec.Json := .array (.cons j43 (.cons j14 .nil))
@[expose] def j45 : Codec.Json := .array (.cons j44 .nil)
@[expose] def j46 : Codec.Json := .array (.cons j3 (.cons j0 (.cons j45 .nil)))
@[expose] def j47 : Codec.Json := .array (.cons j1 (.cons j7 (.cons j10 (.cons j13 (.cons j14 (.cons j14 (.cons j46 .nil)))))))
@[expose] def subject := j15
@[expose] def evidence := j46
@[expose] def frameJson := j47
@[expose] def read := Algebraic.RootReplay.readDescriptor base.codec
  (Tower.contextCodec base.signature) base.sign base.signature subject evidence
@[expose] def cubicHead : DensePoly base.Value :=
  ⟨#[⟨-3⟩,⟨0⟩,⟨0⟩,⟨1⟩], Or.inr (by
    change some (⟨(1 : Rat)⟩ : base.Value) ≠ some 0
    intro same
    have zero := (BaseContext.Element.stored_eq_zero (⟨(1 : Rat)⟩ : base.Value)).mpr
      (Option.some.inj same)
    exact (by decide : (1 : Rat) ≠ 0) zero)⟩
@[expose] def rawSubject : RawDescriptor base.Value Tower.Signature :=
  ⟨base.signature, cubicHead, .finite ⟨-8⟩, .finite ⟨8⟩, [], []⟩
theorem encode_integer (n : Int) :
    base.codec.encode (⟨(n : Rat)⟩ : base.Value) =
      .arr #[.number 0,.number n,.number 1] := by
  have encoded := NumberField.base_encode registry (n : Rat)
  have denominator : ((n : Rat).den : Int) = 1 := by
    rw [Rat.den_intCast]
    exact Nat.ToInt.natCast_ofNat 1
  rw [Rat.num_intCast,denominator] at encoded
  exact encoded

theorem subject_encoded :
    Codec.descriptor base.codec (Tower.contextCodec base.signature) rawSubject = subject := by
  simp only [Codec.descriptor, rawSubject, Codec.poly, Codec.array, Codec.list,
    Codec.endpoint, Tower.contextCodec_encode_self, cubicHead, DensePoly.toArray]
  simp only [Codec.Json.arr, Array.toList_map, List.map_nil]
  change Codec.Json.arr #[contextToken,
    .arr #[base.codec.encode ⟨((-3 : Int) : Rat)⟩,base.codec.encode ⟨((0 : Int) : Rat)⟩,
      base.codec.encode ⟨((0 : Int) : Rat)⟩,base.codec.encode ⟨((1 : Int) : Rat)⟩],
    .arr #[.number 1,base.codec.encode ⟨((-8 : Int) : Rat)⟩],
    .arr #[.number 1,base.codec.encode ⟨((8 : Int) : Rat)⟩],j14,j14] = subject
  rw [encode_integer (-3),encode_integer 0,encode_integer 1,
    encode_integer (-8),encode_integer 8]
  rfl
theorem subject_read :
    Algebraic.SignRequests.readRoot base.codec (Tower.contextCodec base.signature) subject = .ok rawSubject := by
  rw [← subject_encoded]
  apply Algebraic.SignRequests.readRoot_binding
  · exact Tower.contextCodec_lawful _ _
  · intro value member
    exact base.codec_lawful value
  · intro value same
    exact base.codec_lawful value
  · intro value same
    exact base.codec_lawful value

theorem decode_integer (n : Int) :
    base.codec.decode (.arr #[.number 0,.number n,.number 1]) =
      .ok (⟨(n : Rat)⟩ : base.Value) := by
  exact NumberField.decode_payload registry (n : Rat) n 1
    (Rat.num_intCast n) (by rw [Rat.den_intCast]; exact Nat.ToInt.natCast_ofNat 1)

@[expose] def nodeReader := Codec.readNode base.codec (Tower.contextCodec base.signature) j43

/-- A graph with an unsupported version. -/
@[expose] def wrongVersion := Algebraic.RootReplay.readDescriptor base.codec
  (Tower.contextCodec base.signature) base.sign base.signature subject
  (.arr #[.number 2,j0,j45])
/-- The matrix and value remain 1; the claimed count is changed to 2. -/
@[expose] def wrongSystem : Codec.Json := .arr #[j16,j16,.arr #[.number 2],j17,j18,j3]
@[expose] def wrongNode : Codec.Json :=
  .arr #[contextToken,j7,j10,j13,j14,j3,wrongSystem,j38,j41,j16,j42]
@[expose] def wrongNodeReader :=
  Codec.readNode base.codec (Tower.contextCodec base.signature) wrongNode
@[expose] def wrongCount := Algebraic.RootReplay.readDescriptor base.codec
  (Tower.contextCodec base.signature) base.sign base.signature subject
  (.arr #[j3,j0,.arr #[.arr #[wrongNode,j14]]])

end Hex.RCF.RootQuoteTests
