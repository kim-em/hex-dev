/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.Data.Int.OfNat
public import HexRealClosure.NumberFieldTower
public import HexRealClosure.BaseJson

public section

namespace Hex.RealClosure.BaseJsonTests

theorem encode_rational (registry : BaseContext.Registry) (q : Rat) :
    (NumberField.base registry).codec.encode ⟨q⟩ =
      .array (.cons (.number 0) (.cons (.number q.num) (.cons (.number q.den) .nil))) := by
  exact NumberField.base_encode registry q

theorem decode_rational (registry : BaseContext.Registry) (q : Rat) :
    (NumberField.base registry).codec.decode
      (.array (.cons (.number 0) (.cons (.number q.num) (.cons (.number q.den) .nil)))) =
      .ok (⟨q⟩ : (NumberField.base registry).Value) := by
  exact NumberField.base_decode registry q

theorem decode_three (registry : BaseContext.Registry) :
    (NumberField.base registry).codec.decode
      (.array (.cons (.number 0) (.cons (.number 3) (.cons (.number 1) .nil)))) =
      .ok (⟨(3 : Rat)⟩ : (NumberField.base registry).Value) := by
  exact decode_rational registry 3

theorem decode_negative (registry : BaseContext.Registry) :
    (NumberField.base registry).codec.decode
      (.array (.cons (.number 0) (.cons (.number (-3)) (.cons (.number 2) .nil)))) =
      .ok (⟨(⟨-3, 2, by decide, by decide⟩ : Rat)⟩ :
        (NumberField.base registry).Value) := by
  exact NumberField.decode_payload registry (⟨-3, 2, by decide, by decide⟩ : Rat)
    (-3) 2 rfl (Nat.ToInt.natCast_ofNat 2)

theorem decode_bind (registry : BaseContext.Registry) (q : Rat) :
    (do
      let value ← (NumberField.base registry).codec.decode
        (.array (.cons (.number 0) (.cons (.number q.num) (.cons (.number q.den) .nil))))
      pure value.stored : Except String Rat) = .ok q := by
  simp only [NumberField.base_decode registry q, bind, Except.bind, pure, Except.pure]

theorem bind_three (registry : BaseContext.Registry) :
    (do
      let value ← (NumberField.base registry).codec.decode
        (.array (.cons (.number 0) (.cons (.number 3) (.cons (.number 1) .nil))))
      pure value.stored : Except String Rat) = .ok 3 := by
  rw [decode_three]
  rfl

end Hex.RealClosure.BaseJsonTests

/-- info: 'Hex.RealClosure.BaseContext.rational_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.rational_chain

/-- info: 'Hex.RealClosure.BaseContext.Context.write_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Context.write_rational

/-- info: 'Hex.RealClosure.BaseContext.Element.codec_encode_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.codec_encode_rational

/-- info: 'Hex.RealClosure.BaseContext.Element.codec_decode_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.codec_decode_rational

/-- info: 'Hex.RealClosure.Tower.Context.base_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.base_codec

/-- info: 'Hex.RealClosure.NumberField.base_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.NumberField.base_encode

/-- info: 'Hex.RealClosure.NumberField.base_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.NumberField.base_decode

/-- info: 'Hex.RealClosure.NumberField.decode_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.NumberField.decode_payload

/-- info: 'Hex.RealClosure.BaseJsonTests.encode_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseJsonTests.encode_rational

/-- info: 'Hex.RealClosure.BaseJsonTests.decode_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseJsonTests.decode_rational

/-- info: 'Hex.RealClosure.BaseJsonTests.decode_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseJsonTests.decode_three

/-- info: 'Hex.RealClosure.BaseJsonTests.decode_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseJsonTests.decode_negative

/-- info: 'Hex.RealClosure.BaseJsonTests.decode_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseJsonTests.decode_bind

/-- info: 'Hex.RealClosure.BaseJsonTests.bind_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseJsonTests.bind_three
