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
  unfold NumberField.base
  rw [Tower.Context.base_codec (BaseContext.rational registry)]
  simpa only [BaseContext.Syntax.literal, Tower.Literal.toJson] using
    BaseContext.Element.codec_encode_rational registry q

theorem decode_rational (registry : BaseContext.Registry) (q : Rat) :
    (NumberField.base registry).codec.decode
      (.array (.cons (.number 0) (.cons (.number q.num) (.cons (.number q.den) .nil)))) =
      .ok (⟨q⟩ : (NumberField.base registry).Value) := by
  unfold NumberField.base
  rw [Tower.Context.base_codec (BaseContext.rational registry)]
  dsimp only [Tower.Context.Value, Tower.Context.base]
  simpa only [BaseContext.Syntax.literal, Tower.Literal.toJson] using
    BaseContext.Element.codec_decode_rational registry q

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
  let q : Rat := ⟨-3, 2, by decide, by decide⟩
  have decoded := decode_rational registry q
  change (NumberField.base registry).codec.decode
    (.array (.cons (.number 0) (.cons (.number (-3))
      (.cons (.number ((2 : Nat) : Int)) .nil)))) = .ok ⟨q⟩ at decoded
  have denominator : ((2 : Nat) : Int) = 2 := Nat.ToInt.natCast_ofNat 2
  rw [denominator] at decoded
  exact decoded

theorem decode_bind (registry : BaseContext.Registry) :
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
