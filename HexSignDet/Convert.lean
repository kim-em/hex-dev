/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor
public import HexPoly.Interpret
public import HexRealRoots.Map

public section

namespace Hex.SignDet

variable {E : Type u} {F : Type v} {Ctx : Type w} {NewCtx : Type w'}
variable [Zero E] [DecidableEq E] [Zero F] [DecidableEq F]

/-- Change the coefficient representation and literal context of raw input.
No replay evidence is copied. Formal derivative queries are reconstructed
from the mapped head when the new descriptor is built. -/
@[expose] def RawDescriptor.map (convert : E → F)
    (hz : ∀ a, convert a = 0 ↔ a = 0) (context : NewCtx)
    (raw : RawDescriptor E Ctx) : RawDescriptor F NewCtx where
  context := context
  head := DensePoly.Interpret.map convert hz raw.head
  lower := raw.lower.map convert
  upper := raw.upper.map convert
  indices := raw.indices
  signs := raw.signs

/-- Zero reflection preserves degree and therefore descriptor shape. -/
theorem RawDescriptor.map_wellFormed
    (convert : E → F) (hz : ∀ a, convert a = 0 ↔ a = 0)
    (context : NewCtx) (raw : RawDescriptor E Ctx) :
    (raw.map convert hz context).wellFormed = raw.wellFormed := by
  simp only [RawDescriptor.wellFormed, RawDescriptor.map, DensePoly.Interpret.map_degree]
  rfl

variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [One F] [Add F] [Sub F] [Mul F] [NatCast F] [Neg F] [Inv F]
variable [DecidableEq NewCtx]

/-- Rebuild and check a selected-root descriptor in a new coefficient
representation and context. Only the raw head, endpoints and partial word
are converted; all prepared queries, support evidence and matrices are freshly
constructed by the existing descriptor builder. Arbitrary converters can fail;
the companion proves success and root preservation for lawful interpretations
with the same coefficient values. -/
@[expose] def Descriptor.convert {sign : E → Int} {context : Ctx}
    (convert : E → F) (hz : ∀ a, convert a = 0 ↔ a = 0)
    (newSign : F → Int) (newContext : NewCtx) (source : Descriptor E Ctx sign context) :
    Except BuildError (Except DescriptorError (Descriptor F NewCtx newSign newContext)) :=
  Descriptor.build newSign newContext (source.raw.map convert hz newContext)

end Hex.SignDet
