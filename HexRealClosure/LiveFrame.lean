/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveRequest

public section
namespace Hex.RealClosure.Tower.Live

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {request : Request registry}

/-- The frame at an original request position is the result of transport
through the checked inclusion retained at that same position. -/
theorem Collection.frame_transport (collection : Collection base request)
    (index : Fin request.length) :
    (request.frame index).transport?
      (collection.shared.maps.get ⟨index.val, by simp [Request.owners]⟩) =
      some (collection.frame index) := by
  obtain ⟨frame, present, checked⟩ := Request.transport?_frame request
    collection.shared.maps collection.frames collection.produced index
  have equal : frame = collection.frame index :=
    Option.some.inj (present.symm.trans (collection.frame_eq index))
  exact equal ▸ checked

/-- Every value keeps its original request position and retained owner map. -/
theorem Collection.frame_values (collection : Collection base request)
    (index : Fin request.length) :
    (collection.frame index).values = (request.frame index).values.map
      (collection.shared.maps.get ⟨index.val, by simp [Request.owners]⟩).value :=
  Frame.transport?_values _ _ _ (collection.frame_transport index)

/-- Polynomial coefficients use the same retained map as the values. -/
theorem Collection.frame_polynomials (collection : Collection base request)
    (index : Fin request.length) :
    (collection.frame index).polynomials = (request.frame index).polynomials.map
      (collection.shared.maps.get ⟨index.val, by simp [Request.owners]⟩).polynomial :=
  Frame.transport?_polynomials _ _ _ (collection.frame_transport index)

/-- Descriptor heads, bounds, derivative positions and signs retain the
complete original raw descriptor through the same owner map. -/
theorem Collection.frame_descriptors (collection : Collection base request)
    (index : Fin request.length) :
    (collection.frame index).descriptors.map (·.raw) =
      (request.frame index).descriptors.map
        ((request.owners[index.val]'(by simp [Request.owners])).mapDescriptor
          collection.shared.input.context
          (collection.shared.maps.get
            ⟨index.val, by simp [Request.owners]⟩).value) :=
  Frame.transport?_descriptors _ _ _ (collection.frame_transport index)

end Hex.RealClosure.Tower.Live
