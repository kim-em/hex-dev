/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Closure

public section

namespace Hex.Perm

/-- The commutator convention is `[p,q] = p*q*p⁻¹*q⁻¹`. -/
@[expose] def comm (p q : Perm n) : Perm n := p.comp (q.comp (p.inv.comp q.inv))

@[simp] theorem comm_id (p : Perm n) : p.comm (Perm.id n) = Perm.id n := by simp [comm]
@[simp] theorem id_comm (p : Perm n) : (Perm.id n).comm p = Perm.id n := by simp [comm]

theorem comm_comp_left (p q r : Perm n) :
    (p.comp q).comm r = (p.conj (q.comm r)).comp (p.comm r) := by
  ext i
  simp [comm, conj, inv_comp]

theorem comm_comp_right (p q r : Perm n) :
    p.comm (q.comp r) = (p.comm q).comp (q.conj (p.comm r)) := by
  ext i
  simp [comm, conj, inv_comp]

theorem comm_inv_left (p q : Perm n) : p.inv.comm q = p.inv.conj (p.comm q).inv := by
  ext i
  simp [comm, conj, inv_comp]

theorem comm_inv_right (p q : Perm n) : p.comm q.inv = q.inv.conj (p.comm q).inv := by
  ext i
  simp [comm, conj, inv_comp]

theorem conj_comm (g p q : Perm n) : g.conj (p.comm q) = (g.conj p).comm (g.conj q) := by
  ext i
  simp [comm, conj, inv_comp]

theorem comm_eq_id (p q : Perm n) : p.comm q = Perm.id n ↔ p.comp q = q.comp p := by
  constructor
  · intro h
    apply Perm.ext
    intro i
    have he := congrArg (fun r => r.get (q.get (p.get i))) h
    simpa [comm] using he
  · intro h
    apply Perm.ext
    intro i
    have he := congrArg (fun r => r.get (p.inv.get (q.inv.get i))) h
    simpa [comm] using he

end Hex.Perm

namespace Hex.PermGroup.Normal

/-- A normal subgroup containing original generator commutators contains all
element commutators. The two inductions follow multiplication and inversion. -/
theorem comm_generated (G N : Group n) (hn : check G N = true)
    (hs : ∀ p ∈ G.generators, ∀ q ∈ G.generators, Generated N.generators (p.comm q))
    (p q : Perm n) (hp : Generated G.generators p) (hq : Generated G.generators q) :
    Generated N.generators (p.comm q) := by
  have hc := (check_iff G N).mp hn
  have right (s : Perm n) (hs' : s ∈ G.generators) (r : Perm n) (hr : Generated G.generators r) :
      Generated N.generators (s.comm r) := by
    induction hr with
    | id => simpa using (Generated.id (S := N.generators))
    | generator hr => exact hs s hs' _ hr
    | @comp a b ha hb ia ib =>
      rw [Perm.comm_comp_right]
      exact ia.comp (hc _ _ ha ib)
    | @inv a ha ia =>
      rw [Perm.comm_inv_right]
      exact hc _ _ ha.inv ia.inv
  induction hp with
  | id => simpa using (Generated.id (S := N.generators))
  | generator hp => exact right _ hp q hq
  | @comp a b ha hb ia ib =>
    rw [Perm.comm_comp_left]
    exact (hc _ _ ha ib).comp ia
  | @inv a ha ia =>
    rw [Perm.comm_inv_left]
    exact hc _ _ ha.inv ia.inv

end Hex.PermGroup.Normal
