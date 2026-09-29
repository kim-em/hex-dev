/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportClosedQuery
public import HexRealClosureMathlib.SpecializeRegular

public section

namespace Hex.RealClosure.Transport

attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F]

/-- The regular fractions at one parameter form a closed interpretation domain.
No arithmetic-preservation premise is required at a fraction with a pole there. -/
theorem regular_closed (embedding : F →+* ℝ) (t : ℝ) :
    Closed (fun f => Specialize.evalMapped embedding f t) (Specialize.Regular embedding t) := by
  classical
  let ring := Specialize.regularRing embedding t
  let evaluation := Specialize.evaluation embedding t
  exact {
    zero := ring.zero_mem
    add := fun _ _ ha hb => ring.add_mem ha hb
    mul := fun _ _ ha hb => ring.mul_mem ha hb
    sub := fun _ _ ha hb => ring.sub_mem ha hb
    one := ring.one_mem
    natCast := fun n => natCast_mem ring n
    read_zero := Specialize.evalMapped_zero embedding t
    read_add := fun a b ha hb => Specialize.evalMapped_add embedding a b t ha hb
    read_mul := fun a b ha hb => Specialize.evalMapped_mul embedding a b t ha hb
    read_sub := fun a b ha hb => Specialize.evalMapped_sub embedding a b t ha hb
    read_one := Specialize.evalMapped_one embedding t
    read_natCast := fun n => map_natCast evaluation n }

/-- A complete accepted chain uses regularity of its finite stored data,
its actual leading guards and scale signs at the same real parameter. -/
theorem chain_check_regular (embedding : F →+* ℝ) (t : ℝ)
    (sourceSign : Hex.RationalFn F → Int) (targetSign : ℝ → Int)
    (p f : Hex.DensePoly (Hex.RationalFn F)) (cert : Hex.SignedRemainderChain (Hex.RationalFn F))
    (hp : ∀ i < p.size, Specialize.Regular embedding t (p.coeff i))
    (hf : ∀ i < f.size, Specialize.Regular embedding t (f.coeff i))
    (domain : ChainDomain (Specialize.Regular embedding t) cert)
    (head : Leading (fun a => Specialize.evalMapped embedding a t) p)
    (entries : ∀ r ∈ cert.chain, Leading (fun a => Specialize.evalMapped embedding a t) r)
    (signs : ChainSigns (fun a => Specialize.evalMapped embedding a t) sourceSign targetSign cert)
    (accepted : Hex.SignedRemainderChain.check sourceSign p f cert = true) :
    Hex.SignedRemainderChain.check targetSign
      (polynomial (fun a => Specialize.evalMapped embedding a t) p)
      (polynomial (fun a => Specialize.evalMapped embedding a t) f)
      (chain (fun a => Specialize.evalMapped embedding a t) cert) = true := by
  classical
  exact chain_check _ (Specialize.evalMapped_zero embedding t) sourceSign targetSign p f cert
    (ChainData.of_closed _ _ (regular_closed embedding t) sourceSign targetSign p f cert hp hf
      domain head entries signs) accepted

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.regular_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.regular_closed
/-- info: 'Hex.RealClosure.Transport.chain_check_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.chain_check_regular
