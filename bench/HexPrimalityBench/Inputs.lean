/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality

public section

/-!
Shared committed inputs for the compiled and fresh-module `HexPrimality`
evidence.  Keeping the numeral and certificate literals in one module makes
the compiled-search, native-checker, emitted-literal, and kernel-replay rows
about exactly the same subjects.
-/

namespace Hex.PrimalityBench

open Hex.Nat

/-- One prepared decision/certificate input. -/
structure Input where
  n : Nat
  cert : PrimeCert

instance : Hashable Input where
  hash i := hash i.n

instance : Inhabited Input :=
  ⟨{ n := 0, cert := .small 0 }⟩

syntax "primalityInput31" : term
macro_rules
  | `(primalityInput31) => `(2147483647)

syntax "primalityCert31" : term
macro_rules
  | `(primalityCert31) => `(
      PrimeCert.pock primalityInput31
        [(1745337962, 0, .small 2), (1371693800, 1, .small 3),
         (1615909500, 0, .small 7), (447824900, 0, .small 11),
         (505209180, 0, .small 31), (1783259301, 0, .small 151),
         (904659249, 0, .small 331)])

syntax "primalityInput61" : term
macro_rules
  | `(primalityInput61) => `(1945555039024054273)

syntax "primalityCert61" : term
macro_rules
  | `(primalityCert61) => `(
      PrimeCert.pock primalityInput61
        [(891154892214722695, 55, .small 2),
         (110189291828549774, 2, .small 3)])

syntax "primalityInput123" : term
macro_rules
  | `(primalityInput123) => `(
      9304595970494411110326649421962412033)

syntax "primalityCert123" : term
macro_rules
  | `(primalityCert123) => `(
      PrimeCert.pock primalityInput123
        [(8375418187094998941197481872780801521, 119, .small 2),
         (2334070614962599841175388035625407872, 0, .small 7)])

syntax "primalityInput256" : term
macro_rules
  | `(primalityInput256) => `(
      93628759656736142393278101159368737990730026663232799828780155818898507169793)

syntax "primalityCert256" : term
macro_rules
  | `(primalityCert256) => `(
      PrimeCert.pock primalityInput256
        [(70102889390480215286190462442272203759457993577913958689719049669831137574314,
          247, .small 2),
         (60567041566416165658629609816966423895929815708915610491013996188378972927419,
          1, .small 3),
         (51453282114745919379037361758174092241783747333697980824233239301771023768771,
          0, .small 23)])

syntax "primalityInput511" : term
macro_rules
  | `(primalityInput511) => `(
      6651529715244960279866801463953681477304216637559507652230048059971343874294298695522804827606237247330601742147202064290729465301239118684363568061612033)

syntax "primalityCert511" : term
macro_rules
  | `(primalityCert511) => `(
      PrimeCert.pock primalityInput511
        [(2239573051976556212429805419451130451126765006769691640728432847107576893355820385883842286449386148068226313441781843443755213748667373444276605719297450,
          503, .small 2),
         (361654566653739657719147609952455388585247661996028660739245117267353205916198882954554789957254100628591547381090477139597531806551073551582980034682053,
          0, .small 127)])

syntax "primalityInput512" : term
macro_rules
  | `(primalityInput512) => `(
      9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177)

syntax "primalityCert512" : term
macro_rules
  | `(primalityCert512) => `(
      PrimeCert.pock primalityInput512
        [(5725334873067516210622658404270170843764033167110427111354730336291337041845265706524167852273766778719360247071825913712081694748404477146881674699739816,
          145, .small 2),
         (8059057580615090739532488458632536876401511056127662222492008527682579453301543518398857348057566564348657218922698474668680611445015448088465605353064230,
          21,
          .pock 100297
            [(93203, 2, .small 2), (87617, 1, .small 3),
             (51846, 0, .small 7), (44354, 0, .small 199)])])

/-- The table-smooth certificate ladder used for two-sided scientific runs. -/
def smoothSizeParams : Array Nat := #[31, 61, 123, 256, 511]

/-- The full declared certificate-size family, including the rho-backed
exact policy boundary. -/
def sizeParams : Array Nat := #[31, 61, 123, 256, 511, 512]

/-- Map a bit-size rung to its exact committed subject and certificate. -/
def prepInput (bits : Nat) : Input :=
  if bits ≤ 31 then { n := primalityInput31, cert := primalityCert31 }
  else if bits ≤ 61 then { n := primalityInput61, cert := primalityCert61 }
  else if bits ≤ 123 then { n := primalityInput123, cert := primalityCert123 }
  else if bits ≤ 256 then { n := primalityInput256, cert := primalityCert256 }
  else if bits ≤ 511 then { n := primalityInput511, cert := primalityCert511 }
  else { n := primalityInput512, cert := primalityCert512 }

#guard sizeParams.all fun bits =>
  let input := prepInput bits
  checkPrime input.cert && input.cert.subject == input.n

end Hex.PrimalityBench
