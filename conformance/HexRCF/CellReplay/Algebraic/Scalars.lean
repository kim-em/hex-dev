/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.CellReplay.Algebraic.ScalarData1
/-! Shared constructor data from `conformance-fixtures/HexRCF/cell-algebraic-scalars.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Scalars
open Hex.SignDet
@[expose] def j406 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (113)) (.cons (.number (49)) .nil)))
@[expose] def j407 : Codec.Json := .array (.cons (j405) (.cons (j406) .nil))
@[expose] def p17 : Codec.Json := j407
@[expose] def j408 : Codec.Json := .array (.cons (j407) .nil)
@[expose] def j409 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-144)) (.cons (.number (113)) .nil)))
@[expose] def j410 : Codec.Json := .array (.cons (j409) (.cons (j5) .nil))
@[expose] def j411 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (113)) (.cons (.number (72)) .nil)))
@[expose] def j412 : Codec.Json := .array (.cons (j411) (.cons (j19) .nil))
@[expose] def j413 : Codec.Json := .array (.cons (j6) (.cons (j412) (.cons (j37) .nil)))
@[expose] def j414 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (288)) (.cons (.number (113)) .nil)))
@[expose] def j415 : Codec.Json := .array (.cons (j5) (.cons (j172) (.cons (j414) .nil)))
@[expose] def j416 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-113)) (.cons (.number (72)) .nil)))
@[expose] def j417 : Codec.Json := .array (.cons (j416) (.cons (j19) .nil))
@[expose] def j418 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (2401)) (.cons (.number (5184)) .nil)))
@[expose] def j419 : Codec.Json := .array (.cons (j5) (.cons (j417) (.cons (j418) .nil)))
@[expose] def j420 : Codec.Json := .array (.cons (j419) .nil)
@[expose] def j421 : Codec.Json := .array (.cons (j416) (.cons (j5) .nil))
@[expose] def j422 : Codec.Json := .array (.cons (j5) (.cons (j421) .nil))
@[expose] def j423 : Codec.Json := .array (.cons (j422) .nil)
@[expose] def j424 : Codec.Json := .array (.cons (j413) (.cons (j26) (.cons (j415) (.cons (j420) (.cons (j423) .nil)))))
@[expose] def j425 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j410) (.cons (j7) (.cons (j9) (.cons (j32) (.cons (j424) (.cons (j296) (.cons (j387) (.cons (.number (2)) (.cons (.number (1)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j426 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (23137)) (.cons (.number (16272)) .nil)))
@[expose] def j427 : Codec.Json := .array (.cons (j426) (.cons (j19) .nil))
@[expose] def j428 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-32544)) (.cons (.number (23137)) .nil)))
@[expose] def j429 : Codec.Json := .array (.cons (j428) (.cons (j5) .nil))
@[expose] def j430 : Codec.Json := .array (.cons (j6) (.cons (j429) (.cons (j23) .nil)))
@[expose] def j431 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (23137)) (.cons (.number (8136)) .nil)))
@[expose] def j432 : Codec.Json := .array (.cons (j5) (.cons (j40) (.cons (j431) .nil)))
@[expose] def j433 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (32544)) (.cons (.number (23137)) .nil)))
@[expose] def j434 : Codec.Json := .array (.cons (j433) (.cons (j5) .nil))
@[expose] def j435 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (11529602)) (.cons (.number (535320769)) .nil)))
@[expose] def j436 : Codec.Json := .array (.cons (j5) (.cons (j434) (.cons (j435) .nil)))
@[expose] def j437 : Codec.Json := .array (.cons (j436) .nil)
@[expose] def j438 : Codec.Json := .array (.cons (j5) (.cons (j429) .nil))
@[expose] def j439 : Codec.Json := .array (.cons (j438) .nil)
@[expose] def j440 : Codec.Json := .array (.cons (j430) (.cons (j26) (.cons (j432) (.cons (j437) (.cons (j439) .nil)))))
@[expose] def j441 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j427) (.cons (j7) (.cons (j9) (.cons (j32) (.cons (j440) (.cons (j152) (.cons (j34) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j442 : Codec.Json := .array (.cons (j35) (.cons (j425) (.cons (j441) .nil)))
@[expose] def j443 : Codec.Json := .array (.cons (.number (0)) (.cons (j410) (.cons (j53) .nil)))
@[expose] def j444 : Codec.Json := .array (.cons (j443) .nil)
@[expose] def j445 : Codec.Json := .array (.cons (j444) (.cons (j410) .nil))
@[expose] def j446 : Codec.Json := .array (.cons (j445) .nil)
@[expose] def j447 : Codec.Json := .array (.cons (j5) (.cons (j23) (.cons (j414) .nil)))
@[expose] def j448 : Codec.Json := .array (.cons (.number (0)) (.cons (j427) (.cons (j447) .nil)))
@[expose] def j449 : Codec.Json := .array (.cons (j443) (.cons (j448) .nil))
@[expose] def j450 : Codec.Json := .array (.cons (j449) (.cons (j427) .nil))
@[expose] def j451 : Codec.Json := .array (.cons (j450) .nil)
@[expose] def j452 : Codec.Json := .array (.cons (j52) (.cons (j446) (.cons (j451) .nil)))
@[expose] def j453 : Codec.Json := .array (.cons (j5) (.cons (j3) (.cons (j406) .nil)))
@[expose] def j454 : Codec.Json := .array (.cons (.number (0)) (.cons (j410) (.cons (j453) .nil)))
@[expose] def j455 : Codec.Json := .array (.cons (j454) .nil)
@[expose] def j456 : Codec.Json := .array (.cons (j455) .nil)
@[expose] def j457 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j7) (.cons (j9) (.cons (j408) (.cons (.number (3)) (.cons (j75) (.cons (j442) (.cons (j452) (.cons (j456) (.cons (j68) .nil)))))))))))
@[expose] def j458 : Codec.Json := .array (.cons (j457) (.cons (j3) .nil))
@[expose] def j459 : Codec.Json := .array (.cons (j458) .nil)
@[expose] def j460 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j459) .nil)))
@[expose] def g17 : Codec.Json := j460
@[expose] def p18 : Codec.Json := j37
@[expose] def j461 : Codec.Json := .array (.cons (j37) .nil)
@[expose] def j462 : Codec.Json := .array (.cons (j241) .nil)
@[expose] def j463 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j7) (.cons (j9) (.cons (j461) (.cons (.number (3)) (.cons (j22) (.cons (j239) (.cons (j247) (.cons (j462) (.cons (j68) .nil)))))))))))
@[expose] def j464 : Codec.Json := .array (.cons (j463) (.cons (j3) .nil))
@[expose] def j465 : Codec.Json := .array (.cons (j464) .nil)
@[expose] def j466 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j465) .nil)))
@[expose] def g18 : Codec.Json := j466
@[expose] def p19 : Codec.Json := j318
@[expose] def j467 : Codec.Json := .array (.cons (j318) .nil)
@[expose] def j468 : Codec.Json := .array (.cons (j338) .nil)
@[expose] def j469 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j7) (.cons (j9) (.cons (j467) (.cons (.number (3)) (.cons (j75) (.cons (j336) (.cons (j345) (.cons (j468) (.cons (j68) .nil)))))))))))
@[expose] def j470 : Codec.Json := .array (.cons (j469) (.cons (j3) .nil))
@[expose] def j471 : Codec.Json := .array (.cons (j470) .nil)
@[expose] def j472 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j471) .nil)))
@[expose] def g19 : Codec.Json := j472
@[expose] def j473 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (64)) (.cons (.number (49)) .nil)))
@[expose] def j474 : Codec.Json := .array (.cons (j405) (.cons (j473) .nil))
@[expose] def p20 : Codec.Json := j474
@[expose] def j475 : Codec.Json := .array (.cons (j474) .nil)
@[expose] def j476 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (-9)) (.cons (.number (4)) .nil)))
@[expose] def j477 : Codec.Json := .array (.cons (j476) (.cons (j5) .nil))
@[expose] def j478 : Codec.Json := .array (.cons (j97) (.cons (j19) .nil))
@[expose] def j479 : Codec.Json := .array (.cons (j6) (.cons (j478) (.cons (j23) .nil)))
@[expose] def j480 : Codec.Json := .array (.cons (j92) (.cons (j19) .nil))
@[expose] def j481 : Codec.Json := .array (.cons (j5) (.cons (j480) (.cons (j99) .nil)))
@[expose] def j482 : Codec.Json := .array (.cons (j481) .nil)
@[expose] def j483 : Codec.Json := .array (.cons (j5) (.cons (j478) .nil))
@[expose] def j484 : Codec.Json := .array (.cons (j483) .nil)
@[expose] def j485 : Codec.Json := .array (.cons (j479) (.cons (j26) (.cons (j329) (.cons (j482) (.cons (j484) .nil)))))
@[expose] def j486 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j477) (.cons (j7) (.cons (j9) (.cons (j32) (.cons (j485) (.cons (j152) (.cons (j18) (.cons (.number (1)) (.cons (.number (2)) (.cons (.number (-1)) .nil))))))))))))
@[expose] def j487 : Codec.Json := .array (.cons (j6) (.cons (j410) (.cons (j23) .nil)))
@[expose] def j488 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (113)) (.cons (.number (36)) .nil)))
@[expose] def j489 : Codec.Json := .array (.cons (j5) (.cons (j40) (.cons (j488) .nil)))
@[expose] def j490 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (144)) (.cons (.number (113)) .nil)))
@[expose] def j491 : Codec.Json := .array (.cons (j490) (.cons (j5) .nil))
@[expose] def j492 : Codec.Json := .array (.cons (.number (0)) (.cons (.number (4802)) (.cons (.number (12769)) .nil)))
@[expose] def j493 : Codec.Json := .array (.cons (j5) (.cons (j491) (.cons (j492) .nil)))
@[expose] def j494 : Codec.Json := .array (.cons (j493) .nil)
@[expose] def j495 : Codec.Json := .array (.cons (j5) (.cons (j410) .nil))
@[expose] def j496 : Codec.Json := .array (.cons (j495) .nil)
@[expose] def j497 : Codec.Json := .array (.cons (j487) (.cons (j26) (.cons (j489) (.cons (j494) (.cons (j496) .nil)))))
@[expose] def j498 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j412) (.cons (j7) (.cons (j9) (.cons (j32) (.cons (j497) (.cons (j152) (.cons (j34) (.cons (.number (1)) (.cons (.number (0)) (.cons (.number (1)) .nil))))))))))))
@[expose] def j499 : Codec.Json := .array (.cons (j35) (.cons (j486) (.cons (j498) .nil)))
@[expose] def j500 : Codec.Json := .array (.cons (.number (0)) (.cons (j477) (.cons (j53) .nil)))
@[expose] def j501 : Codec.Json := .array (.cons (j500) .nil)
@[expose] def j502 : Codec.Json := .array (.cons (j501) (.cons (j477) .nil))
@[expose] def j503 : Codec.Json := .array (.cons (j502) .nil)
@[expose] def j504 : Codec.Json := .array (.cons (j5) (.cons (j23) (.cons (j95) .nil)))
@[expose] def j505 : Codec.Json := .array (.cons (.number (0)) (.cons (j412) (.cons (j504) .nil)))
@[expose] def j506 : Codec.Json := .array (.cons (j500) (.cons (j505) .nil))
@[expose] def j507 : Codec.Json := .array (.cons (j506) (.cons (j412) .nil))
@[expose] def j508 : Codec.Json := .array (.cons (j507) .nil)
@[expose] def j509 : Codec.Json := .array (.cons (j52) (.cons (j503) (.cons (j508) .nil)))
@[expose] def j510 : Codec.Json := .array (.cons (j5) (.cons (j3) (.cons (j473) .nil)))
@[expose] def j511 : Codec.Json := .array (.cons (.number (0)) (.cons (j477) (.cons (j510) .nil)))
@[expose] def j512 : Codec.Json := .array (.cons (j511) .nil)
@[expose] def j513 : Codec.Json := .array (.cons (j512) .nil)
@[expose] def j514 : Codec.Json := .array (.cons (j4) (.cons (j6) (.cons (j7) (.cons (j9) (.cons (j475) (.cons (.number (3)) (.cons (j22) (.cons (j499) (.cons (j509) (.cons (j513) (.cons (j68) .nil)))))))))))
@[expose] def j515 : Codec.Json := .array (.cons (j514) (.cons (j3) .nil))
@[expose] def j516 : Codec.Json := .array (.cons (j515) .nil)
@[expose] def j517 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j516) .nil)))
@[expose] def g20 : Codec.Json := j517
@[expose] def s0 : Int := -1
@[expose] def s1 : Int := 1
@[expose] def s2 : Int := -1
@[expose] def s3 : Int := 1
@[expose] def s4 : Int := 1
@[expose] def s5 : Int := 1
@[expose] def s6 : Int := 1
@[expose] def s7 : Int := -1
@[expose] def s8 : Int := -1
@[expose] def s9 : Int := 1
@[expose] def s10 : Int := 1
@[expose] def s11 : Int := -1
@[expose] def s12 : Int := 1
@[expose] def s13 : Int := 1
@[expose] def s14 : Int := 1
@[expose] def s15 : Int := 1
@[expose] def s16 : Int := -1
@[expose] def s17 : Int := 1
@[expose] def s18 : Int := -1
@[expose] def s19 : Int := 1
@[expose] def s20 : Int := -1
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Scalars
