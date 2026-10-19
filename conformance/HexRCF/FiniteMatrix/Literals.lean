/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Codec.Json
public import HexRCF.FiniteMatrix.LiteralData5
/-! Shared constructor data from `conformance-fixtures/HexRCF/finite-matrix.json`.
The descriptor reader checks this supplied replay independently of its producer. -/
public section

namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Literals
open Hex.SignDet
@[expose] def j1494 : Codec.Json := .array (.cons (j367) (.cons (j1068) (.cons (j1493) .nil)))
@[expose] def j1495 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1494) .nil)))
@[expose] def j1496 : Codec.Json := .array (.cons (j19) (.cons (j19) (.cons (.number (-1)) (.cons (j369) (.cons (j1495) .nil)))))
@[expose] def packing33 : Codec.Json := j1496
@[expose] def j1497 : Codec.Json := .array (.cons (j43) (.cons (j4) .nil))
@[expose] def j1498 : Codec.Json := .array (.cons (j379) (.cons (j1072) .nil))
@[expose] def j1499 : Codec.Json := .array (.cons (j1498) .nil)
@[expose] def j1500 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1497) (.cons (.number (1)) (.cons (j248) (.cons (j1070) (.cons (j1071) (.cons (j1499) (.cons (j72) .nil)))))))))))
@[expose] def j1501 : Codec.Json := .array (.cons (j1500) (.cons (j253) .nil))
@[expose] def j1502 : Codec.Json := .array (.cons (j389) (.cons (j1068) (.cons (j1501) .nil)))
@[expose] def j1503 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1502) .nil)))
@[expose] def j1504 : Codec.Json := .array (.cons (j43) (.cons (j43) (.cons (.number (1)) (.cons (j391) (.cons (j1503) .nil)))))
@[expose] def packing34 : Codec.Json := j1504
@[expose] def j1505 : Codec.Json := .array (.cons (j604) (.cons (j4) .nil))
@[expose] def j1506 : Codec.Json := .array (.cons (j1015) (.cons (j1072) .nil))
@[expose] def j1507 : Codec.Json := .array (.cons (j1506) .nil)
@[expose] def j1508 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1505) (.cons (.number (1)) (.cons (j248) (.cons (j1070) (.cons (j1071) (.cons (j1507) (.cons (j72) .nil)))))))))))
@[expose] def j1509 : Codec.Json := .array (.cons (j1508) (.cons (j253) .nil))
@[expose] def j1510 : Codec.Json := .array (.cons (j1025) (.cons (j1068) (.cons (j1509) .nil)))
@[expose] def j1511 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1510) .nil)))
@[expose] def j1512 : Codec.Json := .array (.cons (j604) (.cons (j604) (.cons (.number (1)) (.cons (j1027) (.cons (j1511) .nil)))))
@[expose] def packing35 : Codec.Json := j1512
@[expose] def j1513 : Codec.Json := .array (.cons (j142) (.cons (j4) .nil))
@[expose] def j1514 : Codec.Json := .array (.cons (j586) (.cons (j1072) .nil))
@[expose] def j1515 : Codec.Json := .array (.cons (j1514) .nil)
@[expose] def j1516 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1513) (.cons (.number (1)) (.cons (j248) (.cons (j1070) (.cons (j1071) (.cons (j1515) (.cons (j72) .nil)))))))))))
@[expose] def j1517 : Codec.Json := .array (.cons (j1516) (.cons (j253) .nil))
@[expose] def j1518 : Codec.Json := .array (.cons (j590) (.cons (j1068) (.cons (j1517) .nil)))
@[expose] def j1519 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1518) .nil)))
@[expose] def j1520 : Codec.Json := .array (.cons (j142) (.cons (j142) (.cons (.number (1)) (.cons (j592) (.cons (j1519) .nil)))))
@[expose] def packing36 : Codec.Json := j1520
@[expose] def j1521 : Codec.Json := .array (.cons (j11) (.cons (j4) .nil))
@[expose] def j1522 : Codec.Json := .array (.cons (j331) (.cons (j1072) .nil))
@[expose] def j1523 : Codec.Json := .array (.cons (j1522) .nil)
@[expose] def j1524 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1521) (.cons (.number (1)) (.cons (j248) (.cons (j1070) (.cons (j1071) (.cons (j1523) (.cons (j72) .nil)))))))))))
@[expose] def j1525 : Codec.Json := .array (.cons (j1524) (.cons (j253) .nil))
@[expose] def j1526 : Codec.Json := .array (.cons (j335) (.cons (j1068) (.cons (j1525) .nil)))
@[expose] def j1527 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1526) .nil)))
@[expose] def j1528 : Codec.Json := .array (.cons (j11) (.cons (j11) (.cons (.number (1)) (.cons (j337) (.cons (j1527) .nil)))))
@[expose] def packing37 : Codec.Json := j1528
@[expose] def j1529 : Codec.Json := .array (.cons (j478) (.cons (j4) .nil))
@[expose] def j1530 : Codec.Json := .array (.cons (j1039) (.cons (j1072) .nil))
@[expose] def j1531 : Codec.Json := .array (.cons (j1530) .nil)
@[expose] def j1532 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1529) (.cons (.number (1)) (.cons (j1091) (.cons (j1070) (.cons (j1071) (.cons (j1531) (.cons (j72) .nil)))))))))))
@[expose] def j1533 : Codec.Json := .array (.cons (j1532) (.cons (j253) .nil))
@[expose] def j1534 : Codec.Json := .array (.cons (j1049) (.cons (j1068) (.cons (j1533) .nil)))
@[expose] def j1535 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1534) .nil)))
@[expose] def j1536 : Codec.Json := .array (.cons (j478) (.cons (j478) (.cons (.number (-1)) (.cons (j1051) (.cons (j1535) .nil)))))
@[expose] def packing38 : Codec.Json := j1536
@[expose] def j1537 : Codec.Json := .array (.cons (j15) (.cons (j4) .nil))
@[expose] def j1538 : Codec.Json := .array (.cons (j348) (.cons (j1072) .nil))
@[expose] def j1539 : Codec.Json := .array (.cons (j1538) .nil)
@[expose] def j1540 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1537) (.cons (.number (1)) (.cons (j1091) (.cons (j1070) (.cons (j1071) (.cons (j1539) (.cons (j72) .nil)))))))))))
@[expose] def j1541 : Codec.Json := .array (.cons (j1540) (.cons (j253) .nil))
@[expose] def j1542 : Codec.Json := .array (.cons (j358) (.cons (j1068) (.cons (j1541) .nil)))
@[expose] def j1543 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1542) .nil)))
@[expose] def j1544 : Codec.Json := .array (.cons (j15) (.cons (j15) (.cons (.number (-1)) (.cons (j360) (.cons (j1543) .nil)))))
@[expose] def packing39 : Codec.Json := j1544
@[expose] def j1545 : Codec.Json := .array (.cons (j2) (.cons (j4) .nil))
@[expose] def j1546 : Codec.Json := .array (.cons (j298) (.cons (j1072) .nil))
@[expose] def j1547 : Codec.Json := .array (.cons (j1546) .nil)
@[expose] def j1548 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1545) (.cons (.number (1)) (.cons (j1091) (.cons (j1070) (.cons (j1071) (.cons (j1547) (.cons (j72) .nil)))))))))))
@[expose] def j1549 : Codec.Json := .array (.cons (j1548) (.cons (j253) .nil))
@[expose] def j1550 : Codec.Json := .array (.cons (j310) (.cons (j1068) (.cons (j1549) .nil)))
@[expose] def j1551 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1550) .nil)))
@[expose] def j1552 : Codec.Json := .array (.cons (j2) (.cons (j2) (.cons (.number (-1)) (.cons (j312) (.cons (j1551) .nil)))))
@[expose] def packing40 : Codec.Json := j1552
@[expose] def j1553 : Codec.Json := .array (.cons (j1068) .nil)
@[expose] def j1554 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (0)) (.cons (j1553) .nil)))
@[expose] def j1555 : Codec.Json := .array (.cons (j4) (.cons (j4) .nil))
@[expose] def j1556 : Codec.Json := .array (.cons (j201) (.cons (j201) (.cons (j26) (.cons (j26) (.cons (j71) (.cons (.number (1)) .nil))))))
@[expose] def j1557 : Codec.Json := .array (.cons (j1058) (.cons (j1072) .nil))
@[expose] def j1558 : Codec.Json := .array (.cons (j1557) .nil)
@[expose] def j1559 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1555) (.cons (.number (1)) (.cons (j1556) (.cons (j1070) (.cons (j1071) (.cons (j1558) (.cons (j72) .nil)))))))))))
@[expose] def j1560 : Codec.Json := .array (.cons (j1559) (.cons (j201) .nil))
@[expose] def j1561 : Codec.Json := .array (.cons (j1068) (.cons (j1560) .nil))
@[expose] def j1562 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (1)) (.cons (j1561) .nil)))
@[expose] def j1563 : Codec.Json := .array (.cons (j4) (.cons (j4) (.cons (.number (0)) (.cons (j1554) (.cons (j1562) .nil)))))
@[expose] def packing41 : Codec.Json := j1563
@[expose] def j1564 : Codec.Json := .array (.cons (j6) (.cons (j4) .nil))
@[expose] def j1565 : Codec.Json := .array (.cons (j316) (.cons (j1072) .nil))
@[expose] def j1566 : Codec.Json := .array (.cons (j1565) .nil)
@[expose] def j1567 : Codec.Json := .array (.cons (.number (7)) (.cons (j273) (.cons (j274) (.cons (j275) (.cons (j1564) (.cons (.number (1)) (.cons (j248) (.cons (j1070) (.cons (j1071) (.cons (j1566) (.cons (j72) .nil)))))))))))
@[expose] def j1568 : Codec.Json := .array (.cons (j1567) (.cons (j253) .nil))
@[expose] def j1569 : Codec.Json := .array (.cons (j326) (.cons (j1068) (.cons (j1568) .nil)))
@[expose] def j1570 : Codec.Json := .array (.cons (.number (1)) (.cons (.number (2)) (.cons (j1569) .nil)))
@[expose] def j1571 : Codec.Json := .array (.cons (j6) (.cons (j6) (.cons (.number (1)) (.cons (j328) (.cons (j1570) .nil)))))
@[expose] def packing42 : Codec.Json := j1571
@[expose] def j1572 : Codec.Json := .array (.cons (j792) (.cons (.number (1)) .nil))
@[expose] def j1573 : Codec.Json := .array (.cons (j1572) (.cons (j823) .nil))
@[expose] def sign0 : Codec.Json := j1573
@[expose] def j1574 : Codec.Json := .array (.cons (j826) (.cons (.number (-1)) .nil))
@[expose] def j1575 : Codec.Json := .array (.cons (j1574) (.cons (j878) .nil))
@[expose] def sign1 : Codec.Json := j1575
@[expose] def j1576 : Codec.Json := .array (.cons (j178) (.cons (j789) .nil))
@[expose] def sign2 : Codec.Json := j1576
@[expose] def j1577 : Codec.Json := .array (.cons (j168) (.cons (j726) .nil))
@[expose] def sign3 : Codec.Json := j1577
@[expose] def j1578 : Codec.Json := .array (.cons (j880) (.cons (.number (-1)) .nil))
@[expose] def j1579 : Codec.Json := .array (.cons (j1578) (.cons (j906) .nil))
@[expose] def sign4 : Codec.Json := j1579
@[expose] def j1580 : Codec.Json := .array (.cons (j908) (.cons (.number (-1)) .nil))
@[expose] def j1581 : Codec.Json := .array (.cons (j1580) (.cons (j916) .nil))
@[expose] def sign5 : Codec.Json := j1581
@[expose] def j1582 : Codec.Json := .array (.cons (j150) (.cons (j647) .nil))
@[expose] def sign6 : Codec.Json := j1582
@[expose] def j1583 : Codec.Json := .array (.cons (j143) (.cons (j592) .nil))
@[expose] def sign7 : Codec.Json := j1583
@[expose] def j1584 : Codec.Json := .array (.cons (j918) (.cons (.number (1)) .nil))
@[expose] def j1585 : Codec.Json := .array (.cons (j1584) (.cons (j944) .nil))
@[expose] def sign8 : Codec.Json := j1585
@[expose] def j1586 : Codec.Json := .array (.cons (j947) (.cons (.number (-1)) .nil))
@[expose] def j1587 : Codec.Json := .array (.cons (j1586) (.cons (j989) .nil))
@[expose] def sign9 : Codec.Json := j1587
@[expose] def j1588 : Codec.Json := .array (.cons (j114) (.cons (j573) .nil))
@[expose] def sign10 : Codec.Json := j1588
@[expose] def j1589 : Codec.Json := .array (.cons (j105) (.cons (j509) .nil))
@[expose] def sign11 : Codec.Json := j1589
@[expose] def j1590 : Codec.Json := .array (.cons (j440) (.cons (.number (-1)) .nil))
@[expose] def j1591 : Codec.Json := .array (.cons (j1590) (.cons (j996) .nil))
@[expose] def sign12 : Codec.Json := j1591
@[expose] def j1592 : Codec.Json := .array (.cons (j394) (.cons (.number (1)) .nil))
@[expose] def j1593 : Codec.Json := .array (.cons (j1592) (.cons (j1003) .nil))
@[expose] def sign13 : Codec.Json := j1593
@[expose] def j1594 : Codec.Json := .array (.cons (j85) (.cons (j434) .nil))
@[expose] def sign14 : Codec.Json := j1594
@[expose] def j1595 : Codec.Json := .array (.cons (j44) (.cons (j391) .nil))
@[expose] def sign15 : Codec.Json := j1595
@[expose] def j1596 : Codec.Json := .array (.cons (j12) (.cons (j337) .nil))
@[expose] def sign16 : Codec.Json := j1596
@[expose] def j1597 : Codec.Json := .array (.cons (j604) (.cons (.number (1)) .nil))
@[expose] def j1598 : Codec.Json := .array (.cons (j1597) (.cons (j1027) .nil))
@[expose] def sign17 : Codec.Json := j1598
@[expose] def j1599 : Codec.Json := .array (.cons (j478) (.cons (.number (-1)) .nil))
@[expose] def j1600 : Codec.Json := .array (.cons (j1599) (.cons (j1051) .nil))
@[expose] def sign18 : Codec.Json := j1600
@[expose] def j1601 : Codec.Json := .array (.cons (j16) (.cons (j360) .nil))
@[expose] def sign19 : Codec.Json := j1601
@[expose] def j1602 : Codec.Json := .array (.cons (j7) (.cons (j328) .nil))
@[expose] def sign20 : Codec.Json := j1602
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Literals
