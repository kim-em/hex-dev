/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFq.Entry

public section

namespace Hex.GFq

/-- Instance-selected field for C(101, 1). -/
instance committedEntry_101_1 : CommittedEntry 101 1 where
  entry := Hex.Conway.supportedEntry_101_1

/-- Instance-selected field for C(101, 2). -/
instance committedEntry_101_2 : CommittedEntry 101 2 where
  entry := Hex.Conway.supportedEntry_101_2

/-- Instance-selected field for C(101, 3). -/
instance committedEntry_101_3 : CommittedEntry 101 3 where
  entry := Hex.Conway.supportedEntry_101_3

/-- Instance-selected field for C(101, 4). -/
instance committedEntry_101_4 : CommittedEntry 101 4 where
  entry := Hex.Conway.supportedEntry_101_4

/-- Instance-selected field for C(103, 1). -/
instance committedEntry_103_1 : CommittedEntry 103 1 where
  entry := Hex.Conway.supportedEntry_103_1

/-- Instance-selected field for C(103, 2). -/
instance committedEntry_103_2 : CommittedEntry 103 2 where
  entry := Hex.Conway.supportedEntry_103_2

/-- Instance-selected field for C(103, 3). -/
instance committedEntry_103_3 : CommittedEntry 103 3 where
  entry := Hex.Conway.supportedEntry_103_3

/-- Instance-selected field for C(103, 4). -/
instance committedEntry_103_4 : CommittedEntry 103 4 where
  entry := Hex.Conway.supportedEntry_103_4

/-- Instance-selected field for C(107, 1). -/
instance committedEntry_107_1 : CommittedEntry 107 1 where
  entry := Hex.Conway.supportedEntry_107_1

/-- Instance-selected field for C(107, 2). -/
instance committedEntry_107_2 : CommittedEntry 107 2 where
  entry := Hex.Conway.supportedEntry_107_2

/-- Instance-selected field for C(107, 3). -/
instance committedEntry_107_3 : CommittedEntry 107 3 where
  entry := Hex.Conway.supportedEntry_107_3

/-- Instance-selected field for C(107, 4). -/
instance committedEntry_107_4 : CommittedEntry 107 4 where
  entry := Hex.Conway.supportedEntry_107_4

/-- Instance-selected field for C(109, 1). -/
instance committedEntry_109_1 : CommittedEntry 109 1 where
  entry := Hex.Conway.supportedEntry_109_1

/-- Instance-selected field for C(109, 2). -/
instance committedEntry_109_2 : CommittedEntry 109 2 where
  entry := Hex.Conway.supportedEntry_109_2

/-- Instance-selected field for C(109, 3). -/
instance committedEntry_109_3 : CommittedEntry 109 3 where
  entry := Hex.Conway.supportedEntry_109_3

/-- Instance-selected field for C(109, 4). -/
instance committedEntry_109_4 : CommittedEntry 109 4 where
  entry := Hex.Conway.supportedEntry_109_4

/-- Instance-selected field for C(113, 1). -/
instance committedEntry_113_1 : CommittedEntry 113 1 where
  entry := Hex.Conway.supportedEntry_113_1

/-- Instance-selected field for C(113, 2). -/
instance committedEntry_113_2 : CommittedEntry 113 2 where
  entry := Hex.Conway.supportedEntry_113_2

/-- Instance-selected field for C(113, 3). -/
instance committedEntry_113_3 : CommittedEntry 113 3 where
  entry := Hex.Conway.supportedEntry_113_3

/-- Instance-selected field for C(113, 4). -/
instance committedEntry_113_4 : CommittedEntry 113 4 where
  entry := Hex.Conway.supportedEntry_113_4

/-- Instance-selected field for C(127, 1). -/
instance committedEntry_127_1 : CommittedEntry 127 1 where
  entry := Hex.Conway.supportedEntry_127_1

/-- Instance-selected field for C(127, 2). -/
instance committedEntry_127_2 : CommittedEntry 127 2 where
  entry := Hex.Conway.supportedEntry_127_2

/-- Instance-selected field for C(127, 3). -/
instance committedEntry_127_3 : CommittedEntry 127 3 where
  entry := Hex.Conway.supportedEntry_127_3

/-- Instance-selected field for C(127, 4). -/
instance committedEntry_127_4 : CommittedEntry 127 4 where
  entry := Hex.Conway.supportedEntry_127_4

/-- Instance-selected field for C(131, 1). -/
instance committedEntry_131_1 : CommittedEntry 131 1 where
  entry := Hex.Conway.supportedEntry_131_1

/-- Instance-selected field for C(131, 2). -/
instance committedEntry_131_2 : CommittedEntry 131 2 where
  entry := Hex.Conway.supportedEntry_131_2

/-- Instance-selected field for C(131, 3). -/
instance committedEntry_131_3 : CommittedEntry 131 3 where
  entry := Hex.Conway.supportedEntry_131_3

/-- Instance-selected field for C(131, 4). -/
instance committedEntry_131_4 : CommittedEntry 131 4 where
  entry := Hex.Conway.supportedEntry_131_4

/-- Instance-selected field for C(137, 1). -/
instance committedEntry_137_1 : CommittedEntry 137 1 where
  entry := Hex.Conway.supportedEntry_137_1

/-- Instance-selected field for C(137, 2). -/
instance committedEntry_137_2 : CommittedEntry 137 2 where
  entry := Hex.Conway.supportedEntry_137_2

/-- Instance-selected field for C(137, 3). -/
instance committedEntry_137_3 : CommittedEntry 137 3 where
  entry := Hex.Conway.supportedEntry_137_3

/-- Instance-selected field for C(137, 4). -/
instance committedEntry_137_4 : CommittedEntry 137 4 where
  entry := Hex.Conway.supportedEntry_137_4

/-- Instance-selected field for C(139, 1). -/
instance committedEntry_139_1 : CommittedEntry 139 1 where
  entry := Hex.Conway.supportedEntry_139_1

/-- Instance-selected field for C(139, 2). -/
instance committedEntry_139_2 : CommittedEntry 139 2 where
  entry := Hex.Conway.supportedEntry_139_2

/-- Instance-selected field for C(139, 3). -/
instance committedEntry_139_3 : CommittedEntry 139 3 where
  entry := Hex.Conway.supportedEntry_139_3

/-- Instance-selected field for C(139, 4). -/
instance committedEntry_139_4 : CommittedEntry 139 4 where
  entry := Hex.Conway.supportedEntry_139_4

/-- Instance-selected field for C(149, 1). -/
instance committedEntry_149_1 : CommittedEntry 149 1 where
  entry := Hex.Conway.supportedEntry_149_1

/-- Instance-selected field for C(149, 2). -/
instance committedEntry_149_2 : CommittedEntry 149 2 where
  entry := Hex.Conway.supportedEntry_149_2

/-- Instance-selected field for C(149, 3). -/
instance committedEntry_149_3 : CommittedEntry 149 3 where
  entry := Hex.Conway.supportedEntry_149_3

/-- Instance-selected field for C(149, 4). -/
instance committedEntry_149_4 : CommittedEntry 149 4 where
  entry := Hex.Conway.supportedEntry_149_4

/-- Instance-selected field for C(151, 1). -/
instance committedEntry_151_1 : CommittedEntry 151 1 where
  entry := Hex.Conway.supportedEntry_151_1

/-- Instance-selected field for C(151, 2). -/
instance committedEntry_151_2 : CommittedEntry 151 2 where
  entry := Hex.Conway.supportedEntry_151_2

/-- Instance-selected field for C(151, 3). -/
instance committedEntry_151_3 : CommittedEntry 151 3 where
  entry := Hex.Conway.supportedEntry_151_3

/-- Instance-selected field for C(151, 4). -/
instance committedEntry_151_4 : CommittedEntry 151 4 where
  entry := Hex.Conway.supportedEntry_151_4

/-- Instance-selected field for C(157, 1). -/
instance committedEntry_157_1 : CommittedEntry 157 1 where
  entry := Hex.Conway.supportedEntry_157_1

/-- Instance-selected field for C(157, 2). -/
instance committedEntry_157_2 : CommittedEntry 157 2 where
  entry := Hex.Conway.supportedEntry_157_2

/-- Instance-selected field for C(157, 3). -/
instance committedEntry_157_3 : CommittedEntry 157 3 where
  entry := Hex.Conway.supportedEntry_157_3

/-- Instance-selected field for C(157, 4). -/
instance committedEntry_157_4 : CommittedEntry 157 4 where
  entry := Hex.Conway.supportedEntry_157_4

/-- Instance-selected field for C(163, 1). -/
instance committedEntry_163_1 : CommittedEntry 163 1 where
  entry := Hex.Conway.supportedEntry_163_1

/-- Instance-selected field for C(163, 2). -/
instance committedEntry_163_2 : CommittedEntry 163 2 where
  entry := Hex.Conway.supportedEntry_163_2

/-- Instance-selected field for C(163, 3). -/
instance committedEntry_163_3 : CommittedEntry 163 3 where
  entry := Hex.Conway.supportedEntry_163_3

/-- Instance-selected field for C(163, 4). -/
instance committedEntry_163_4 : CommittedEntry 163 4 where
  entry := Hex.Conway.supportedEntry_163_4

/-- Instance-selected field for C(167, 1). -/
instance committedEntry_167_1 : CommittedEntry 167 1 where
  entry := Hex.Conway.supportedEntry_167_1

/-- Instance-selected field for C(167, 2). -/
instance committedEntry_167_2 : CommittedEntry 167 2 where
  entry := Hex.Conway.supportedEntry_167_2

/-- Instance-selected field for C(167, 3). -/
instance committedEntry_167_3 : CommittedEntry 167 3 where
  entry := Hex.Conway.supportedEntry_167_3

/-- Instance-selected field for C(167, 4). -/
instance committedEntry_167_4 : CommittedEntry 167 4 where
  entry := Hex.Conway.supportedEntry_167_4

/-- Instance-selected field for C(173, 1). -/
instance committedEntry_173_1 : CommittedEntry 173 1 where
  entry := Hex.Conway.supportedEntry_173_1

/-- Instance-selected field for C(173, 2). -/
instance committedEntry_173_2 : CommittedEntry 173 2 where
  entry := Hex.Conway.supportedEntry_173_2

/-- Instance-selected field for C(173, 3). -/
instance committedEntry_173_3 : CommittedEntry 173 3 where
  entry := Hex.Conway.supportedEntry_173_3

/-- Instance-selected field for C(173, 4). -/
instance committedEntry_173_4 : CommittedEntry 173 4 where
  entry := Hex.Conway.supportedEntry_173_4

/-- Instance-selected field for C(179, 1). -/
instance committedEntry_179_1 : CommittedEntry 179 1 where
  entry := Hex.Conway.supportedEntry_179_1

/-- Instance-selected field for C(179, 2). -/
instance committedEntry_179_2 : CommittedEntry 179 2 where
  entry := Hex.Conway.supportedEntry_179_2

/-- Instance-selected field for C(179, 3). -/
instance committedEntry_179_3 : CommittedEntry 179 3 where
  entry := Hex.Conway.supportedEntry_179_3

/-- Instance-selected field for C(179, 4). -/
instance committedEntry_179_4 : CommittedEntry 179 4 where
  entry := Hex.Conway.supportedEntry_179_4

/-- Instance-selected field for C(181, 1). -/
instance committedEntry_181_1 : CommittedEntry 181 1 where
  entry := Hex.Conway.supportedEntry_181_1

/-- Instance-selected field for C(181, 2). -/
instance committedEntry_181_2 : CommittedEntry 181 2 where
  entry := Hex.Conway.supportedEntry_181_2

/-- Instance-selected field for C(181, 3). -/
instance committedEntry_181_3 : CommittedEntry 181 3 where
  entry := Hex.Conway.supportedEntry_181_3

/-- Instance-selected field for C(181, 4). -/
instance committedEntry_181_4 : CommittedEntry 181 4 where
  entry := Hex.Conway.supportedEntry_181_4

/-- Instance-selected field for C(191, 1). -/
instance committedEntry_191_1 : CommittedEntry 191 1 where
  entry := Hex.Conway.supportedEntry_191_1

/-- Instance-selected field for C(191, 2). -/
instance committedEntry_191_2 : CommittedEntry 191 2 where
  entry := Hex.Conway.supportedEntry_191_2

/-- Instance-selected field for C(191, 3). -/
instance committedEntry_191_3 : CommittedEntry 191 3 where
  entry := Hex.Conway.supportedEntry_191_3

/-- Instance-selected field for C(191, 4). -/
instance committedEntry_191_4 : CommittedEntry 191 4 where
  entry := Hex.Conway.supportedEntry_191_4

/-- Instance-selected field for C(193, 1). -/
instance committedEntry_193_1 : CommittedEntry 193 1 where
  entry := Hex.Conway.supportedEntry_193_1

/-- Instance-selected field for C(193, 2). -/
instance committedEntry_193_2 : CommittedEntry 193 2 where
  entry := Hex.Conway.supportedEntry_193_2

/-- Instance-selected field for C(193, 3). -/
instance committedEntry_193_3 : CommittedEntry 193 3 where
  entry := Hex.Conway.supportedEntry_193_3

/-- Instance-selected field for C(193, 4). -/
instance committedEntry_193_4 : CommittedEntry 193 4 where
  entry := Hex.Conway.supportedEntry_193_4

/-- Instance-selected field for C(197, 1). -/
instance committedEntry_197_1 : CommittedEntry 197 1 where
  entry := Hex.Conway.supportedEntry_197_1

/-- Instance-selected field for C(197, 2). -/
instance committedEntry_197_2 : CommittedEntry 197 2 where
  entry := Hex.Conway.supportedEntry_197_2

/-- Instance-selected field for C(197, 3). -/
instance committedEntry_197_3 : CommittedEntry 197 3 where
  entry := Hex.Conway.supportedEntry_197_3

/-- Instance-selected field for C(197, 4). -/
instance committedEntry_197_4 : CommittedEntry 197 4 where
  entry := Hex.Conway.supportedEntry_197_4

/-- Instance-selected field for C(199, 1). -/
instance committedEntry_199_1 : CommittedEntry 199 1 where
  entry := Hex.Conway.supportedEntry_199_1

/-- Instance-selected field for C(199, 2). -/
instance committedEntry_199_2 : CommittedEntry 199 2 where
  entry := Hex.Conway.supportedEntry_199_2

/-- Instance-selected field for C(199, 3). -/
instance committedEntry_199_3 : CommittedEntry 199 3 where
  entry := Hex.Conway.supportedEntry_199_3

/-- Instance-selected field for C(199, 4). -/
instance committedEntry_199_4 : CommittedEntry 199 4 where
  entry := Hex.Conway.supportedEntry_199_4

/-- Instance-selected field for C(211, 1). -/
instance committedEntry_211_1 : CommittedEntry 211 1 where
  entry := Hex.Conway.supportedEntry_211_1

/-- Instance-selected field for C(211, 2). -/
instance committedEntry_211_2 : CommittedEntry 211 2 where
  entry := Hex.Conway.supportedEntry_211_2

/-- Instance-selected field for C(211, 3). -/
instance committedEntry_211_3 : CommittedEntry 211 3 where
  entry := Hex.Conway.supportedEntry_211_3

/-- Instance-selected field for C(211, 4). -/
instance committedEntry_211_4 : CommittedEntry 211 4 where
  entry := Hex.Conway.supportedEntry_211_4

/-- Instance-selected field for C(223, 1). -/
instance committedEntry_223_1 : CommittedEntry 223 1 where
  entry := Hex.Conway.supportedEntry_223_1

/-- Instance-selected field for C(223, 2). -/
instance committedEntry_223_2 : CommittedEntry 223 2 where
  entry := Hex.Conway.supportedEntry_223_2

/-- Instance-selected field for C(223, 3). -/
instance committedEntry_223_3 : CommittedEntry 223 3 where
  entry := Hex.Conway.supportedEntry_223_3

/-- Instance-selected field for C(223, 4). -/
instance committedEntry_223_4 : CommittedEntry 223 4 where
  entry := Hex.Conway.supportedEntry_223_4

/-- Instance-selected field for C(227, 1). -/
instance committedEntry_227_1 : CommittedEntry 227 1 where
  entry := Hex.Conway.supportedEntry_227_1

/-- Instance-selected field for C(227, 2). -/
instance committedEntry_227_2 : CommittedEntry 227 2 where
  entry := Hex.Conway.supportedEntry_227_2

/-- Instance-selected field for C(227, 3). -/
instance committedEntry_227_3 : CommittedEntry 227 3 where
  entry := Hex.Conway.supportedEntry_227_3

/-- Instance-selected field for C(227, 4). -/
instance committedEntry_227_4 : CommittedEntry 227 4 where
  entry := Hex.Conway.supportedEntry_227_4

/-- Instance-selected field for C(229, 1). -/
instance committedEntry_229_1 : CommittedEntry 229 1 where
  entry := Hex.Conway.supportedEntry_229_1

/-- Instance-selected field for C(229, 2). -/
instance committedEntry_229_2 : CommittedEntry 229 2 where
  entry := Hex.Conway.supportedEntry_229_2

/-- Instance-selected field for C(229, 3). -/
instance committedEntry_229_3 : CommittedEntry 229 3 where
  entry := Hex.Conway.supportedEntry_229_3

/-- Instance-selected field for C(229, 4). -/
instance committedEntry_229_4 : CommittedEntry 229 4 where
  entry := Hex.Conway.supportedEntry_229_4

/-- Instance-selected field for C(233, 1). -/
instance committedEntry_233_1 : CommittedEntry 233 1 where
  entry := Hex.Conway.supportedEntry_233_1

/-- Instance-selected field for C(233, 2). -/
instance committedEntry_233_2 : CommittedEntry 233 2 where
  entry := Hex.Conway.supportedEntry_233_2

/-- Instance-selected field for C(233, 3). -/
instance committedEntry_233_3 : CommittedEntry 233 3 where
  entry := Hex.Conway.supportedEntry_233_3

/-- Instance-selected field for C(233, 4). -/
instance committedEntry_233_4 : CommittedEntry 233 4 where
  entry := Hex.Conway.supportedEntry_233_4

/-- Instance-selected field for C(239, 1). -/
instance committedEntry_239_1 : CommittedEntry 239 1 where
  entry := Hex.Conway.supportedEntry_239_1

/-- Instance-selected field for C(239, 2). -/
instance committedEntry_239_2 : CommittedEntry 239 2 where
  entry := Hex.Conway.supportedEntry_239_2

/-- Instance-selected field for C(239, 3). -/
instance committedEntry_239_3 : CommittedEntry 239 3 where
  entry := Hex.Conway.supportedEntry_239_3

/-- Instance-selected field for C(239, 4). -/
instance committedEntry_239_4 : CommittedEntry 239 4 where
  entry := Hex.Conway.supportedEntry_239_4

/-- Instance-selected field for C(241, 1). -/
instance committedEntry_241_1 : CommittedEntry 241 1 where
  entry := Hex.Conway.supportedEntry_241_1

/-- Instance-selected field for C(241, 2). -/
instance committedEntry_241_2 : CommittedEntry 241 2 where
  entry := Hex.Conway.supportedEntry_241_2

/-- Instance-selected field for C(241, 3). -/
instance committedEntry_241_3 : CommittedEntry 241 3 where
  entry := Hex.Conway.supportedEntry_241_3

/-- Instance-selected field for C(241, 4). -/
instance committedEntry_241_4 : CommittedEntry 241 4 where
  entry := Hex.Conway.supportedEntry_241_4

/-- Instance-selected field for C(251, 1). -/
instance committedEntry_251_1 : CommittedEntry 251 1 where
  entry := Hex.Conway.supportedEntry_251_1

/-- Instance-selected field for C(251, 2). -/
instance committedEntry_251_2 : CommittedEntry 251 2 where
  entry := Hex.Conway.supportedEntry_251_2

/-- Instance-selected field for C(251, 3). -/
instance committedEntry_251_3 : CommittedEntry 251 3 where
  entry := Hex.Conway.supportedEntry_251_3

/-- Instance-selected field for C(251, 4). -/
instance committedEntry_251_4 : CommittedEntry 251 4 where
  entry := Hex.Conway.supportedEntry_251_4

/-- Instance-selected field for C(257, 1). -/
instance committedEntry_257_1 : CommittedEntry 257 1 where
  entry := Hex.Conway.supportedEntry_257_1

/-- Instance-selected field for C(257, 2). -/
instance committedEntry_257_2 : CommittedEntry 257 2 where
  entry := Hex.Conway.supportedEntry_257_2

/-- Instance-selected field for C(257, 3). -/
instance committedEntry_257_3 : CommittedEntry 257 3 where
  entry := Hex.Conway.supportedEntry_257_3

/-- Instance-selected field for C(257, 4). -/
instance committedEntry_257_4 : CommittedEntry 257 4 where
  entry := Hex.Conway.supportedEntry_257_4

/-- Instance-selected field for C(263, 1). -/
instance committedEntry_263_1 : CommittedEntry 263 1 where
  entry := Hex.Conway.supportedEntry_263_1

/-- Instance-selected field for C(263, 2). -/
instance committedEntry_263_2 : CommittedEntry 263 2 where
  entry := Hex.Conway.supportedEntry_263_2

/-- Instance-selected field for C(263, 3). -/
instance committedEntry_263_3 : CommittedEntry 263 3 where
  entry := Hex.Conway.supportedEntry_263_3

/-- Instance-selected field for C(263, 4). -/
instance committedEntry_263_4 : CommittedEntry 263 4 where
  entry := Hex.Conway.supportedEntry_263_4

/-- Instance-selected field for C(269, 1). -/
instance committedEntry_269_1 : CommittedEntry 269 1 where
  entry := Hex.Conway.supportedEntry_269_1

/-- Instance-selected field for C(269, 2). -/
instance committedEntry_269_2 : CommittedEntry 269 2 where
  entry := Hex.Conway.supportedEntry_269_2

/-- Instance-selected field for C(269, 3). -/
instance committedEntry_269_3 : CommittedEntry 269 3 where
  entry := Hex.Conway.supportedEntry_269_3

/-- Instance-selected field for C(269, 4). -/
instance committedEntry_269_4 : CommittedEntry 269 4 where
  entry := Hex.Conway.supportedEntry_269_4

end Hex.GFq
