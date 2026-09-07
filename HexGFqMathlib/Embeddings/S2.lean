/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGFqMathlib.Subfield

public section

namespace HexGFqMathlib.Conway

/-- The canonical embedding of GF(227^1) into GF(227^4). -/
noncomputable def embed_227_1_4 :
    Hex.GFq 227 1 Hex.Conway.supportedEntry_227_1 →+*
      Hex.GFq 227 4 Hex.Conway.supportedEntry_227_4 :=
  conwayEmbed 227 1 4 _ _ Hex.Conway.compat_227_1_4

/-- The canonical embedding of GF(227^2) into GF(227^4). -/
noncomputable def embed_227_2_4 :
    Hex.GFq 227 2 Hex.Conway.supportedEntry_227_2 →+*
      Hex.GFq 227 4 Hex.Conway.supportedEntry_227_4 :=
  conwayEmbed 227 2 4 _ _ Hex.Conway.compat_227_2_4

/-- The canonical embedding of GF(229^1) into GF(229^2). -/
noncomputable def embed_229_1_2 :
    Hex.GFq 229 1 Hex.Conway.supportedEntry_229_1 →+*
      Hex.GFq 229 2 Hex.Conway.supportedEntry_229_2 :=
  conwayEmbed 229 1 2 _ _ Hex.Conway.compat_229_1_2

/-- The canonical embedding of GF(229^1) into GF(229^3). -/
noncomputable def embed_229_1_3 :
    Hex.GFq 229 1 Hex.Conway.supportedEntry_229_1 →+*
      Hex.GFq 229 3 Hex.Conway.supportedEntry_229_3 :=
  conwayEmbed 229 1 3 _ _ Hex.Conway.compat_229_1_3

/-- The canonical embedding of GF(229^1) into GF(229^4). -/
noncomputable def embed_229_1_4 :
    Hex.GFq 229 1 Hex.Conway.supportedEntry_229_1 →+*
      Hex.GFq 229 4 Hex.Conway.supportedEntry_229_4 :=
  conwayEmbed 229 1 4 _ _ Hex.Conway.compat_229_1_4

/-- The canonical embedding of GF(229^2) into GF(229^4). -/
noncomputable def embed_229_2_4 :
    Hex.GFq 229 2 Hex.Conway.supportedEntry_229_2 →+*
      Hex.GFq 229 4 Hex.Conway.supportedEntry_229_4 :=
  conwayEmbed 229 2 4 _ _ Hex.Conway.compat_229_2_4

/-- The canonical embedding of GF(233^1) into GF(233^2). -/
noncomputable def embed_233_1_2 :
    Hex.GFq 233 1 Hex.Conway.supportedEntry_233_1 →+*
      Hex.GFq 233 2 Hex.Conway.supportedEntry_233_2 :=
  conwayEmbed 233 1 2 _ _ Hex.Conway.compat_233_1_2

/-- The canonical embedding of GF(233^1) into GF(233^3). -/
noncomputable def embed_233_1_3 :
    Hex.GFq 233 1 Hex.Conway.supportedEntry_233_1 →+*
      Hex.GFq 233 3 Hex.Conway.supportedEntry_233_3 :=
  conwayEmbed 233 1 3 _ _ Hex.Conway.compat_233_1_3

/-- The canonical embedding of GF(233^1) into GF(233^4). -/
noncomputable def embed_233_1_4 :
    Hex.GFq 233 1 Hex.Conway.supportedEntry_233_1 →+*
      Hex.GFq 233 4 Hex.Conway.supportedEntry_233_4 :=
  conwayEmbed 233 1 4 _ _ Hex.Conway.compat_233_1_4

/-- The canonical embedding of GF(233^2) into GF(233^4). -/
noncomputable def embed_233_2_4 :
    Hex.GFq 233 2 Hex.Conway.supportedEntry_233_2 →+*
      Hex.GFq 233 4 Hex.Conway.supportedEntry_233_4 :=
  conwayEmbed 233 2 4 _ _ Hex.Conway.compat_233_2_4

/-- The canonical embedding of GF(239^1) into GF(239^2). -/
noncomputable def embed_239_1_2 :
    Hex.GFq 239 1 Hex.Conway.supportedEntry_239_1 →+*
      Hex.GFq 239 2 Hex.Conway.supportedEntry_239_2 :=
  conwayEmbed 239 1 2 _ _ Hex.Conway.compat_239_1_2

/-- The canonical embedding of GF(239^1) into GF(239^3). -/
noncomputable def embed_239_1_3 :
    Hex.GFq 239 1 Hex.Conway.supportedEntry_239_1 →+*
      Hex.GFq 239 3 Hex.Conway.supportedEntry_239_3 :=
  conwayEmbed 239 1 3 _ _ Hex.Conway.compat_239_1_3

/-- The canonical embedding of GF(239^1) into GF(239^4). -/
noncomputable def embed_239_1_4 :
    Hex.GFq 239 1 Hex.Conway.supportedEntry_239_1 →+*
      Hex.GFq 239 4 Hex.Conway.supportedEntry_239_4 :=
  conwayEmbed 239 1 4 _ _ Hex.Conway.compat_239_1_4

/-- The canonical embedding of GF(239^2) into GF(239^4). -/
noncomputable def embed_239_2_4 :
    Hex.GFq 239 2 Hex.Conway.supportedEntry_239_2 →+*
      Hex.GFq 239 4 Hex.Conway.supportedEntry_239_4 :=
  conwayEmbed 239 2 4 _ _ Hex.Conway.compat_239_2_4

/-- The canonical embedding of GF(241^1) into GF(241^2). -/
noncomputable def embed_241_1_2 :
    Hex.GFq 241 1 Hex.Conway.supportedEntry_241_1 →+*
      Hex.GFq 241 2 Hex.Conway.supportedEntry_241_2 :=
  conwayEmbed 241 1 2 _ _ Hex.Conway.compat_241_1_2

/-- The canonical embedding of GF(241^1) into GF(241^3). -/
noncomputable def embed_241_1_3 :
    Hex.GFq 241 1 Hex.Conway.supportedEntry_241_1 →+*
      Hex.GFq 241 3 Hex.Conway.supportedEntry_241_3 :=
  conwayEmbed 241 1 3 _ _ Hex.Conway.compat_241_1_3

/-- The canonical embedding of GF(241^1) into GF(241^4). -/
noncomputable def embed_241_1_4 :
    Hex.GFq 241 1 Hex.Conway.supportedEntry_241_1 →+*
      Hex.GFq 241 4 Hex.Conway.supportedEntry_241_4 :=
  conwayEmbed 241 1 4 _ _ Hex.Conway.compat_241_1_4

/-- The canonical embedding of GF(241^2) into GF(241^4). -/
noncomputable def embed_241_2_4 :
    Hex.GFq 241 2 Hex.Conway.supportedEntry_241_2 →+*
      Hex.GFq 241 4 Hex.Conway.supportedEntry_241_4 :=
  conwayEmbed 241 2 4 _ _ Hex.Conway.compat_241_2_4

/-- The canonical embedding of GF(251^1) into GF(251^2). -/
noncomputable def embed_251_1_2 :
    Hex.GFq 251 1 Hex.Conway.supportedEntry_251_1 →+*
      Hex.GFq 251 2 Hex.Conway.supportedEntry_251_2 :=
  conwayEmbed 251 1 2 _ _ Hex.Conway.compat_251_1_2

/-- The canonical embedding of GF(251^1) into GF(251^3). -/
noncomputable def embed_251_1_3 :
    Hex.GFq 251 1 Hex.Conway.supportedEntry_251_1 →+*
      Hex.GFq 251 3 Hex.Conway.supportedEntry_251_3 :=
  conwayEmbed 251 1 3 _ _ Hex.Conway.compat_251_1_3

/-- The canonical embedding of GF(251^1) into GF(251^4). -/
noncomputable def embed_251_1_4 :
    Hex.GFq 251 1 Hex.Conway.supportedEntry_251_1 →+*
      Hex.GFq 251 4 Hex.Conway.supportedEntry_251_4 :=
  conwayEmbed 251 1 4 _ _ Hex.Conway.compat_251_1_4

/-- The canonical embedding of GF(251^2) into GF(251^4). -/
noncomputable def embed_251_2_4 :
    Hex.GFq 251 2 Hex.Conway.supportedEntry_251_2 →+*
      Hex.GFq 251 4 Hex.Conway.supportedEntry_251_4 :=
  conwayEmbed 251 2 4 _ _ Hex.Conway.compat_251_2_4

/-- The canonical embedding of GF(257^1) into GF(257^2). -/
noncomputable def embed_257_1_2 :
    Hex.GFq 257 1 Hex.Conway.supportedEntry_257_1 →+*
      Hex.GFq 257 2 Hex.Conway.supportedEntry_257_2 :=
  conwayEmbed 257 1 2 _ _ Hex.Conway.compat_257_1_2

/-- The canonical embedding of GF(257^1) into GF(257^3). -/
noncomputable def embed_257_1_3 :
    Hex.GFq 257 1 Hex.Conway.supportedEntry_257_1 →+*
      Hex.GFq 257 3 Hex.Conway.supportedEntry_257_3 :=
  conwayEmbed 257 1 3 _ _ Hex.Conway.compat_257_1_3

/-- The canonical embedding of GF(257^1) into GF(257^4). -/
noncomputable def embed_257_1_4 :
    Hex.GFq 257 1 Hex.Conway.supportedEntry_257_1 →+*
      Hex.GFq 257 4 Hex.Conway.supportedEntry_257_4 :=
  conwayEmbed 257 1 4 _ _ Hex.Conway.compat_257_1_4

/-- The canonical embedding of GF(257^2) into GF(257^4). -/
noncomputable def embed_257_2_4 :
    Hex.GFq 257 2 Hex.Conway.supportedEntry_257_2 →+*
      Hex.GFq 257 4 Hex.Conway.supportedEntry_257_4 :=
  conwayEmbed 257 2 4 _ _ Hex.Conway.compat_257_2_4

/-- The canonical embedding of GF(263^1) into GF(263^2). -/
noncomputable def embed_263_1_2 :
    Hex.GFq 263 1 Hex.Conway.supportedEntry_263_1 →+*
      Hex.GFq 263 2 Hex.Conway.supportedEntry_263_2 :=
  conwayEmbed 263 1 2 _ _ Hex.Conway.compat_263_1_2

/-- The canonical embedding of GF(263^1) into GF(263^3). -/
noncomputable def embed_263_1_3 :
    Hex.GFq 263 1 Hex.Conway.supportedEntry_263_1 →+*
      Hex.GFq 263 3 Hex.Conway.supportedEntry_263_3 :=
  conwayEmbed 263 1 3 _ _ Hex.Conway.compat_263_1_3

/-- The canonical embedding of GF(263^1) into GF(263^4). -/
noncomputable def embed_263_1_4 :
    Hex.GFq 263 1 Hex.Conway.supportedEntry_263_1 →+*
      Hex.GFq 263 4 Hex.Conway.supportedEntry_263_4 :=
  conwayEmbed 263 1 4 _ _ Hex.Conway.compat_263_1_4

/-- The canonical embedding of GF(263^2) into GF(263^4). -/
noncomputable def embed_263_2_4 :
    Hex.GFq 263 2 Hex.Conway.supportedEntry_263_2 →+*
      Hex.GFq 263 4 Hex.Conway.supportedEntry_263_4 :=
  conwayEmbed 263 2 4 _ _ Hex.Conway.compat_263_2_4

/-- The canonical embedding of GF(269^1) into GF(269^2). -/
noncomputable def embed_269_1_2 :
    Hex.GFq 269 1 Hex.Conway.supportedEntry_269_1 →+*
      Hex.GFq 269 2 Hex.Conway.supportedEntry_269_2 :=
  conwayEmbed 269 1 2 _ _ Hex.Conway.compat_269_1_2

/-- The canonical embedding of GF(269^1) into GF(269^3). -/
noncomputable def embed_269_1_3 :
    Hex.GFq 269 1 Hex.Conway.supportedEntry_269_1 →+*
      Hex.GFq 269 3 Hex.Conway.supportedEntry_269_3 :=
  conwayEmbed 269 1 3 _ _ Hex.Conway.compat_269_1_3

/-- The canonical embedding of GF(269^1) into GF(269^4). -/
noncomputable def embed_269_1_4 :
    Hex.GFq 269 1 Hex.Conway.supportedEntry_269_1 →+*
      Hex.GFq 269 4 Hex.Conway.supportedEntry_269_4 :=
  conwayEmbed 269 1 4 _ _ Hex.Conway.compat_269_1_4

/-- The canonical embedding of GF(269^2) into GF(269^4). -/
noncomputable def embed_269_2_4 :
    Hex.GFq 269 2 Hex.Conway.supportedEntry_269_2 →+*
      Hex.GFq 269 4 Hex.Conway.supportedEntry_269_4 :=
  conwayEmbed 269 2 4 _ _ Hex.Conway.compat_269_2_4

/-- The canonical embedding of GF(271^1) into GF(271^2). -/
noncomputable def embed_271_1_2 :
    Hex.GFq 271 1 Hex.Conway.supportedEntry_271_1 →+*
      Hex.GFq 271 2 Hex.Conway.supportedEntry_271_2 :=
  conwayEmbed 271 1 2 _ _ Hex.Conway.compat_271_1_2

/-- The canonical embedding of GF(271^1) into GF(271^3). -/
noncomputable def embed_271_1_3 :
    Hex.GFq 271 1 Hex.Conway.supportedEntry_271_1 →+*
      Hex.GFq 271 3 Hex.Conway.supportedEntry_271_3 :=
  conwayEmbed 271 1 3 _ _ Hex.Conway.compat_271_1_3

/-- The canonical embedding of GF(271^1) into GF(271^4). -/
noncomputable def embed_271_1_4 :
    Hex.GFq 271 1 Hex.Conway.supportedEntry_271_1 →+*
      Hex.GFq 271 4 Hex.Conway.supportedEntry_271_4 :=
  conwayEmbed 271 1 4 _ _ Hex.Conway.compat_271_1_4

/-- The canonical embedding of GF(271^2) into GF(271^4). -/
noncomputable def embed_271_2_4 :
    Hex.GFq 271 2 Hex.Conway.supportedEntry_271_2 →+*
      Hex.GFq 271 4 Hex.Conway.supportedEntry_271_4 :=
  conwayEmbed 271 2 4 _ _ Hex.Conway.compat_271_2_4

/-- The canonical embedding of GF(277^1) into GF(277^2). -/
noncomputable def embed_277_1_2 :
    Hex.GFq 277 1 Hex.Conway.supportedEntry_277_1 →+*
      Hex.GFq 277 2 Hex.Conway.supportedEntry_277_2 :=
  conwayEmbed 277 1 2 _ _ Hex.Conway.compat_277_1_2

/-- The canonical embedding of GF(277^1) into GF(277^3). -/
noncomputable def embed_277_1_3 :
    Hex.GFq 277 1 Hex.Conway.supportedEntry_277_1 →+*
      Hex.GFq 277 3 Hex.Conway.supportedEntry_277_3 :=
  conwayEmbed 277 1 3 _ _ Hex.Conway.compat_277_1_3

/-- The canonical embedding of GF(277^1) into GF(277^4). -/
noncomputable def embed_277_1_4 :
    Hex.GFq 277 1 Hex.Conway.supportedEntry_277_1 →+*
      Hex.GFq 277 4 Hex.Conway.supportedEntry_277_4 :=
  conwayEmbed 277 1 4 _ _ Hex.Conway.compat_277_1_4

/-- The canonical embedding of GF(277^2) into GF(277^4). -/
noncomputable def embed_277_2_4 :
    Hex.GFq 277 2 Hex.Conway.supportedEntry_277_2 →+*
      Hex.GFq 277 4 Hex.Conway.supportedEntry_277_4 :=
  conwayEmbed 277 2 4 _ _ Hex.Conway.compat_277_2_4

/-- The canonical embedding of GF(281^1) into GF(281^2). -/
noncomputable def embed_281_1_2 :
    Hex.GFq 281 1 Hex.Conway.supportedEntry_281_1 →+*
      Hex.GFq 281 2 Hex.Conway.supportedEntry_281_2 :=
  conwayEmbed 281 1 2 _ _ Hex.Conway.compat_281_1_2

/-- The canonical embedding of GF(281^1) into GF(281^3). -/
noncomputable def embed_281_1_3 :
    Hex.GFq 281 1 Hex.Conway.supportedEntry_281_1 →+*
      Hex.GFq 281 3 Hex.Conway.supportedEntry_281_3 :=
  conwayEmbed 281 1 3 _ _ Hex.Conway.compat_281_1_3

/-- The canonical embedding of GF(281^1) into GF(281^4). -/
noncomputable def embed_281_1_4 :
    Hex.GFq 281 1 Hex.Conway.supportedEntry_281_1 →+*
      Hex.GFq 281 4 Hex.Conway.supportedEntry_281_4 :=
  conwayEmbed 281 1 4 _ _ Hex.Conway.compat_281_1_4

/-- The canonical embedding of GF(281^2) into GF(281^4). -/
noncomputable def embed_281_2_4 :
    Hex.GFq 281 2 Hex.Conway.supportedEntry_281_2 →+*
      Hex.GFq 281 4 Hex.Conway.supportedEntry_281_4 :=
  conwayEmbed 281 2 4 _ _ Hex.Conway.compat_281_2_4

/-- The canonical embedding of GF(283^1) into GF(283^2). -/
noncomputable def embed_283_1_2 :
    Hex.GFq 283 1 Hex.Conway.supportedEntry_283_1 →+*
      Hex.GFq 283 2 Hex.Conway.supportedEntry_283_2 :=
  conwayEmbed 283 1 2 _ _ Hex.Conway.compat_283_1_2

/-- The canonical embedding of GF(283^1) into GF(283^3). -/
noncomputable def embed_283_1_3 :
    Hex.GFq 283 1 Hex.Conway.supportedEntry_283_1 →+*
      Hex.GFq 283 3 Hex.Conway.supportedEntry_283_3 :=
  conwayEmbed 283 1 3 _ _ Hex.Conway.compat_283_1_3

/-- The canonical embedding of GF(283^1) into GF(283^4). -/
noncomputable def embed_283_1_4 :
    Hex.GFq 283 1 Hex.Conway.supportedEntry_283_1 →+*
      Hex.GFq 283 4 Hex.Conway.supportedEntry_283_4 :=
  conwayEmbed 283 1 4 _ _ Hex.Conway.compat_283_1_4

/-- The canonical embedding of GF(283^2) into GF(283^4). -/
noncomputable def embed_283_2_4 :
    Hex.GFq 283 2 Hex.Conway.supportedEntry_283_2 →+*
      Hex.GFq 283 4 Hex.Conway.supportedEntry_283_4 :=
  conwayEmbed 283 2 4 _ _ Hex.Conway.compat_283_2_4

/-- The canonical embedding of GF(293^1) into GF(293^2). -/
noncomputable def embed_293_1_2 :
    Hex.GFq 293 1 Hex.Conway.supportedEntry_293_1 →+*
      Hex.GFq 293 2 Hex.Conway.supportedEntry_293_2 :=
  conwayEmbed 293 1 2 _ _ Hex.Conway.compat_293_1_2

/-- The canonical embedding of GF(293^1) into GF(293^3). -/
noncomputable def embed_293_1_3 :
    Hex.GFq 293 1 Hex.Conway.supportedEntry_293_1 →+*
      Hex.GFq 293 3 Hex.Conway.supportedEntry_293_3 :=
  conwayEmbed 293 1 3 _ _ Hex.Conway.compat_293_1_3

/-- The canonical embedding of GF(293^1) into GF(293^4). -/
noncomputable def embed_293_1_4 :
    Hex.GFq 293 1 Hex.Conway.supportedEntry_293_1 →+*
      Hex.GFq 293 4 Hex.Conway.supportedEntry_293_4 :=
  conwayEmbed 293 1 4 _ _ Hex.Conway.compat_293_1_4

/-- The canonical embedding of GF(293^2) into GF(293^4). -/
noncomputable def embed_293_2_4 :
    Hex.GFq 293 2 Hex.Conway.supportedEntry_293_2 →+*
      Hex.GFq 293 4 Hex.Conway.supportedEntry_293_4 :=
  conwayEmbed 293 2 4 _ _ Hex.Conway.compat_293_2_4

/-- The canonical embedding of GF(307^1) into GF(307^2). -/
noncomputable def embed_307_1_2 :
    Hex.GFq 307 1 Hex.Conway.supportedEntry_307_1 →+*
      Hex.GFq 307 2 Hex.Conway.supportedEntry_307_2 :=
  conwayEmbed 307 1 2 _ _ Hex.Conway.compat_307_1_2

/-- The canonical embedding of GF(307^1) into GF(307^3). -/
noncomputable def embed_307_1_3 :
    Hex.GFq 307 1 Hex.Conway.supportedEntry_307_1 →+*
      Hex.GFq 307 3 Hex.Conway.supportedEntry_307_3 :=
  conwayEmbed 307 1 3 _ _ Hex.Conway.compat_307_1_3

/-- The canonical embedding of GF(307^1) into GF(307^4). -/
noncomputable def embed_307_1_4 :
    Hex.GFq 307 1 Hex.Conway.supportedEntry_307_1 →+*
      Hex.GFq 307 4 Hex.Conway.supportedEntry_307_4 :=
  conwayEmbed 307 1 4 _ _ Hex.Conway.compat_307_1_4

/-- The canonical embedding of GF(307^2) into GF(307^4). -/
noncomputable def embed_307_2_4 :
    Hex.GFq 307 2 Hex.Conway.supportedEntry_307_2 →+*
      Hex.GFq 307 4 Hex.Conway.supportedEntry_307_4 :=
  conwayEmbed 307 2 4 _ _ Hex.Conway.compat_307_2_4

/-- The canonical embedding of GF(311^1) into GF(311^2). -/
noncomputable def embed_311_1_2 :
    Hex.GFq 311 1 Hex.Conway.supportedEntry_311_1 →+*
      Hex.GFq 311 2 Hex.Conway.supportedEntry_311_2 :=
  conwayEmbed 311 1 2 _ _ Hex.Conway.compat_311_1_2

/-- The canonical embedding of GF(311^1) into GF(311^3). -/
noncomputable def embed_311_1_3 :
    Hex.GFq 311 1 Hex.Conway.supportedEntry_311_1 →+*
      Hex.GFq 311 3 Hex.Conway.supportedEntry_311_3 :=
  conwayEmbed 311 1 3 _ _ Hex.Conway.compat_311_1_3

/-- The canonical embedding of GF(311^1) into GF(311^4). -/
noncomputable def embed_311_1_4 :
    Hex.GFq 311 1 Hex.Conway.supportedEntry_311_1 →+*
      Hex.GFq 311 4 Hex.Conway.supportedEntry_311_4 :=
  conwayEmbed 311 1 4 _ _ Hex.Conway.compat_311_1_4

/-- The canonical embedding of GF(311^2) into GF(311^4). -/
noncomputable def embed_311_2_4 :
    Hex.GFq 311 2 Hex.Conway.supportedEntry_311_2 →+*
      Hex.GFq 311 4 Hex.Conway.supportedEntry_311_4 :=
  conwayEmbed 311 2 4 _ _ Hex.Conway.compat_311_2_4

/-- The canonical embedding of GF(313^1) into GF(313^2). -/
noncomputable def embed_313_1_2 :
    Hex.GFq 313 1 Hex.Conway.supportedEntry_313_1 →+*
      Hex.GFq 313 2 Hex.Conway.supportedEntry_313_2 :=
  conwayEmbed 313 1 2 _ _ Hex.Conway.compat_313_1_2

/-- The canonical embedding of GF(313^1) into GF(313^3). -/
noncomputable def embed_313_1_3 :
    Hex.GFq 313 1 Hex.Conway.supportedEntry_313_1 →+*
      Hex.GFq 313 3 Hex.Conway.supportedEntry_313_3 :=
  conwayEmbed 313 1 3 _ _ Hex.Conway.compat_313_1_3

/-- The canonical embedding of GF(313^1) into GF(313^4). -/
noncomputable def embed_313_1_4 :
    Hex.GFq 313 1 Hex.Conway.supportedEntry_313_1 →+*
      Hex.GFq 313 4 Hex.Conway.supportedEntry_313_4 :=
  conwayEmbed 313 1 4 _ _ Hex.Conway.compat_313_1_4

/-- The canonical embedding of GF(313^2) into GF(313^4). -/
noncomputable def embed_313_2_4 :
    Hex.GFq 313 2 Hex.Conway.supportedEntry_313_2 →+*
      Hex.GFq 313 4 Hex.Conway.supportedEntry_313_4 :=
  conwayEmbed 313 2 4 _ _ Hex.Conway.compat_313_2_4

/-- The canonical embedding of GF(317^1) into GF(317^2). -/
noncomputable def embed_317_1_2 :
    Hex.GFq 317 1 Hex.Conway.supportedEntry_317_1 →+*
      Hex.GFq 317 2 Hex.Conway.supportedEntry_317_2 :=
  conwayEmbed 317 1 2 _ _ Hex.Conway.compat_317_1_2

/-- The canonical embedding of GF(317^1) into GF(317^3). -/
noncomputable def embed_317_1_3 :
    Hex.GFq 317 1 Hex.Conway.supportedEntry_317_1 →+*
      Hex.GFq 317 3 Hex.Conway.supportedEntry_317_3 :=
  conwayEmbed 317 1 3 _ _ Hex.Conway.compat_317_1_3

/-- The canonical embedding of GF(317^1) into GF(317^4). -/
noncomputable def embed_317_1_4 :
    Hex.GFq 317 1 Hex.Conway.supportedEntry_317_1 →+*
      Hex.GFq 317 4 Hex.Conway.supportedEntry_317_4 :=
  conwayEmbed 317 1 4 _ _ Hex.Conway.compat_317_1_4

/-- The canonical embedding of GF(317^2) into GF(317^4). -/
noncomputable def embed_317_2_4 :
    Hex.GFq 317 2 Hex.Conway.supportedEntry_317_2 →+*
      Hex.GFq 317 4 Hex.Conway.supportedEntry_317_4 :=
  conwayEmbed 317 2 4 _ _ Hex.Conway.compat_317_2_4

/-- The canonical embedding of GF(331^1) into GF(331^2). -/
noncomputable def embed_331_1_2 :
    Hex.GFq 331 1 Hex.Conway.supportedEntry_331_1 →+*
      Hex.GFq 331 2 Hex.Conway.supportedEntry_331_2 :=
  conwayEmbed 331 1 2 _ _ Hex.Conway.compat_331_1_2

/-- The canonical embedding of GF(331^1) into GF(331^3). -/
noncomputable def embed_331_1_3 :
    Hex.GFq 331 1 Hex.Conway.supportedEntry_331_1 →+*
      Hex.GFq 331 3 Hex.Conway.supportedEntry_331_3 :=
  conwayEmbed 331 1 3 _ _ Hex.Conway.compat_331_1_3

/-- The canonical embedding of GF(331^1) into GF(331^4). -/
noncomputable def embed_331_1_4 :
    Hex.GFq 331 1 Hex.Conway.supportedEntry_331_1 →+*
      Hex.GFq 331 4 Hex.Conway.supportedEntry_331_4 :=
  conwayEmbed 331 1 4 _ _ Hex.Conway.compat_331_1_4

/-- The canonical embedding of GF(331^2) into GF(331^4). -/
noncomputable def embed_331_2_4 :
    Hex.GFq 331 2 Hex.Conway.supportedEntry_331_2 →+*
      Hex.GFq 331 4 Hex.Conway.supportedEntry_331_4 :=
  conwayEmbed 331 2 4 _ _ Hex.Conway.compat_331_2_4

/-- The canonical embedding of GF(337^1) into GF(337^2). -/
noncomputable def embed_337_1_2 :
    Hex.GFq 337 1 Hex.Conway.supportedEntry_337_1 →+*
      Hex.GFq 337 2 Hex.Conway.supportedEntry_337_2 :=
  conwayEmbed 337 1 2 _ _ Hex.Conway.compat_337_1_2

/-- The canonical embedding of GF(337^1) into GF(337^3). -/
noncomputable def embed_337_1_3 :
    Hex.GFq 337 1 Hex.Conway.supportedEntry_337_1 →+*
      Hex.GFq 337 3 Hex.Conway.supportedEntry_337_3 :=
  conwayEmbed 337 1 3 _ _ Hex.Conway.compat_337_1_3

/-- The canonical embedding of GF(337^1) into GF(337^4). -/
noncomputable def embed_337_1_4 :
    Hex.GFq 337 1 Hex.Conway.supportedEntry_337_1 →+*
      Hex.GFq 337 4 Hex.Conway.supportedEntry_337_4 :=
  conwayEmbed 337 1 4 _ _ Hex.Conway.compat_337_1_4

/-- The canonical embedding of GF(337^2) into GF(337^4). -/
noncomputable def embed_337_2_4 :
    Hex.GFq 337 2 Hex.Conway.supportedEntry_337_2 →+*
      Hex.GFq 337 4 Hex.Conway.supportedEntry_337_4 :=
  conwayEmbed 337 2 4 _ _ Hex.Conway.compat_337_2_4

/-- The canonical embedding of GF(347^1) into GF(347^2). -/
noncomputable def embed_347_1_2 :
    Hex.GFq 347 1 Hex.Conway.supportedEntry_347_1 →+*
      Hex.GFq 347 2 Hex.Conway.supportedEntry_347_2 :=
  conwayEmbed 347 1 2 _ _ Hex.Conway.compat_347_1_2

/-- The canonical embedding of GF(347^1) into GF(347^3). -/
noncomputable def embed_347_1_3 :
    Hex.GFq 347 1 Hex.Conway.supportedEntry_347_1 →+*
      Hex.GFq 347 3 Hex.Conway.supportedEntry_347_3 :=
  conwayEmbed 347 1 3 _ _ Hex.Conway.compat_347_1_3

/-- The canonical embedding of GF(347^1) into GF(347^4). -/
noncomputable def embed_347_1_4 :
    Hex.GFq 347 1 Hex.Conway.supportedEntry_347_1 →+*
      Hex.GFq 347 4 Hex.Conway.supportedEntry_347_4 :=
  conwayEmbed 347 1 4 _ _ Hex.Conway.compat_347_1_4

/-- The canonical embedding of GF(347^2) into GF(347^4). -/
noncomputable def embed_347_2_4 :
    Hex.GFq 347 2 Hex.Conway.supportedEntry_347_2 →+*
      Hex.GFq 347 4 Hex.Conway.supportedEntry_347_4 :=
  conwayEmbed 347 2 4 _ _ Hex.Conway.compat_347_2_4

/-- The canonical embedding of GF(349^1) into GF(349^2). -/
noncomputable def embed_349_1_2 :
    Hex.GFq 349 1 Hex.Conway.supportedEntry_349_1 →+*
      Hex.GFq 349 2 Hex.Conway.supportedEntry_349_2 :=
  conwayEmbed 349 1 2 _ _ Hex.Conway.compat_349_1_2

/-- The canonical embedding of GF(349^1) into GF(349^3). -/
noncomputable def embed_349_1_3 :
    Hex.GFq 349 1 Hex.Conway.supportedEntry_349_1 →+*
      Hex.GFq 349 3 Hex.Conway.supportedEntry_349_3 :=
  conwayEmbed 349 1 3 _ _ Hex.Conway.compat_349_1_3

/-- The canonical embedding of GF(349^1) into GF(349^4). -/
noncomputable def embed_349_1_4 :
    Hex.GFq 349 1 Hex.Conway.supportedEntry_349_1 →+*
      Hex.GFq 349 4 Hex.Conway.supportedEntry_349_4 :=
  conwayEmbed 349 1 4 _ _ Hex.Conway.compat_349_1_4

/-- The canonical embedding of GF(349^2) into GF(349^4). -/
noncomputable def embed_349_2_4 :
    Hex.GFq 349 2 Hex.Conway.supportedEntry_349_2 →+*
      Hex.GFq 349 4 Hex.Conway.supportedEntry_349_4 :=
  conwayEmbed 349 2 4 _ _ Hex.Conway.compat_349_2_4

/-- The canonical embedding of GF(353^1) into GF(353^2). -/
noncomputable def embed_353_1_2 :
    Hex.GFq 353 1 Hex.Conway.supportedEntry_353_1 →+*
      Hex.GFq 353 2 Hex.Conway.supportedEntry_353_2 :=
  conwayEmbed 353 1 2 _ _ Hex.Conway.compat_353_1_2

/-- The canonical embedding of GF(353^1) into GF(353^3). -/
noncomputable def embed_353_1_3 :
    Hex.GFq 353 1 Hex.Conway.supportedEntry_353_1 →+*
      Hex.GFq 353 3 Hex.Conway.supportedEntry_353_3 :=
  conwayEmbed 353 1 3 _ _ Hex.Conway.compat_353_1_3

/-- The canonical embedding of GF(353^1) into GF(353^4). -/
noncomputable def embed_353_1_4 :
    Hex.GFq 353 1 Hex.Conway.supportedEntry_353_1 →+*
      Hex.GFq 353 4 Hex.Conway.supportedEntry_353_4 :=
  conwayEmbed 353 1 4 _ _ Hex.Conway.compat_353_1_4

/-- The canonical embedding of GF(353^2) into GF(353^4). -/
noncomputable def embed_353_2_4 :
    Hex.GFq 353 2 Hex.Conway.supportedEntry_353_2 →+*
      Hex.GFq 353 4 Hex.Conway.supportedEntry_353_4 :=
  conwayEmbed 353 2 4 _ _ Hex.Conway.compat_353_2_4

/-- The canonical embedding of GF(359^1) into GF(359^2). -/
noncomputable def embed_359_1_2 :
    Hex.GFq 359 1 Hex.Conway.supportedEntry_359_1 →+*
      Hex.GFq 359 2 Hex.Conway.supportedEntry_359_2 :=
  conwayEmbed 359 1 2 _ _ Hex.Conway.compat_359_1_2

/-- The canonical embedding of GF(359^1) into GF(359^3). -/
noncomputable def embed_359_1_3 :
    Hex.GFq 359 1 Hex.Conway.supportedEntry_359_1 →+*
      Hex.GFq 359 3 Hex.Conway.supportedEntry_359_3 :=
  conwayEmbed 359 1 3 _ _ Hex.Conway.compat_359_1_3

/-- The canonical embedding of GF(359^1) into GF(359^4). -/
noncomputable def embed_359_1_4 :
    Hex.GFq 359 1 Hex.Conway.supportedEntry_359_1 →+*
      Hex.GFq 359 4 Hex.Conway.supportedEntry_359_4 :=
  conwayEmbed 359 1 4 _ _ Hex.Conway.compat_359_1_4

/-- The canonical embedding of GF(359^2) into GF(359^4). -/
noncomputable def embed_359_2_4 :
    Hex.GFq 359 2 Hex.Conway.supportedEntry_359_2 →+*
      Hex.GFq 359 4 Hex.Conway.supportedEntry_359_4 :=
  conwayEmbed 359 2 4 _ _ Hex.Conway.compat_359_2_4

/-- The canonical embedding of GF(367^1) into GF(367^2). -/
noncomputable def embed_367_1_2 :
    Hex.GFq 367 1 Hex.Conway.supportedEntry_367_1 →+*
      Hex.GFq 367 2 Hex.Conway.supportedEntry_367_2 :=
  conwayEmbed 367 1 2 _ _ Hex.Conway.compat_367_1_2

/-- The canonical embedding of GF(367^1) into GF(367^3). -/
noncomputable def embed_367_1_3 :
    Hex.GFq 367 1 Hex.Conway.supportedEntry_367_1 →+*
      Hex.GFq 367 3 Hex.Conway.supportedEntry_367_3 :=
  conwayEmbed 367 1 3 _ _ Hex.Conway.compat_367_1_3

/-- The canonical embedding of GF(367^1) into GF(367^4). -/
noncomputable def embed_367_1_4 :
    Hex.GFq 367 1 Hex.Conway.supportedEntry_367_1 →+*
      Hex.GFq 367 4 Hex.Conway.supportedEntry_367_4 :=
  conwayEmbed 367 1 4 _ _ Hex.Conway.compat_367_1_4

/-- The canonical embedding of GF(367^2) into GF(367^4). -/
noncomputable def embed_367_2_4 :
    Hex.GFq 367 2 Hex.Conway.supportedEntry_367_2 →+*
      Hex.GFq 367 4 Hex.Conway.supportedEntry_367_4 :=
  conwayEmbed 367 2 4 _ _ Hex.Conway.compat_367_2_4

/-- The canonical embedding of GF(373^1) into GF(373^2). -/
noncomputable def embed_373_1_2 :
    Hex.GFq 373 1 Hex.Conway.supportedEntry_373_1 →+*
      Hex.GFq 373 2 Hex.Conway.supportedEntry_373_2 :=
  conwayEmbed 373 1 2 _ _ Hex.Conway.compat_373_1_2

/-- The canonical embedding of GF(373^1) into GF(373^3). -/
noncomputable def embed_373_1_3 :
    Hex.GFq 373 1 Hex.Conway.supportedEntry_373_1 →+*
      Hex.GFq 373 3 Hex.Conway.supportedEntry_373_3 :=
  conwayEmbed 373 1 3 _ _ Hex.Conway.compat_373_1_3

/-- The canonical embedding of GF(373^1) into GF(373^4). -/
noncomputable def embed_373_1_4 :
    Hex.GFq 373 1 Hex.Conway.supportedEntry_373_1 →+*
      Hex.GFq 373 4 Hex.Conway.supportedEntry_373_4 :=
  conwayEmbed 373 1 4 _ _ Hex.Conway.compat_373_1_4

/-- The canonical embedding of GF(373^2) into GF(373^4). -/
noncomputable def embed_373_2_4 :
    Hex.GFq 373 2 Hex.Conway.supportedEntry_373_2 →+*
      Hex.GFq 373 4 Hex.Conway.supportedEntry_373_4 :=
  conwayEmbed 373 2 4 _ _ Hex.Conway.compat_373_2_4

/-- The canonical embedding of GF(379^1) into GF(379^2). -/
noncomputable def embed_379_1_2 :
    Hex.GFq 379 1 Hex.Conway.supportedEntry_379_1 →+*
      Hex.GFq 379 2 Hex.Conway.supportedEntry_379_2 :=
  conwayEmbed 379 1 2 _ _ Hex.Conway.compat_379_1_2

/-- The canonical embedding of GF(379^1) into GF(379^3). -/
noncomputable def embed_379_1_3 :
    Hex.GFq 379 1 Hex.Conway.supportedEntry_379_1 →+*
      Hex.GFq 379 3 Hex.Conway.supportedEntry_379_3 :=
  conwayEmbed 379 1 3 _ _ Hex.Conway.compat_379_1_3

/-- The canonical embedding of GF(379^1) into GF(379^4). -/
noncomputable def embed_379_1_4 :
    Hex.GFq 379 1 Hex.Conway.supportedEntry_379_1 →+*
      Hex.GFq 379 4 Hex.Conway.supportedEntry_379_4 :=
  conwayEmbed 379 1 4 _ _ Hex.Conway.compat_379_1_4

/-- The canonical embedding of GF(379^2) into GF(379^4). -/
noncomputable def embed_379_2_4 :
    Hex.GFq 379 2 Hex.Conway.supportedEntry_379_2 →+*
      Hex.GFq 379 4 Hex.Conway.supportedEntry_379_4 :=
  conwayEmbed 379 2 4 _ _ Hex.Conway.compat_379_2_4

/-- The canonical embedding of GF(383^1) into GF(383^2). -/
noncomputable def embed_383_1_2 :
    Hex.GFq 383 1 Hex.Conway.supportedEntry_383_1 →+*
      Hex.GFq 383 2 Hex.Conway.supportedEntry_383_2 :=
  conwayEmbed 383 1 2 _ _ Hex.Conway.compat_383_1_2

/-- The canonical embedding of GF(383^1) into GF(383^3). -/
noncomputable def embed_383_1_3 :
    Hex.GFq 383 1 Hex.Conway.supportedEntry_383_1 →+*
      Hex.GFq 383 3 Hex.Conway.supportedEntry_383_3 :=
  conwayEmbed 383 1 3 _ _ Hex.Conway.compat_383_1_3

/-- The canonical embedding of GF(383^1) into GF(383^4). -/
noncomputable def embed_383_1_4 :
    Hex.GFq 383 1 Hex.Conway.supportedEntry_383_1 →+*
      Hex.GFq 383 4 Hex.Conway.supportedEntry_383_4 :=
  conwayEmbed 383 1 4 _ _ Hex.Conway.compat_383_1_4

/-- The canonical embedding of GF(383^2) into GF(383^4). -/
noncomputable def embed_383_2_4 :
    Hex.GFq 383 2 Hex.Conway.supportedEntry_383_2 →+*
      Hex.GFq 383 4 Hex.Conway.supportedEntry_383_4 :=
  conwayEmbed 383 2 4 _ _ Hex.Conway.compat_383_2_4

/-- The canonical embedding of GF(389^1) into GF(389^2). -/
noncomputable def embed_389_1_2 :
    Hex.GFq 389 1 Hex.Conway.supportedEntry_389_1 →+*
      Hex.GFq 389 2 Hex.Conway.supportedEntry_389_2 :=
  conwayEmbed 389 1 2 _ _ Hex.Conway.compat_389_1_2

/-- The canonical embedding of GF(389^1) into GF(389^3). -/
noncomputable def embed_389_1_3 :
    Hex.GFq 389 1 Hex.Conway.supportedEntry_389_1 →+*
      Hex.GFq 389 3 Hex.Conway.supportedEntry_389_3 :=
  conwayEmbed 389 1 3 _ _ Hex.Conway.compat_389_1_3

/-- The canonical embedding of GF(389^1) into GF(389^4). -/
noncomputable def embed_389_1_4 :
    Hex.GFq 389 1 Hex.Conway.supportedEntry_389_1 →+*
      Hex.GFq 389 4 Hex.Conway.supportedEntry_389_4 :=
  conwayEmbed 389 1 4 _ _ Hex.Conway.compat_389_1_4

/-- The canonical embedding of GF(389^2) into GF(389^4). -/
noncomputable def embed_389_2_4 :
    Hex.GFq 389 2 Hex.Conway.supportedEntry_389_2 →+*
      Hex.GFq 389 4 Hex.Conway.supportedEntry_389_4 :=
  conwayEmbed 389 2 4 _ _ Hex.Conway.compat_389_2_4

/-- The canonical embedding of GF(397^1) into GF(397^2). -/
noncomputable def embed_397_1_2 :
    Hex.GFq 397 1 Hex.Conway.supportedEntry_397_1 →+*
      Hex.GFq 397 2 Hex.Conway.supportedEntry_397_2 :=
  conwayEmbed 397 1 2 _ _ Hex.Conway.compat_397_1_2

/-- The canonical embedding of GF(397^1) into GF(397^3). -/
noncomputable def embed_397_1_3 :
    Hex.GFq 397 1 Hex.Conway.supportedEntry_397_1 →+*
      Hex.GFq 397 3 Hex.Conway.supportedEntry_397_3 :=
  conwayEmbed 397 1 3 _ _ Hex.Conway.compat_397_1_3

/-- The canonical embedding of GF(397^1) into GF(397^4). -/
noncomputable def embed_397_1_4 :
    Hex.GFq 397 1 Hex.Conway.supportedEntry_397_1 →+*
      Hex.GFq 397 4 Hex.Conway.supportedEntry_397_4 :=
  conwayEmbed 397 1 4 _ _ Hex.Conway.compat_397_1_4

/-- The canonical embedding of GF(397^2) into GF(397^4). -/
noncomputable def embed_397_2_4 :
    Hex.GFq 397 2 Hex.Conway.supportedEntry_397_2 →+*
      Hex.GFq 397 4 Hex.Conway.supportedEntry_397_4 :=
  conwayEmbed 397 2 4 _ _ Hex.Conway.compat_397_2_4

/-- The canonical embedding of GF(401^1) into GF(401^2). -/
noncomputable def embed_401_1_2 :
    Hex.GFq 401 1 Hex.Conway.supportedEntry_401_1 →+*
      Hex.GFq 401 2 Hex.Conway.supportedEntry_401_2 :=
  conwayEmbed 401 1 2 _ _ Hex.Conway.compat_401_1_2

/-- The canonical embedding of GF(401^1) into GF(401^3). -/
noncomputable def embed_401_1_3 :
    Hex.GFq 401 1 Hex.Conway.supportedEntry_401_1 →+*
      Hex.GFq 401 3 Hex.Conway.supportedEntry_401_3 :=
  conwayEmbed 401 1 3 _ _ Hex.Conway.compat_401_1_3

/-- The canonical embedding of GF(401^1) into GF(401^4). -/
noncomputable def embed_401_1_4 :
    Hex.GFq 401 1 Hex.Conway.supportedEntry_401_1 →+*
      Hex.GFq 401 4 Hex.Conway.supportedEntry_401_4 :=
  conwayEmbed 401 1 4 _ _ Hex.Conway.compat_401_1_4

/-- The canonical embedding of GF(401^2) into GF(401^4). -/
noncomputable def embed_401_2_4 :
    Hex.GFq 401 2 Hex.Conway.supportedEntry_401_2 →+*
      Hex.GFq 401 4 Hex.Conway.supportedEntry_401_4 :=
  conwayEmbed 401 2 4 _ _ Hex.Conway.compat_401_2_4

/-- The canonical embedding of GF(409^1) into GF(409^2). -/
noncomputable def embed_409_1_2 :
    Hex.GFq 409 1 Hex.Conway.supportedEntry_409_1 →+*
      Hex.GFq 409 2 Hex.Conway.supportedEntry_409_2 :=
  conwayEmbed 409 1 2 _ _ Hex.Conway.compat_409_1_2

/-- The canonical embedding of GF(409^1) into GF(409^3). -/
noncomputable def embed_409_1_3 :
    Hex.GFq 409 1 Hex.Conway.supportedEntry_409_1 →+*
      Hex.GFq 409 3 Hex.Conway.supportedEntry_409_3 :=
  conwayEmbed 409 1 3 _ _ Hex.Conway.compat_409_1_3

/-- The canonical embedding of GF(409^1) into GF(409^4). -/
noncomputable def embed_409_1_4 :
    Hex.GFq 409 1 Hex.Conway.supportedEntry_409_1 →+*
      Hex.GFq 409 4 Hex.Conway.supportedEntry_409_4 :=
  conwayEmbed 409 1 4 _ _ Hex.Conway.compat_409_1_4

/-- The canonical embedding of GF(409^2) into GF(409^4). -/
noncomputable def embed_409_2_4 :
    Hex.GFq 409 2 Hex.Conway.supportedEntry_409_2 →+*
      Hex.GFq 409 4 Hex.Conway.supportedEntry_409_4 :=
  conwayEmbed 409 2 4 _ _ Hex.Conway.compat_409_2_4

/-- The canonical embedding of GF(419^1) into GF(419^2). -/
noncomputable def embed_419_1_2 :
    Hex.GFq 419 1 Hex.Conway.supportedEntry_419_1 →+*
      Hex.GFq 419 2 Hex.Conway.supportedEntry_419_2 :=
  conwayEmbed 419 1 2 _ _ Hex.Conway.compat_419_1_2

/-- The canonical embedding of GF(419^1) into GF(419^3). -/
noncomputable def embed_419_1_3 :
    Hex.GFq 419 1 Hex.Conway.supportedEntry_419_1 →+*
      Hex.GFq 419 3 Hex.Conway.supportedEntry_419_3 :=
  conwayEmbed 419 1 3 _ _ Hex.Conway.compat_419_1_3

end HexGFqMathlib.Conway
