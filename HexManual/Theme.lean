/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

/-!
Site-wide visual theme for the `HexManual` Verso site.

The theme layers green-and-orange accents over the default Verso stylesheet:
green (`#2d6a4f`) for structure (headings, ToC, header bar) and orange
(`#e76f51`) for interaction (links on hover, current ToC entry, prev/next).
It is injected as a single `<style>` element into every page's `<head>` via
`config.extraHead` (see `Main.lean`); nothing here depends on the document
content, so it applies uniformly across the whole site.

The colour scheme is adapted from the Formal Frontier
`Sutherland-NumberTheory-verso` course notes.
-/

namespace HexManual.Theme

/-- The CSS for the site-wide theme, injected verbatim into each page's `<head>`. -/
def css : String :=
"/* === Hex manual: custom theme === */
/* Green and orange accents over the default Verso theme */

:root {
  /* Headings */
  --verso-structure-color: #2d6a4f;

  /* TOC sidebar */
  --verso-toc-background-color: #f0f7f2;

  /* Selection highlight */
  --verso-selected-color: #fde8d0;

  /* Code syntax highlighting */
  --verso-code-keyword-color: #2d6a4f;
  --verso-code-const-color: #5a4a3a;
}

/* ===== Header bar ===== */
header {
  background: linear-gradient(135deg, #2d6a4f 0%, #3a7d5c 100%) !important;
  box-shadow: 0 2px 8px rgba(45, 106, 79, 0.3) !important;
}
.header-title, .header-title h1 {
  color: white !important;
}

/* ===== Section headings ===== */
h1, h2, h3 {
  color: #2d6a4f;
}

/* ===== Links ===== */
a {
  color: #40916c;
}
a:hover {
  color: #e76f51;
}

/* ===== TOC sidebar ===== */
#toc .split-toc .title a {
  color: #2d6a4f;
}
#toc .split-toc .title .current a {
  color: #e76f51;
  font-weight: bold;
}

/* ===== Prev/next navigation ===== */
.prev-next-buttons a {
  color: #e76f51 !important;
  font-weight: 600;
}
.prev-next-buttons a:hover {
  color: #d45a3a !important;
}
.prev-next-buttons .arrow {
  color: #e76f51;
}

/* ===== Definition / Theorem / Lemma boxes ===== */

/* Definitions: green accent */
section:has(> h2[id*='Definition']) {
  background: #f5faf7;
  border-left: 4px solid #2d6a4f;
  padding: 0.8rem 1.2rem;
  margin: 1.5rem 0;
  border-radius: 0 6px 6px 0;
}
section:has(> h2[id*='Definition']) > h2 {
  margin-top: 0.3rem;
}

/* Theorems and Propositions: orange accent */
section:has(> h2[id*='Theorem']),
section:has(> h2[id*='Proposition']) {
  background: #fef6f0;
  border-left: 4px solid #e76f51;
  padding: 0.8rem 1.2rem;
  margin: 1.5rem 0;
  border-radius: 0 6px 6px 0;
}
section:has(> h2[id*='Theorem']) > h2,
section:has(> h2[id*='Proposition']) > h2 {
  margin-top: 0.3rem;
  color: #c05630;
}

/* Lemmas and Corollaries: muted green accent */
section:has(> h2[id*='Lemma']),
section:has(> h2[id*='Corollary']) {
  background: #f7faf5;
  border-left: 4px solid #74b49b;
  padding: 0.8rem 1.2rem;
  margin: 1.5rem 0;
  border-radius: 0 6px 6px 0;
}
section:has(> h2[id*='Lemma']) > h2,
section:has(> h2[id*='Corollary']) > h2 {
  margin-top: 0.3rem;
}

/* Examples: warm neutral accent */
section:has(> h2[id*='Example']) {
  background: #faf9f6;
  border-left: 4px solid #c9b99a;
  padding: 0.8rem 1.2rem;
  margin: 1.5rem 0;
  border-radius: 0 6px 6px 0;
}
section:has(> h2[id*='Example']) > h2 {
  margin-top: 0.3rem;
  color: #8a7a5a;
}

/* Remarks: subtle grey */
section:has(> h2[id*='Remark']) {
  background: #f8f8f8;
  border-left: 4px solid #b0b0b0;
  padding: 0.8rem 1.2rem;
  margin: 1.5rem 0;
  border-radius: 0 6px 6px 0;
}
section:has(> h2[id*='Remark']) > h2 {
  margin-top: 0.3rem;
  color: #666;
}

/* ===== Lean code blocks: more separation from prose ===== */
code.hl.lean.block {
  background: #fef8f0 !important;
  border-left: 3px solid #40916c;
  padding: 0.75rem 1rem !important;
  border-radius: 4px;
  display: block;
  margin: 1.5rem 0;
  box-shadow: 0 1px 3px rgba(0,0,0,0.06);
  font-size: 0.88em;
}

/* Doc comments in code blocks */
.doc-comment.token {
  color: #40916c !important;
}

/* ===== Display math breathing room ===== */
code.math.display {
  display: block;
  margin: 1.2rem 0;
}

/* ===== QED symbol: right-aligned ===== */
.qed-square {
  float: right;
  margin-left: 1em;
}

/* ===== Inline code ===== */
code.math.inline, code.math.display {
  color: #3a3a3a;
}

/* ===== Permalink widget ===== */
.permalink-widget a {
  color: #b7d4c0 !important;
}
.permalink-widget a:hover {
  color: #e76f51 !important;
}

/* ===== Search box ===== */
input[type='search'] {
  border-color: #b7d4c0 !important;
}
input[type='search']:focus {
  border-color: #40916c !important;
  outline-color: #40916c;
}

/* ===== Home page title section ===== */
.titlepage {
  text-align: center;
  padding: 2rem 0 1.5rem;
  margin-bottom: 1.5rem;
  border-bottom: 2px solid #e8f0e8;
}
.titlepage h1 {
  font-size: 2.4rem;
  letter-spacing: -0.02em;
  margin-bottom: 0.3rem;
}
.titlepage .authors {
  font-size: 1.15rem;
  color: #666;
  margin-bottom: 1.2rem;
}
.titlepage + p,
.titlepage ~ p {
  max-width: 38rem;
  margin-left: auto;
  margin-right: auto;
  text-align: center;
  color: #444;
  line-height: 1.6;
}

/* Home page Contents heading */
.titlepage ~ section > h2 {
  text-align: center;
  margin-top: 2rem;
}
.titlepage ~ section .section-toc {
  list-style: none;
  padding: 0;
  text-align: center;
}
.titlepage ~ section .section-toc li {
  padding: 0.4rem 0;
}
.titlepage ~ section .section-toc a {
  font-size: 1.1rem;
  font-weight: 500;
}
"

open Verso.Output in
/-- The theme as a `<style>` element for `config.extraHead`. `escape := false`
keeps CSS combinators like `>` and `:has(...)` intact. -/
def head : Html := .tag "style" #[] (.text false css)

end HexManual.Theme
