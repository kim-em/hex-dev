/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexManual
import HexManual.Theme

open Verso.Genre Manual

/--
Render configuration for the `HexManual` Verso site: multi-page HTML only
(no single-page or TeX output), with a navigation depth of two so each
chapter and its top-level sections get their own pages.
-/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  -- Site-wide green/orange theme (a `<style>` plus a small kind-tagging
  -- `<script>`), injected into every page's `<head>` (see
  -- `HexManual/Theme.lean`).
  extraHead := HexManual.Theme.head
  -- Bundle the committed comparator figures into the site root (served at
  -- `<pages>/figures/…`); the HexLLL performance chapter embeds them. A
  -- directory copy so Verso's `copyRecursively` creates the `figures/` dir
  -- (a nested file dest is not created and fails).
  extraFiles := [("reports/figures", "figures")]

/--
Entry point for the `hexmanual` executable. Renders the `HexManual` document
to static HTML. Pass `--output <dir>` to choose the destination (defaults to
`_out`); the browsable site lands in `<dir>/html-multi`.
-/
def main := manualMain (%doc HexManual) (config := config)
