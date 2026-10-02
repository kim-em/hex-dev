/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : (!![247303931, 247303931, 247303931, 247303931; 247303931, 465318329, 465318329, 29289533; -247303931, -29289533, 204302889, -231725907; -247303931, -465318329, -698910751, -85645945] : Matrix (Fin 4) (Fin 4) ℚ)⁻¹ = !![(-151011458671391 / 10834268020862763357090), (-1 / 218014398), (-1 / 88618005), (-1 / 88618005); (362407089787 / 38472080110513853130), (848885 / 95726524924233), (20710631 / 2957213488679730), (1 / 88618005); (-4025458 / 1478606744339865), (-1 / 233592422), (-2012729 / 1478606744339865), (-1 / 177236010); (1 / 88618005), 0, (1 / 177236010), (1 / 177236010)] := by inverse

#print axioms result
