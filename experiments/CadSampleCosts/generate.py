#!/usr/bin/env python3
"""Generate literal/replay modules from the checked Emit module's Lake output.

lake build +CadSampleCosts.Emit:olean > emit.log
python3 experiments/CadSampleCosts/generate.py emit.log
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent
CASES = {
    'Vanishing': '∀ x : ℝ, x^4+x^2-1=0 → (x^2)^2+x^2-1=0',
    'Nlsat': '∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0',
    'CircleParabola': '∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0',
    'Circles': '∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0',
    'Kahan': '∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0',
    'Sphere': '∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0',
    'Tower4': '∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0',
    'Tower8': '∀ y : ℝ, y^8-2=0 → y>1 → y-y^2<0',
}
SAMPLES = {
 'Sphere': ('∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 2*((t^3-9*t)/4)^2=1 ∧ 3*((11*t-t^3)/6)^2=1 ∧ (t^3-9*t)/4>0 ∧ (11*t-t^3)/6>0 ∧ 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0', 'sphereSample'),
 'Nlsat': ('∀ a b : ℝ, 16*a^3-8*a^2+a+16=0 → a<0 → a^2+b^2=1 → a^3+2*a^2+3*b^2-5<0', 'nlsatSign'),
 'CircleParabola': ('∀ a b : ℝ, a^2+b^2=1 → b=a^2 → a>0 → b-a<0', 'circleParabolaSign'),
 'Circles': ('∀ a b : ℝ, a^2+b^2=1 → (a-1)^2+b^2=1 → b>0 → b-a>0', 'circlesSign'),
 'Kahan': ('∀ t : ℝ, t^2-2=0 → 1<t → t<2 → ((1+t)/4)^2+(t/8)^2-1<0', 'kahanSign'),
}
PREFIX = 'CadSampleCosts'
HEADER = '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
'''


def generate(log):
    keys = ['carrier_degree', 'carrier_height', 'sturm_max_height', 'sturm_length', 'atom_count']
    rows = {m[0]: dict(zip(keys, map(int, m[1:]))) for m in re.findall(
        r'CAD_(\w+)_META (\d+) (\d+) (\d+) (\d+) (\d+)', log)}
    if set(rows) != set(CASES):
        raise ValueError('metadata/case mismatch')
    (ROOT/'kernel-inputs.json').write_text(json.dumps(rows, indent=2)+'\n')
    fixtures = HEADER + 'public import HexRCF.Certificate\npublic section\n\n'
    validate = HEADER + f'public import {PREFIX}.Support\npublic meta import {PREFIX}.Support\n'
    for case in CASES:
        validate += f'public import {PREFIX}.{case}.Replay\npublic import {PREFIX}.{case}.Kernel\n'
    validate += '\npublic section\nnamespace CadSampleCosts\n'
    for case, goal in CASES.items():
        for kind in ('INPUT', 'CERT'):
            matches = re.findall(rf'CAD_{case}_{kind}_BEGIN\n(.*?)\nCAD_{case}_{kind}_END', log, re.S)
            if len(matches) != 1:
                raise ValueError(f'expected one {case} {kind}, got {len(matches)}')
            name = f'cad{case}{kind.title()}'
            fixtures += f'syntax "{name}" : term\nmacro_rules\n  | `({name}) => `({matches[0]})\n\n'
        folder = ROOT / case
        folder.mkdir(exist_ok=True)
        body = HEADER + f'public import {PREFIX}.Fixtures\npublic import HexRCF.Soundness\n'
        body += f'public import {PREFIX}.Transport\npublic meta import {PREFIX}.Support\n'
        body += f'public section\nnamespace CadSampleCosts.{case}\n'
        body += f'@[expose] def input : Hex.RCF.Sentence := cad{case}Input\n'
        body += f'@[expose] def certificate : Hex.RCF.Certificate := cad{case}Cert\n'
        body += f'theorem correspondence : input.toProp ↔ ({goal}) := cad_correspondence% ({goal})\n'
        (folder / 'Literal.lean').write_text(body + f'end CadSampleCosts.{case}\n')
        body += 'theorem accepted : certificate.check input = true := by decide +kernel\n'
        body += 'theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted\n'
        body += f'theorem sign : {goal} := correspondence.mp result\n'
        if case in SAMPLES:
            statement, transport = SAMPLES[case]
            body += f'theorem sample : {statement} := {transport} sign\n'
        (folder / 'Replay.lean').write_text(body + f'end CadSampleCosts.{case}\n')
        kernel = HEADER + f'public import {PREFIX}.Fixtures\nimport Mathlib.Util.CountHeartbeats\n'
        kernel += f'public section\nnamespace CadSampleCosts.{case}.Kernel\n'
        kernel += f'@[expose] def input : Hex.RCF.Sentence := cad{case}Input\n'
        kernel += f'@[expose] def certificate : Hex.RCF.Certificate := cad{case}Cert\n'
        kernel += 'set_option profiler true in\nset_option profiler.threshold 0 in\n#count_heartbeats in\n'
        kernel += 'theorem accepted : certificate.check input = true := by decide +kernel\n'
        (folder / 'Kernel.lean').write_text(kernel + f'end CadSampleCosts.{case}.Kernel\n')
        validate += f'\ntheorem {case[0].lower()+case[1:]} : {goal} :=\n'
        validate += f'  (cad_correspondence% ({goal})).mp {case}.result\n'
    # Axiom traversals belong to this untimed validation module.
    names = []
    transport = (ROOT / 'Transport.lean').read_text()
    names += [f'CadSampleCosts.{n}' for n in re.findall(r'^theorem (\w+)', transport, re.M)]
    for case in CASES:
        names += [f'CadSampleCosts.{case}.Kernel.accepted']
        names += [f'CadSampleCosts.{case}.{n}' for n in
                  (['accepted', 'result', 'sign', 'sample'] if case in SAMPLES else ['accepted', 'result', 'sign'])]
    for name in names:
        validate += f'\n#print axioms {name}\n'
    (ROOT / 'axiom-names.json').write_text(json.dumps(names, indent=2) + '\n')
    (ROOT / 'Fixtures.lean').write_text(fixtures.rstrip() + '\n')
    (ROOT / 'Validate.lean').write_text(validate + '\nend CadSampleCosts\n')


if __name__ == '__main__':
    generate(pathlib.Path(sys.argv[1]).read_text())
