#!/usr/bin/env python3
"""Generate literal/replay modules from the checked Emit module's Lake output.

lake build +HexIntervalAlgebraic.Experiment.CadSampleCosts.Emit:olean > emit.log
python3 HexIntervalAlgebraic/Experiment/CadSampleCosts/generate.py emit.log
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent
CASES = {
    'Nlsat': '∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0',
    'CircleParabola': '∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0',
    'Circles': '∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0',
    'Kahan': '∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0',
    'Sphere': '∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0',
    'Tower4': '∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0',
    'Tower8': '∀ y : ℝ, y^8-2=0 → y>1 → y-y^2<0',
}
PREFIX = 'HexIntervalAlgebraic.Experiment.CadSampleCosts'
HEADER = '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
'''


def generate(log):
    fixtures = HEADER + 'public import HexRCF.Certificate\npublic section\n\n'
    validate = HEADER + f'public import {PREFIX}.Support\npublic meta import {PREFIX}.Support\n'
    for case in CASES:
        validate += f'public import {PREFIX}.{case}.Replay\n'
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
        body += f'public section\nnamespace CadSampleCosts.{case}\n'
        body += f'@[expose] def input : Hex.RCF.Sentence := cad{case}Input\n'
        body += f'@[expose] def certificate : Hex.RCF.Certificate := cad{case}Cert\n'
        (folder / 'Literal.lean').write_text(body + f'end CadSampleCosts.{case}\n')
        body += 'theorem accepted : certificate.check input = true := by decide +kernel\n'
        body += 'theorem result : input.toProp := Hex.RCF.check_sound input certificate accepted\n'
        body += '#print axioms result\n'
        (folder / 'Replay.lean').write_text(body + f'end CadSampleCosts.{case}\n')
        validate += f'\ntheorem {case[0].lower()+case[1:]} : {goal} :=\n'
        validate += f'  (cad_correspondence% ({goal})).mp {case}.result\n'
    (ROOT / 'Fixtures.lean').write_text(fixtures)
    (ROOT / 'Validate.lean').write_text(validate + '\nend CadSampleCosts\n')


if __name__ == '__main__':
    generate(pathlib.Path(sys.argv[1]).read_text())
