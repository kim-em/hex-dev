#!/usr/bin/env python3
"""Check printed Lean reconstruction code with exact FLINT/SymPy semantics.

The generated Lean fixture compiles the actual expressions. This oracle checks
both quoting and the values reconstructed from their native JSON arguments;
replay graph acceptance remains the native checked reader's responsibility.
"""
from fractions import Fraction
import json
import math
from pathlib import Path
import sys
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_closure_root_format import parse_record, integers, root
from scripts.oracle.real_closure_number_field_samples import Reader, require
from scripts.oracle.real_algebraic_qqbar import QQBar, VERSION

CASES = ['rational value', 'rational polynomial', 'point root', 'universal roots',
         'selected reducible root', 'split inverse', 'algebraic polynomial',
         'nested root', 'nested root multiplicity', 'successive infinitesimal',
         'infinitesimal point']
READERS = ['restoreElementText', 'restorePolynomialText', 'restoreRootText',
           'restoreRootSetText', 'restoreRootText', 'restoreElementText',
           'restorePolynomialText', 'restoreRootText', 'restoreRootSetText',
           'restoreElementText', 'restoreRootText']
ERRORS = [('changed reader', 'wrong reconstruction expression'),
          ('missing policy', 'missing reconstruction policy'),
          ('source byte limit', 'reconstruction expression byte limit exceeded'),
          ('packet integer limit', 'integer token limit exceeded'),
          ('truncated literal', 'truncated certificate syntax'),
          ('wrong literal type', 'expected a string'),
          ('unknown provider', 'unknown validated base'),
          ('invalid stored point', 'invalid base payload'),
          ('escaped unknown provider', 'unknown validated base'),
          ('noncanonical expression', 'noncanonical reconstruction expression')]


def argument(row):
    require(set(row) == {'case', 'reader', 'representation', 'packet_text'}, 'wrong Repr record')
    source = row['representation']
    start = '(Hex.RealClosure.Tower.Catalog.' + row['reader'] + ' catalog '
    end = ' limits)'
    require(type(source) is str and source.startswith(start) and source.endswith(end),
            'wrong checked Lean expression')
    literal = parse_record(source[len(start):-len(end)])
    require(type(literal) is str and literal == row['packet_text'], 'quoted packet differs')
    packet = parse_record(literal)
    integers(packet)
    require(type(packet) is list and len(packet) == 2, 'wrong Repr packet fields')
    return packet


def infinitesimal(raw, depth):
    require(type(raw) is list and len(raw) == 3, 'wrong infinitesimal value')
    if depth == 0:
        require(raw[0] == 0 and raw[2] > 0 and math.gcd(*raw[1:]) == 1,
                'noncanonical base rational')
        return sp.Rational(raw[1], raw[2])
    require(raw[0] == 1 and type(raw[1]) is list and type(raw[2]) is list,
            'wrong rational function')
    epsilon = sp.Symbol(f'epsilon{depth}')
    parts = []
    for coefficients in raw[1:]:
        values = [infinitesimal(a, depth-1) for a in coefficients]
        require(not values or values[-1] != 0, 'rational function trailing zero')
        parts.append(sum((a * epsilon**i for i, a in enumerate(values)), sp.Integer(0)))
    require(parts[1] != 0, 'zero rational function denominator')
    return sp.cancel(parts[0] / parts[1])


def verify(rows):
    require([row.get('case') for row in rows] == CASES + ['checked reconstruction failures', 'escaped Lean literals'],
            'missing or reordered Repr cases')
    with QQBar() as q:
        reader = Reader(q)
        alpha = q.unary('sqrt', q.number(2))
        beta = q.unary('sqrt', alpha)
        expected = {0: q.number(Fraction(1,3)), 2: q.number(Fraction(1,3)), 4: alpha,
                    5: q.unary('inv', q.binary('sub', alpha, q.number(3))), 7: beta}
        for i, row in enumerate(rows[:len(CASES)]):
            require(row['reader'] == READERS[i], 'wrong object reader')
            binding, payload = argument(row)
            if i >= 9:
                require(binding == [[], 2, []], 'lost infinitesimal order')
                if i == 10:
                    require(type(payload) is list and len(payload) == 2 and payload[0] == 0,
                            'wrong infinitesimal root kind')
                    payload = payload[1]
                value = infinitesimal(payload, 2)
                require(sp.cancel(value - sp.Symbol('epsilon2')**(-1 if i == 9 else 1)) == 0,
                        'wrong infinitesimal value')
                continue
            parents = reader.context(binding)
            require(len(parents) == (1 if i in (5,6,7,8) else 0), 'wrong algebraic predecessor')
            require(not parents or reader.same(parents[0], alpha), 'wrong predecessor embedding')
            if i in (0,5):
                value = reader.value(payload, parents)
            elif i in (1,6):
                coefficients = reader.poly(payload, parents)
                constant = q.number(-2) if i == 1 else q.unary('neg', alpha)
                require(reader.same_poly(coefficients, [constant, q.number(0), q.number(1)]),
                        'wrong printed polynomial')
                continue
            elif i == 3:
                require(payload == [0, []], 'lost universal roots')
                continue
            elif i == 8:
                require(type(payload) is list and len(payload) == 2 and payload[0] == 1 and
                        type(payload[1]) is list and len(payload[1]) == 1, 'wrong finite root set')
                entry = payload[1][0]
                require(type(entry) is list and len(entry) == 2 and entry[1] == 3,
                        'wrong root multiplicity')
                require(reader.same(root(reader, binding, entry[0]), beta), 'wrong repeated root')
                continue
            else:
                value = root(reader, binding, payload)
            require(reader.same(value, expected[i]), 'wrong printed value')
    failure = rows[len(CASES)]
    require(set(failure) == {'case','rejections'} and type(failure['rejections']) is list and
            len(failure['rejections']) == len(ERRORS), 'missing native rejection')
    functions = ['Catalog.readElementRepr catalog', 'ReprFormat.read "restoreRootText"',
                 'Catalog.readRootRepr catalog', 'Catalog.readRootRepr catalog',
                 'ReprFormat.read "restoreRootText"', 'ReprFormat.read "restoreRootText"',
                 'Catalog.restoreRootText catalog', 'Catalog.restoreRootText catalog',
                 'Catalog.restoreRootText catalog', 'ReprFormat.read "restoreRootText"']
    for i, (entry, (name, message)) in enumerate(zip(failure['rejections'], ERRORS)):
        require(set(entry) == {'case','message','expression'} and entry['case'] == name and
                entry['message'] == message, 'missing or changed native rejection')
        prefix = '(Hex.RealClosure.Tower.' + functions[i] + ' '
        suffix = (' { bytes := 1 })' if i == 2 else ' { digits := 0 })' if i == 3 else ' limits)')
        source = entry['expression']
        require(type(source) is str and source.startswith(prefix) and source.endswith(suffix),
                'wrong rejection expression')
        value = parse_record(source[len(prefix):-len(suffix)])
        require(type(value) is str, 'rejection argument is not a string')
        if i in (6,7,8):
            expected_packet = [[[['missing',0]],0,[]],[0,[0,1,1]]] if i == 6 else \
                [[[],0,[]],[0,[0,1,0]]] if i == 7 else \
                [[[['α\n"\\λ𐐷',17]],0,[]],[0,[0,1,1]]]
            require(parse_record(value) == expected_packet, 'changed rejected packet')
    literals = rows[-1]
    require(set(literals) == {'case','literals'} and type(literals['literals']) is list and
            len(literals['literals']) == 5, 'missing escaped literals')
    for entry, text in zip(literals['literals'], ['"', '\\', chr(1), 'λ𐐷', r'\u0001']):
        require(set(entry) == {'quoted','codepoints'} and type(entry['quoted']) is str and
                type(entry['codepoints']) is list and all(type(n) is int for n in entry['codepoints']) and
                entry['codepoints'] == [ord(c) for c in text] and
                parse_record(entry['quoted']) == text, 'wrong Lean literal code points')
    return len(CASES)


def lean_checks(rows):
    """Compile the actual printed code, with the documented caller bindings."""
    template = '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRepr
public meta import HexRealClosure.TowerBytes
public meta import HexRealClosure.RootBytes
public meta import HexRealClosure.ReprFormat
public meta import HexRealClosure.TowerRepr

/-! Generated from hexrealclosure_repr_conformance by real_closure_repr.py --lean-checks. -/

public section

open Hex.RealClosure Hex.RealClosure.Tower
private def registry : BaseContext.Registry := fun _ => none
private def catalog : Catalog registry := Catalog.empty registry
private def limits : Hex.SignDet.Codec.Limits := {}
'''
    for kind in ['Element', 'Polynomial', 'Root', 'RootSet']:
        template += f'''
private def check{kind} (result : Except String (Packed{kind} registry)) (expected : String) : Bool :=
  match result with
  | .error _ => false
  | .ok value => value.writeText == expected
'''
    for row in rows[:len(CASES)]:
        argument(row)
        kind = row['reader'].removeprefix('restore').removesuffix('Text')
        template += '\n-- ' + row['case'] + '\n#guard check' + kind + ' ' + row['representation']
        template += ' ' + json.dumps(row['packet_text'], ensure_ascii=False) + '\n'
    template += """
private def checkError {α : Type u} (result : Except String α) (expected : String) : Bool :=
  match result with
  | .error message => message == expected
  | .ok _ => false
"""
    for entry in rows[len(CASES)]['rejections']:
        template += '\n-- ' + entry['case'] + '\n#guard checkError ' + entry['expression']
        template += ' ' + json.dumps(entry['message']) + '\n'
    for entry in rows[-1]['literals']:
        points = ', '.join('Char.ofNat ' + str(n) for n in entry['codepoints'])
        template += '\n#guard (' + entry['quoted'] + ' : String) == String.ofList [' + points + ']\n'
    return template


if __name__ == '__main__':
    generate = '--lean-checks' in sys.argv
    files = [a for a in sys.argv[1:] if a != '--lean-checks']
    text = Path(files[0]).read_text() if files else sys.stdin.read()
    rows = [parse_record(line) for line in text.splitlines() if line.strip()]
    if generate:
        verify(rows)
        print(lean_checks(rows), end='')
    else:
        print(f'verified {verify(rows)} printed Lean expressions with {VERSION} and SymPy {sp.__version__}')
