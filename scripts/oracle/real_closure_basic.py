#!/usr/bin/env python3
"""Exact Z3 RCF checks of CADE 2013 section 4 introductory tower examples.

The source's pi-dependent cases are unsupported without a caller provider.
Selected roots, transported coefficients and native arithmetic are checked in
one exact RCF context; native replay graph acceptance is checked by the emitter.
"""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.sign_det_z3 import RCF, check_version
from scripts.oracle.real_closure_isolation import native_value, sign
from scripts.oracle.real_closure_number_field_samples import require

CASES = ['basic square root', 'basic infinitesimal', 'basic unsupported']


def parse_record(text):
    def pairs(entries):
        out = {}
        for key, value in entries:
            require(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    def invalid(_):
        raise ValueError('noninteger JSON number')
    return json.loads(text, object_pairs_hook=pairs, parse_float=invalid, parse_constant=invalid)


def integers(value):
    if type(value) is int:
        return
    require(type(value) is list, 'noninteger native leaf')
    for child in value:
        integers(child)


class Reader:
    def __init__(self):
        self.rcf = RCF({'id': 10377, 'levels': ['epsilon1'],
                        'order': 'each-new-level-smaller-than-positive-base-elements'})

    def value(self, data, roots, depth):
        integers(data)
        return native_value(self.rcf, data, roots, depth)

    def selected(self, frame, roots, depth):
        integers(frame)
        require(type(frame) is list and len(frame) == 7 and frame[0] == [0] and
                type(frame[6]) is list and frame[6], 'incomplete selected root')
        r = self.rcf
        head = [self.value(c, roots, depth) for c in frame[1]]
        require(len(head) > 1 and head[-1] != 0 and r.squarefree(head), 'invalid selected head')
        def endpoint(raw):
            if raw == [0]:
                return (-1,None)
            if raw == [2]:
                return (1,None)
            require(type(raw) is list and len(raw) == 2 and raw[0] == 1, 'invalid endpoint')
            return (0,self.value(raw[1], roots, depth))
        lower, upper = endpoint(frame[2]), endpoint(frame[3])
        slots, signs = frame[4:6]
        require(type(slots) is list and all(type(i) is int and 1 <= i < len(head) for i in slots)
                and len(set(slots)) == len(slots) and type(signs) is list and len(signs) == len(slots)
                and all(type(s) is int and s in (-1,0,1) for s in signs), 'invalid Thom word')
        derivatives = r.derivatives(head)
        candidates = [a for a in r.api.MkRoots(head, r.context)
                      if (lower[0] == -1 or lower[0] == 0 and lower[1] < a) and
                         (upper[0] == 1 or upper[0] == 0 and a < upper[1]) and
                         [sign(r.eval(derivatives[i-1], a)) for i in slots] == signs]
        require(len(candidates) == 1, 'descriptor does not select one root')
        return candidates[0]

    def context(self, signature, depth, count):
        integers(signature)
        require(type(signature) is list and len(signature) == 3 and signature[0] == [] and
                signature[1] == depth and type(signature[2]) is list and len(signature[2]) == count,
                'wrong stage or algebraic depth')
        roots = []
        for frame in signature[2]:
            roots.append(self.selected(frame, roots, depth))
        return roots


def verify(rows):
    check_version()
    require([row.get('case') for row in rows] == CASES, 'missing or reordered basic cases')
    r = Reader()
    q = r.rcf
    first = rows[0]
    require(set(first) == {'case','context','roots','multiplicities','values','signs'}, 'wrong basic root record')
    require(type(first['roots']) is list and len(first['roots']) == 2 and
            first['multiplicities'] == [1,1] and all(type(n) is int for n in first['multiplicities']),
            'wrong square-root multiplicities')
    original = [r.selected(frame, [], 0) for frame in first['roots']]
    alpha = original[1]
    require(original[0] == -alpha and original[0] < 0 and alpha > 0 and alpha*alpha == 2,
            'wrong square-root selection or order')
    roots = r.context(first['context'], 0, 1)
    require(roots[0] == alpha and first['context'][2][0] == first['roots'][1],
            'square-root owner differs from actual producer')
    require(len(q.api.MkRoots([q.one*-2,q.zero,q.one],q.context)) == 2 and
            q.squarefree([q.one*-2,q.zero,q.one]), 'wrong independent square-root count/multiplicity')
    expected = [alpha, q.one.__div__(alpha), q.one*2, alpha*alpha*alpha+1]
    values = [r.value(a, roots, 0) for a in first['values']]
    require(values == expected and first['signs'] == [sign(a) for a in expected] and
            all(type(s) is int for s in first['signs']), 'wrong square-root arithmetic')

    second = rows[1]
    require(set(second) == {'case','parent','context','parameter','transported_values','transported_signs','bound','head','root',
                           'multiplicity','values','signs'}, 'wrong basic infinitesimal record')
    parents = r.context(second['parent'], 1, 1)
    child = r.context(second['context'], 1, 2)
    require(parents[0] == alpha and child[0] == alpha and
            second['context'][2][:-1] == second['parent'][2] and
            second['root'] == second['context'][2][-1], 'lost original square-root owner')
    epsilon = q.levels[0]
    require(r.value(second['parameter'], parents, 1) == epsilon, 'wrong parameter')
    transported = [r.value(a, parents, 1) for a in second['transported_values']]
    require(transported == expected and second['transported_signs'] == [1,1,1,1] and
            all(type(s) is int for s in second['transported_signs']), 'wrong transported arithmetic')
    old = first['context'][2][0]
    lifted = second['parent'][2][0]
    require(lifted[4:6] == old[4:6], 'changed transported Thom data')
    require([r.value(c, [], 1) for c in lifted[1]] == [r.value(c, [], 0) for c in old[1]],
            'changed transported defining polynomial')
    for before, after in zip(old[2:4], lifted[2:4]):
        require(before[0] == after[0] and (len(before) == len(after) == 1 or
                len(before) == len(after) == 2 and r.value(before[1], [], 0) == r.value(after[1], [], 1)),
                'changed transported endpoint')
    bound = r.value(second['bound'], parents, 1)
    require(bound == q.one.__div__(epsilon)-10**27 and bound > 0, 'wrong reciprocal comparison')
    head = [r.value(a, parents, 1) for a in second['head']]
    require(head == [-epsilon,q.zero,q.zero,q.one], 'wrong paper cubic')
    require(len(q.api.MkRoots(head,q.context)) == 1 and q.squarefree(head),
            'wrong independent cubic count/multiplicity')
    beta = r.selected(second['root'], parents, 1)
    require(beta == child[-1] and beta > epsilon and beta < 1 and beta**3 == epsilon and
            type(second['multiplicity']) is int and second['multiplicity'] == 1, 'wrong infinitesimal root')
    expected = [beta,epsilon,beta-epsilon,q.zero,beta-1]
    values = [r.value(a, child, 1) for a in second['values']]
    require(values == expected and second['signs'] == [1,1,1,0,-1] and
            all(type(s) is int for s in second['signs']), 'wrong infinitesimal arithmetic')
    require(rows[2] == {'case':'basic unsupported',
                       'cases':['pi-infinitesimal-cubic','pi-infinitesimal-comparison'],
                       'cubic_coefficients':['-pi','sqrt(2)+pi','epsilon','1'],
                       'comparison':'2+2*pi+pi^2-2*epsilon-2*pi*epsilon+epsilon^2 < 2+2*pi+pi^2',
                       'reason':'requires a caller-validated pi approximation provider and progress laws'},
            'missing source non-coverage')
    return len(values) + 4


if __name__ == '__main__':
    text = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    print(f'verified {verify([parse_record(line) for line in text.splitlines() if line.strip()])} basic values with Z3 4.15.4')
