#!/usr/bin/env python3
"""Exact FLINT semantics for original number-field coordinates and native samples.

Reconstruct selected real roots, evaluate every coefficient in its original
embedding, and check all sections, sectors and repeated-root multiplicities.
Native certificate graphs and byte readers are exercised by the Lean emitter;
this oracle independently checks their selected-root semantics.
"""
from fractions import Fraction
from functools import cmp_to_key
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.oracle.real_algebraic_qqbar import QQBar, VERSION

CASES = ['cubic field', 'middle cubic field', 'common quadratic fields', 'rational field']
HEADS = [[-2,0,0,1], [1,-3,0,1], [1,0,-10,0,1], [-2,1]]


def require(test, message):
    if not test:
        raise ValueError(message)


def parse_record(text):
    def pairs(entries):
        result = {}
        for key, value in entries:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs)


class Reader:
    def __init__(self, q):
        self.q = q
        self.zero, self.one = q.number(0), q.number(1)
        self.contexts = {}

    def sign(self, value):
        return self.q.compare(value, self.zero)

    def same(self, a, b):
        return self.q.compare(a, b) == 0

    def rat(self, raw):
        require(isinstance(raw, list) and len(raw) == 2 and
                all(type(i) is int for i in raw) and raw[1] > 0 and
                math.gcd(*raw) == 1, 'noncanonical rational')
        return self.q.number(Fraction(*raw))

    def evaluate(self, coefficients, x):
        value = self.zero
        for a in reversed(coefficients):
            value = self.q.binary('add', a, self.q.binary('mul', x, value))
        return value

    def coordinate(self, raw, generator):
        require(isinstance(raw, list), 'malformed original coordinate')
        coefficients = [self.rat(c) for c in raw]
        require(not coefficients or self.sign(coefficients[-1]) != 0, 'coordinate trailing zero')
        return self.evaluate(coefficients, generator)

    def value(self, raw, roots):
        require(isinstance(raw, list), 'malformed native value')
        if not roots:
            require(len(raw) == 3 and type(raw[0]) is int and raw[0] == 0,
                    'native predecessor is not rational')
            return self.rat(raw[1:])
        if raw == []:
            return self.zero
        require(len(raw) == 2 and isinstance(raw[0], list) and raw[0] and
                type(raw[1]) is int and raw[1] in (-1,1), 'malformed stored value')
        coefficients = [self.value(a, roots[:-1]) for a in raw[0]]
        require(self.sign(coefficients[-1]) != 0, 'native coefficient trailing zero')
        value = self.evaluate(coefficients, roots[-1])
        require(self.sign(value) == raw[1], 'native cached sign differs')
        return value

    def poly(self, raw, roots):
        require(isinstance(raw, list), 'malformed native polynomial')
        coefficients = [self.value(a, roots) for a in raw]
        require(not coefficients or self.sign(coefficients[-1]) != 0, 'polynomial trailing zero')
        return coefficients

    def same_poly(self, a, b):
        return len(a) == len(b) and all(self.same(x,y) for x,y in zip(a,b))

    def endpoint(self, raw, roots):
        require(isinstance(raw, list) and raw and type(raw[0]) is int, 'malformed endpoint')
        if raw == [0]:
            return (-1,None)
        if raw == [2]:
            return (1,None)
        require(len(raw) == 2 and raw[0] == 1, 'malformed finite endpoint')
        return (0,self.value(raw[1],roots))

    def same_endpoint(self, a, b):
        return a[0] == b[0] and (a[0] != 0 or self.same(a[1],b[1]))

    def between(self, x, lower, upper):
        return (lower[0] == -1 or lower[0] == 0 and self.q.compare(lower[1],x) < 0) and \
               (upper[0] == 1 or upper[0] == 0 and self.q.compare(x,upper[1]) < 0)

    def context(self, raw):
        require(isinstance(raw,list) and len(raw) == 3 and raw[0] == [] and
                type(raw[1]) is int and raw[1] == 0 and isinstance(raw[2],list),
                'wrong context predecessor')
        key = json.dumps(raw, separators=(',',':'))
        if key in self.contexts:
            return self.contexts[key]
        roots = []
        for frame in raw[2]:
            require(isinstance(frame,list) and len(frame) == 7 and frame[0] == [0] and
                    type(frame[0][0]) is int and isinstance(frame[6],list), 'malformed root frame')
            head = self.poly(frame[1],roots)
            require(len(head) > 1, 'constant selected head')
            lower, upper = self.endpoint(frame[2],roots), self.endpoint(frame[3],roots)
            slots, signs = frame[4:6]
            require(isinstance(slots,list) and all(type(i) is int and 1 <= i < len(head) for i in slots)
                    and len(set(slots)) == len(slots) and isinstance(signs,list) and
                    len(signs) == len(slots) and all(type(s) is int and s in (-1,0,1) for s in signs),
                    'malformed Thom data')
            derivatives = []
            derivative = head
            for _ in range(len(head)-1):
                derivative = [self.q.binary('mul',self.q.number(i),a)
                              for i,a in enumerate(derivative) if i]
                derivatives.append(derivative)
            candidates = self.q.roots(head)
            require(all(m == 1 for _,m in candidates), 'repeated selected head')
            selected = [x for x,_ in candidates if self.between(x,lower,upper) and
                        [self.sign(self.evaluate(derivatives[i-1],x)) for i in slots] == signs]
            require(len(selected) == 1, 'context does not select one root')
            roots.append(selected[0])
        self.contexts[key] = roots
        return roots

    def multiply(self, a, b):
        if not a or not b:
            return []
        output = [self.zero] * (len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                output[i+j] = self.q.binary('add', output[i+j], self.q.binary('mul',x,y))
        return output

    def sample(self, parent, original, sample, cell):
        require(isinstance(sample,dict) and set(sample) ==
                {'context','value','cell','polynomials','signs','member'}, 'malformed sample')
        roots = self.context(sample['context'])
        local_bound = 1 if cell[0] == 'section' else sum(x[0] == 0 for x in cell[1:])
        require(sample['context'][:2] == parent[:2] and
                sample['context'][2][:len(parent[2])] == parent[2] and
                len(roots) <= len(parent[2])+local_bound, 'nonlocal sample context')
        converted = [self.poly(p,roots) for p in sample['polynomials']]
        require(len(converted) == len(original) and
                all(self.same_poly(a,b) for a,b in zip(converted,original)),
                'sample coefficient conversion changed original values')
        point = self.value(sample['value'],roots)
        actual = sample['cell']
        if cell[0] == 'section':
            require(set(actual) == {'kind','root'} and actual['kind'] == 'section', 'wrong section kind')
            require(self.same(self.value(actual['root'],roots),cell[1]) and self.same(point,cell[1]),
                    'wrong section boundary')
        else:
            require(set(actual) == {'kind','lower','upper'} and actual['kind'] == 'sector', 'wrong sector kind')
            lower,upper = self.endpoint(actual['lower'],roots),self.endpoint(actual['upper'],roots)
            require(self.same_endpoint(lower,cell[1]) and self.same_endpoint(upper,cell[2]),
                    'wrong sector bounds')
            require(self.between(point,lower,upper), 'sample outside sector')
        require(sample['member'] is True, 'native membership failed')
        require(isinstance(sample['signs'],list) and all(type(s) is int for s in sample['signs']) and
                sample['signs'] == [self.sign(self.evaluate(p,point)) for p in original],
                'wrong original sign vector')


def verify(rows):
    require([r.get('case') for r in rows] == CASES, 'missing or reordered cases')
    with QQBar() as q:
        r = Reader(q)
        for index,row in enumerate(rows):
            require(set(row) == {'case','generator_head','generator_lower','generator_upper','inputs',
                                'packed_inputs','context','original_polynomials','polynomials',
                                'sections','sectors','repeated_roots'}, 'malformed family')
            require(row['generator_head'] == HEADS[index] and
                    all(type(z) is int for z in row['generator_head']), 'wrong generator polynomial')
            lower,upper = r.rat(row['generator_lower']),r.rat(row['generator_upper'])
            candidates = [x for x,_ in q.roots([q.number(z,q.integer) for z in HEADS[index]],integer=True)
                          if q.compare(lower,x) < 0 and q.compare(x,upper) < 0]
            require(len(candidates) == 1, 'wrong original embedding bounds')
            generator = candidates[0]
            a,b = q.unary('sqrt',q.number(2)),q.unary('sqrt',q.number(3))
            if index == 0:
                require(q.compare(q.number(1),generator) < 0 and q.compare(generator,q.number(2)) < 0,
                        'wrong cubic embedding')
                expected_inputs = [generator]
            elif index == 1:
                require(q.compare(r.zero,generator) < 0 and q.compare(generator,r.one) < 0,
                        'wrong middle cubic embedding')
                expected_inputs = [generator]
            elif index == 2:
                require(r.same(generator,q.binary('add',a,b)), 'wrong common generator embedding')
                expected_inputs = [a,b]
            else:
                require(r.same(generator,q.number(2)), 'wrong rational embedding')
                expected_inputs = [r.one,q.number(2)]
            original_inputs = [r.coordinate(c,generator) for c in row['inputs']]
            require(len(original_inputs) == len(expected_inputs) and
                    all(r.same(x,y) for x,y in zip(original_inputs,expected_inputs)),
                    'original input coordinates changed')
            parent = r.context(row['context'])
            require(len(parent) == 1 and r.same(parent[0],generator), 'native field changed embedding')
            packed_inputs = [r.value(c,parent) for c in row['packed_inputs']]
            require(len(packed_inputs) == len(original_inputs) and
                    all(r.same(x,y) for x,y in zip(packed_inputs,original_inputs)), 'packed input changed')
            original = [[r.coordinate(a,generator) for a in p] for p in row['original_polynomials']]
            if index == 3:
                expected = [[r.one],[q.number(2)],[]]
            else:
                expected = [[q.unary('neg',expected_inputs[-1]),r.zero,r.one],
                            [q.unary('neg',a if index == 2 else r.one),r.one]]
            require(len(original) == len(expected) and
                    all(r.same_poly(x,y) for x,y in zip(original,expected)), 'wrong original polynomials')
            packed = [r.poly(p,parent) for p in row['polynomials']]
            require(len(packed) == len(original) and
                    all(r.same_poly(x,y) for x,y in zip(packed,original)), 'packed coefficients changed')
            boundaries = []
            for p in original:
                if len(p) > 1:
                    for x,_ in q.roots(p):
                        if all(not r.same(x,y) for y in boundaries):
                            boundaries.append(x)
            boundaries.sort(key=cmp_to_key(q.compare))
            require(len(row['sections']) == len(boundaries) and len(row['sectors']) == len(boundaries)+1,
                    'incomplete cells')
            for sample,x in zip(row['sections'],boundaries):
                r.sample(row['context'],original,sample,('section',x))
            endpoints = [(-1,None)] + [(0,x) for x in boundaries] + [(1,None)]
            for sample,l,u in zip(row['sectors'],endpoints,endpoints[1:]):
                r.sample(row['context'],original,sample,('sector',l,u))
            repeated = r.multiply(r.multiply(original[0],original[0]),original[1])
            roots = sorted(q.roots(repeated),key=cmp_to_key(lambda x,y:q.compare(x[0],y[0])))
            require(len(row['repeated_roots']) == len(roots), 'incomplete repeated roots')
            for entry,(x,multiplicity) in zip(row['repeated_roots'],roots):
                require(set(entry) == {'multiplicity','sample'} and type(entry['multiplicity']) is int and
                        entry['multiplicity'] == multiplicity, 'wrong original multiplicity')
                r.sample(row['context'],original,entry['sample'],('section',x))
    return len(rows)


if __name__ == '__main__':
    source = Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    print(f'verified {verify([parse_record(line) for line in source.splitlines() if line.strip()])} '
          f'number-field sample families with {VERSION}')
