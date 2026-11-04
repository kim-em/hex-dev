#!/usr/bin/env python3
"""Freeze a balanced F4 corpus before collecting acceptance measurements."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess

import sympy

REVISION = 'f18c2db3a288f20f63f752b44e0171cf1cb86163'
BATCH_SIZE = 1024
FIELDS = [(2, 2), (15, 32003), (31, 2147483647)]
PUBLIC = {
    'cyclic': ['cyclic7', 'cyclic9', 'cyclic10'],
    'kat': ['kat8', 'kat14', 'kat15'],
    'eco': ['eco11', 'eco14', 'eco15'],
    'noon': ['noon5', 'noon6', 'noon7'],
    'reimer': ['reimer6', 'reimer7', 'reimer8'],
    'minrank': [f'minrank_d_2_p_2_q_{q}_r_2' for q in [4, 6, 7]],
    'sparse-structured': ['KLYZ12', 'KLYZ13', 'KLYZ22'],
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def canonical(generators, p, variables):
    """Combine coefficients in the ordinary polynomial ring; retain squares."""
    result, seen = [], set()
    for polynomial in generators:
        terms = {}
        for powers, coefficient in polynomial:
            assert len(powers) == variables and all(e >= 0 for e in powers)
            key = tuple(powers)
            terms[key] = (terms.get(key, 0) + coefficient) % p
        polynomial = [[list(e), c] for e, c in sorted(terms.items(),
                      key=lambda item: (-sum(item[0]), tuple(reversed(item[0])))) if c]
        key = json.dumps(polynomial)
        if polynomial and key not in seen:
            seen.add(key)
            result.append(polynomial)
    return result


def public_input(data, p, integer_lift=False):
    # Input expressions come from the pinned, trusted public example checkout.
    lines = data.decode().splitlines()
    names = [name.strip() for name in lines[0].split(',') if name.strip()]
    assert len(names) == len(set(names)) and names
    assert int(lines[1].strip().rstrip(',')) in [0, p] or integer_lift, 'coefficient-field mismatch'
    symbols = [sympy.Symbol(name) for name in names]
    local = dict(zip(names, symbols))
    generators = []
    for expression in ''.join(lines[2:]).split(','):
        if not expression.strip():
            continue
        polynomial = sympy.Poly(sympy.sympify(expression.replace('^', '**'), locals=local),
                                *symbols, domain='ZZ')
        generators.append([[list(e), int(c)] for e, c in polynomial.terms()])
    return dict(p=p, variables=len(names), order='grevlex',
                generators=canonical(generators, p, len(names)))


def generated(family, n, p, seed):
    rng = random.Random(seed)

    def term(*indices, coefficient=1):
        powers = [0] * n
        for i in indices:
            powers[i] += 1
        return [powers, coefficient]

    if family == 'dense-quadratic':
        support = [term(i) for i in range(n)] + [term(i, j) for i in range(n) for j in range(i, n)]
        polynomials = [[[powers, rng.randrange(p)] for powers, _ in support] for _ in range(n)]
    elif family == 'triangular':
        polynomials = [[term(i, n-1), term(i+1, coefficient=-1)] for i in range(n-1)]
        polynomials.append([term(n-1, n-1), term(coefficient=-1)])
    elif family == 'positive-dimensional':
        # Successive substitution leaves the final two variables free.
        polynomials = [[term(i), term(i+1, i+2, coefficient=-1)] for i in range(n-2)]
    elif family == 'sparse-structured':
        polynomials = [[term(i, i, i), term((i+1) % n, coefficient=-1),
                        term((i+3) % n, coefficient=-1)] for i in range(n)]
    else:
        raise ValueError(family)
    return dict(p=p, variables=n, order='grevlex', generators=canonical(polynomials, p, n))


def main():
    if not __debug__:
        raise SystemExit("corpus validation requires Python without -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gamba', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    checkout = args.gamba.resolve()
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    assert revision == REVISION, 'public input revision differs'
    assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no',
                                        '--', 'examples', 'LICENSE.md'], cwd=checkout), 'modified public inputs'
    out = args.output.resolve()
    out.mkdir(exist_ok=False)
    files, cases = {}, []

    def put(path, data):
        assert path not in files
        files[path] = sha(data)
        dest = out / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)

    put('upstream/gamba/LICENSE.md', (checkout / 'LICENSE.md').read_bytes())

    def record(name, family, split, value, provenance):
        relative = f'{split}/{name}.json'
        put(relative, encoded(value))
        cases.append(dict(name=name, family=family, split=split, input=relative,
                          p=value['p'], variables=value['variables'], order=value['order'],
                          input_sha256=files[relative], provenance=provenance))

    for family, names in PUBLIC.items():
        for name in names:
            for width, p in FIELDS:
                filename = f'{name}-{0 if p == 2 else width}.txt'
                source = checkout / 'examples' / filename
                if not source.is_file():
                    assert p == 2
                    filename = f'{name}-15.txt'
                    source = checkout / 'examples' / filename
                data = source.read_bytes()
                relative = f'upstream/gamba/examples/{filename}'
                if relative not in files:
                    put(relative, data)
                provenance = dict(repository='https://github.com/gblanco92/gamba', revision=revision,
                                  path=f'examples/{filename}', sha256=sha(data),
                                  source_characteristic=int(data.decode().splitlines()[1].strip().rstrip(',')),
                                  conversion='Written integer coefficients reduced modulo the target prime; ordinary polynomial ring. Cross-characteristic lifts define new systems, not field homomorphisms.')
                record(f'{name}-{width}', family, 'primary', public_input(data, p, integer_lift=p == 2), provenance)
    for family, sizes in [('dense-quadratic', [6, 8, 10]), ('triangular', [6, 8, 10]),
                          ('positive-dimensional', [6, 8, 10])]:
        for n in sizes:
            for width, p in FIELDS:
                seed = 109870000 + 1000*n + p
                value = generated(family, n, p, seed)
                record(f'{family}{n}-{width}', family, 'primary', value, dict(seed=seed, generator=family))
                if family == 'triangular':
                    value = dict(value, order='lex')
                    record(f'{family}{n}-{width}-lex', family, 'lex', value, dict(seed=seed, generator=family))
    for family, sizes in [('dense-quadratic', [8, 10, 12]), ('sparse-structured', [6, 8, 10]),
                          ('positive-dimensional', [7, 9, 11])]:
        for n in sizes:
            for width, p in FIELDS:
                seed = 109879000 + 1000*n + p
                record(f'{family}{n}-{width}-heldout', family, 'heldout', generated(family, n, p, seed),
                       dict(seed=seed, generator=family))
    primary = [c for c in cases if c['split'] == 'primary']
    assert len(primary) == 90
    assert {family: sum(c['family'] == family for c in primary) for family in
            {c['family'] for c in primary}} == {family: 9 for family in PUBLIC | dict.fromkeys(
                ['dense-quadratic', 'triangular', 'positive-dimensional'])}
    assert sum(c['split'] == 'lex' for c in cases) == 9
    assert sum(c['split'] == 'heldout' for c in cases) == 27
    protocol = dict(
        format=2, purpose='Fixed F4 performance corpus; no performance result or leadership claim.',
        primary='90 grevlex systems: ten equally weighted families, three cases in each of three prime fields.',
        lex='Nine separate lex systems; compare only engines supporting the identical order.',
        heldout='27 additional inputs; do not use them to select implementation policies or thresholds.',
        outputs='Complete monic reduced bases in the ordinary polynomial ring, including characteristic two.',
        threads=[1, 2, 4, 8], wall_seconds_per_process=300, address_space_bytes=8*2**30,
        output_bytes_per_file=256*2**20, initial_pairs=2,
        hex_limits={**dict.fromkeys(['work', 'packed-bytes', 'monomials', 'pairs', 'rounds',
                    'matrix-entries', 'matrix-rows', 'basis'], 2**50), 'variables': 1000000, 'batch-size': BATCH_SIZE},
        schedule='Lease one CPU for single-thread trials. Trial-major adjacent pairs alternate AB/BA. Record all completed samples and failures; one unchanged repeat after inconclusive results.',
        comparisons='Match field, variable precedence, order, deterministic guarantee and full output. Report unsupported routes separately. No loss of solved coverage is allowed.',
        scoring='For each comparator, compute geometric mean Hex/comparator ratios within each family across fields, then geometric mean with equal family weights. Also report each field width separately. Retain missing families, failures, timeouts and per-instance coverage; never score jointly solved ratios as success after a coverage loss.',
        checking='Unchecked candidate time, certificate generation, independent native verification and kernel checking are separate results. Compare every coefficient and exponent of complete bases outside candidate timing.',
        compilers='Record exact source, compiler, flags, runtime, ISA availability, thread environment and executable hashes. CI timings are excluded.',
        sympy_version=sympy.__version__, public_revision=revision,
        generator_sha256=sha(Path(__file__).read_bytes()))
    put('suite.json', encoded(dict(protocol=protocol, cases=cases)))
    put('generator.py', Path(__file__).read_bytes())
    (out / 'sha256.json').write_bytes(encoded(files))
    print(json.dumps(dict(output=str(out), cases=len(cases), suite_sha256=files['suite.json'])))


if __name__ == '__main__':
    main()
