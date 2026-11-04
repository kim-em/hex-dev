#!/usr/bin/env python3
"""Check the fixed F4 corpus and reproduce its measurement protocol."""
import argparse
from collections import Counter
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_capsule import Capsule
from scripts.bench.groebner_trie_report import require


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--current', action='store_true')
    args = parser.parse_args()
    cap = Capsule(args.archive)
    suite = cap.json('suite.json')
    protocol, cases = suite['protocol'], suite['cases']
    require(len(cases) == 126 and len({c['name'] for c in cases}) == 126, 'case identities differ')
    require(Counter(c['split'] for c in cases) == {'primary': 90, 'lex': 9, 'heldout': 27},
            'split sizes differ')
    fields = {2, 32003, 2147483647}
    families = {'cyclic', 'kat', 'eco', 'noon', 'reimer', 'minrank', 'sparse-structured',
                'dense-quadratic', 'triangular', 'positive-dimensional'}
    primary = [c for c in cases if c['split'] == 'primary']
    require(Counter(c['family'] for c in primary) == dict.fromkeys(families, 9), 'family balance differs')
    require(Counter((c['family'], c['p']) for c in primary) ==
            {(f, p): 3 for f in families for p in fields}, 'field balance differs')
    for c in cases:
        raw = cap.read(c['input'])
        require(hashlib.sha256(raw).hexdigest() == c['input_sha256'], 'input hash differs')
        value = cap.json(c['input'])
        require(value['p'] == c['p'] and value['p'] in fields and
                value['variables'] == c['variables'] and type(value['variables']) is int and
                value['variables'] > 0 and value['order'] == c['order'] and
                c['order'] == ('lex' if c['split'] == 'lex' else 'grevlex'), 'field/order metadata differs')
        require(value['generators'], 'missing generators')
        for polynomial in value['generators']:
            require(polynomial and len({tuple(e) for e, _ in polynomial}) == len(polynomial),
                    'noncanonical polynomial support')
            for powers, coefficient in polynomial:
                require(len(powers) == c['variables'] and all(type(e) is int and e >= 0 for e in powers)
                        and type(coefficient) is int and 0 < coefficient < c['p'], 'invalid term')
        provenance = c['provenance']
        if 'path' in provenance:
            data = cap.read('upstream/gamba/' + provenance['path'])
            require(hashlib.sha256(data).hexdigest() == provenance['sha256'] and
                    provenance['revision'] == protocol['public_revision'] and
                    int(data.decode().splitlines()[1].strip().rstrip(',')) ==
                    provenance['source_characteristic'], 'public input provenance differs')
    require(hashlib.sha256(cap.read('generator.py')).hexdigest() == protocol['generator_sha256'],
            'generator hash differs')
    if args.current:
        require((ROOT / 'scripts/bench/groebner_corpus.py').read_bytes() == cap.read('generator.py'),
                'current generator differs')
    require(protocol['wall_seconds_per_process'] == 300 and protocol['address_space_bytes'] == 8*2**30
            and protocol['output_bytes_per_file'] == 256*2**20 and protocol['initial_pairs'] == 2
            and protocol['threads'] == [1, 2, 4, 8], 'resource protocol differs')
    require(protocol['hex_limits'] == {**dict.fromkeys(['work', 'packed-bytes', 'monomials', 'pairs',
            'rounds', 'matrix-entries', 'matrix-rows', 'basis'], 2**50), 'variables': 1000000,
            'batch-size': 64}, 'Hex internal limits differ')
    lines = ['# Fixed finite-field F4 performance corpus', '',
        'This corpus fixes inputs and a comparison protocol before measurements or tuning against it. '
        'It contains no timing result and establishes no performance milestone. The primary route '
        'is ordinary prime-field polynomial rings with grevlex order and complete monic reduced output. '
        'No characteristic-two field equations are added.', '',
        '## Inputs', '',
        'The primary corpus contains 90 systems: ten equally weighted families, three cases per family '
        'in each of F₂, F₃₂₀₀₃ and F₂₁₄₇₄₈₃₆₄₇. Published hard systems include Cyclic-9/10, '
        'Katsura-14/15 and Eco-14/15. Public cases overlap existing development inputs at the smaller '
        'sizes; they are not described as held out.', '',
        '| Family | Cases per field | Systems across fields |', '|---|---|---:|']
    for family in sorted(families):
        names = [c['name'] for c in primary if c['family'] == family and c['p'] == 32003]
        lines.append(f'| {family} | {", ".join(n.removesuffix("-15") for n in names)} | 9 |')
    lines += ['', 'Nine additional triangular systems use lex order and are reported separately for '
        'comparators that support that exact order. Twenty-seven additional dense-quadratic, sparse '
        'structured and positive-dimensional systems are held out: their sizes and seeds are fixed, '
        'but they must not select implementation policies or thresholds. Positive-dimensional systems '
        'leave two free variables by successive polynomial substitution.', '',
        f'Public examples and their GPL-3.0 license are retained from [GamBa `{protocol["public_revision"]}`]'
        f'(https://github.com/gblanco92/gamba/tree/{protocol["public_revision"]}/examples). '
        'GamBa’s `-2` filename suffix denotes the two-bit prime 3. F₂ cases instead use explicit '
        'integer coefficients from characteristic-zero examples where available, or written integer '
        'lifts of the 32003 examples. Cross-characteristic lifts define new systems; they do not claim '
        'a field homomorphism. Every case records its actual source characteristic, path, hash, variable '
        'precedence, target field and order. Generated inputs record their exact seeds and generator.', '',
        '## Measurement protocol', '',
        'Each process has 300 seconds of wall time, 8 GiB of address space and 256 MiB per output file. '
        'Use two initial adjacent pairs in trial-major order, alternating AB/BA. Lease a CPU for '
        'single-thread runs and retain every completed sample, outlier, failure, timeout, memory '
        'observation and host-activity record. One unchanged repeat is permitted after inconclusive '
        'results. Never wait for a quiet core or discard a completed sample.', '',
        'The Hex batch size is fixed at 64. Internal work and storage counters have explicit 2⁵⁰ '
        'ceilings instead of the smaller development-sweep defaults. The common wall-time and '
        'address-space limits apply in addition. The variable cap is 1,000,000. Record any internal exhaustion '
        'separately from process timeouts, allocation failures and invalid inputs.', '',
        'Measure candidate production through complete reduced output with parsing, setup and launch '
        'included consistently. Match coefficient field, variable precedence, order, deterministic '
        'guarantees and output. Record exact source revisions, licenses, compiler/runtime versions, '
        'flags, ISA availability, thread environment and executable hashes. Single-thread and equal-thread '
        '2/4/8-thread results are separate; the corpus does not assert that Hex currently implements '
        'parallel elimination. Unsupported routes remain explicit.', '',
        'For each comparator, take the geometric mean of jointly solved Hex/comparator ratios within '
        'each family across fields, then the geometric mean with equal family weights. Also report '
        'field-width strata, per-instance and per-family losses, solved counts, cactus data and peak RSS. '
        'Missing families, timeouts and coverage losses remain visible: jointly solved ratios cannot '
        'establish leadership if Hex loses solved coverage under matched resource limits.', '',
        'Candidate production yields unchecked candidates. Compare every coefficient and exponent of '
        'complete bases outside candidate timing. Certificate generation, independent native verification, '
        'kernel checking and complete checked calls need separate results. Minimum comparator coverage '
        'is msolve, Groebner.jl, Giac and Singular, supplemented by faster fully open-source engines. '
        'GamBa, Magma and FGb remain additional targets where usable. No CI timing supports a scientific '
        'performance claim.', '', '## Replay', '',
        f'Corpus capsule `{cap.path.name}`: SHA-256 `{cap.sha256}`. All inputs, original public examples, '
        'license and generator have individual SHA-256 bindings. The generator requires the pinned '
        f'public checkout and SymPy {protocol["sympy_version"]}. Reproduction uses:', '', '```bash',
        'python3 scripts/bench/groebner_corpus.py --gamba /path/to/pinned/gamba --output /new/corpus',
        'python3 scripts/bench/groebner_corpus_report.py \\',
        f'  --archive reports/bench-results/raw/{cap.path.name} \\',
        '  --report reports/bench-results/hexgroebner-corpus.md --check', '```', '',
        'Add `--current` to bind replay to the archived generator. Field-boundary, characteristic-two, '
        'canonicalization, seeded-support and positive-dimension checks run with '
        '`python3 -m unittest scripts.bench.test_groebner_corpus`.', '',
        '[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.', '']
    text = '\n'.join(lines)
    if args.check:
        require(args.report.read_text() == text, 'report differs; regenerate it')
    else:
        args.report.write_text(text)
    print('Verified fixed F4 corpus: 126 inputs, hashes, field/order identity, family balance and protocol.')


if __name__ == '__main__':
    main()
