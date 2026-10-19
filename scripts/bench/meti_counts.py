"""Select actual generated-C workers for MetiTarski operation counts.

Loop counters run after the compiler's tail-recursion label. Their totals
include terminal tests; they are not counts of successful Euclidean steps.
Forwarders and names occurring only in specialization suffixes do not count.
"""
from __future__ import annotations

import re
import json

ENTRY = re.compile(r'^LEAN_EXPORT [^;\n{}]*\b(\w+)\([^\n;]*\)\{', re.M)
TOKENS = re.compile(r'"(?:\\.|[^"\\])*"|/\*.*?\*/|//[^\n]*|[{}]', re.S)

# The first component is the declaration name before specialization, without
# the pinned compiler's package prefix. Every category remains separate.
WORKERS = {
    'Hex_DensePoly_gcd': ('poly_gcd', False),
    'Hex_DensePoly_xgcd': ('poly_xgcd', False),
    'Hex_DensePoly_xgcdLeft': ('poly_xgcd_left', False),
    'Hex_DensePoly_pseudoGcd': ('poly_pseudo_gcd', False),
    'Hex_DensePoly_gcdWithImpl': ('poly_gcd_with', False),
    'Hex_DensePoly_xgcdWithImpl': ('poly_xgcd_with', False),
    'Hex_DensePoly_xgcdLeftWithImpl': ('poly_xgcd_left_with', False),
    'Hex_DensePoly_gcdAuxImpl': ('gcd_loop_tests', True),
    'Hex_RealClosure_Yun_loop': ('yun_loop_tests', True),
    'Hex_SignedRemainderChain_buildAux': ('chain_loop_tests', True),
    'Hex_SignedRemainderChain_build': ('signed_chains', False),
    'Hex_RealClosure_Bisection_Frontier_advance_x3f': ('bisection_nodes', False),
    'Hex_SignDet_solveSystem': ('bkr_solves', False),
    'Hex_RealClosure_Algebraic_Element_sign': ('algebraic_sign_reads', False),
    'Hex_RealClosure_Algebraic_Context_signPoly': ('algebraic_sign_poly', False),
}
KINDS = tuple(name for name, _ in WORKERS.values())


def classify(name: str):
    """Recognize the declared worker, never a callee in its suffix."""
    declaration, *specialization = name.split('___at___', 1)
    if specialization and re.fullmatch(r'.+_spec__\d+(?:___redArg)?', specialization[0]) is None:
        return None
    if not declaration.startswith('lp_Hex_'):
        return None
    declaration = declaration.removeprefix('lp_Hex_')
    if declaration.endswith('___redArg'):
        declaration = declaration.removesuffix('___redArg')
    return WORKERS.get(declaration)


def instrument(source: str):
    """Insert observer calls without changing any original C token."""
    insertions = []
    functions = []
    for match in ENTRY.finditer(source):
        name = match.group(1)
        selected = classify(name)
        if selected is None:
            continue
        depth = 1
        end = None
        for token in TOKENS.finditer(source, match.end()):
            if token.group() == '{':
                depth += 1
            elif token.group() == '}':
                depth -= 1
            if depth == 0:
                end = token.end()
                break
        if end is None:
            raise ValueError(f'unterminated generated worker: {name}')
        body = source[match.end():end]
        if not name.endswith('___redArg') and name + '___redArg(' in body:
            continue
        kind, loop = selected
        position = match.end()
        if loop:
            label = re.match(r'\s*_start:\s*\{', body)
            if label is None:
                raise ValueError(f'missing tail-recursion label: {name}')
            position += label.end()
        number = KINDS.index(kind)
        insertions.append((position, f'\nhex_meti_count({number});'))
        functions.append(dict(name=name, kind=kind, loop_tests=loop))
    for position, insertion in reversed(insertions):
        source = source[:position] + insertion + source[position:]
    if functions:
        source = 'extern void hex_meti_count(unsigned);\n' + source
    return source, functions


def _distinct(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate counter key: {key}')
        result[key] = value
    return result


def parse_record(stderr: str):
    """Require one completed producer region with bounded integral counts."""
    events = [line for line in stderr.splitlines() if line.startswith('METI ')]
    if (len(events) != 3 or events[:2] != ['METI BEGIN', 'METI END'] or
            not events[2].startswith('METI COUNTERS ')):
        raise ValueError('incomplete or duplicate counter region')
    record = json.loads(events[2].removeprefix('METI COUNTERS '), object_pairs_hook=_distinct)
    fields = {'schema', 'valid', 'counts', 'lean_nat_gcd', 'gmp_gcd', 'gmp_gcdext'}
    if (not isinstance(record, dict) or set(record) != fields or type(record['schema']) is not int or
            record['schema'] != 1 or record['valid'] is not True or
            not isinstance(record['counts'], dict) or set(record['counts']) != set(KINDS)):
        raise ValueError('invalid counter schema or region')
    values = list(record['counts'].values()) + [record[k] for k in
                                              ['lean_nat_gcd', 'gmp_gcd', 'gmp_gcdext']]
    if any(type(value) is not int or not 0 <= value < 2**64 for value in values):
        raise ValueError('invalid integral counter value')
    if not record['counts']['yun_loop_tests'] or not record['counts']['signed_chains']:
        raise ValueError('empty observed producer region')
    return record


def check_packet(stdout: str, expected: str, degree: int):
    """Bind the observed process to the unchanged committed functional packet.

    This is packet identity, not independent mathematical replay. The exact
    original-input oracle must validate this same output separately.
    """
    if stdout != expected:
        raise ValueError('functional packet differs from committed fixture')
    packet = json.loads(stdout)
    if (not isinstance(packet, dict) or
            any(type(packet.get(k)) is not int for k in
                ['schema', 'degree', 'root_count', 'multiplicity', 'equation_sign']) or
            packet.get('schema') != 1 or packet.get('workload') != 'metitarski-degree-ladder' or
            packet['degree'] != degree or
            packet.get('root_count') != 1 or packet.get('multiplicity') != 1 or
            packet.get('equation_sign') != 0 or packet.get('first_replay') is not True or
            packet.get('root_replay') is not True):
        raise ValueError('incomplete functional validation')
    return packet
