"""Registered inputs for complete rational root route comparisons."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Suite:
    cases: tuple[str, ...]
    emit: str
    fixture: str
    protocol: str


RESOURCE_FORMAT = ('{"maximum_resident_set_kib": %M, "user_seconds": %U, '
                   '"system_seconds": %S, "elapsed_seconds": %e, "exit_status": %x}')


SUITES = {
    'multiplicity': Suite(
        ('Zero', 'Constant', 'Multiplicity1', 'Multiplicity2', 'Multiplicity4', 'Multiplicity8'),
        'emit', 'conformance-fixtures/HexRealClosure/trivial-measurements.jsonl',
        'reports/bench-results/real-closure-trivial/protocol.md'),
    'distinct': Suite(
        ('Rational2', 'Rational4', 'Rational6', 'Rational8',
         'Quadratic2', 'Quadratic4', 'Quadratic6', 'Quadratic8'),
        'emit-distinct', 'conformance-fixtures/HexRealClosure/trivial-distinct.jsonl',
        'reports/bench-results/real-closure-distinct/protocol.md'),
}


def configuration(name):
    if name not in SUITES:
        raise ValueError('unknown root route suite: ' + str(name))
    return SUITES[name]
