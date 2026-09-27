#!/usr/bin/env python3
"""Focused fresh-module determinant comparison with serial admission limits."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import time

PROCESS_SECONDS = 60
TOTAL_SECONDS = 30 * 60
PAIRS = 6


@dataclass(frozen=True)
class Case:
    name: str
    family: str
    dimension: int
    complexity: int


class Admission:
    """A timeout blocks larger comparable cases; a total deadline covers failures."""

    def __init__(self, started: float | None = None):
        self.started = time.monotonic() if started is None else started
        self.timeouts: dict[tuple[str, str], list[Case]] = {}

    def admit(self, case: Case, arm: str, now: float | None = None) -> tuple[bool, str | None]:
        now = time.monotonic() if now is None else now
        if now - self.started >= TOTAL_SECONDS:
            return False, "aggregate measurement limit"
        for prior in self.timeouts.get((case.family, arm), []):
            if prior.dimension <= case.dimension and prior.complexity <= case.complexity:
                return False, f"larger comparable case after timeout: {prior.name}"
        return True, None

    def observe(self, case: Case, arm: str, state: str) -> None:
        if state == "timeout":
            self.timeouts.setdefault((case.family, arm), []).append(case)


def output_path() -> Path:
    return Path(__file__).resolve().parents[2] / "reports/bench-results/det-general.json"

CASES = (
    Case('Numeric2', 'numeric-equality', 2, 1),
    Case('Symbolic2', 'symbolic-equality', 2, 2),
    Case('ResultNumeric2', 'numeric-result', 2, 1),
    Case('ResultSymbolic2', 'symbolic-result', 2, 2),
    Case('Quotient2', 'quotient-equality', 2, 3),
    Case('Quadratic4', 'symbolic-equality', 4, 4),
    Case('ResultQuadratic4', 'symbolic-result', 4, 4),
    Case('TwoTerm4', 'quotient-equality', 4, 3),
    Case('DegreeEight4', 'quotient-equality', 4, 8),
    Case('Products5', 'quotient-equality', 5, 5),
    Case('Identity5', 'symbolic-equality', 5, 5),
    Case('DenseGeneric4', 'generic-equality', 4, 5),
    Case('Independent6', 'quotient-equality', 6, 7),
    Case('RankOne10', 'symbolic-equality', 10, 10),
    Case('ResultSymbolic3', 'symbolic-result', 3, 3),
    Case('ResultIdentity4', 'symbolic-result', 4, 4),
)


def run(output: Path, selected: set[str] | None = None, prior_seconds: float = 0) -> dict:
    """Retain every adjacent AB/BA sample, failure and skipped admission."""
    import json
    import os
    import statistics
    from scripts.bench import fresh_module_sweep as sweep
    from scripts.bench.cpu_lease import cpu_lease

    cases = [c for c in CASES if selected is None or c.name in selected]
    prefix = 'HexPolyDetMathlib.ProofProbe'
    axioms = ('propext', 'Classical.choice', 'Quot.sound')
    pairs = tuple(sweep.ProbePair(f'{c.name}{arm}',
        sweep.ProbeModule(f'{prefix}.{c.name}{arm}Baseline'),
        sweep.ProbeModule(f'{prefix}.{c.name}{arm}', axioms),
        {'case': c.name, 'arm': arm, 'fresh_module_budget_ms': 60000})
        for c in cases for arm in ('Mathlib', 'Hex'))
    spec = sweep.SweepSpec(__doc__ or '', pairs, 'HexPolyDetMathlibProofProbe',
        'hex-det-general-v1', 'adjacent-fresh-module-olean-wall',
        'hex-det-general', required_samples=PAIRS, absolute_only=True,
        extra_sources=(Path('scripts/bench/det_general.py'),))
    sweep.validate_spec(spec)
    started = time.monotonic()
    budget_started = started - prior_seconds
    admission = Admission(budget_started)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    rows: list[dict] = []
    output.parent.mkdir(parents=True, exist_ok=True)
    environment = sweep.environment()
    source_hashes = sweep.source_hashes(spec, Path(__file__))

    def save() -> dict:
        summary = {}
        for case in cases:
            per_arm = {}
            for arm in ('Mathlib', 'Hex'):
                samples = [r for r in rows if r['case'] == case.name and r['arm'] == arm]
                values = [r['net_nanos'] for r in samples if r.get('net_nanos') is not None]
                per_arm[arm] = {
                    'observed': len(samples), 'complete': len(values),
                    'median_net_nanos': statistics.median(values) if len(values) == PAIRS else None,
                    'states': [r['state'] for r in samples],
                }
            reference = per_arm['Mathlib']['median_net_nanos']
            candidate = per_arm['Hex']['median_net_nanos']
            summary[case.name] = {'arms': per_arm,
                'ratio_mathlib_over_hex': reference / candidate if reference is not None and candidate and candidate > 0 else None}
        report = {
            'schema': spec.schema, 'source_hashes': source_hashes,
            'environment': environment, 'cpu': cpu, 'started_monotonic': started,
            'elapsed_seconds': time.monotonic() - started,
            'prior_measurement_seconds': prior_seconds,
            'aggregate_elapsed_seconds': time.monotonic() - budget_started,
            'schedule_complete': len(rows) == len(cases) * 2 * PAIRS,
            'measurement_complete': len(rows) == len(cases) * 2 * PAIRS and all(r['state'] == 'complete' for r in rows),
            'subset': selected is not None, 'samples': rows, 'summary': summary,
        }
        output.write_text(json.dumps(report, indent=2) + '\n')
        return report

    def build(module: sweep.ProbeModule, case: Case, arm: str):
        observed = []
        allowed, reason = admission.admit(case, arm)
        if not allowed:
            return {'state': 'skipped', 'reason': reason}
        remaining = TOTAL_SECONDS - (time.monotonic() - budget_started)
        if remaining <= 0:
            return {'state': 'skipped', 'reason': 'aggregate measurement limit'}
        try:
            result = sweep.build_sample(module.module, min(PROCESS_SECONDS, remaining), cpu,
                [cpu], lambda _m, row: observed.append(row), retain_compiler_output=True)
            sweep.validate_axioms(case.name, arm, module, result)
            return dict(result, state='complete')
        except RuntimeError as exc:
            row = dict(observed[-1]) if observed else {'state': 'failed'}
            row['error'] = str(exc)
            admission.observe(case, arm, row['state'])
            return row

    try:
        if TOTAL_SECONDS - (time.monotonic() - budget_started) > 0:
            sweep.warm_imports(spec, min(PROCESS_SECONDS, TOTAL_SECONDS - (time.monotonic() - budget_started)))
        for trial in range(PAIRS):
            for case in sweep.rotate(cases, trial):
                arms = ('Mathlib', 'Hex') if trial % 2 == 0 else ('Hex', 'Mathlib')
                for arm in arms:
                    print(f'[{trial + 1}/{PAIRS}] {case.name} {arm}', flush=True)
                    pair = next(p for p in pairs if p.name == f'{case.name}{arm}')
                    built = {role: build(module, case, arm)
                             for role, module in sweep.ordered_modules(pair, trial)}
                    good = all(item['state'] == 'complete' for item in built.values())
                    rows.append({'case': case.name, 'arm': arm, 'trial': trial + 1,
                        'order': [role for role, _ in sweep.ordered_modules(pair, trial)],
                        'state': 'complete' if good else next(item['state'] for item in built.values() if item['state'] != 'complete'),
                        'baseline': built['reference'], 'proof': built['candidate'],
                        'net_nanos': int(built['candidate']['wall_nanos']) - int(built['reference']['wall_nanos']) if good else None})
                    save()
        return save()
    finally:
        lease.close()


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=output_path())
    parser.add_argument('--case', action='append', choices=[c.name for c in CASES])
    parser.add_argument('--prior-seconds', type=float, default=0)
    args = parser.parse_args()
    run(args.output, set(args.case) if args.case else None, args.prior_seconds)
