#!/usr/bin/env python3
"""Focused fresh-module determinant comparison with serial admission limits."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
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

    def __init__(self, started: float | None = None, seconds: float = TOTAL_SECONDS):
        self.started = time.monotonic() if started is None else started
        self.seconds = seconds
        self.timeouts: dict[tuple[str, str], list[Case]] = {}

    def admit(self, case: Case, arm: str, now: float | None = None) -> tuple[bool, str | None]:
        now = time.monotonic() if now is None else now
        if now - self.started >= self.seconds:
            return False, "aggregate measurement limit"
        for prior in self.timeouts.get((case.family, arm), []):
            if prior.dimension <= case.dimension and prior.complexity <= case.complexity:
                return False, f"same or larger comparable case after timeout: {prior.name}"
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
    Case('Tridiagonal4', 'symbolic-equality', 4, 4),
    Case('ResultTridiagonal4', 'symbolic-result', 4, 4),
    Case('OriginalQuadratic4', 'original-polynomial', 4, 4),
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


PREFIX = 'HexPolyDetMathlib.ProofProbe'
AXIOMS = ('propext', 'Classical.choice', 'Quot.sound')


def audited_axioms(module: str, output: str) -> list[str]:
    """Read this audit's declaration, not an unrelated dependency's log output."""
    stem = module.removesuffix('Audit')
    declaration = 'certificate' if stem.rsplit('.', 1)[-1].startswith('Result') else 'result'
    name = f'{stem}.{declaration}'
    match = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^]]*)\]", output)
    if match is None:
        raise RuntimeError(f'missing axiom audit for {name}')
    return [item.strip() for item in match[1].split(',') if item.strip()]


def validate_sources(root: Path, cases: list[Case]) -> None:
    """Keep diagnostics out of timings and check each separate audit's subject."""
    directory = root / 'bench/HexPolyDetMathlib/ProofProbe'
    for case in cases:
        imports = []
        statements = []
        for arm in ('Mathlib', 'Hex'):
            stem = f'{case.name}{arm}'
            for suffix in ('', 'Baseline'):
                source = (directory / f'{stem}{suffix}.lean').read_text()
                if re.search(r'^\s*(#|run_meta\b|run_cmd\b|trace_state\b|set_option\s+(profiler|diagnostics|trace\.))', source, re.M):
                    raise ValueError(f'diagnostic in timed module: {stem}{suffix}')
                imports.append(re.findall(r'^import .+$', source, re.M))
                if not suffix:
                    match = re.search(rf'(?:theorem|def) {re.escape(PREFIX + "." + stem)}\.(?:result|certificate)\s*(.*?)\s*:=\s*by', source, re.S)
                    if match is None:
                        raise ValueError(f'missing exported proof declaration: {stem}')
                    statements.append(' '.join(match[1].split()))
            audit = (directory / f'{stem}Audit.lean').read_text()
            declaration = 'certificate' if case.name.startswith('Result') else 'result'
            if re.findall(r'^import .+$', audit, re.M) != [f'import {PREFIX}.{stem}']:
                raise ValueError(f'audit must import its proof module: {stem}')
            if re.findall(r'^#print axioms .+$', audit, re.M) != [f'#print axioms {PREFIX}.{stem}.{declaration}']:
                raise ValueError(f'audit must inspect its exported declaration: {stem}')
        if not imports[0] or any(value != imports[0] for value in imports):
            raise ValueError(f'proof arms and baselines must have identical imports: {case.name}')
        if statements[0] != statements[1]:
            raise ValueError(f'proof arms must state the same theorem/result type: {case.name}')


def run(output: Path, selected: set[str] | None = None, prior_seconds: float = 0,
        seconds: float = TOTAL_SECONDS) -> dict:
    """Retain every adjacent AB/BA sample, failure and skipped admission."""
    import json
    import os
    import statistics
    from scripts.bench import fresh_module_sweep as sweep
    from scripts.bench.cpu_lease import cpu_lease

    cases = [c for c in CASES if selected is None or c.name in selected]
    if not 0 < seconds <= TOTAL_SECONDS or prior_seconds < 0:
        raise ValueError('seconds must be positive and at most 1800; prior seconds must be nonnegative')
    validate_sources(Path(__file__).resolve().parents[2], cases)
    pairs = tuple(sweep.ProbePair(f'{c.name}{arm}',
        sweep.ProbeModule(f'{PREFIX}.{c.name}{arm}Baseline'),
        sweep.ProbeModule(f'{PREFIX}.{c.name}{arm}'),
        {'case': c.name, 'arm': arm, 'fresh_module_budget_ms': 60000})
        for c in cases for arm in ('Mathlib', 'Hex'))
    spec = sweep.SweepSpec(__doc__ or '', pairs, 'HexPolyDetMathlibProofProbe',
        'hex-det-general-v2', 'adjacent-fresh-module-olean-wall',
        'hex-det-general', required_samples=PAIRS, absolute_only=True,
        extra_sources=(Path('scripts/bench/det_general.py'),
            *(Path(f'bench/HexPolyDetMathlib/ProofProbe/{c.name}{arm}Audit.lean')
              for c in cases for arm in ('Mathlib', 'Hex')),
            *(Path(f'bench/HexPolyDetMathlib/ProofProbe/Imports{arm}.lean')
              for arm in ('Mathlib', 'Hex'))))
    sweep.validate_spec(spec)
    started = time.monotonic()
    budget_started = started - prior_seconds
    admission = Admission(budget_started, seconds)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    rows: list[dict] = []
    preparations: list[dict] = []
    audits: list[dict] = []
    imports: list[dict] = []
    warmup: dict = {'state': 'pending'}
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
                    'median_proof_nanos': statistics.median(r['proof']['wall_nanos'] for r in samples) if len(values) == PAIRS else None,
                    'median_baseline_nanos': statistics.median(r['baseline']['wall_nanos'] for r in samples) if len(values) == PAIRS else None,
                    'states': [r['state'] for r in samples],
                }
            reference = per_arm['Mathlib']['median_net_nanos']
            candidate = per_arm['Hex']['median_net_nanos']
            summary[case.name] = {'arms': per_arm,
                'ratio_mathlib_over_hex': reference / candidate if reference and reference > 0 and candidate and candidate > 0 else None}
        report = {
            'schema': spec.schema, 'source_hashes': source_hashes,
            'environment': environment, 'cpu': cpu, 'started_monotonic': started,
            'elapsed_seconds': time.monotonic() - started,
            'prior_measurement_seconds': prior_seconds,
            'protocol': {'pairs': PAIRS, 'process_seconds': PROCESS_SECONDS,
                         'total_seconds': seconds, 'matching_imports': True,
                         'axiom_audits_outside_timing': True},
            'aggregate_elapsed_seconds': time.monotonic() - budget_started,
            'schedule_complete': len(rows) == len(cases) * 2 * PAIRS,
            'measurement_complete': len(rows) == len(cases) * 2 * PAIRS
                and len(audits) == len(cases) * 2 and len(preparations) == len(cases) * 2
                and len(imports) == PAIRS * 2 and warmup['state'] == 'complete'
                and all(r['state'] == 'complete' for r in rows + preparations + audits + imports),
            'subset': selected is not None, 'samples': rows, 'summary': summary,
            'warmup': warmup, 'proof_preparation': preparations,
            'audits': audits, 'import_samples': imports,
        }
        output.write_text(json.dumps(report, indent=2) + '\n')
        return report

    def build(module: sweep.ProbeModule, case: Case, arm: str):
        observed = []
        allowed, reason = admission.admit(case, arm)
        if not allowed:
            return {'state': 'skipped', 'reason': reason}
        remaining = seconds - (time.monotonic() - budget_started)
        if remaining <= 0:
            return {'state': 'skipped', 'reason': 'aggregate measurement limit'}
        try:
            result = sweep.build_sample(module.module, min(PROCESS_SECONDS, remaining), cpu,
                [cpu], lambda _m, row: observed.append(row), retain_compiler_output=True)
            if module.module.endswith('Audit'):
                result['axioms'] = audited_axioms(module.module, result['compiler_output'])
            elif re.search(rf'(?:info|trace): [^\n]*{re.escape(module.module.rsplit(".", 1)[-1])}\.lean:', result['compiler_output']):
                raise RuntimeError(f'diagnostic output from timed module: {module.module}')
            sweep.validate_axioms(case.name, arm, module, result)
            return dict(result, state='complete')
        except RuntimeError as exc:
            row = dict(observed[-1]) if observed else {'state': 'failed'}
            if row.get('state') != 'timeout':
                row['state'] = 'failed'
            elif remaining < PROCESS_SECONDS:
                row['state'] = 'truncated'
                row['reason'] = 'aggregate measurement limit reached during build'
            row['error'] = str(exc)
            admission.observe(case, arm, row['state'])
            return row

    try:
        save()
        warm_started = time.monotonic()
        remaining = seconds - (warm_started - budget_started)
        if remaining <= 0:
            warmup = {'state': 'skipped', 'reason': 'aggregate measurement limit'}
            return save()
        try:
            sweep.warm_imports(spec, min(PROCESS_SECONDS, remaining))
            warmup = {'state': 'complete', 'elapsed_seconds': time.monotonic() - warm_started}
        except RuntimeError as exc:
            warmup = {'state': 'failed', 'error': str(exc),
                      'elapsed_seconds': time.monotonic() - warm_started}
            return save()
        for case in cases:
            for arm in ('Mathlib', 'Hex'):
                print(f'[prepare] {case.name} {arm}', flush=True)
                preparation = build(sweep.ProbeModule(f'{PREFIX}.{case.name}{arm}'), case, arm)
                preparations.append(dict(preparation, case=case.name, arm=arm))
                save()
                print(f'[audit] {case.name} {arm}', flush=True)
                result = build(sweep.ProbeModule(f'{PREFIX}.{case.name}{arm}Audit', AXIOMS), case, arm) if preparation['state'] == 'complete' else {
                    'state': 'skipped',
                    'reason': f"proof preparation {preparation['state']}: {preparation.get('reason', preparation.get('error', ''))}"}
                audits.append(dict(result, case=case.name, arm=arm))
                save()
        for trial in range(PAIRS):
            for arm in (('Mathlib', 'Hex') if trial % 2 == 0 else ('Hex', 'Mathlib')):
                result = build(sweep.ProbeModule(f'{PREFIX}.Imports{arm}'),
                               Case('Imports', 'imports', 0, 0), arm)
                imports.append(dict(result, trial=trial + 1, arm=arm))
                save()
            for case in sweep.rotate(cases, trial):
                arms = ('Mathlib', 'Hex') if trial % 2 == 0 else ('Hex', 'Mathlib')
                for arm in arms:
                    print(f'[{trial + 1}/{PAIRS}] {case.name} {arm}', flush=True)
                    pair = next(p for p in pairs if p.name == f'{case.name}{arm}')
                    audited = next(r for r in audits if r['case'] == case.name and r['arm'] == arm)
                    built = {role: build(module, case, arm) if audited['state'] == 'complete'
                             else {'state': 'skipped', 'reason': f"audit {audited['state']}: {audited.get('reason', audited.get('error', ''))}"}
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
    parser.add_argument('--seconds', type=float, default=TOTAL_SECONDS,
                        help='total allowance including audits and import builds, at most 1800')
    args = parser.parse_args()
    result = run(args.output, set(args.case) if args.case else None, args.prior_seconds, args.seconds)
    raise SystemExit(0 if result['measurement_complete'] else 1)
