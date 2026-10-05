#!/usr/bin/env python3
"""Validate and summarize every retained point in the declared degree ladder."""
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

FUNCTION = 'Hex.RealClosure.Bench.measureMetiSecond'
DEGREES = [3,5,7,9]
TRIALS = 6
SOURCES = {'bench/HexRealClosure/Bench.lean','bench/HexRealClosure/Phase4.lean',
           'scripts/bench/real_closure_metitarski_scaling.py',
           'scripts/oracle/real_closure_metitarski_scaling.py',
           'scripts/bench/analyze_real_closure_metitarski_scaling.py',
           'scripts/bench/cpu_lease.py','scripts/oracle/real_algebraic_qqbar.py'}


def require(test,message):
    if not test:
        raise ValueError(message)


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def summarize(folder,archive=False):
    folder = Path(folder)
    record = json.loads((folder/'manifest.json').read_text())
    require(record['schema'] == 1 and record['status'] == 'completed'
            and record['degrees'] == DEGREES and record['trials'] == TRIALS
            and record['dirty'] is False and record['affinity'] == [record['cpu']],
            'wrong capture protocol')
    require(set(record['source_hashes']) == SOURCES, 'changed frozen source inventory')
    omitted = {}
    if archive:
        index = json.loads((folder/'archive.json').read_text())
        require(index['schema'] == 'metitarski-scaling-v1' and index['commit'] == record['commit'],
                'wrong archive index')
        omitted = index['omitted_snapshots']
        require(set(omitted) == {'hexrealclosure_bench','hexrealclosure_phase4'},
                'unexpected omitted snapshot')
        for name,checksum in index['files'].items():
            relative = Path(name)
            require(not relative.is_absolute() and '..' not in relative.parts
                    and str(relative) == name, 'invalid archive path')
            path = folder/relative
            require(not any(p.is_symlink() for p in [path,*path.parents]), 'redirected archive path')
            require(digest(path) == checksum,'changed archive file: '+name)
        actual = {str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file()}
        require(actual == set(index['files']) | {'archive.json','README.md'},
                'unexpected archive file inventory')
    for name,checksum in record['artifacts'].items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts and str(relative) == name,
                'invalid artifact path')
        path = folder/relative
        require(not any(p.is_symlink() for p in [path,*path.parents]), 'redirected artifact path')
        if name in omitted:
            require(not path.exists() and omitted[name] == checksum
                    and record[name+'_sha256'] == checksum,'wrong omitted snapshot identity')
        else:
            require(digest(path) == checksum,'changed artifact: '+name)
    for name in ['hexrealclosure_bench','hexrealclosure_phase4']:
        require(record[name+'_sha256'] == record['artifacts'].get(name),
                'snapshot identity differs from artifact digest')
    for name,checksum in record['source_hashes'].items():
        require(record['artifacts'].get('sources/'+name) == checksum,
                'frozen source differs from measured identity')
    for command in record['commands']:
        argv = command['argv']
        measurement = (Path(argv[0]).name == 'hexrealclosure_bench'
                       and argv[1:3] == ['run',FUNCTION])
        allowed = [0,2] if measurement else [0]
        require(command['acceptable_exit_codes'] == allowed
                and command.get('exit_code') in allowed
                and not command.get('incomplete',False), 'incomplete capture command')
    document = json.loads((folder/'measurements.json').read_text())
    require(document['export_schema_version'] == 1 and len(document['results']) == 1,
            'wrong measurement inventory')
    result = document['results'][0]
    require(result['kind'] == 'parametric' and result['function'] == FUNCTION
            and not result['budget_truncated'], 'different benchmark or truncated schedule')
    config = result['config']
    require(config['param_schedule'] == {'kind':'custom','params':DEGREES}
            and config['outer_trials'] == TRIALS and config['target_inner_nanos'] == 500000000
            and config['max_seconds_per_call'] == 120 and config['signal_floor_multiplier'] == 1,
            'changed benchmark configuration')
    for env in (document['env'],result['env']):
        require(env['git_commit'] == record['commit'] and env['git_dirty'] is False,
                'measurement source differs from frozen capture')
    points = result['points']
    require([(p['trial_index'],p['param']) for p in points] ==
            [(t,n) for t in range(TRIALS) for n in DEGREES], 'changed trial-major schedule')
    for p in points:
        require(p['status'] in ('ok','timed_out','killed_at_cap','error'), 'unknown measurement status')
        if p['status'] != 'ok':
            continue
        require(p['result_hash'] == '0x1' and not p['below_signal_floor']
                and type(p['inner_repeats']) is int and p['inner_repeats'] > 0
                and type(p['total_nanos']) is int and p['total_nanos'] > 0,
                'invalid completed measurement')
        require(math.isfinite(p['per_call_nanos']) and
                math.isclose(p['per_call_nanos'],p['total_nanos']/p['inner_repeats'],rel_tol=1e-12),
                'per-call value differs from raw measurement')
    rows = []
    functional = record['functional']
    require([f['degree'] for f in functional] == DEGREES,'missing functional rung')
    for n,entry in zip(DEGREES,functional):
        functional = json.loads((folder/entry['fixture']).read_text())
        measured = json.loads((folder/entry['measured_input']).read_text())
        require(all(measured.get(key) == functional[key] for key in
                    ['degree','head','first_coefficients','first']),
                'measured input differs from functional fixture')
        checked = json.loads((folder/entry['oracle']).read_text())
        require(checked['degree'] == n and checked['real_roots'] == 1 and checked['multiplicity'] == 1,
                'functional result differs from measured rung')
        rung = [p for p in points if p['param'] == n]
        values = [Fraction(p['total_nanos'],p['inner_repeats']) for p in rung if p['status'] == 'ok']
        median = statistics.median(values) if values else None
        rows.append(dict(degree=n,completed_trials=len(values),
                         batches=[dict(trial_index=p['trial_index'],total_nanos=p['total_nanos'],
                                       inner_repeats=p['inner_repeats'])
                                  for p in rung if p['status'] == 'ok'],
                         failures=[p for p in rung if p['status'] != 'ok'],
                         median_ns=float(median) if median is not None else None,
                         min_ns=float(min(values)) if values else None,max_ns=float(max(values)) if values else None,
                         normalized_median_ns=float(median/(n**3)) if median is not None else None,
                         head_bytes=checked['head_bytes'],descriptor_bytes=checked['descriptor_bytes']))
    return dict(schema=1,source=record['commit'],attempts=len(points),
                completed_samples=sum(p['status'] == 'ok' for p in points),rows=rows,
                harness_verdict=result['verdict'],harness_slope=result['slope'],
                harness_dropped_leading=result['verdict_dropped_leading'],
                interpretation='Finite degree ladder over one fixed coefficient field; all six attempts retained per rung, including caps/errors. Medians use every completed point; incomplete rungs do not establish the full declared-family model. Descriptive medians/ranges and n^3-normalized medians, not an asymptotic theorem or host-independent budget.')


if __name__ == '__main__':
    print(json.dumps(summarize(Path(sys.argv[1]),archive='--archive' in sys.argv[2:]),
                     indent=2,sort_keys=True))
