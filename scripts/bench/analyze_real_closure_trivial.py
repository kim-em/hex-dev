#!/usr/bin/env python3
"""Audit the retained rational root route comparison and paired estimates."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics
import shlex

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.analyze_real_closure_samples import audit_archive
from scripts.bench.real_closure_trivial_suites import configuration, RESOURCE_FORMAT

CASES = ('Zero', 'Constant', 'Multiplicity1', 'Multiplicity2', 'Multiplicity4', 'Multiplicity8')


def summarize(values):
    return dict(samples=len(values), median=statistics.median(values),
                minimum=min(values), maximum=max(values), values=values)


def analyze(directory, archive_index):
    directory = Path(directory)
    metadata = json.loads((directory / 'metadata.json').read_text())
    suite_name = metadata.get('suite', 'multiplicity')
    suite = configuration(suite_name)
    expected_arms = 12 * len(suite.cases)
    if metadata['status'] != 'completed' or len(metadata['observations']) != expected_arms:
        raise ValueError(f'capture did not complete all {expected_arms} registered arms')
    if metadata['rounds'] != 6 or tuple(metadata['cases']) != suite.cases:
        raise ValueError('capture changed the registered workload')
    if metadata['affinity'] != [metadata['cpu']]:
        raise ValueError('capture affinity differs from the selected CPU')
    if not isinstance(archive_index, dict) or not all(
            name in archive_index for name in ('omitted_executable', 'source_git_blobs', 'source')):
        raise ValueError('committed archive index is required')
    omitted = archive_index['omitted_executable']
    if archive_index['source'] != metadata['source']:
        raise ValueError('archive source differs from original capture')
    for name, expected in metadata['artifacts'].items():
        path = directory / name
        if not path.is_file() and omitted and name == omitted['path'] and expected == omitted['sha256']:
            continue
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('retained artifact digest differs: ' + name)
    for name, expected in metadata['source_hashes'].items():
        if metadata['artifacts']['sources/' + name] != expected:
            raise ValueError('source snapshot differs from recorded source: ' + name)
    if set(archive_index['source_git_blobs']) != set(metadata['source_hashes']):
        raise ValueError('committed source snapshot set differs')
    for name, expected in archive_index['source_git_blobs'].items():
        data = (directory / 'sources' / name).read_bytes()
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        if hashlib.sha1(blob).hexdigest() != expected:
            raise ValueError('source snapshot differs from committed Git blob: ' + name)
    if metadata['binary_sha256'] != omitted['sha256']:
        raise ValueError('measured executable digest differs from its archive index')
    commands = metadata['commands']
    preparation = {command['stdout']: command for command in commands[:metadata['observations'][0]['command_index']]}
    labels = ('compiler-version.stdout', 'build.stdout', 'lean-version.stdout',
              'cpu-info.stdout', 'functional.stdout', 'oracle.stdout')
    if suite_name == 'distinct':
        labels = labels + ('time-version.stdout',)
    if set(preparation) != set(labels):
        raise ValueError('preparation command labels differ')
    for name in labels:
        if preparation[name]['exit_code'] != 0:
            raise ValueError('preparation command failed: ' + name)
    functional = preparation['functional.stdout']
    executable = functional['command'][0]
    if functional['command'][1:] != [suite.emit] or Path(executable).name != omitted['path']:
        raise ValueError('functional command has a different measured executable')
    if (directory / functional['stderr']).read_bytes():
        raise ValueError('functional run reported an error or panic')
    fixture = directory / 'sources' / suite.fixture
    if (directory / 'functional.stdout').read_bytes() != fixture.read_bytes():
        raise ValueError('functional output differs from the committed fixture')
    oracle = json.loads((directory / 'oracle.stdout').read_text())
    if oracle['verified_arms'] != 2 * len(suite.cases) or oracle['oracle'] != 'python-flint 0.9.0 / FLINT 3.6.0':
        raise ValueError('exact oracle coverage or version differs')
    oracle_command = preparation['oracle.stdout']
    oracle_argv = oracle_command['command']
    # Historical frozen captures predate the explicit CLI suite argument.
    oracle_tail = oracle_argv[2:]
    if (oracle_tail not in ([str(Path(executable).parent / 'functional.stdout')],
                           ['--suite', suite_name, str(Path(executable).parent / 'functional.stdout')])
            or Path(oracle_argv[1]).parts[-3:] !=
                ('scripts', 'oracle', 'real_closure_trivial_measurements.py')):
        raise ValueError('oracle command has a different script or functional input')
    if (directory / oracle_command['stderr']).read_bytes():
        raise ValueError('oracle run reported an error')
    expected_schedule = []
    for trial in range(6):
        for case in suite.cases:
            arms = ('generic', 'canonical') if trial % 2 == 0 else ('canonical', 'generic')
            expected_schedule.extend((trial, case, 'generic', arm) for arm in arms)
    rows = metadata['observations']
    if [(r['trial'], r['case'], r['pair'], r['arm']) for r in rows] != expected_schedule:
        raise ValueError('paired adjacency or alternating trial schedule changed')
    timings = {}
    resources = {}
    child_resources = {}
    details = []
    for row in rows:
        export = json.loads((directory / row['export']).read_text())
        if len(export['results']) != 1 or export['export_schema_version'] != 1:
            raise ValueError('unexpected benchmark export schema')
        result = export['results'][0]
        expected = f'Hex.RealClosure.TrivialMeasurements.{row["case"]}.{row["arm"]}'
        if (result['function'] != expected or result['env']['git_commit'] != metadata['source']
                or result['env']['git_dirty']):
            raise ValueError('export changed its registered function or frozen source')
        command = metadata['commands'][row['command_index']]
        measured_command = command.get('measured_command', command['command'])
        if (measured_command[:2] != [executable, 'run']
                or command['exit_code'] != row['exit_code'] or measured_command[2] != expected
                or Path(measured_command[-1]).name != row['export']):
            raise ValueError('observation differs from recorded command')
        if (directory / command['stderr']).read_bytes():
            raise ValueError('benchmark parent driver reported an error')
        if row['exit_code'] != 0 or result['budget_truncated'] or not result['hashes_agree']:
            raise ValueError('failed, truncated or inconsistent benchmark arm')
        if result['expected_hash_check']['status'] != 'match' or result['observed_hash'] != '0x1':
            raise ValueError('complete root consumer hash did not match')
        config = result['config']
        if (config['repeats'] != 1 or config['min_total_seconds'] != 0.5
                or not config['warmup_first_iter'] or config['max_seconds_per_call'] != 120):
            raise ValueError('fixed-call protocol differs from registration')
        points = result['points']
        if (len(points) != 1 or points[0]['status'] != 'ok'
                or points[0]['inner_repeats'] <= 0 or points[0]['total_nanos'] <= 0):
            raise ValueError('incomplete fixed-call batch')
        point = points[0]
        estimate = point['total_nanos'] / point['inner_repeats'] / 1e6
        timings[row['trial'], row['case'], row['arm']] = estimate
        detail = dict(**row, per_call_ms=estimate, raw_point=point,
                      config=config, budget_truncated=result['budget_truncated'])
        if suite_name == 'distinct':
            tool = metadata.get('resource_capture', {})
            if (tool.get('format') != RESOURCE_FORMAT or tool.get('unit') != 'KiB'
                    or not tool.get('sha256') or not tool.get('tool')):
                raise ValueError('resource tool identity or format differs')
            resource_file = command.get('resources')
            if not isinstance(resource_file, str) or resource_file != command['stdout'].removesuffix('.stdout') + '.resources.json':
                raise ValueError('resource file is not bound to its benchmark arm')
            wrapper = [tool['tool'], '-f', RESOURCE_FORMAT, '-o',
                       str(Path(executable).parent / resource_file), '--', *measured_command]
            if command['command'] != wrapper:
                raise ValueError('resource command differs from its measured arm')
            try:
                usage = json.loads((directory / resource_file).read_text())
            except json.JSONDecodeError as error:
                raise ValueError('resource record is not JSON; GNU time may have reported a failed arm') from error
            if set(usage) != {'maximum_resident_set_kib', 'user_seconds', 'system_seconds',
                              'elapsed_seconds', 'exit_status'}:
                raise ValueError('resource record schema differs')
            if (type(usage['maximum_resident_set_kib']) is not int
                    or usage['maximum_resident_set_kib'] <= 0
                    or type(usage['exit_status']) is not int or usage['exit_status'] != 0
                    or any(type(usage[key]) not in (int, float) or not math.isfinite(usage[key]) or usage[key] < 0
                           for key in ('user_seconds', 'system_seconds', 'elapsed_seconds'))):
                raise ValueError('resource record is incomplete or unsuccessful')
            child_peak = point.get('peak_rss_kb')
            if type(child_peak) is not int or child_peak <= 0:
                raise ValueError('measuring child peak RSS is absent or invalid')
            child_resources[row['trial'], row['case'], row['arm']] = child_peak
            resources[row['trial'], row['case'], row['arm']] = usage['maximum_resident_set_kib']
            detail['whole_arm_resources'] = usage
        details.append(detail)
    comparisons = []
    for case in suite.cases:
        generic = [timings[trial, case, 'generic'] for trial in range(6)]
        canonical = [timings[trial, case, 'canonical'] for trial in range(6)]
        comparisons.append(dict(case=case, generic_ms=summarize(generic),
                                canonical_ms=summarize(canonical),
                                generic_over_canonical=summarize([a/b for a, b in zip(generic, canonical)]),
                                generic_minus_canonical_ms=summarize([a-b for a, b in zip(generic, canonical)])))
    result = dict(source=metadata['source'], cpu=metadata['cpu'], host=metadata['host'],
                  observations=expected_arms, comparisons=comparisons, raw_batches=details,
                  inference='descriptive paired batch estimates on this shared host; no significance or asymptotic claim')
    if suite_name == 'distinct':
        driver = metadata.get('driver', {})
        for filename, fingerprint in (('source', 'source_sha256'), ('trace', 'trace_sha256')):
            if (driver.get(filename) not in metadata['artifacts']
                    or driver.get(fingerprint) != metadata['artifacts'][driver[filename]]):
                raise ValueError('compiled driver artifact is not bound to its capture')
        trace = json.loads((directory / driver['trace']).read_text())
        compile_commands = [shlex.split(item['message'][3:]) for item in trace['log']
                            if item['message'].startswith('.> ')]
        if (compile_commands != [driver.get('compile_command')]
                or len(compile_commands) != 1
                or compile_commands[0][0] != metadata['compiler_override']
                or '-c' not in compile_commands[0]
                or not driver.get('object_sha256') or driver.get('object_size', 0) <= 0):
            raise ValueError('benchmark driver compiler trace differs from recorded compiler')
        time_version = preparation['time-version.stdout']
        if (time_version['command'] != [metadata['resource_capture']['tool'], '--version']
                or 'GNU Time' not in (directory / time_version['stdout']).read_text()):
            raise ValueError('resource tool is not the recorded GNU time')
        if metadata.get('panic_abort') is not True:
            raise ValueError('capture did not abort on native panics')
        result.update(suite=suite_name, functional_inputs=oracle['results'],
                      resource_scope=metadata['resource_capture']['scope'])
        for comparison in comparisons:
            case = comparison['case']
            for arm in ('generic', 'canonical'):
                comparison[arm + '_maximum_resident_set_kib'] = summarize([
                    resources[trial, case, arm] for trial in range(6)])
                comparison[arm + '_child_peak_rss_kib'] = summarize([
                    child_resources[trial, case, arm] for trial in range(6)])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--archive-index', type=Path, required=True)
    args = parser.parse_args()
    index = audit_archive(args.directory, args.archive_index, 'capture_sha256')
    args.output.write_text(json.dumps(analyze(args.directory, index), indent=2) + '\n')


if __name__ == '__main__':
    main()
