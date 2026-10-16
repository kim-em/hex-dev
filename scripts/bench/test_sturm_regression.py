#!/usr/bin/env python3
"""Check the declared comparison scope without taking performance samples."""
from copy import deepcopy
from contextlib import redirect_stdout, nullcontext
import hashlib
import gzip
import io
import json
import os
from pathlib import Path
import runpy
import subprocess
import shutil
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import sturm_regression as collector
from sturm_regression import AUXILIARY, NATIVE_FIXED, native_harness_pins, registrations


class ArchivedCapProposalTest(unittest.TestCase):
    """The proposed real campaign names exactly the retained failure inputs."""

    def test_proposal_matches_archived_context_and_failed_exports(self):
        root = Path(collector.__file__).resolve().parents[2]
        archive = root / 'reports/bench-results/sturm-phase6-comparison'
        raw = gzip.decompress((archive / 'capture/context.json.gz').read_bytes())
        context = json.loads(raw)
        policy = json.loads((archive / 'cap-proposal.json').read_text())['cap_protocol']
        self.assertEqual(policy['previous_context_sha256'], hashlib.sha256(raw).hexdigest())
        self.assertEqual(policy['benchmarks'], context['benchmarks'])
        expected = set()
        for failure in context['parent_failures']:
            matching = [r['command'] for r in context['commands']
                        if r['command'][1:3] == ['run', failure['function']]
                        and Path(r['command'][r['command'].index('--export-file') + 1]).name.endswith(
                            '-' + failure['arm'] + '.json')]
            command = matching[-1]
            name = Path(command[command.index('--export-file') + 1]).name
            expected.add(name)
            exported = gzip.decompress((archive / 'capture' / (name + '.gz')).read_bytes())
            self.assertEqual(policy['previous_exports'][name], hashlib.sha256(exported).hexdigest())
            self.assertGreater(policy['seconds'], json.loads(exported)['results'][0]['config']['max_seconds_per_call'])
        self.assertEqual(set(policy['previous_exports']), expected)


class BelowResolutionTest(unittest.TestCase):
    def setUp(self):
        root = Path(collector.__file__).resolve().parents[2]
        archive = root / 'reports/bench-results/sign-det-phase6-comparison/initial-capture'
        self.raw = gzip.decompress((archive / '0-0-candidate.json.gz').read_bytes())
        self.document = json.loads(self.raw)
        self.name = self.document['results'][0]['function']
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'export.json'

    def accepted(self, code=2):
        self.path.write_text(json.dumps(self.document))
        return collector.below_resolution_export(code, self.path, self.name)

    def test_actual_complete_below_floor_export_is_retained(self):
        self.assertTrue(self.accepted())

    def test_other_exit_codes_remain_fatal(self):
        for code in (1, 7, -15):
            self.assertFalse(self.accepted(code))

    def test_failure_and_integrity_mutations_are_refused(self):
        for key, value in [('kind', 'fixed'), ('function', 'different'),
                           ('budget_truncated', True), ('verdict', 'consistent_with_declared_complexity'),
                           ('trial_summaries', [{}]), ('points', [])]:
            with self.subTest(key=key):
                self.document = json.loads(self.raw)
                self.document['results'][0][key] = value
                self.assertFalse(self.accepted())
        for key, value in [('status', 'timedOut'), ('error', 'failed'), ('result_hash', None),
                           ('below_signal_floor', False), ('inner_repeats', 0),
                           ('total_nanos', 0), ('per_call_nanos', float('nan')),
                           ('trial_index', 1), ('param', 7)]:
            with self.subTest(key=key):
                self.document = json.loads(self.raw)
                self.document['results'][0]['points'][0][key] = value
                self.assertFalse(self.accepted())

    def test_partial_schedule_is_not_complete(self):
        self.document['results'][0]['points'].pop()
        self.assertFalse(self.accepted())

    def test_malformed_or_missing_export_remains_fatal(self):
        self.assertFalse(collector.below_resolution_export(2, self.path, self.name))
        for raw in ('not json', '{}', '{"results":[null]}'):
            self.path.write_text(raw)
            self.assertFalse(collector.below_resolution_export(2, self.path, self.name))


class ResolutionProtocolTest(unittest.TestCase):
    """Authenticate the archived real failure without executing any benchmark."""

    def setUp(self):
        root = Path(collector.__file__).resolve().parents[2]
        archive = root / 'reports/bench-results/sign-det-phase6-comparison/initial-capture'
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name) / 'original'
        self.directory.mkdir()
        for name in ('context.json', 'decision.json', '0-0-baseline.json', '0-0-candidate.json'):
            (self.directory / name).write_bytes(gzip.decompress((archive / (name + '.gz')).read_bytes()))
        self.context = json.loads((self.directory / 'context.json').read_text())
        self.sources = deepcopy(self.context['sources'])
        self.identity = self.context['comparison_identity']
        self.names = self.context['benchmarks'][:]
        self.reservation = Path(self.temp.name) / 'reserved.json'
        self.context.update(decision_reservation=str(self.reservation), host=collector.platform.node())
        for record in self.context['commands']:
            command = record['command']
            if command[1:2] == ['run']:
                command[-1] = str(self.directory / Path(command[-1]).name)
        self.registry = Path(self.temp.name) / 'registry'
        bench = self.registry / 'bench/HexSignDet/Bench.lean'
        bench.parent.mkdir(parents=True)
        bench.write_bytes((root / 'bench/HexSignDet/Bench.lean').read_bytes())
        core = self.registry / '.lake/packages/lean-bench/LeanBench/Core.lean'
        core.parent.mkdir(parents=True)
        core.write_text('structure BenchmarkConfig where\n  killGraceMs : Nat := 100\n  signalFloorMultiplier : Float := 10.0\n')
        self.policy = dict(target_inner_nanos=2_250_000_000,
                           target_benchmarks=sorted(collector.SIGN_DET_RESOLUTION),
                           planning_spawn_floor_nanos=1_000_000_000, reason='Retain the floor; increase timed work',
                           benchmarks=self.names[:])
        self.bind()

    def bind(self):
        path = self.directory / 'context.json'
        path.write_text(json.dumps(self.context))
        digest = collector.digest(path)
        self.reservation.write_text(json.dumps(dict(first_output=str(self.directory), context_sha256=digest)))
        self.policy.update(previous_context_sha256=digest, previous_exports={
            name: collector.digest(self.directory / name)
            for name in ('0-0-baseline.json', '0-0-candidate.json')})

    def validate(self):
        return collector.validate_resolution_protocol(self.directory, self.policy, self.sources,
                                                      self.identity, self.reservation, self.names, self.registry)

    def test_retained_complete_below_floor_pair_authenticates(self):
        self.assertEqual(self.validate()['exports'], self.policy['previous_exports'])

    def test_budget_is_checked_against_the_frozen_runner_and_registration_caps(self):
        budgets = collector.resolution_budget(self.registry, self.policy)
        self.assertEqual(budgets['Hex.SignDetBench.Height.runCheck']['maximum_target_nanos'], 2_275_000_000)
        self.assertEqual(budgets['Hex.SignDetBench.runSmallFull']['maximum_target_nanos'], 14_775_000_000)
        self.policy['target_inner_nanos'] = 4_000_000_000
        with self.assertRaisesRegex(RuntimeError, 'would be clamped'):
            collector.resolution_budget(self.registry, self.policy)

    def test_unfiltered_or_partial_target_scope_is_refused(self):
        self.policy['target_benchmarks'].append('Hex.SignDetBench.runProduce')
        with self.assertRaisesRegex(RuntimeError, 'four filtered'):
            self.validate()

    def test_changed_cap_is_detected_before_reservation(self):
        path = self.registry / 'bench/HexSignDet/Bench.lean'
        path.write_text(path.read_text().replace('maxSecondsPerCall := 10', 'maxSecondsPerCall := 8'))
        with self.assertRaisesRegex(RuntimeError, 'would be clamped'):
            self.validate()

    def test_proposal_binds_actual_archived_context_and_both_exports(self):
        root = Path(collector.__file__).resolve().parents[2]
        report = root / 'reports/bench-results/sign-det-phase6-comparison'
        proposal = json.loads((report / 'resolution-proposal.json').read_text())
        raw = gzip.decompress((report / 'initial-capture/context.json.gz').read_bytes())
        context = json.loads(raw)
        self.assertEqual(proposal['comparison_identity'], context['comparison_identity'])
        self.assertEqual(proposal['guard_sha256'], context['guard_sha256'])
        self.assertEqual(proposal['source_heads'], {a: s['head'] for a, s in context['sources'].items()})
        self.assertEqual(proposal['binaries'], {a: s['binary_sha256'] for a, s in context['sources'].items()})
        policy = proposal['resolution_protocol']
        self.assertEqual(policy['target_inner_nanos'], 2_250_000_000)
        self.assertEqual(policy['target_benchmarks'], sorted(collector.SIGN_DET_RESOLUTION))
        self.assertEqual(policy['planning_spawn_floor_nanos'], 1_000_000_000)
        self.assertEqual(policy['previous_context_sha256'], hashlib.sha256(raw).hexdigest())
        self.assertEqual(policy['benchmarks'], context['benchmarks'])
        for name, digest in policy['previous_exports'].items():
            self.assertEqual(digest, hashlib.sha256(gzip.decompress(
                (report / 'initial-capture' / (name + '.gz')).read_bytes())).hexdigest())

    def test_target_and_policy_shape_cannot_create_another_protocol(self):
        for value in (True, 1_000_000_000, 8_000_000_000, '4000000000'):
            with self.subTest(value=value), self.assertRaisesRegex(RuntimeError, '2.25-second'):
                self.policy['target_inner_nanos'] = value
                self.validate()
        self.policy['target_inner_nanos'] = 2_250_000_000
        self.policy['extra'] = 'another slot'
        with self.assertRaisesRegex(RuntimeError, 'incomplete resolution'):
            self.validate()

    def test_changed_or_partial_frozen_scope_is_refused(self):
        self.policy['benchmarks'].pop()
        with self.assertRaisesRegex(RuntimeError, 'every original timing'):
            self.validate()
        self.policy['benchmarks'] = self.names[:]
        self.sources['candidate']['binary_sha256'] = 'different'
        with self.assertRaisesRegex(RuntimeError, 'frozen producer'):
            self.validate()

    def test_failed_status_and_integrity_are_required_even_after_rebinding(self):
        original = deepcopy(self.context)
        for key, value in (('status', 'completed'), ('profile', 'sturm'), ('integrity_failure', 'changed'),
                           ('reruns', 1), ('attempt_reserved', False), ('measurements_collected', False),
                           ('resolution_protocol', {}), ('cap_protocol', {})):
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'intact original'):
                self.context = deepcopy(original)
                self.context[key] = value
                self.bind()
                self.validate()

    def test_foreign_reservation_host_and_modified_exports_are_refused(self):
        self.context['host'] = 'foreign-host'
        self.bind()
        with self.assertRaisesRegex(RuntimeError, 'reservation or host'):
            self.validate()
        self.context['host'] = collector.platform.node()
        self.bind()
        path = self.directory / '0-0-baseline.json'
        path.write_text(path.read_text() + '\n')
        with self.assertRaisesRegex(RuntimeError, 'export hashes'):
            self.validate()

    def test_wrong_answers_and_incomplete_original_baseline_are_refused(self):
        path = self.directory / '0-0-baseline.json'
        original = path.read_bytes()
        for key, value in (('result_hash', 'wrong'), ('result_hash', None), ('status', 'error'),
                           ('error', 'failed'), ('trial_index', 1), ('total_nanos', float('inf'))):
            with self.subTest(key=key), self.assertRaises((RuntimeError, ValueError)):
                doc = json.loads(original)
                doc['results'][0]['points'][0][key] = value
                path.write_text(json.dumps(doc))
                self.bind()
                self.validate()

    def test_original_failure_must_be_the_recorded_complete_export(self):
        self.context['parent_failures'][0]['returncode'] = 7
        self.bind()
        with self.assertRaisesRegex(RuntimeError, 'below-floor exit'):
            self.validate()

    def test_below_floor_labels_must_match_actual_timings(self):
        path = self.directory / '0-0-candidate.json'
        doc = json.loads(path.read_text())
        result = doc['results'][0]
        result['points'][0]['total_nanos'] = result['spawn_floor_nanos'] * result['config']['signal_floor_multiplier']
        path.write_text(json.dumps(doc))
        self.context['parent_failures'][0]['results'] = doc['results']
        self.bind()
        with self.assertRaisesRegex(RuntimeError, 'declared signal floor'):
            self.validate()

    def test_decision_context_and_journal_bindings_are_checked(self):
        self.reservation.write_text('{}')
        with self.assertRaisesRegex(RuntimeError, 'first attempt'):
            self.validate()
        self.bind()
        (self.directory / 'decision.json').write_text('{}')
        with self.assertRaisesRegex(RuntimeError, 'original decision'):
            self.validate()


class RegistrationTest(unittest.TestCase):
    def setUp(self):
        self.lines = ["registered benchmarks:",
                      "Hex.SturmBench.runInteger expected complexity: n ^ 4",
                      "Hex.SturmFrontendBench.runPrepared expected complexity: n ^ 4",
                      AUXILIARY + " expected complexity: n ^ 2"]
        self.lines += [name + " [fixed] repeats=4" for name in sorted(NATIVE_FIXED)]
        self.lines += ["Hex.SturmExternalBench.runFlintCount [fixed] repeats=4"]

    def select(self):
        return registrations("\n".join(self.lines))

    def test_timing_scope_and_correctness_controls(self):
        names, native, excluded = self.select()
        self.assertEqual(len(names), 2)
        self.assertEqual(set(native), NATIVE_FIXED)
        self.assertEqual(set(excluded), {AUXILIARY, "Hex.SturmExternalBench.runFlintCount"})
        self.assertNotIn(AUXILIARY, names)

    def test_no_native_controls(self):
        self.lines = [line for line in self.lines if "runNative" not in line]
        with self.assertRaisesRegex(RuntimeError, "native fixed"):
            self.select()

    def test_missing_one_native_control(self):
        self.lines = [line for line in self.lines if "runNative64" not in line]
        with self.assertRaisesRegex(RuntimeError, "native fixed"):
            self.select()

    def test_duplicate_native_control(self):
        self.lines.append(sorted(NATIVE_FIXED)[0] + " [fixed] repeats=4")
        with self.assertRaisesRegex(RuntimeError, "native fixed"):
            self.select()

    def test_missing_auxiliary_requires_scope_review(self):
        self.lines = [line for line in self.lines if AUXILIARY not in line]
        with self.assertRaisesRegex(RuntimeError, "auxiliary registration"):
            self.select()

    def test_empty_timing_scope(self):
        self.lines = [line for line in self.lines if "expected complexity:" not in line]
        with self.assertRaisesRegex(RuntimeError, "unexpected computational"):
            self.select()

    def test_only_auxiliary_refused(self):
        self.lines = [line for line in self.lines if 'expected complexity:' not in line or AUXILIARY in line]
        with self.assertRaisesRegex(RuntimeError, 'empty timing selection'):
            self.select()

    def test_unknown_computational_namespace(self):
        self.lines.append("Other.run expected complexity: n")
        with self.assertRaisesRegex(RuntimeError, "unexpected computational"):
            self.select()

    def test_duplicate_timing_registration(self):
        self.lines.append(self.lines[1])
        with self.assertRaisesRegex(RuntimeError, "unexpected computational"):
            self.select()

    def test_unhashed_registration(self):
        self.lines[1] += " (no Hashable)"
        with self.assertRaisesRegex(RuntimeError, "unhashed"):
            self.select()


class NativePinTest(unittest.TestCase):
    def setUp(self):
        self.manifest = {"packages": [
            {"name": name, "type": "git", "rev": "old", "url": "https://example.test/" + name}
            for name in ("Cli", "«lean-bench»", "mathlib", "TauCeti")]}

    def test_proof_only_pin_changes_do_not_confuse_native_comparison(self):
        changed = deepcopy(self.manifest)
        changed["packages"][2]["rev"] = "new"
        changed["packages"][3]["rev"] = "new"
        self.assertEqual(native_harness_pins(changed), native_harness_pins(self.manifest))

    def test_cli_and_runner_pin_changes_are_visible(self):
        for index in (0, 1):
            changed = deepcopy(self.manifest)
            changed["packages"][index]["rev"] = "new"
            self.assertNotEqual(native_harness_pins(changed), native_harness_pins(self.manifest))

    def test_missing_cli_refused(self):
        self.manifest["packages"].pop(0)
        with self.assertRaisesRegex(RuntimeError, "dependency pin"):
            native_harness_pins(self.manifest)


class CollectorTest(unittest.TestCase):
    """Run the real collector against synthetic executable and git inputs."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "source"
        self.root.mkdir()
        repo = Path(collector.__file__).resolve().parents[2]
        for name in collector.TOOL_SOURCES:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((repo / name).read_bytes())
        for name in ("bench/HexSturm/Bench.lean", "bench/HexSturm/Frontend.lean",
                     ".lake/packages/lean-bench/LeanBench/Stats.lean", "lean-toolchain"):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("synthetic frozen input\n")
        (self.root / 'bench/HexSturm/Bench.lean').write_text('def config := { maxSecondsPerCall := 1800 }\n')
        (self.root / '.lake/packages/lean-bench/LeanBench/Core.lean').write_text(
            'structure BenchmarkConfig where\n  maxSecondsPerCall : Float := 1.0\n'
            'structure FixedBenchmarkConfig where\n  maxSecondsPerCall : Float := 60.0\n')
        evidence = self.root / 'reports/bench-results/sturm-phase6-comparison/retained.json'
        evidence.parent.mkdir(parents=True, exist_ok=True)
        evidence.write_text('{"retained":true}\n')
        manifest = {"packages": [{"name": name, "type": "git", "rev": "stub", "url": "stub"}
                                 for name in ("Cli", "«lean-bench»")]}
        (self.root / "lake-manifest.json").write_text(json.dumps(manifest))
        def git(*args):
            return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.DEVNULL, text=True).strip()
        git("init", "-q")
        git("add", ".")
        git("-c", "user.name=Control", "-c", "user.email=control@example.test", "commit", "-qm", "synthetic source")
        head = git("rev-parse", "HEAD")
        listing = "\n".join(["Hex.SturmBench.runInteger expected complexity: n ^ 4",
                             AUXILIARY + " expected complexity: n ^ 2",
                             *[name + " [fixed] repeats=4" for name in sorted(NATIVE_FIXED)]])
        self.binaries = {}
        for arm in ("baseline", "candidate"):
            path = self.base / arm
            program = '''#!/usr/bin/env python3
import json,sys,os,signal,subprocess,time
from pathlib import Path
arm=ARM
mode=MODE
if sys.argv[1]=='list':
    print(LISTING)
elif sys.argv[1]=='run':
    target=Path(sys.argv[sys.argv.index('--export-file')+1])
    adapted='--max-seconds-per-call' in sys.argv
    cap=float(sys.argv[sys.argv.index('--max-seconds-per-call')+1]) if adapted else 120
    killed=mode.startswith('cap') and not adapted and (mode!='cap-later' or target.name.startswith('1-'))
    status='killed_at_cap' if killed else 'ok'
    result={'kind':'parametric','function':sys.argv[2],
            'config':{'max_seconds_per_call':120 if mode=='cap-ignore' else cap},'budget_truncated':False,
            'points':[{'param':65 if mode=='cap-split' and arm=='candidate' else 64,
                       'result_hash':'wrong' if mode=='mismatch' and arm=='candidate' else 'same',
                       'status':'error' if mode=='cap-error' and arm=='candidate' else
                                'timedOut' if mode in ('timeout','exit','exit-worker') and arm=='candidate' else status,
                       'per_call_nanos':100,'error':None}]}
    if mode in ('cap-null','cap-mismatch'):
        result['points'].insert(0,{'param':32,'status':'ok','error':None,'per_call_nanos':50,
                                  'result_hash':None if mode=='cap-null' else arm})
    if mode=='below-resolution' and arm=='candidate':
        result.update(verdict='inconclusive', trial_summaries=[])
        result['config'].update(outer_trials=1, param_schedule={'kind':'custom','params':[64]})
        result['points'][0].update(error=None, below_signal_floor=True,
                                   total_nanos=100, inner_repeats=1, trial_index=0)
    elif mode=='below-resolution':
        result['config'].update(outer_trials=1, param_schedule={'kind':'custom','params':[64]})
    target.write_text(json.dumps({'results':[result]}))
    if mode=='below-resolution' and arm=='candidate':sys.exit(2)
    if (mode=='interrupt' or (mode=='cap-interrupt' and adapted)) and arm=='candidate':
        worker=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'])
        Path(__file__+'.worker-pid').write_text(str(worker.pid))
        os.kill(os.getppid(),signal.SIGINT)
        time.sleep(60)
    if mode in ('exit-worker','ok-worker') and arm=='candidate':
        worker=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'])
        Path(__file__+'.worker-pid').write_text(str(worker.pid))
    if mode in ('exit','exit-worker') and arm=='candidate':sys.exit(7)
    if mode=='mutate' and arm=='candidate':
        with open(__file__,'a') as handle:handle.write('\\n# mutation\\n')
'''.replace('ARM', repr(arm)).replace('MODE', repr('ok')).replace('LISTING', repr(listing))
            path.write_text(program)
            path.chmod(0o755)
            self.binaries[arm] = path
        self.guard = self.base / "guard"
        self.guard.write_text("#!/usr/bin/env python3\nimport sys,json\nfrom pathlib import Path\nPath(sys.argv[1]).write_text('{}')\nsys.exit(0)\n")
        self.guard.chmod(0o755)
        hashes = {str(path.relative_to(self.root)): collector.digest(path)
                  for path in self.root.rglob('*') if path.is_file() and '.git' not in path.parts
                  and (path.suffix == '.lean' or path.name in {'lean-toolchain', 'lake-manifest.json'})}
        self.sources = {}
        for arm, binary in self.binaries.items():
            source = self.base / (arm + "-source.json")
            source.write_text(json.dumps({"status": [], "head": head,
                                         "binary_sha256": collector.digest(binary), "sources": hashes}))
            self.sources[arm] = source
        self.decision = self.base / "decision.json"
        self.lease_exception = None
        self.account_home = self.base / 'account'
        self.bind_decision()

    def bind_decision(self):
        for arm, path in self.sources.items():
            source = json.loads(path.read_text())
            source['binary_sha256'] = collector.digest(self.binaries[arm])
            path.write_text(json.dumps(source))
        self.decision.write_text(json.dumps({
            'question': 'synthetic collector control', 'interruption': 'retain incomplete data',
            'regression': 'retain and investigate', 'inconclusive_rerun': 'one unchanged rerun',
            'interruption_consumes_decision': True,
            'guard_build': {'command': ['synthetic', 'guard'], 'result': 'success',
                            'source_head': json.loads(self.sources['candidate'].read_text())['head']},
            'script_sha256': collector.digest(Path(collector.__file__)),
            'guard_sha256': collector.digest(self.guard),
            'tool_sources': {p: collector.digest(self.root / p) for p in collector.TOOL_SOURCES},
            **{arm + '_source_sha256': collector.digest(path) for arm, path in self.sources.items()}}))

    def run_collector(self, name='capture', extra=(), legacy_state=None):
        output = self.base / name
        args = [str(x) for pair in (
            ('--root', self.root), ('--guard', self.guard), ('--decision', self.decision),
            ('--output', output), *[("--" + arm, path) for arm, path in self.binaries.items()],
            *[("--" + arm + '-source', path) for arm, path in self.sources.items()]) for x in pair]
        with patch.object(collector, 'cpu_lease', return_value=(0, io.StringIO()), side_effect=self.lease_exception) as lease, \
             patch.object(collector.os, 'sched_setaffinity'), \
             patch.object(collector.pwd, 'getpwuid', return_value=SimpleNamespace(pw_dir=str(self.account_home))), \
             (patch.object(collector, 'state_directory', return_value=legacy_state)
              if legacy_state is not None else nullcontext()), \
             redirect_stdout(io.StringIO()):
            try:
                result = collector.main([*args, *map(str, extra)])
            finally:
                self.context = json.loads((output / 'context.json').read_text())
                self.lease_calls = lease.call_count
        return result, output

    def test_complete_order_and_guard_arguments(self):
        code, output = self.run_collector()
        self.assertEqual(code, 0)
        commands = self.context['commands']
        runs = [r['command'] for r in commands if r['command'][1:2] == ['run']]
        self.assertEqual([Path(c[0]).name for c in runs],
                         ['baseline','candidate','candidate','baseline','baseline','candidate','candidate','baseline'])
        self.assertTrue(all(c[c.index('--outer-trials') + 1] == '1' for c in runs))
        guard = commands[-1]['command']
        self.assertEqual(guard[2:], [str(output / f'{trial}-0-{arm}.json')
                                    for arm in ('baseline','candidate') for trial in range(4)])
        self.assertEqual([p['ratios'][0]['candidate_over_baseline'] for p in self.context['paired_ratios']], [1] * 4)

    def test_preflight_does_not_lease_or_measure(self):
        code, _ = self.run_collector(extra=['--preflight'])
        self.assertEqual(code, 0)
        self.assertEqual(self.lease_calls, 0)
        self.assertEqual(self.context['outcome'], 'preflight')
        self.assertFalse(self.context['measurements_collected'])
        self.assertNotIn('pass', self.context)

    def test_sturm_function_mismatch_keeps_cross_arm_error(self):
        path = self.binaries['candidate']
        path.write_text(path.read_text().replace(
            '    target.write_text(', "    result['function']='wrong'\n    target.write_text("))
        self.bind_decision()
        with self.assertRaisesRegex(RuntimeError, 'cross-arm input/configuration/hash mismatch'):
            self.run_collector()
        self.assertEqual(self.context['parent_failures'][1]['function'], 'wrong')

    def mode(self, value):
        path = self.binaries['candidate']
        path.write_text(path.read_text().replace("mode='ok'", 'mode=' + repr(value)))
        self.bind_decision()

    def cap_failure(self, mode='cap'):
        for path in self.binaries.values():
            path.write_text(path.read_text().replace("mode='ok'", 'mode=' + repr(mode)))
        self.bind_decision()
        with self.assertRaisesRegex(RuntimeError, 'failed parent'):
            self.run_collector('original')
        return self.base / 'original'

    def bind_cap(self, previous, seconds=3600):
        context = json.loads((previous / 'context.json').read_text())
        decision = json.loads(self.decision.read_text())
        decision['tooling_root_head'] = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=self.root, text=True).strip()
        exports = {}
        for failure in context['parent_failures']:
            commands = [r['command'] for r in context['commands']
                        if r['command'][1:3] == ['run', failure['function']]
                        and Path(r['command'][r['command'].index('--export-file')+1]).name.endswith(
                            '-' + failure['arm'] + '.json')]
            command = commands[-1]
            path = Path(command[command.index('--export-file')+1])
            exports[path.name] = collector.digest(path)
        decision['cap_protocol'] = {
            'seconds': seconds, 'reason': 'Increase only the operational cap for every original family',
            'benchmarks': context['benchmarks'],
            'previous_context_sha256': collector.digest(previous / 'context.json'),
            'previous_exports': exports}
        self.decision.write_text(json.dumps(decision))

    def tooling_commit(self, path, contents):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents)
        subprocess.check_call(['git', 'add', path], cwd=self.root, stdout=subprocess.DEVNULL)
        subprocess.check_call(['git', '-c', 'user.name=Control', '-c', 'user.email=control@example.test',
                               'commit', '-qm', 'tooling input'], cwd=self.root)

    def assert_worker_stopped(self):
        worker = int(Path(str(self.binaries['candidate']) + '.worker-pid').read_text())
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            try:
                os.kill(worker, 0)
            except ProcessLookupError:
                return
            stat = Path('/proc') / str(worker) / 'stat'
            try:
                if stat.read_text().split()[2] == 'Z':
                    return
            except FileNotFoundError:
                pass
            time.sleep(0.01)
        os.kill(worker, 9)
        self.fail('benchmark worker survived parent interruption')

    def test_cap_tooling_commit_preserves_original_build_manifests(self):
        first = self.cap_failure()
        original = {arm: path.read_bytes() for arm, path in self.sources.items()}
        source_head = json.loads(self.sources['candidate'].read_text())['head']
        self.tooling_commit('reports/bench-results/sturm-phase6-comparison/note.md', 'tooling only\n')
        self.bind_cap(first)
        code, _ = self.run_collector('adapted', ['--cap-from', first])
        self.assertEqual(code, 0)
        self.assertEqual(self.context['sources']['candidate']['head'], source_head)
        self.assertNotEqual(self.context['tooling_root_head'], source_head)
        self.assertEqual({arm: path.read_bytes() for arm, path in self.sources.items()}, original)

    def test_cap_tooling_commit_refuses_other_changes(self):
        first = self.cap_failure()
        self.tooling_commit('unapproved.md', 'outside the tooling allowlist\n')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'unapproved paths'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_default_mode_still_requires_exact_build_commit(self):
        self.tooling_commit('reports/bench-results/sturm-phase6-comparison/note.md', 'tooling only\n')
        with self.assertRaisesRegex(RuntimeError, 'candidate tree differs'):
            self.run_collector()

    def test_parametric_default_is_separate_from_fixed_benchmark_default(self):
        path = self.root / '.lake/packages/lean-bench/LeanBench/Core.lean'
        path.write_text(path.read_text().replace('60.0', '50000.0'))
        self.assertEqual(collector.registered_cap(self.root), 1800)

    def test_cap_cannot_relabel_old_build_to_new_tooling_commit(self):
        first = self.cap_failure()
        self.tooling_commit('reports/bench-results/sturm-phase6-comparison/note.md', 'tooling only\n')
        source = self.sources['candidate']
        document = json.loads(source.read_text())
        document['head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=self.root, text=True).strip()
        source.write_text(json.dumps(document))
        self.bind_decision()
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'original source manifests'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_cap_keeps_original_guard_build_provenance(self):
        first = self.cap_failure()
        self.bind_cap(first)
        decision = json.loads(self.decision.read_text())
        decision['guard_build']['command'] = ['a', 'different', 'build']
        self.decision.write_text(json.dumps(decision))
        with self.assertRaisesRegex(RuntimeError, 'original guard-build provenance'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_cap_refuses_relocated_state_even_with_copied_journal(self):
        first = self.cap_failure()
        original = Path(self.context['decision_reservation'])
        relocated = self.base / 'relocated-state'
        target = relocated / 'hex/sturm-comparisons' / original.name
        target.parent.mkdir(parents=True)
        target.write_bytes(original.read_bytes())
        self.bind_cap(first)
        self.run_collector('adapted', ['--cap-from', first])
        with patch.dict(collector.os.environ, {'XDG_STATE_HOME': str(relocated)}):
            with self.assertRaisesRegex(RuntimeError, 'decision already used'):
                self.run_collector('relocated', ['--cap-from', first])
        self.assertFalse(target.with_name(target.stem + '-cap.json').exists())
        self.assertEqual(self.lease_calls, 0)

    def test_state_directory_ignores_environment_and_path_home(self):
        account = self.base / 'os-account'
        with patch.object(collector.pwd, 'getpwuid', return_value=SimpleNamespace(pw_dir=str(account))), \
             patch.object(Path, 'home', return_value=self.base / 'environment-home'), \
             patch.dict(collector.os.environ, {'XDG_STATE_HOME': str(self.base / 'relocated')}):
            self.assertEqual(collector.state_directory(), account / '.local/state')

    def test_environment_relocation_does_not_unlock_a_default_attempt(self):
        self.guard_code(1)
        self.run_collector()
        relocated = self.base / 'relocated'
        with patch.dict(collector.os.environ, {'XDG_STATE_HOME': str(relocated)}):
            with self.assertRaisesRegex(RuntimeError, 'decision already used'):
                self.run_collector('again')
        self.assertTrue(Path(self.context['decision_reservation']).is_relative_to(
            self.account_home / '.local/state'))
        self.assertFalse(relocated.exists())

    def test_original_regenerated_in_relocated_state_cannot_authorize_adaptation(self):
        self.cap_failure()
        # Emulate the old collector's environment-selected state directory.
        with self.assertRaisesRegex(RuntimeError, 'failed parent'):
            self.run_collector('regenerated-original', legacy_state=self.base / 'old-relocated-state')
        regenerated = self.base / 'regenerated-original'
        self.bind_cap(regenerated)
        with self.assertRaisesRegex(RuntimeError, 'original reservation path'):
            self.run_collector('adapted', ['--cap-from', regenerated])
        self.assertFalse(self.context['attempt_reserved'])

    def test_tooling_head_must_match_the_decision(self):
        first = self.cap_failure()
        self.bind_cap(first)
        decision = json.loads(self.decision.read_text())
        decision['tooling_root_head'] = '0' * 40
        self.decision.write_text(json.dumps(decision))
        with self.assertRaisesRegex(RuntimeError, 'tooling root differs'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_tooling_commit_must_descend_from_original(self):
        first = self.cap_failure()
        subprocess.check_call(['git', 'checkout', '--orphan', 'unrelated'], cwd=self.root,
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        subprocess.check_call(['git', '-c', 'user.name=Control', '-c', 'user.email=control@example.test',
                               'commit', '-qm', 'unrelated history'], cwd=self.root)
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'does not descend'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_new_lean_file_under_report_directory_is_refused(self):
        first = self.cap_failure()
        self.tooling_commit('reports/bench-results/sturm-phase6-comparison/Extra.lean', 'def extra := 1\n')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'unapproved paths'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_tooling_commit_cannot_rewrite_existing_raw_evidence(self):
        first = self.cap_failure()
        self.tooling_commit('reports/bench-results/sturm-phase6-comparison/retained.json', '{}\n')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'unapproved paths'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_cap_refuses_different_host(self):
        with patch.object(collector.platform, 'node', return_value='another-host'):
            first = self.cap_failure()
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'original host'):
            self.run_collector('foreign-host', ['--cap-from', first])

    def test_cap_refuses_different_killed_parameters(self):
        first = self.cap_failure('cap-split')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'different cap parameters'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_cap_refuses_one_arm_error(self):
        first = self.cap_failure('cap-error')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'per-call cap termination'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_cap_refuses_missing_completed_hash(self):
        first = self.cap_failure('cap-null')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'no result hash'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_cap_refuses_mismatched_completed_hashes(self):
        first = self.cap_failure('cap-mismatch')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'parameters or hashes differ'):
            self.run_collector('adapted', ['--cap-from', first])

    def test_interrupted_cap_capture_consumes_slot_and_kills_worker(self):
        first = self.cap_failure('cap-interrupt')
        self.bind_cap(first)
        with self.assertRaises(KeyboardInterrupt):
            self.run_collector('adapted', ['--cap-from', first])
        self.assertEqual(self.context['status'], 'interrupted')
        self.assertTrue(self.context['attempt_reserved'])
        self.assertEqual(self.context['commands'][-1]['status'], 'interrupted')
        self.assert_worker_stopped()
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('retry', ['--cap-from', first])

    def test_deleting_cap_rerun_receipt_does_not_allow_another_rerun(self):
        self.guard_code(2)
        first = self.cap_failure()
        self.bind_cap(first)
        _, adapted = self.run_collector('adapted', ['--cap-from', first])
        self.run_collector('repeat', ['--cap-from', first, '--rerun-of', adapted])
        (adapted / 'unchanged-rerun.json').unlink()
        with self.assertRaisesRegex(RuntimeError, 'already reserved'):
            self.run_collector('again', ['--cap-from', first, '--rerun-of', adapted])

    def test_cap_adaptation_preserves_original_reservation_and_balanced_schedule(self):
        first = self.cap_failure()
        journal = Path(self.context['decision_reservation'])
        original = journal.read_bytes()
        self.bind_cap(first)
        code, _ = self.run_collector('adapted', ['--cap-from', first])
        self.assertEqual(code, 0)
        self.assertEqual(journal.read_bytes(), original)
        self.assertNotEqual(str(journal), self.context['decision_reservation'])
        runs = [r['command'] for r in self.context['commands'] if r['command'][1:2] == ['run']]
        self.assertEqual([Path(c[0]).name for c in runs],
                         ['baseline','candidate','candidate','baseline','baseline','candidate','candidate','baseline'])
        self.assertTrue(all(c[c.index('--max-seconds-per-call') + 1] == '3600' for c in runs))
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('another', ['--cap-from', first])
        self.bind_cap(first, 7200)
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('larger', ['--cap-from', first])

    def test_cap_preflight_neither_reserves_nor_measures(self):
        first = self.cap_failure()
        self.bind_cap(first)
        code, _ = self.run_collector('preflight', ['--cap-from', first, '--preflight'])
        self.assertEqual(code, 0)
        self.assertFalse(self.context['attempt_reserved'])
        self.assertFalse(self.context['measurements_collected'])
        self.assertEqual(self.lease_calls, 0)
        self.assertFalse(Path(self.context['decision_reservation']).exists())

    def test_consumed_adaptation_is_not_preflight_eligible(self):
        first = self.cap_failure()
        self.bind_cap(first)
        self.run_collector('adapted', ['--cap-from', first])
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('preflight', ['--cap-from', first, '--preflight'])
        self.assertEqual(self.lease_calls, 0)

    def test_later_block_failure_preserves_earlier_completed_pairs(self):
        first = self.cap_failure('cap-later')
        original = {p.name: p.read_bytes() for p in first.glob('[0-9]*.json')}
        self.assertEqual(len(original), 4)
        self.bind_cap(first)
        code, _ = self.run_collector('adapted', ['--cap-from', first])
        self.assertEqual(code, 0)
        self.assertEqual({p.name: p.read_bytes() for p in first.glob('[0-9]*.json')}, original)

    def test_cap_protocol_and_input_are_required_together(self):
        first = self.cap_failure()
        with self.assertRaisesRegex(RuntimeError, 'required together'):
            self.run_collector('missing-policy', ['--cap-from', first])
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'required together'):
            self.run_collector('missing-input')

    def test_cap_policy_rejects_invalid_limits(self):
        first = self.cap_failure()
        for index, cap in enumerate([True, 0, -1, '3600', float('inf'), float('nan'),
                                     120, 300, 1800.1234567, collector.MAX_CAP_SECONDS + 1]):
            with self.subTest(cap=cap):
                self.bind_cap(first, cap)
                with self.assertRaisesRegex(RuntimeError, 'whole seconds|registration limit'):
                    self.run_collector('bad-cap-' + str(index), ['--cap-from', first])
                self.assertEqual(self.lease_calls, 0)

    def test_cap_policy_cannot_drop_original_families(self):
        first = self.cap_failure()
        self.bind_cap(first)
        decision = json.loads(self.decision.read_text())
        decision['cap_protocol']['benchmarks'] = []
        self.decision.write_text(json.dumps(decision))
        with self.assertRaisesRegex(RuntimeError, 'every original timing family'):
            self.run_collector('subset', ['--cap-from', first])
        self.assertEqual(self.lease_calls, 0)

    def test_cap_policy_refuses_context_and_export_tampering(self):
        first = self.cap_failure()
        self.bind_cap(first)
        export = next(first.glob('[0-9]*-baseline.json'))
        export.write_text(export.read_text() + '\n')
        with self.assertRaisesRegex(RuntimeError, 'export hashes'):
            self.run_collector('changed-export', ['--cap-from', first])
        original = first / 'context.json'
        original.write_text(original.read_text() + '\n')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'retained first attempt'):
            self.run_collector('changed-context', ['--cap-from', first])

    def test_cap_adaptation_refuses_changed_native_inputs(self):
        first = self.cap_failure()
        source = self.sources['baseline']
        document = json.loads(source.read_text())
        document['sources']['extra.lean'] = 'changed'
        source.write_text(json.dumps(document))
        self.bind_decision()
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'original source manifests'):
            self.run_collector('changed-inputs', ['--cap-from', first])

    def test_non_cap_failure_does_not_authorize_cap_adaptation(self):
        self.mode('timeout')
        with self.assertRaises(RuntimeError):
            self.run_collector('original')
        first = self.base / 'original'
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'per-call cap termination'):
            self.run_collector('wrong-failure', ['--cap-from', first])

    def test_cap_adaptation_verifies_parent_applied_the_limit(self):
        first = self.cap_failure('cap-ignore')
        self.bind_cap(first)
        with self.assertRaisesRegex(RuntimeError, 'parent did not apply'):
            self.run_collector('ignored', ['--cap-from', first])
        self.assertTrue(self.context['attempt_reserved'])

    def test_cap_adaptation_keeps_one_inconclusive_rerun(self):
        self.guard_code(2)
        first = self.cap_failure()
        self.bind_cap(first)
        _, adapted = self.run_collector('adapted', ['--cap-from', first])
        self.assertEqual(self.context['outcome'], 'inconclusive')
        self.run_collector('repeat', ['--cap-from', first, '--rerun-of', adapted])
        self.assertEqual(self.context['reruns'], 1)
        with self.assertRaisesRegex(RuntimeError, 'already reserved'):
            self.run_collector('repeat-again', ['--cap-from', first, '--rerun-of', adapted])

    def test_cap_regression_cannot_be_retried_as_inconclusive(self):
        self.guard_code(1)
        first = self.cap_failure()
        self.bind_cap(first)
        _, adapted = self.run_collector('adapted', ['--cap-from', first])
        self.assertEqual(self.context['outcome'], 'regression')
        with self.assertRaisesRegex(RuntimeError, 'completed inconclusive'):
            self.run_collector('repeat', ['--cap-from', first, '--rerun-of', adapted])

    def test_cap_adaptation_does_not_free_the_original_default_slot(self):
        first = self.cap_failure()
        self.bind_cap(first)
        self.run_collector('adapted', ['--cap-from', first])
        self.bind_decision()
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('default-again')

    def test_hash_mismatch_aborts(self):
        self.mode('mismatch')
        with self.assertRaisesRegex(RuntimeError, 'cross-arm'):
            self.run_collector()
        self.assertEqual(self.context['status'], 'failed')

    def test_midrun_binary_change_invalidates_result(self):
        self.mode('mutate')
        code, _ = self.run_collector()
        self.assertEqual(code, 1)
        self.assertTrue(self.context['integrity_failure'])
        self.assertEqual(self.context['outcome'], 'invalid')

    def test_failure_status_is_retained(self):
        self.mode('timeout')
        with self.assertRaisesRegex(RuntimeError, 'failed parent'):
            self.run_collector()
        self.assertEqual(self.context['parent_failures'][1]['points'][0]['status'], 'timedOut')

    def test_early_input_error_is_not_integrity_failure(self):
        self.sources['baseline'].unlink()
        with self.assertRaises(FileNotFoundError):
            self.run_collector()
        self.assertNotIn('integrity_failure', self.context)

    def guard_code(self, code):
        self.guard.write_text(self.guard.read_text().replace('sys.exit(0)', f'sys.exit({code})'))
        self.bind_decision()

    def test_only_one_unchanged_inconclusive_rerun(self):
        self.guard_code(2)
        code, first = self.run_collector()
        self.assertEqual(code, 1)
        self.assertEqual(self.context['outcome'], 'inconclusive')
        _, second = self.run_collector('rerun', ['--rerun-of', first])
        self.assertEqual(self.context['reruns'], 1)
        self.assertEqual(self.context['rerun_of'], str(first))
        with self.assertRaisesRegex(RuntimeError, 'already reserved'):
            self.run_collector('third', ['--rerun-of', first])
        with self.assertRaisesRegex(RuntimeError, 'rerun a rerun'):
            self.run_collector('fourth', ['--rerun-of', second])

    def test_regression_is_not_an_inconclusive_rerun(self):
        self.guard_code(1)
        _, first = self.run_collector()
        self.assertEqual(self.context['outcome'], 'regression')
        with self.assertRaisesRegex(RuntimeError, 'completed inconclusive'):
            self.run_collector('rerun', ['--rerun-of', first])

    def test_changed_guard_is_not_unchanged_rerun(self):
        self.guard_code(2)
        _, first = self.run_collector()
        self.guard.write_text(self.guard.read_text() + '\n# changed guard\n')
        self.bind_decision()
        with self.assertRaisesRegex(RuntimeError, 'bindings differ: guard_sha256'):
            self.run_collector('rerun', ['--rerun-of', first])

    def test_preflight_does_not_reserve_rerun(self):
        self.guard_code(2)
        _, first = self.run_collector()
        code, _ = self.run_collector('preflight', ['--rerun-of', first, '--preflight'])
        self.assertEqual(code, 0)
        self.assertFalse((first / 'unchanged-rerun.json').exists())

    def test_missing_tool_binding_refused_before_measurement(self):
        decision = json.loads(self.decision.read_text())
        decision['tool_sources'].pop('scripts/bench/cpu_lease.py')
        self.decision.write_text(json.dumps(decision))
        with self.assertRaisesRegex(RuntimeError, 'incomplete tool'):
            self.run_collector()
        self.assertEqual(self.lease_calls, 0)
        self.assertFalse(self.context['measurements_collected'])

    def test_fresh_attempt_cannot_replace_regression(self):
        self.guard_code(1)
        self.run_collector()
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_fresh_attempt_cannot_reset_rerun_count(self):
        self.guard_code(2)
        _, first = self.run_collector()
        self.run_collector('rerun', ['--rerun-of', first])
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_lease_failure_does_not_consume_rerun(self):
        self.guard_code(2)
        _, first = self.run_collector()
        self.lease_exception = RuntimeError('all measurement CPU leases are held')
        with self.assertRaisesRegex(RuntimeError, 'CPU leases'):
            self.run_collector('no-lease', ['--rerun-of', first])
        self.assertFalse(self.context['attempt_reserved'])
        self.assertFalse((first / 'unchanged-rerun.json').exists())
        self.lease_exception = None
        self.run_collector('retry', ['--rerun-of', first])
        self.assertTrue(self.context['attempt_reserved'])

    def test_loaded_helper_must_match_binding(self):
        other = self.base / 'other-helper.py'
        other.write_text('unbound helper\n')
        with patch.object(collector.sys.modules['cpu_lease'], '__file__', str(other)):
            with self.assertRaisesRegex(RuntimeError, 'loaded helper'):
                self.run_collector()
        self.assertEqual(self.lease_calls, 0)

    def test_copying_decision_cannot_reset_attempt(self):
        self.guard_code(1)
        self.run_collector()
        other = self.base / 'another-directory'
        other.mkdir()
        copied = other / 'decision.json'
        copied.write_bytes(self.decision.read_bytes())
        self.decision = copied
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_reformatting_decision_cannot_reset_attempt(self):
        self.guard_code(1)
        self.run_collector()
        self.decision.write_text(json.dumps(json.loads(self.decision.read_text()), indent=4) + '\n')
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_rewording_question_cannot_reset_attempt(self):
        self.guard_code(1)
        self.run_collector()
        decision = json.loads(self.decision.read_text())
        decision['question'] = 'another description of the same executables'
        self.decision.write_text(json.dumps(decision))
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_another_checkout_cannot_reset_attempt(self):
        self.guard_code(1)
        self.run_collector()
        other = self.base / 'another-checkout'
        shutil.copytree(self.root, other)
        self.root = other
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_first_context_tampering_refused(self):
        self.guard_code(2)
        _, first = self.run_collector()
        data = json.loads((first / 'context.json').read_text())
        data['extra'] = 'modified'
        (first / 'context.json').write_text(json.dumps(data))
        with self.assertRaisesRegex(RuntimeError, 'retained first decision'):
            self.run_collector('rerun', ['--rerun-of', first])

    def test_nonzero_parent_exit_keeps_export_status(self):
        self.mode('exit')
        with self.assertRaisesRegex(RuntimeError, 'parent measurement failed'):
            self.run_collector()
        failure = self.context['parent_failures'][0]
        self.assertEqual(failure['returncode'], 7)
        self.assertEqual(failure['results'][0]['points'][0]['status'], 'timedOut')

    def test_below_resolution_continues_all_blocks_to_native_guard(self):
        self.mode('below-resolution')
        baseline = self.binaries['baseline']
        baseline.write_text(baseline.read_text().replace("mode='ok'", "mode='below-resolution'"))
        self.bind_decision()
        self.guard_code(2)
        code, _ = self.run_collector()
        self.assertEqual(code, 1)
        self.assertEqual(self.context['status'], 'completed')
        self.assertEqual(self.context['outcome'], 'inconclusive')
        self.assertFalse(self.context['pass'])
        self.assertEqual(len(self.context['below_resolution_exports']), 4)
        self.assertEqual(len(self.context['paired_ratios']), 4)
        self.assertEqual(len(self.context['guards']), 1)

    def test_below_resolution_cannot_pass_with_wrong_checker_result(self):
        self.mode('below-resolution')
        baseline = self.binaries['baseline']
        baseline.write_text(baseline.read_text().replace("mode='ok'", "mode='below-resolution'"))
        self.bind_decision()
        self.assertEqual(self.run_collector()[0], 1)
        self.assertEqual(self.context['outcome'], 'invalid')
        self.assertFalse(self.context['pass'])
        self.assertEqual(self.context['guards'][0]['returncode'], 0)
        self.assertEqual(self.context['below_resolution_guard_passes'],
                         ['Hex.SturmBench.runInteger'])

    def test_nonzero_parent_exit_also_stops_its_worker(self):
        self.mode('exit-worker')
        with self.assertRaisesRegex(RuntimeError, 'parent measurement failed'):
            self.run_collector()
        self.assert_worker_stopped()

    def test_successful_parent_also_stops_its_worker(self):
        self.mode('ok-worker')
        self.assertEqual(self.run_collector()[0], 0)
        self.assert_worker_stopped()

    def test_interruption_consumes_reserved_first_attempt(self):
        self.mode('interrupt')
        with self.assertRaises(KeyboardInterrupt):
            self.run_collector()
        self.assertEqual(self.context['status'], 'interrupted')
        self.assertTrue(self.context['attempt_reserved'])
        self.assert_worker_stopped()
        with self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('fresh')

    def test_invalid_family_does_not_hide_other_regression(self):
        for binary in self.binaries.values():
            binary.write_text(binary.read_text().replace(
                'expected complexity: n ^ 4',
                r'expected complexity: n ^ 4\nHex.SturmFrontendBench.runPrepared expected complexity: n ^ 4'))
        self.guard.write_text(self.guard.read_text().replace(
            'sys.exit(0)', "sys.exit(3 if 'guard-0' in sys.argv[1] else 1)"))
        self.bind_decision()
        code, _ = self.run_collector()
        self.assertEqual(code, 1)
        self.assertEqual(self.context['outcome'], 'invalid')
        self.assertEqual(self.context['regression_findings'], ['Hex.SturmFrontendBench.runPrepared'])


class SignDetScopeTest(unittest.TestCase):
    def test_real_bench_local_import_closure(self):
        root = Path(collector.__file__).resolve().parents[2]
        parse_imports = runpy.run_path(str(root / 'scripts/ci/check_benches_mathlib_free.py'))['_parse_imports']
        for profile, first in (('sign-det', 'HexSignDet.Bench'),
                               ('sign-det-interacting', 'HexSignDet.InteractingBench')):
            pending, found = [first], set()
            while pending:
                module = pending.pop()
                path = root / 'bench' / Path(*module.split('.')).with_suffix('.lean')
                if not path.exists() or str(path.relative_to(root)) in found:
                    continue
                found.add(str(path.relative_to(root)))
                pending.extend(parse_imports(path))
            self.assertEqual(set(collector.registration_paths(profile)), found)

    def listing(self, profile):
        params = collector.SIGN_DET_PARAMETRIC if profile == 'sign-det' else set()
        fixed = collector.timing_fixed(profile) | (collector.SIGN_DET_REFERENCES if params else set())
        return '\n'.join([*[name + ' expected complexity: n' for name in sorted(params)],
                          *[name + ' [fixed] repeats=1' for name in sorted(fixed)]])

    def test_primary_complete_scope(self):
        names, fixed, excluded = registrations(self.listing('sign-det'), 'sign-det')
        self.assertEqual(set(names), collector.SIGN_DET_PARAMETRIC | collector.SIGN_DET_FIXED)
        self.assertEqual(len(names), 31)
        self.assertEqual(set(fixed), collector.SIGN_DET_FIXED | collector.SIGN_DET_REFERENCES)
        self.assertEqual(set(excluded), collector.SIGN_DET_REFERENCES)

    def test_interacting_complete_scope(self):
        names, fixed, excluded = registrations(self.listing('sign-det-interacting'), 'sign-det-interacting')
        self.assertEqual(set(names), collector.INTERACTING_FIXED)
        self.assertEqual(names, fixed)
        self.assertEqual(excluded, [])

    def test_missing_duplicate_extra_and_unhashed_refused(self):
        for profile in ('sign-det', 'sign-det-interacting'):
            lines = self.listing(profile).splitlines()
            for text in ('\n'.join(lines[1:]), '\n'.join(lines + lines[:1]),
                         '\n'.join(lines + ['Other.run [fixed] repeats=1']),
                         '\n'.join(lines) + '\n(no Hashable)'):
                with self.subTest(profile=profile, text=text), self.assertRaises(RuntimeError):
                    registrations(text, profile)

    def test_registration_hash_addition_and_formatting_only(self):
        old = 'setup_fixed_benchmark run where { repeats := 1, minTotalSeconds := 0.1 }'
        new = 'setup_fixed_benchmark run where {\n repeats := 1, minTotalSeconds := 0.1,\n expectedHash := some 0x1234 }'
        self.assertEqual(collector.registration_source(old), collector.registration_source(new))
        for changed in (new.replace('0.1', '0.2'), new.replace('run where', 'other where')):
            self.assertNotEqual(collector.registration_source(old), collector.registration_source(changed))

    def test_registration_string_spaces_are_significant(self):
        self.assertNotEqual(collector.registration_source('def s := "a b"'),
                            collector.registration_source('def s := "ab"'))

    def test_callback_indentation_and_unicode_identifier_boundaries(self):
        for old, new in (
                ('def f := do\n  for i in xs do\n    a\n    b\n  return x',
                 'def f := do\n  for i in xs do\n    a\n  b\n  return x'),
                ('def f := x₁ y', 'def f := x₁y'),
                ('def s := "a  \nb"', 'def s := "a\nb"')):
            self.assertNotEqual(collector.registration_source(old), collector.registration_source(new))

    def test_complex_fixed_configuration_layout_is_preserved(self):
        old = 'setup_fixed_benchmark f where {\n expectedHash := some (Id.run do\n   a\n   b) }'
        new = old.replace('   b', ' b')
        self.assertNotEqual(collector.registration_source(old), collector.registration_source(new))

    def test_comment_mask_preserves_code_columns_and_nested_comments(self):
        for old, new in (
                ('def f := do\n    a\n    /- c -/ b', 'def f := do\n    a\n    /- c\n-/ b'),
                ('def f := do\n    /- c -/ a', 'def f := do\n    /- longer -/ a')):
            self.assertNotEqual(collector.registration_source(old), collector.registration_source(new))
        self.assertEqual(collector.registration_source('def f := 1 /- x /- y -/ z -/'),
                         collector.registration_source('def f := 1'))
        text = 'def s := "-- /- literal -/"\ndef c := \'"\' -- comment\ndef f := 1'
        self.assertIn('"-- /- literal -/"', collector.source_layout(text))
        self.assertTrue(collector.source_layout(text).endswith('def f := 1'))

    def test_comma_free_configuration_fields_keep_layout(self):
        old = 'setup_fixed_benchmark f where { a := f\n  b }'
        new = old.replace('\n  b', '\n      b')
        self.assertNotEqual(collector.registration_source(old), collector.registration_source(new))

    def test_current_fixed_registrations_match_unguarded_form(self):
        root = Path(collector.__file__).resolve().parents[2]
        for module, names, repeats in (('SharedRoots', ('runOne', 'runTwo', 'runThree'), 6),
                                       ('InteractingBench', ('depthOne', 'depthTwo'), 1)):
            new = (root / 'bench/HexSignDet' / (module + '.lean')).read_text()
            old = new
            for name in names:
                pattern = r'setup_fixed_benchmark ' + name + r'\s+where\s+\{[^}]+\}'
                old, count = collector.re.subn(pattern,
                    f'setup_fixed_benchmark {name} where {{ repeats := {repeats}, '
                    'minTotalSeconds := 0.1, maxSecondsPerCall := 10 }', old)
                self.assertEqual(count, 1)
            self.assertEqual(collector.registration_source(old), collector.registration_source(new))

    def test_hash_text_in_strings_and_callback_records_is_not_erased(self):
        for old, new in (
                ('def s := "x"', 'def s := "x, expectedHash := some 0x1234"'),
                ('def r := { other := 1 }', 'def r := { other := 1, expectedHash := some 0x1234 }'),
                ('setup_fixed_benchmark run where config\ndef r := { other := 1 }',
                 'setup_fixed_benchmark run where config\ndef r := { other := 1, expectedHash := some 0x1234 }')):
            self.assertNotEqual(collector.registration_source(old), collector.registration_source(new))

    def test_hash_field_first_middle_and_only(self):
        for old, new in (
                ('{ repeats := 1 }', '{ expectedHash := some 0x1234, repeats := 1 }'),
                ('{ repeats := 1, warmup := true }', '{ repeats := 1, expectedHash := some 0x1234, warmup := true }'),
                ('{}', '{ expectedHash := some 0x1234 }')):
            prefix = 'setup_fixed_benchmark run where '
            self.assertEqual(collector.registration_source(prefix + old),
                             collector.registration_source(prefix + new))

    def test_fixed_pair_guard_strengthening_and_integer_ratios(self):
        base = {'kind': 'fixed', 'function': 'case', 'budget_truncated': False,
                'hashable': True, 'hashes_agree': True, 'observed_hash': 'same',
                'config': {'repeats': 1, 'expected_hash': None, 'min_total_seconds': 0.1},
                'points': [{'repeat_index': 0, 'result_hash': 'same', 'status': 'ok',
                            'total_nanos': 1005, 'inner_repeats': 10}]}
        current = deepcopy(base)
        current['config']['expected_hash'] = 'same'
        current['points'][0]['total_nanos'] = 1105
        collector.validate_pair(base, current, 'case', 'fixed')
        self.assertEqual(collector.paired_ratios(base, current, 'fixed'),
                         [{'repeat_index': 0, 'candidate_over_baseline': 1.1}])
        for mutation in ('removal', 'timing', 'hash', 'observed', 'kind', 'subject', 'unhashable'):
            a, b = deepcopy(base), deepcopy(current)
            if mutation == 'removal':
                a['config']['expected_hash'], b['config']['expected_hash'] = 'same', None
            elif mutation == 'timing':
                b['config']['min_total_seconds'] = 0.2
            elif mutation == 'hash':
                b['config']['expected_hash'] = 'wrong'
            elif mutation == 'observed':
                b['observed_hash'] = 'wrong'
            elif mutation == 'kind':
                b['kind'] = 'parametric'
            elif mutation == 'subject':
                b['function'] = 'other'
            else:
                b['hashable'] = False
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                collector.validate_pair(a, b, 'case', 'fixed')


class SignDetCollectorTest(unittest.TestCase):
    """Exercise the existing collector's complete mixed/fixed paths, without timings."""
    setUp = CollectorTest.setUp
    bind_decision = CollectorTest.bind_decision
    run_collector = CollectorTest.run_collector

    def prepare(self, profile, mode='ok'):
        for name in collector.registration_paths(profile):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('def callback := 1\n')
        subprocess.check_call(['git', 'add', '.'], cwd=self.root, stdout=subprocess.DEVNULL)
        subprocess.check_call(['git', '-c', 'user.name=Control', '-c', 'user.email=control@example.test',
                               'commit', '-qm', 'synthetic sign-determination registrations'], cwd=self.root)
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=self.root, text=True).strip()
        for path in self.sources.values():
            source = json.loads(path.read_text())
            source['head'] = head
            source['sources'].update({name: collector.digest(self.root / name)
                                      for name in collector.registration_paths(profile)})
            path.write_text(json.dumps(source))
        listing = SignDetScopeTest().listing(profile)
        for arm, path in self.binaries.items():
            program = path.read_text()
            start = program.index('    print(')
            end = program.index('\n', start)
            program = program[:start] + '    print(' + repr(listing) + ')' + program[end:]
            fixed = '''
    if sys.argv[2] in FIXED:
        result.update(kind='fixed',hashable=True,hashes_agree=True,observed_hash='same')
        result['config'].update(repeats=1,min_total_seconds=0.1,
                                expected_hash='same' if arm=='candidate' else None)
        result['points']=[{'repeat_index':0,'result_hash':'same','status':'ok',
                           'inner_repeats':1,'total_nanos':100_000_000}]
        if MODE=='kind' and arm=='candidate':result['kind']='parametric'
        if MODE=='error' and arm=='candidate':
            result['points'][0].update(status='error',error='fixed failure')
        if MODE=='hash' and arm=='candidate':result['hashes_agree']=False
'''.replace('FIXED', repr(sorted(collector.timing_fixed(profile)))).replace('MODE', repr(mode))
            program = program.replace('    target.write_text(', fixed + '    target.write_text(')
            path.write_text(program)
        self.bind_decision()
        decision = json.loads(self.decision.read_text())
        decision['profile'] = profile
        self.decision.write_text(json.dumps(decision))

    def test_complete_primary_mixed_blocks_and_fixed_options(self):
        self.prepare('sign-det')
        code, _ = self.run_collector(extra=['--profile', 'sign-det'])
        self.assertEqual(code, 0)
        self.assertEqual(self.context['outcome'], 'pass')
        self.assertEqual(len(self.context['guards']), 31)
        runs = [r['command'] for r in self.context['commands'] if r['command'][1:2] == ['run']]
        self.assertEqual(len(runs), 31 * 4 * 2)
        for command in runs:
            self.assertEqual('--outer-trials' in command, command[2] in collector.SIGN_DET_PARAMETRIC)
        for pair in range(0, len(runs), 2):
            block = pair // (31 * 2)
            self.assertEqual([Path(c[0]).name for c in runs[pair:pair+2]],
                             ['baseline', 'candidate'] if block % 2 == 0 else ['candidate', 'baseline'])
        for record in self.context['commands']:
            command = record['command']
            if command[1:2] == ['verify']:
                self.assertEqual(len(command[2:]), 34)
                self.assertEqual(len(set(command[2:])), 34)
        self.assertEqual(set(self.context['excluded_registrations']), collector.SIGN_DET_REFERENCES)

    def resolution_execution(self, honor=True):
        """Stub only admission here; ResolutionProtocolTest checks the real archive."""
        self.prepare('sign-det')
        if honor:
            for binary in self.binaries.values():
                binary.write_text(binary.read_text().replace('    target.write_text(',
                    "    if '--target-inner-nanos' in sys.argv:\n"
                    "        requested=int(sys.argv[sys.argv.index('--target-inner-nanos')+1])\n"
                    "        cap=60 if sys.argv[2].endswith(('runSmallFull','runSmallReduced')) else 10\n"
                    "        floor=50_000_000+(int(target.name.split('-')[0])+(arm=='candidate'))*10_000_000\n"
                    "        result['config']['target_inner_nanos']=min(requested,(cap*1_000_000_000+100_000_000-floor)//4)\n"
                    '    target.write_text('))
        self.bind_decision()
        decision = json.loads(self.decision.read_text())
        decision['profile'] = 'sign-det'
        self.decision.write_text(json.dumps(decision))
        previous = self.base / 'original'
        previous.mkdir()
        (previous / 'decision.json').write_bytes(self.decision.read_bytes())
        (previous / 'context.json').write_text(json.dumps({'decision_sha256': collector.digest(self.decision)}))
        decision.update(tooling_root_head=json.loads(self.sources['candidate'].read_text())['head'],
                        resolution_protocol={'target_inner_nanos': 2_250_000_000})
        self.decision.write_text(json.dumps(decision))
        return previous

    def test_resolution_target_applies_only_to_filtered_workloads(self):
        previous = self.resolution_execution()
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}):
            code, _ = self.run_collector(extra=['--profile', 'sign-det', '--resolution-from', previous])
        self.assertEqual(code, 0)
        runs = [record['command'] for record in self.context['commands'] if record['command'][1:2] == ['run']]
        self.assertEqual(len(runs), 31 * 4 * 2)
        for command in runs:
            self.assertEqual('--target-inner-nanos' in command, command[2] in collector.SIGN_DET_RESOLUTION)
            if '--target-inner-nanos' in command:
                self.assertEqual(command[command.index('--target-inner-nanos') + 1], '2250000000')
        self.assertTrue(self.context['decision_reservation'].endswith('-resolution.json'))
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}), \
             self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('renamed', ['--profile', 'sign-det', '--resolution-from', previous])

    def test_ignored_target_fails_and_consumes_the_resolution_slot(self):
        previous = self.resolution_execution(honor=False)
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}), \
             self.assertRaisesRegex(RuntimeError, 'exported inner-work target'):
            self.run_collector(extra=['--profile', 'sign-det', '--resolution-from', previous])
        self.assertTrue(self.context['attempt_reserved'])
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}), \
             self.assertRaisesRegex(RuntimeError, 'decision already used'):
            self.run_collector('again', ['--profile', 'sign-det', '--resolution-from', previous])

    def test_pinned_runner_clamp_would_be_detected_even_if_admission_were_bypassed(self):
        previous = self.resolution_execution()
        decision = json.loads(self.decision.read_text())
        decision['resolution_protocol']['target_inner_nanos'] = 4_000_000_000
        self.decision.write_text(json.dumps(decision))
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}), \
             self.assertRaisesRegex(RuntimeError, 'including runner clamp'):
            self.run_collector(extra=['--profile', 'sign-det', '--resolution-from', previous])

    def test_resolution_preflight_does_not_lease_or_reserve(self):
        previous = self.resolution_execution()
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}):
            self.assertEqual(self.run_collector(extra=[
                '--profile', 'sign-det', '--resolution-from', previous, '--preflight'])[0], 0)
        self.assertEqual(self.lease_calls, 0)
        self.assertFalse(self.context['attempt_reserved'])
        self.assertFalse(Path(self.context['decision_reservation']).exists())

    def test_resolution_rerun_requires_completed_inconclusive_and_is_available_only_once(self):
        self.guard.write_text(self.guard.read_text().replace('sys.exit(0)', 'sys.exit(2)'))
        previous = self.resolution_execution()
        with patch.object(collector, 'validate_resolution_protocol', return_value={'synthetic': True}):
            _, adapted = self.run_collector(extra=['--profile', 'sign-det', '--resolution-from', previous])
            with self.assertRaisesRegex(RuntimeError, 'completed inconclusive'):
                self.run_collector('invalid-original-rerun', [
                    '--profile', 'sign-det', '--resolution-from', previous, '--rerun-of', previous])
            self.run_collector('rerun', [
                '--profile', 'sign-det', '--resolution-from', previous, '--rerun-of', adapted])
            self.assertEqual(self.context['reruns'], 1)
            self.assertTrue(self.context['rerun_reservation'].endswith('-resolution-rerun.json'))
            with self.assertRaisesRegex(RuntimeError, 'already reserved'):
                self.run_collector('another', [
                    '--profile', 'sign-det', '--resolution-from', previous, '--rerun-of', adapted])

    def test_complete_interacting_fixed_blocks(self):
        self.prepare('sign-det-interacting')
        code, _ = self.run_collector(extra=['--profile', 'sign-det-interacting'])
        self.assertEqual(code, 0)
        self.assertEqual(len(self.context['guards']), 2)
        self.assertEqual(self.context['outcome'], 'pass')
        runs = [r['command'] for r in self.context['commands'] if r['command'][1:2] == ['run']]
        self.assertEqual(len(runs), 16)
        self.assertTrue(all('--outer-trials' not in c for c in runs))

    def test_fixed_preflight_without_measurements(self):
        self.prepare('sign-det-interacting')
        code, _ = self.run_collector(extra=['--profile', 'sign-det-interacting', '--preflight'])
        self.assertEqual(code, 0)
        self.assertFalse(self.context['measurements_collected'])
        self.assertFalse(self.context['attempt_reserved'])
        self.assertEqual(self.lease_calls, 0)

    def test_wrong_profile_refused_before_reservation(self):
        self.prepare('sign-det-interacting')
        with self.assertRaisesRegex(RuntimeError, 'profile differs'):
            self.run_collector(extra=['--profile', 'sign-det'])
        self.assertFalse(self.context['attempt_reserved'])

    def test_non_sturm_cap_adaptation_is_refused(self):
        with redirect_stdout(io.StringIO()), patch('sys.stderr', new=io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                collector.main(['--profile', 'sign-det-interacting', '--cap-from', 'old',
                                '--root', str(self.root), '--guard', str(self.guard),
                                '--decision', str(self.decision), '--output', str(self.base / 'unused'),
                                '--baseline', str(self.binaries['baseline']),
                                '--candidate', str(self.binaries['candidate']),
                                '--baseline-source', str(self.sources['baseline']),
                                '--candidate-source', str(self.sources['candidate'])])
        self.assertEqual(error.exception.code, 2)
        self.assertFalse((self.base / 'unused').exists())

    def test_changed_helper_source_refused_before_reservation(self):
        self.prepare('sign-det')
        path = 'bench/HexSignDet/Phases.lean'
        (self.root / path).write_text('def callback := 2\n')
        subprocess.check_call(['git', 'add', path], cwd=self.root, stdout=subprocess.DEVNULL)
        subprocess.check_call(['git', '-c', 'user.name=Control', '-c', 'user.email=control@example.test',
                               'commit', '-qm', 'changed timed work'], cwd=self.root)
        candidate = json.loads(self.sources['candidate'].read_text())
        candidate['head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=self.root, text=True).strip()
        candidate['sources'][path] = collector.digest(self.root / path)
        self.sources['candidate'].write_text(json.dumps(candidate))
        self.bind_decision()
        decision = json.loads(self.decision.read_text())
        decision['profile'] = 'sign-det'
        self.decision.write_text(json.dumps(decision))
        with self.assertRaisesRegex(RuntimeError, 'registration inputs/configuration changed'):
            self.run_collector(extra=['--profile', 'sign-det'])
        self.assertFalse(self.context['attempt_reserved'])
        self.assertFalse(self.context['measurements_collected'])

    def test_wrong_fixed_kind_retains_consumed_failure(self):
        self.prepare('sign-det-interacting', mode='kind')
        with self.assertRaisesRegex(RuntimeError, 'invalid parent result'):
            self.run_collector(extra=['--profile', 'sign-det-interacting'])
        self.assertEqual(self.context['status'], 'failed')
        self.assertTrue(self.context['measurements_collected'])
        self.assertTrue(self.context['attempt_reserved'])

    def test_failed_fixed_repeat_keeps_index(self):
        self.prepare('sign-det-interacting', mode='error')
        with self.assertRaisesRegex(RuntimeError, 'incomplete/failed parent measurement'):
            self.run_collector(extra=['--profile', 'sign-det-interacting'])
        point = self.context['parent_failures'][1]['points'][0]
        self.assertEqual(point['repeat_index'], 0)
        self.assertEqual(point['error'], 'fixed failure')
        self.assertNotIn('param', point)
        self.assertTrue(self.context['attempt_reserved'])

    def test_failed_fixed_hash_keeps_arm_status(self):
        self.prepare('sign-det-interacting', mode='hash')
        with self.assertRaisesRegex(RuntimeError, 'fixed result hash mismatch'):
            self.run_collector(extra=['--profile', 'sign-det-interacting'])
        self.assertFalse(self.context['parent_failures'][1]['hashes_agree'])
        self.assertTrue(self.context['attempt_reserved'])


class RuntimeSetupTest(unittest.TestCase):
    def test_ignored_hangup_is_preserved(self):
        def disposition(sig):
            return collector.signal.SIG_IGN if sig == collector.signal.SIGHUP else collector.signal.SIG_DFL
        with patch.object(collector.signal, 'getsignal', side_effect=disposition), \
             patch.object(collector.signal, 'signal') as install:
            collector.install_signals()
        self.assertEqual([call.args[0] for call in install.call_args_list], [collector.signal.SIGTERM])

    def test_installed_handlers_raise_interruption(self):
        with patch.object(collector.signal, 'getsignal', return_value=collector.signal.SIG_DFL), \
             patch.object(collector.signal, 'signal') as install:
            collector.install_signals()
        for call in install.call_args_list:
            with self.assertRaises(KeyboardInterrupt):
                call.args[1](call.args[0], None)


if __name__ == "__main__":
    unittest.main()
