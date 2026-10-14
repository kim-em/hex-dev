#!/usr/bin/env python3
"""Check the declared comparison scope without taking performance samples."""
from copy import deepcopy
from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest
from unittest.mock import patch

import sturm_regression as collector
from sturm_regression import AUXILIARY, NATIVE_FIXED, native_harness_pins, registrations


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
import json,sys
from pathlib import Path
arm=ARM
mode=MODE
if sys.argv[1]=='list':
    print(LISTING)
elif sys.argv[1]=='run':
    target=Path(sys.argv[sys.argv.index('--export-file')+1])
    result={'kind':'parametric','function':sys.argv[2],'config':{},'budget_truncated':False,
            'points':[{'param':64,'result_hash':'wrong' if mode=='mismatch' and arm=='candidate' else 'same',
                       'status':'timedOut' if mode in ('timeout','exit') and arm=='candidate' else 'ok',
                       'per_call_nanos':100,'error':None}]}
    target.write_text(json.dumps({'results':[result]}))
    if mode=='exit' and arm=='candidate':sys.exit(7)
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
                  for path in self.root.rglob('*') if path.is_file() and '.git' not in path.parts}
        self.sources = {}
        for arm, binary in self.binaries.items():
            source = self.base / (arm + "-source.json")
            source.write_text(json.dumps({"status": [], "head": head,
                                         "binary_sha256": collector.digest(binary), "sources": hashes}))
            self.sources[arm] = source
        self.decision = self.base / "decision.json"
        self.lease_exception = None
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

    def run_collector(self, name='capture', extra=()):
        output = self.base / name
        args = [str(x) for pair in (
            ('--root', self.root), ('--guard', self.guard), ('--decision', self.decision),
            ('--output', output), *[("--" + arm, path) for arm, path in self.binaries.items()],
            *[("--" + arm + '-source', path) for arm, path in self.sources.items()]) for x in pair]
        with patch.object(collector, 'cpu_lease', return_value=(0, io.StringIO()), side_effect=self.lease_exception) as lease, \
             patch.object(collector.os, 'sched_setaffinity'), \
             patch.dict(collector.os.environ, {'XDG_STATE_HOME': str(self.base / 'state')}), \
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

    def mode(self, value):
        path = self.binaries['candidate']
        path.write_text(path.read_text().replace("mode='ok'", 'mode=' + repr(value)))
        self.bind_decision()

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

    def test_interruption_consumes_reserved_first_attempt(self):
        original = collector.subprocess.run
        def interrupt(command, *args, **kwargs):
            if command[0] == str(self.binaries['candidate']) and command[1] == 'run':
                raise KeyboardInterrupt()
            return original(command, *args, **kwargs)
        with patch.object(collector.subprocess, 'run', side_effect=interrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.run_collector()
        self.assertEqual(self.context['status'], 'interrupted')
        self.assertTrue(self.context['attempt_reserved'])
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

    def test_empty_and_relative_state_paths_use_home(self):
        for value in ('', 'relative'):
            with patch.dict(collector.os.environ, {'XDG_STATE_HOME': value}):
                self.assertEqual(collector.state_directory(), Path.home() / '.local/state')


if __name__ == "__main__":
    unittest.main()
