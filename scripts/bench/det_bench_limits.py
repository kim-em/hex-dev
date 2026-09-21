"""Resource admission for the manual determinant proof sweep (no timing claims)."""
from __future__ import annotations
import fcntl
import json
import os
from pathlib import Path
import signal
import sys
import time

STAGE_SECONDS = {'classify': 600, 'forced': 1200, 'dispatch': 1800}
WORKFLOW_SECONDS = 3600


def dominates(case, smaller):
    """Coordinatewise growth within one mathematical family and carrier.

    This is a scheduling policy, not a claim that runtimes are monotone.
    Incomparable dimension/degree/support combinations remain independent.
    """
    if any(case.get(k) != smaller.get(k) for k in ('family', 'carrier', 'modulus', 'missing', 'scope_probe')):
        return False
    coordinates = ('dimension', 'atoms', 'degree', 'support')
    return all(case.get(k, 0) >= smaller.get(k, 0) for k in coordinates)


class TimeoutFrontier:
    def __init__(self):
        self.failures = []

    def observe(self, case, arm, state):
        if state == 'timeout':
            self.failures.append(dict(case=dict(case), arm=arm))

    def blocker(self, case, arm):
        return next((dict(state='skipped-timeout', blocked_by=f['case']['stem'],
                          blocked_arm=arm)
                     for f in self.failures if f['arm'] == arm and dominates(case, f['case'])), None)


def reserve(path, stage):
    """Reserve before launching, so interrupted/repeated invocations cannot reset the cap."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a+') as file:
        fcntl.flock(file, fcntl.LOCK_EX)
        file.seek(0)
        text = file.read()
        ledger = json.loads(text) if text else dict(limit_seconds=WORKFLOW_SECONDS, stages={})
        if stage in ledger['stages']:
            raise ValueError(f'{stage} already attempted in {path}; refusing an implicit rerun')
        seconds = STAGE_SECONDS[stage]
        if sum(s['reserved_seconds'] for s in ledger['stages'].values()) + seconds > WORKFLOW_SECONDS:
            raise ValueError('one-hour determinant workflow budget exhausted')
        ledger['stages'][stage] = dict(reserved_seconds=seconds, started_unix=time.time())
        file.seek(0); file.truncate(); json.dump(ledger, file, indent=2); file.flush(); os.fsync(file.fileno())
    return seconds


def stop_tree(root):
    """Stop owned descendants even when a timed build starts a new session."""
    owned = {root}
    while True:
        for pid in owned:
            try:
                os.kill(pid, signal.SIGSTOP)
            except ProcessLookupError:
                pass
        more = set()
        for path in Path('/proc').iterdir():
            if not path.name.isdigit():
                continue
            try:
                parent = int((path / 'stat').read_text().rsplit(')', 1)[1].split()[1])
                if parent in owned:
                    more.add(int(path.name))
            except (OSError, ValueError):
                pass
        if more <= owned:
            break
        owned |= more
    for pid in owned:
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def supervise(action, seconds, status_path):
    """A bounded local child, with no service or background monitor installation."""
    started = time.monotonic()
    pid = os.fork()
    if pid == 0:
        try:
            action(started + seconds)
        except BaseException:
            import traceback
            traceback.print_exc()
            os._exit(1)
        sys.stdout.flush()
        sys.stderr.flush()
        os._exit(0)
    reason = 'finished'
    def interrupted(_signum, _frame):
        raise KeyboardInterrupt
    old_handlers = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGTERM, signal.SIGINT)}
    try:
        while True:
            finished, status = os.waitpid(pid, os.WNOHANG)
            if finished:
                code = os.waitstatus_to_exitcode(status)
                break
            if time.monotonic() - started >= seconds:
                reason = 'workflow-budget-exhausted'
                stop_tree(pid)
                os.waitpid(pid, 0)
                code = 124
                break
            time.sleep(min(.1, max(.001, seconds - (time.monotonic() - started))))
    except BaseException:
        stop_tree(pid)
        os.waitpid(pid, 0)
        raise
    finally:
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
    status_path.write_text(json.dumps(dict(state=reason, exit_status=code,
        elapsed_seconds=time.monotonic() - started, limit_seconds=seconds), indent=2) + '\n')
    return code
