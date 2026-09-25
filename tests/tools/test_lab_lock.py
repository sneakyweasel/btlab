"""At most one holder at a time; a dead holder's lock is recovered, never waited on forever."""
import io
import os
import signal
from pathlib import Path
import subprocess
import sys

import pytest

TOOLS = Path(__file__).resolve().parents[2] / 'tools'
sys.path.insert(0, str(TOOLS))
import lab_lock

HOLD = ('import sys, time; sys.path.insert(0, sys.argv[2]); import lab_lock; from pathlib import Path\n'
        'with lab_lock.exclusive(Path(sys.argv[1]), purpose="test holder", root="fixture"):\n'
        '    print("held", flush=True); time.sleep(120)\n')


def test_a_second_holder_is_blocked_and_told_whom_it_waits_on(tmp_path):
    lock = tmp_path / 'build.lock'
    with lab_lock.exclusive(lock, purpose='first build', root=tmp_path) as held:
        assert held['holder']['pid'] == os.getpid()
        with pytest.raises(lab_lock.LockBusy) as busy:
            with lab_lock.exclusive(lock, purpose='second build', wait=False):
                pass
        assert busy.value.holder['purpose'] == 'first build'
        out = io.StringIO()
        with pytest.raises(lab_lock.LockBusy):
            with lab_lock.exclusive(lock, purpose='second build', timeout=0.3, poll=0.05, out=out):
                pass
        assert f'held by PID {os.getpid()}' in out.getvalue()
    with lab_lock.exclusive(lock, purpose='second build', wait=False) as later:
        assert 'recovered_stale_holder' not in later
    assert lab_lock.read_holder(lock) is None


def test_a_killed_holder_is_recovered(tmp_path):
    lock = tmp_path / 'build.lock'
    child = subprocess.Popen([sys.executable, '-c', HOLD, str(lock), str(TOOLS)],
                             stdout=subprocess.PIPE, text=True)
    try:
        assert child.stdout.readline().strip() == 'held'
        with pytest.raises(lab_lock.LockBusy) as busy:
            with lab_lock.exclusive(lock, purpose='waiting build', wait=False):
                pass
        holder = busy.value.holder
        assert holder['purpose'] == 'test holder'
        # A Windows venv python.exe is a launcher; the record names the interpreter itself.
        os.kill(holder['pid'], signal.SIGTERM)
        child.wait(timeout=30)
    finally:
        child.kill()
        child.wait()
        child.stdout.close()
    # The record still names the dead process; the operating system released its lock.
    assert lab_lock.read_holder(lock)['pid'] == holder['pid']
    with lab_lock.exclusive(lock, purpose='next build', timeout=10, poll=0.05, out=io.StringIO()) as held:
        assert held['recovered_stale_holder']['pid'] == holder['pid']
        assert lab_lock.read_holder(lock)['purpose'] == 'next build'


def test_a_stale_record_with_a_dead_pid_does_not_block(tmp_path):
    lock = tmp_path / 'build.lock'
    dead = subprocess.run([sys.executable, '-c', 'import os; print(os.getpid())'],
                          capture_output=True, text=True, check=True)
    pid = int(dead.stdout.split()[-1])
    lock.write_bytes(b'\0')
    lab_lock.holder_path(lock).write_text(f'{{"pid": {pid}, "purpose": "crashed build"}}', encoding='utf-8')
    with lab_lock.exclusive(lock, purpose='next build', wait=False, out=io.StringIO()) as held:
        assert held['recovered_stale_holder']['pid'] == pid


def test_the_build_lock_is_machine_wide_unless_overridden(tmp_path, monkeypatch):
    monkeypatch.delenv(lab_lock.BUILD_LOCK_ENV, raising=False)
    assert not lab_lock.build_lock_path().is_relative_to(TOOLS.parent)
    monkeypatch.setenv(lab_lock.BUILD_LOCK_ENV, str(tmp_path / 'x.lock'))
    assert lab_lock.build_lock_path() == tmp_path / 'x.lock'
