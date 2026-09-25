"""Exclusive process locks for expensive or single-writer laboratory steps.

The operating system holds the lock on an open file, so a crashed or killed holder
releases it without cleanup. A holder record beside it names the process (PID, start
time, checkout, purpose) so waiters can say whom they wait on; a record left by a
holder that died is reported as recovered when the next caller acquires the lock.
"""
from __future__ import annotations

from contextlib import contextmanager
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import uuid

#: One Lean build or semantic export per machine: each export loads the whole library
#: into a single lean.exe of about 5 GB, and concurrent ones stall every session.
BUILD_LOCK_ENV = 'BTLAB_LEAN_BUILD_LOCK'


def build_lock_path() -> Path:
    override = os.environ.get(BUILD_LOCK_ENV)
    return Path(override) if override else Path(tempfile.gettempdir()) / 'btlab' / 'lean-build.lock'


class LockBusy(RuntimeError):
    def __init__(self, path: Path, holder: dict | None):
        self.path, self.holder = path, holder
        super().__init__(f'{path} is held by {describe(holder)}')


def holder_path(path: Path) -> Path:
    return path.with_name(path.name + '.holder.json')


def read_holder(path: Path) -> dict | None:
    try:
        value = json.loads(holder_path(path).read_text(encoding='utf-8'))
        return value if isinstance(value, dict) else None
    except (OSError, ValueError):
        return None


def describe(holder: dict | None) -> str:
    if not holder:
        return 'an unidentified process'
    return (f"PID {holder.get('pid')} since {holder.get('started_utc')} "
            f"({holder.get('purpose')} in {holder.get('root')})")


def _try_lock(stream) -> bool:
    if os.name == 'nt':
        import msvcrt
        stream.seek(0)
        try:
            msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            return True
        except OSError:
            return False
    import fcntl
    try:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        return True
    except OSError:
        return False


def _unlock(stream):
    if os.name == 'nt':
        import msvcrt
        stream.seek(0)
        msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
    else:
        import fcntl
        fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


@contextmanager
def exclusive(path: Path, *, purpose: str, root: Path | str = '', wait: bool = True,
              timeout: float | None = None, poll: float = 2.0, notice: float = 60.0, out=None):
    """Hold `path` exclusively. Without `wait`, or after `timeout` seconds, raise LockBusy.

    Yields a report with the holder record written for this process and, when a previous
    record named a process that no longer held the lock, that stale record.
    """
    out = sys.stderr if out is None else out
    path.parent.mkdir(parents=True, exist_ok=True)
    stream = path.open('a+b')
    try:
        if stream.seek(0, os.SEEK_END) == 0:
            # Windows locks byte ranges; give the range a byte to cover.
            stream.write(b'\0')
            stream.flush()
        started, last = time.monotonic(), None
        while not _try_lock(stream):
            holder = read_holder(path)
            if not wait or (timeout is not None and time.monotonic() - started >= timeout):
                raise LockBusy(path, holder)
            if last is None or time.monotonic() - last >= notice:
                print(f'Waiting for {path}: held by {describe(holder)}', file=out, flush=True)
                last = time.monotonic()
            time.sleep(poll)
        try:
            previous = read_holder(path)
            record = {'pid': os.getpid(), 'started_utc': datetime.now(timezone.utc).isoformat(),
                      'purpose': purpose, 'root': str(root), 'token': uuid.uuid4().hex}
            temporary = path.with_name(f'{path.name}.{record["token"]}.tmp')
            temporary.write_text(json.dumps(record), encoding='utf-8', newline='\n')
            temporary.replace(holder_path(path))
            report = {'lock': str(path), 'holder': record,
                      'waited_seconds': round(time.monotonic() - started, 1)}
            if previous:
                # This process holds the OS lock, so whoever wrote that record no longer does.
                report['recovered_stale_holder'] = previous
                print(f'Recovered {path} from {describe(previous)}, which no longer holds it',
                      file=out, flush=True)
            try:
                yield report
            finally:
                if (read_holder(path) or {}).get('token') == record['token']:
                    holder_path(path).unlink(missing_ok=True)
        finally:
            _unlock(stream)
    finally:
        stream.close()
