"""Prevent a pytest process from modifying canonical research outputs."""
from __future__ import annotations

import os
from pathlib import Path
import sys
from urllib.parse import parse_qs, urlsplit
from urllib.request import url2pathname


def install(root: Path) -> None:
    """Protect records for this process; subprocesses need their own guard.

    Audit hooks cover pathlib, builtins.open and os.open, including writes that
    reproduce identical bytes. This is an accidental-write check, not a sandbox.
    """
    protected = tuple((root / name).resolve() for name in (
        'docs/research', 'data/research/juggler', 'data/research/collatz',
    ))

    def check(path: object) -> None:
        if not isinstance(path, (str, bytes, os.PathLike)):
            return
        target = Path(os.fsdecode(path)).resolve()
        if any(target.is_relative_to(parent) for parent in protected):
            raise RuntimeError(
                f'Tests must not modify research records: {target}. '
                'Pass output_root=tmp_path to the artifact writer.'
            )

    def audit(event: str, args: tuple) -> None:
        if event == 'open':
            path, mode, flags = args
            if (mode and any(c in mode for c in 'wax+')) or (
                flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
            ):
                check(path)
        elif event in {'os.remove', 'os.rmdir', 'os.mkdir', 'os.chmod', 'os.utime'}:
            check(args[0])
        elif event in {'os.rename', 'os.link'}:
            check(args[0])
            check(args[1])
        elif event == 'os.symlink':
            check(args[1])
        elif event == 'sqlite3.connect':
            path = args[0]
            if isinstance(path, str) and path.startswith('file:'):
                uri = urlsplit(path)
                if parse_qs(uri.query).get('mode') == ['ro']:
                    return
                path = url2pathname(('//' + uri.netloc if uri.netloc else '') + uri.path)
            check(path)

    sys.addaudithook(audit)
