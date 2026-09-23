"""Writing reports must exercise disposable files, preserving curated evidence."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sqlite3
import sys

import pytest

from research.experiments.outputs import artifact_path
from research.juggler_sequence import twin_flight
from research.juggler_sequence.atlas.storage import connect, sqlite_path

ROOT = Path(__file__).resolve().parents[2]


def test_explicit_output_layout_and_unchanged_defaults(tmp_path):
    canonical = ROOT / 'docs/research/juggler_twin_flight.json'
    assert artifact_path(canonical) == canonical
    assert artifact_path(canonical, tmp_path) == tmp_path / 'docs/research/juggler_twin_flight.json'
    with pytest.raises(ValueError):
        artifact_path(ROOT.parent / 'outside.json', tmp_path)


def test_writing_same_payload_to_two_roots_is_independent(tmp_path):
    payload = twin_flight.probe_payload()
    original = twin_flight.JSON_PATH
    roots = [tmp_path / 'one', tmp_path / 'two']
    for root in roots:
        assert twin_flight.write_artifacts(payload, output_root=root) is payload
        report = root / 'docs/research/juggler_twin_flight.json'
        summary = root / 'data/research/juggler/twin_flight/summary.json'
        assert json.loads(report.read_text(encoding='utf-8')) == payload
        assert json.loads(summary.read_text(encoding='utf-8'))['classification'] == payload['decision']['classification']
    assert twin_flight.JSON_PATH == original
    assert (roots[0] / 'docs/research/juggler_twin_flight.md').read_bytes() == (
        roots[1] / 'docs/research/juggler_twin_flight.md').read_bytes()


def test_audit_guard_blocks_real_writes_and_allows_reads(tmp_path):
    # Install in a child process: audit hooks cannot be removed.
    record = tmp_path / 'docs/research/record.json'
    record.parent.mkdir(parents=True)
    record.write_text('curated', encoding='utf-8')
    script = '''
import os
import sqlite3
from pathlib import Path
import sys
from test_output_guard import install
root = Path(sys.argv[1])
path = root / 'docs/research/record.json'
install(root)
assert path.read_text() == 'curated'
operations = [
    lambda: path.write_text('curated'),
    lambda: open(path, 'wb'),
    lambda: os.open(path, os.O_WRONLY),
    lambda: path.unlink(),
    lambda: path.rename(root / 'moved.json'),
    lambda: (root / 'docs/research/new').mkdir(),
    lambda: sqlite3.connect(path),
    lambda: sqlite3.connect(path.as_uri() + '?mode=rw', uri=True),
]
for operation in operations:
    try:
        operation()
    except RuntimeError as exc:
        assert 'output_root=tmp_path' in str(exc)
    else:
        raise AssertionError('unguarded write')
(root / 'disposable.json').write_text('allowed')
assert path.read_text() == 'curated'
'''
    result = subprocess.run([sys.executable, '-c', script, str(tmp_path)], cwd=ROOT / 'tools',
                            text=True, capture_output=True)
    assert result.returncode == 0, result.stderr


def test_atlas_reads_do_not_create_initialize_or_write(tmp_path):
    missing = tmp_path / 'missing'
    with pytest.raises(sqlite3.OperationalError):
        connect(missing, read_only=True)
    assert not missing.exists()

    path = sqlite_path(tmp_path)
    con = sqlite3.connect(path)
    con.execute('CREATE TABLE sentinel (value TEXT)')
    con.execute("INSERT INTO sentinel VALUES ('curated')")
    con.commit()
    con.close()
    before = path.read_bytes()
    con = connect(tmp_path, read_only=True)
    try:
        assert con.execute('SELECT value FROM sentinel').fetchone()[0] == 'curated'
        with pytest.raises(sqlite3.OperationalError, match='readonly'):
            con.execute("INSERT INTO sentinel VALUES ('changed')")
        assert [r[0] for r in con.execute("SELECT name FROM sqlite_master WHERE type='table'")] == ['sentinel']
    finally:
        con.close()
    assert path.read_bytes() == before
