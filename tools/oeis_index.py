"""Build an atomic, reproducible OEIS search index from a committed local mirror.

No fetching or source edits. The large index stays under ignored data/external/.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tarfile
import tempfile
import time

from oeis_source import SEARCH_FIELDS, parse_record, term_key

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from research.repository import query as git_query, query_command, query_environment
DEFAULT_DB = ROOT / 'data/external/oeis/catalog.sqlite3'
DEFAULT_MIRROR = ROOT.parent / 'oeisdata'
SCHEMA = 1
LICENSE = {'owner': 'OEIS Foundation, Inc.', 'license': 'CC BY-SA 4.0',
           'url': 'https://oeis.org/wiki/Legal_Documents'}


def revision(mirror: Path, ref: str = 'HEAD') -> str:
    return git_query(mirror, 'rev-parse', '--verify', '--end-of-options', ref + '^{commit}',
                     text=True, timeout=15, check=True).stdout.strip()


def records(mirror: Path, commit: str):
    """Stream Git's immutable tree without extracting hundreds of thousands of files."""
    with subprocess.Popen(query_command(mirror, 'archive', '--format=tar', commit, 'seq'),
                          env=query_environment(mirror), stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
        try:
            with tarfile.open(fileobj=process.stdout, mode='r|') as archive:
                for member in archive:
                    if member.isfile() and member.name.endswith('.seq'):
                        stream = archive.extractfile(member)
                        yield Path(member.name).stem, stream.read().decode('utf-8')
            if process.wait() != 0:
                raise RuntimeError(process.stderr.read().decode('utf-8', errors='replace'))
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()


def create_database(destination: Path, entries, metadata: dict, progress=None) -> dict:
    """Publish only a complete validated database; preserve the previous one on failure."""
    destination = destination.resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    handle, filename = tempfile.mkstemp(prefix=destination.name + '.', suffix='.building',
                                        dir=destination.parent)
    os.close(handle)
    staging = Path(filename)
    count = term_count = issues_count = 0
    issue_examples = []
    digest = hashlib.sha256()
    connection = None
    started = time.monotonic()
    try:
        connection = sqlite3.connect(staging)
        connection.executescript('''
            PRAGMA journal_mode=OFF;
            PRAGMA synchronous=OFF;
            PRAGMA temp_store=MEMORY;
            PRAGMA cache_size=-131072;
            CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
            CREATE TABLE entries (
                id INTEGER PRIMARY KEY, aid TEXT UNIQUE NOT NULL, name TEXT NOT NULL,
                first_index INTEGER, offset_raw TEXT, keywords TEXT, revision TEXT,
                terms TEXT, term_count INTEGER, fields TEXT, sha256 TEXT, issues TEXT);
            CREATE TABLE refs (source TEXT, target TEXT, field TEXT,
                               PRIMARY KEY(source,target,field)) WITHOUT ROWID;
        ''')
        connection.execute('CREATE VIRTUAL TABLE text_search USING fts5(' +
                           ','.join(SEARCH_FIELDS) + ", content='', tokenize='unicode61 remove_diacritics 2')")
        connection.execute("CREATE VIRTUAL TABLE term_search USING fts5(tokens, content='')")
        for identifier, text in entries:
            record = parse_record(identifier, text)
            number = int(identifier[1:])
            terms = record['terms']
            connection.execute('INSERT INTO entries VALUES (?,?,?,?,?,?,?,?,?,?,?,?)', (
                number, identifier, record['name'], record['first_index'], record['offset_raw'],
                record['keywords'], record['revision'], ','.join(terms), len(terms),
                json.dumps(record['fields'], ensure_ascii=False), record['sha256'],
                json.dumps(record['issues'], ensure_ascii=False)))
            connection.execute('INSERT INTO text_search(rowid,' + ','.join('"' + f + '"' for f in SEARCH_FIELDS) +
                               ') VALUES (?,' + ','.join('?' for _ in SEARCH_FIELDS) + ')',
                (number, *[record['searchable'][f] for f in SEARCH_FIELDS]))
            if terms:
                connection.execute('INSERT INTO term_search(rowid,tokens) VALUES (?,?)',
                                   (number, ' '.join(map(term_key, terms))))
            connection.executemany('INSERT INTO refs VALUES (?,?,?)',
                [(identifier, target, field) for target, field in record['references']])
            digest.update(identifier.encode() + bytes.fromhex(record['sha256']))
            count += 1
            term_count += len(terms)
            if record['issues']:
                issues_count += 1
                if len(issue_examples) < 20:
                    issue_examples.append({'aid': identifier, 'issues': record['issues']})
            if count % 10000 == 0:
                connection.commit()
                if progress:
                    progress(count, time.monotonic() - started)
        if not count:
            raise ValueError('The mirror contains no sequence records; old index preserved')
        connection.execute('CREATE INDEX refs_target ON refs(target,source,field)')
        for table in ('text_search', 'term_search'):
            connection.execute(f"INSERT INTO {table}({table}) VALUES ('optimize')")
            connection.execute(f"INSERT INTO {table}({table}) VALUES ('integrity-check')")
        info = dict(metadata, schema=SCHEMA, records=count, stored_terms=term_count,
                    records_with_parse_issues=issues_count, parse_issue_examples=issue_examples,
                    content_sha256=digest.hexdigest(), attribution=LICENSE,
                    built_at=datetime.now(timezone.utc).isoformat(),
                    snapshot_basis='committed OEIS .seq records; supplementary files are not indexed')
        connection.executemany('INSERT INTO meta VALUES (?,?)',
                               [(key, json.dumps(value, ensure_ascii=False)) for key, value in info.items()])
        connection.commit()
        if connection.execute('PRAGMA quick_check').fetchone()[0] != 'ok':
            raise RuntimeError('SQLite integrity check failed; previous index preserved')
        connection.close()
        connection = None
        os.replace(staging, destination)
        return info
    finally:
        if connection is not None:
            connection.close()
        staging.unlink(missing_ok=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mirror', type=Path, default=os.environ.get('OEIS_MIRROR', DEFAULT_MIRROR))
    parser.add_argument('--database', type=Path, default=os.environ.get('OEIS_DATABASE', DEFAULT_DB))
    parser.add_argument('--revision', default='HEAD')
    args = parser.parse_args(argv)
    commit = revision(args.mirror, args.revision)
    exported = git_query(args.mirror, 'show', commit + ':time.txt', text=True, check=True).stdout.strip()
    result = create_database(args.database, records(args.mirror, commit), {
        'mirror': str(args.mirror.resolve()), 'revision': commit, 'exported_at': exported,
        'upstream': 'https://github.com/oeis/oeisdata'},
        progress=lambda count, seconds: print(f'{count:,} records indexed in {seconds:.1f}s',
                                             file=sys.stderr, flush=True))
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
