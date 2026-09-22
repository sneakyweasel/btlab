"""Bounded, read-only OEIS discovery over a local immutable SQLite snapshot."""
from __future__ import annotations

import argparse
import base64
from contextlib import contextmanager
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import time

from oeis_index import DEFAULT_DB, DEFAULT_MIRROR, LICENSE, ROOT, SCHEMA, revision
from oeis_source import FIELDS, SEARCH_FIELDS, aid, integer, term_key

NOTICE = ('Matches concern the terms and text stored in this dated OEIS snapshot. '
          'A finite match does not establish a sequence identity; absence does not establish novelty. '
          'Entry comments are published content, not pending edits or editorial discussions.')


def bounds(limit: int, offset: int, maximum: int = 50):
    if isinstance(limit, bool) or not isinstance(limit, int) or not 1 <= limit <= maximum:
        raise ValueError(f'limit must be an integer between 1 and {maximum}')
    if isinstance(offset, bool) or not isinstance(offset, int) or not 0 <= offset <= 100000:
        raise ValueError('offset must be an integer between 0 and 100000')


def transformed(terms: list[str], transform: str, multiplier: int, addend: int) -> list[str]:
    if not 3 <= len(terms) <= 128 or any(not isinstance(v, str) or len(v) > 1000 for v in terms):
        raise ValueError('Supply 3–128 decimal integer strings, each at most 1000 characters')
    values = [int(integer(v)) for v in terms]
    if transform == 'differences':
        values = [b - a for a, b in zip(values, values[1:])]
    elif transform == 'partial_sums':
        values = list(itertools.accumulate(values))
    elif transform == 'negate':
        values = [-v for v in values]
    elif transform != 'identity':
        raise ValueError('transform must be identity, differences, partial_sums or negate')
    if len(values) < 3:
        raise ValueError('The transformed sequence must contain at least three terms')
    if any(isinstance(v, bool) or not isinstance(v, int) or abs(v) > 1000000
           for v in (multiplier, addend)):
        raise ValueError('multiplier and addend must be integers of absolute value at most 1000000')
    return [str(multiplier * value + addend) for value in values]


def positions(stored: list[str], query: list[str], mode: str) -> list[int] | None:
    if mode == 'prefix':
        return list(range(len(query))) if stored[:len(query)] == query else None
    if mode == 'contiguous':
        for i in range(len(stored) - len(query) + 1):
            if stored[i:i + len(query)] == query:
                return list(range(i, i + len(query)))
        return None
    cursor, found = 0, []
    for value in query:
        try:
            cursor = stored.index(value, cursor)
        except ValueError:
            return None
        found.append(cursor)
        cursor += 1
    return found


class OEIS:
    def __init__(self, database: Path | None = None, mirror: Path | None = None,
                 query_seconds: float = 10):
        self.database = Path(database or os.environ.get('OEIS_DATABASE', DEFAULT_DB)).resolve()
        self.mirror = Path(mirror or os.environ.get('OEIS_MIRROR', DEFAULT_MIRROR)).resolve()
        self.query_seconds = query_seconds

    @contextmanager
    def connect(self):
        if not self.database.is_file():
            raise ValueError('OEIS index is missing. Run python tools/oeis_index.py first.')
        connection = sqlite3.connect(self.database.as_uri() + '?mode=ro', uri=True)
        connection.row_factory = sqlite3.Row
        deadline = time.monotonic() + self.query_seconds
        connection.set_progress_handler(lambda: int(time.monotonic() > deadline), 10000)
        try:
            metadata = {r['key']: json.loads(r['value']) for r in connection.execute('SELECT * FROM meta')}
            if metadata.get('schema') != SCHEMA:
                raise ValueError('OEIS index schema is incompatible; rebuild it with tools/oeis_index.py')
            yield connection, metadata
        except sqlite3.OperationalError as exc:
            if 'interrupt' in str(exc):
                raise ValueError('Query exceeded its time budget; narrow the terms or fields') from exc
            raise ValueError(f'Invalid OEIS query or index: {exc}') from exc
        finally:
            connection.close()

    @staticmethod
    def envelope(metadata: dict) -> dict:
        return {'snapshot': metadata['content_sha256'], 'exported_at': metadata.get('exported_at'),
                'revision': metadata.get('revision'), 'attribution': metadata['attribution'],
                'notice': NOTICE}

    @staticmethod
    def summary(row) -> dict:
        return {key: row[key] for key in ('aid', 'name', 'first_index', 'term_count')} | {
            'entry_revision': row['revision']}

    def get(self, identifier: str, fields: list[str] | None = None, limit: int = 24, offset: int = 0):
        identifier = aid(identifier)
        bounds(limit, offset)
        allowed = set(FIELDS.values()) | {'other'}
        if fields is not None and (not fields or set(fields) - allowed):
            raise ValueError('fields must be chosen from: ' + ', '.join(sorted(allowed)))
        with self.connect() as (db, metadata):
            row = db.execute('SELECT * FROM entries WHERE aid=?', (identifier,)).fetchone()
            result = dict(self.envelope(metadata), status='found' if row else 'not_found', aid=identifier)
            if row is None:
                return result
            selected = [f for f in json.loads(row['fields'])
                        if f['field'] in fields] if fields is not None else [
                            f for f in json.loads(row['fields']) if f['field'] != 'terms']
            chunks = []
            for field in selected:
                count = max(1, (len(field['text']) + 999) // 1000)
                for part in range(count):
                    chunks.append(dict(field, text=field['text'][part * 1000:(part + 1) * 1000],
                                       part=part + 1, parts=count))
            result.update(self.summary(row), offset_raw=row['offset_raw'], keywords=row['keywords'].split(','),
                fields=chunks[offset:offset + limit], total_chunks=len(chunks), offset=offset,
                next_offset=offset + limit if offset + limit < len(chunks) else None,
                record_sha256=row['sha256'], parse_issues=json.loads(row['issues']),
                url=f'https://oeis.org/{identifier}',
                snapshot_url=f"https://github.com/oeis/oeisdata/blob/{metadata.get('revision')}/seq/{identifier[:4]}/{identifier}.seq")
            return result

    def terms(self, identifier: str, start_position: int = 0, limit: int = 50):
        identifier = aid(identifier)
        bounds(limit, start_position, 200)
        with self.connect() as (db, metadata):
            row = db.execute('SELECT * FROM entries WHERE aid=?', (identifier,)).fetchone()
            result = dict(self.envelope(metadata), status='found' if row else 'not_found', aid=identifier)
            if row is None:
                return result
            values = row['terms'].split(',') if row['terms'] else []
            result.update(first_index=row['first_index'], stored_terms=len(values),
                source='published %S/%T/%U fields; b-files are not included',
                parse_issues=json.loads(row['issues']),
                terms=[{'position': i, 'n': row['first_index'] + i if row['first_index'] is not None else None,
                        'value': values[i]} for i in range(start_position, min(len(values), start_position + limit))],
                next_position=start_position + limit if start_position + limit < len(values) else None)
            return result

    def search(self, query: str, fields: list[str] | None = None, keyword: str | None = None,
               syntax: str = 'words', limit: int = 15, offset: int = 0):
        bounds(limit, offset)
        if not query.strip() or len(query) > 1000:
            raise ValueError('Supply a nonempty query of at most 1000 characters')
        if fields is not None and (not fields or set(fields) - set(SEARCH_FIELDS)):
            raise ValueError('Search fields: ' + ', '.join(SEARCH_FIELDS))
        if keyword and not re.fullmatch('[a-z]+', keyword):
            raise ValueError('keyword must be one OEIS keyword, such as nonn or fini')
        if syntax == 'words':
            words = re.findall(r'\w+', query, flags=re.UNICODE)
            if not words:
                raise ValueError('Text search needs words; use match_terms for integer sequences')
            expression = ' AND '.join('"' + word + '"' for word in words)
        elif syntax == 'fts':
            expression = query
        else:
            raise ValueError('syntax must be words or fts')
        if fields:
            expression = '{' + ' '.join(fields) + '} : (' + expression + ')'
        with self.connect() as (db, metadata):
            if re.fullmatch('A[0-9]{6}', query.strip().upper()) and not fields and not keyword:
                exact = db.execute('SELECT * FROM entries WHERE aid=?', (query.strip().upper(),)).fetchone()
                hits = [dict(self.summary(exact), excerpt=exact['name'], matched_field='name')] if exact else []
                return dict(self.envelope(metadata), query=query, total=len(hits), results=hits[offset:offset + limit],
                            offset=offset, next_offset=None)
            where = 'text_search MATCH ?'
            parameters = [expression]
            if keyword:
                where += " AND instr(','||e.keywords||',',?)>0"
                parameters.append(',' + keyword + ',')
            join = ' FROM text_search JOIN entries e ON e.id=text_search.rowid WHERE ' + where
            total = db.execute('SELECT count(*)' + join, parameters).fetchone()[0]
            rows = db.execute('SELECT e.*, bm25(text_search,8,3,3,2,1,1,1,1,1) AS score' + join +
                ' ORDER BY score,e.id LIMIT ? OFFSET ?', (*parameters, limit, offset)).fetchall()
            results = []
            needles = [w.casefold() for w in re.findall(r'\w+', query) if w not in {'AND', 'OR', 'NOT', 'NEAR'}]
            for row in rows:
                choices = [r for r in json.loads(row['fields'])
                           if r['field'] in (fields or SEARCH_FIELDS)]
                best = max(choices, key=lambda r: sum(n in r['text'].casefold() for n in needles),
                           default={'field': 'name', 'text': row['name']})
                at = min((best['text'].casefold().find(n) for n in needles if n in best['text'].casefold()), default=0)
                start = max(0, at - 100)
                results.append(dict(self.summary(row), matched_field=best['field'],
                    excerpt=best['text'][start:start + 500], excerpt_truncated=len(best['text']) > 500,
                    url=f"https://oeis.org/{row['aid']}"))
            return dict(self.envelope(metadata), query=query, total=total, offset=offset, results=results,
                        next_offset=offset + limit if offset + limit < total else None)

    def match_terms(self, terms: list[str], mode: str = 'contiguous', transform: str = 'identity',
                    multiplier: int = 1, addend: int = 0, limit: int = 15, cursor: str | None = None):
        bounds(limit, 0)
        if mode not in {'contiguous', 'prefix', 'subsequence'}:
            raise ValueError('mode must be contiguous, prefix or subsequence')
        query = transformed(terms, transform, multiplier, addend)
        keys = [term_key(value) for value in query]
        expression = (' AND '.join('"' + key + '"' for key in sorted(set(keys))) if mode == 'subsequence'
                      else ('^ ' if mode == 'prefix' else '') + '"' + ' '.join(keys) + '"')
        fingerprint = hashlib.sha256(json.dumps([query, mode]).encode()).hexdigest()[:24]
        after = -1
        with self.connect() as (db, metadata):
            if cursor:
                try:
                    saved = json.loads(base64.urlsafe_b64decode(cursor))
                    if saved['snapshot'] != metadata['content_sha256'] or saved['query'] != fingerprint:
                        raise ValueError('The query or snapshot changed; restart without a cursor')
                    after = saved['after']
                    if type(after) is not int or not -1 <= after <= 999999:
                        raise ValueError('Invalid cursor position')
                except (KeyError, TypeError, ValueError) as exc:
                    raise ValueError('Invalid, stale or mismatched continuation cursor') from exc
            rows = db.execute('SELECT e.* FROM term_search JOIN entries e ON e.id=term_search.rowid '
                              'WHERE term_search MATCH ? AND e.id>? ORDER BY e.id LIMIT 2001',
                              (expression, after))
            results, scanned = [], 0
            for row in rows:
                scanned += 1
                after = row['id']
                match = positions(row['terms'].split(','), query, mode)
                if match is not None:
                    results.append(dict(self.summary(row), first_match_positions=match,
                        oeis_indices=[row['first_index'] + i for i in match] if row['first_index'] is not None else None,
                        matched_terms=query, relation='first finite stored-term match; not a proof of identity'))
                if len(results) == limit or scanned == 2000:
                    break
            more = rows.fetchone() is not None
            next_cursor = base64.urlsafe_b64encode(json.dumps({
                'snapshot': metadata['content_sha256'], 'query': fingerprint, 'after': after}).encode()).decode() if more else None
            return dict(self.envelope(metadata), mode=mode, input_terms=terms, searched_terms=query,
                transformation={'operation': transform, 'multiplier': multiplier, 'addend': addend,
                                'order': 'apply operation, then multiply, then add'},
                results=results, scanned_candidates=scanned, next_cursor=next_cursor,
                exhausted=not more, scope='stored entry terms only; no b-files, no novelty conclusion')

    def neighbors(self, identifier: str, direction: str = 'both', explicit_only: bool = True,
                  limit: int = 30, offset: int = 0):
        identifier = aid(identifier)
        bounds(limit, offset)
        if direction not in {'incoming', 'outgoing', 'both'}:
            raise ValueError('direction must be incoming, outgoing or both')
        with self.connect() as (db, metadata):
            statements, params = [], []
            for way in ('outgoing', 'incoming'):
                if direction not in {way, 'both'}:
                    continue
                target, source = ('target', 'source') if way == 'outgoing' else ('source', 'target')
                statements.append(f"SELECT {target} AS aid, '{way}' AS direction, field FROM refs WHERE {source}=?" +
                                  (" AND field='crossrefs'" if explicit_only else ''))
                params.append(identifier)
            query = 'WITH links AS (' + ' UNION ALL '.join(statements) + ') '
            grouped = 'SELECT aid,direction,group_concat(field) AS fields FROM links GROUP BY aid,direction'
            total = db.execute(query + 'SELECT count(*) FROM (' + grouped + ')', params).fetchone()[0]
            rows = db.execute(query + 'SELECT g.*,e.name FROM (' + grouped +
                ') g LEFT JOIN entries e ON e.aid=g.aid ORDER BY g.aid,g.direction LIMIT ? OFFSET ?',
                (*params, limit, offset)).fetchall()
            exists = db.execute('SELECT 1 FROM entries WHERE aid=?', (identifier,)).fetchone() is not None
            return dict(self.envelope(metadata), aid=identifier, indexed=exists, total=total,
                relation='explicit %Y cross-references' if explicit_only else 'textual A-number references, not mathematical equivalence',
                results=[dict(r, fields=sorted(set(r['fields'].split(',')))) for r in rows],
                next_offset=offset + limit if offset + limit < total else None)

    def bfile(self, identifier: str, start_position: int = 0, limit: int = 50):
        identifier = aid(identifier)
        bounds(limit, start_position, 200)
        path = self.mirror / 'files' / identifier[:4] / ('b' + identifier[1:] + '.txt')
        result = {'aid': identifier, 'url': f'https://oeis.org/{identifier}/b{identifier[1:]}.txt',
                  'source': 'local supplementary file, separate from the indexed entry snapshot',
                  'attribution': LICENSE}
        if not path.is_file():
            return dict(result, status='not_local')
        if not path.resolve().is_relative_to(self.mirror):
            raise ValueError('Supplementary file resolves outside the configured mirror')
        with path.open(encoding='utf-8-sig') as source:
            first = source.readline()
            if first.strip() == 'version https://git-lfs.github.com/spec/v1':
                return dict(result, status='lfs_pointer', metadata=source.read(1024).strip(),
                            hint='The content is not local. Fetch it explicitly outside the read-only MCP.')
            source.seek(0)
            values, seen = [], 0
            deadline = time.monotonic() + self.query_seconds
            for line_no, line in enumerate(source, 1):
                if time.monotonic() > deadline:
                    raise ValueError('Supplementary file scan exceeded its time budget')
                text = line.strip()
                if not text or text.startswith('#'):
                    continue
                parts = text.split()
                if len(parts) != 2:
                    raise ValueError(f'Malformed b-file at line {line_no}; no terms were silently skipped')
                index, value = map(integer, parts)
                if seen >= start_position:
                    values.append({'n': index, 'value': value})
                seen += 1
                if len(values) > limit:
                    break
        return dict(result, status='available', terms=values[:limit],
                    next_position=start_position + limit if len(values) > limit else None,
                    file_modified_ns=path.stat().st_mtime_ns)

    def status(self):
        if not self.database.is_file():
            return {'status': 'missing_index', 'build_command': 'python tools/oeis_index.py',
                    'mirror_available': (self.mirror / 'seq').is_dir()}
        with self.connect() as (_, metadata):
            result = dict(metadata, status='ready', database_bytes=self.database.stat().st_size,
                          read_only=True, network_requests=False)
        try:
            current = revision(self.mirror)
            result.update(current_mirror_revision=current, indexed_revision_is_current=current == metadata.get('revision'))
        except (OSError, ValueError, subprocess.SubprocessError):
            result.update(current_mirror_revision=None, indexed_revision_is_current=None)
        result['notice'] = NOTICE
        return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--database', type=Path)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('status')
    for name in ('get', 'terms', 'neighbors', 'bfile'):
        sub = commands.add_parser(name)
        sub.add_argument('identifier')
    search = commands.add_parser('search')
    search.add_argument('query')
    search.add_argument('--fields', nargs='+')
    search.add_argument('--syntax', choices=('words', 'fts'), default='words')
    match = commands.add_parser('match')
    match.add_argument('terms', help='comma-separated decimal integers')
    match.add_argument('--mode', choices=('contiguous', 'prefix', 'subsequence'), default='contiguous')
    match.add_argument('--transform', default='identity')
    args = parser.parse_args(argv)
    store = OEIS(args.database)
    if args.command == 'search':
        value = store.search(args.query, fields=args.fields, syntax=args.syntax)
    elif args.command == 'match':
        value = store.match_terms(args.terms.split(','), mode=args.mode, transform=args.transform)
    elif args.command == 'status':
        value = store.status()
    else:
        value = getattr(store, args.command)(args.identifier)
    print(json.dumps(value, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
