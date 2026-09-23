"""Exact matching, provenance, paging and read-only behavior on independent small records."""
import hashlib
import json
from pathlib import Path
import sqlite3
import sys

import pytest

TOOLS = Path(__file__).resolve().parents[2] / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from oeis_catalog import OEIS
from oeis_index import create_database
from oeis_lab_links import lab_links
from oeis_source import integer, parse_record


def record(identifier, terms, name='A sequence', offset=0, extra=''):
    return identifier, (f'%I {identifier} #7 Jan 01 2026 00:00:00\n'
        f'%S {identifier} {",".join(map(str, terms))}\n%N {identifier} {name}\n'
        f'%O {identifier} {offset},1\n%K {identifier} sign\n' + extra)


@pytest.fixture
def catalog(tmp_path):
    database = tmp_path / 'oeis.sqlite3'
    entries = [
        record('A000001', [-5, 0, 9007199254740993, 9, 16], 'Signed large numbers', -2,
               '%C A000001 Hidden phoenix theorem.\n%Y A000001 Cf. A000002.\n'),
        record('A000002', [1, 1, 2, 3, 5, 8, 13], 'Fibonacci example', 0,
               '%F A000002 a(n) = a(n-1) + a(n-2).\n%C A000002 Compare A000001.\n'),
        record('A000003', [2, 3, 5, 7, 11, 13], 'Prime example', 1),
        record('A000004', [1, 2, 3, 4, 5], 'Natural example', 1),
        record('A000005', [-1, -2, -3, -4], 'Negative example', 1),
        record('A000006', [2, 4, 6, 8], 'Even example', 0),
        record('A000007', [1, 2, 4, 8], 'Powers example', 0),
    ]
    create_database(database, entries, {'revision': 'a' * 40, 'exported_at': '2026-01-01'})
    return OEIS(database, mirror=tmp_path / 'mirror')


def test_parser_preserves_fields_unknown_tags_big_integers_and_continuations():
    identifier, source = record('A000001', ['+0002', '-0', '9' * 5000], offset=-3,
        extra='%C A000001 A quoted comment.\n%Z A000001 Unrecognized field is retained.\n'
              '%o A000001 (Python)\n%o A000001 print("never executed")\n')
    parsed = parse_record(identifier, source)
    assert parsed['terms'] == ['2', '0', '9' * 5000]
    assert parsed['first_index'] == -3
    assert parsed['sha256'] == hashlib.sha256(source.encode()).hexdigest()
    assert any(f['code'] == 'Z' and f['field'] == 'other' for f in parsed['fields'])
    assert len([f for f in parsed['fields'] if f['field'] == 'programs']) == 2


def test_malformed_term_does_not_create_a_false_contiguous_run():
    identifier, source = record('A000001', ['1', 'unknown', '2', '3'])
    parsed = parse_record(identifier, source)
    assert parsed['issues'] and parsed['terms'] == []


def test_snapshot_and_entry_revisions_remain_distinct(catalog):
    result = catalog.get('A000001', fields=['comments'])
    assert result['revision'] == 'a' * 40
    assert result['entry_revision'].startswith('#7')
    assert result['fields'][0]['text'] == 'Hidden phoenix theorem.'
    assert result['available_fields']['terms'] == 1
    assert result['field_chunks'] == {'comments': 1}
    assert '/blob/' + 'a' * 40 in result['snapshot_url']
    assert catalog.get('A999999')['status'] == 'not_found'


def test_long_fields_are_losslessly_pageable(tmp_path):
    text = ('mathematics αβγ ' * 310) + 'last hypothesis'
    database = tmp_path / 'long.sqlite3'
    create_database(database, [record('A000001', [1, 2, 3], extra=f'%C A000001 {text}\n')], {})
    catalog = OEIS(database)
    offset, parts = 0, []
    while offset is not None:
        page = catalog.get('A000001', fields=['comments'], limit=1, offset=offset)
        parts += page['fields']
        offset = page['next_offset']
    assert ''.join(p['text'] for p in parts) == text
    assert [p['part'] for p in parts] == list(range(1, len(parts) + 1))


def test_text_search_covers_comments_fields_phrases_and_keywords(catalog):
    assert catalog.search('PHOENIX')['results'][0]['aid'] == 'A000001'
    assert catalog.search('phoenix', fields=['name'])['total'] == 0
    assert catalog.search('"phoenix theorem"', syntax='fts')['total'] == 1
    assert catalog.search('example', keyword='nonn')['total'] == 0
    first = catalog.search('example', limit=2)
    second = catalog.search('example', limit=2, offset=first['next_offset'])
    assert not ({r['aid'] for r in first['results']} & {r['aid'] for r in second['results']})
    with pytest.raises(ValueError, match='Invalid OEIS query'):
        catalog.search('"unterminated', syntax='fts')
    assert catalog.search('A000002')['results'][0]['aid'] == 'A000002'


def test_integer_terms_keep_sign_precision_and_actual_offset(catalog):
    terms = catalog.terms('A000001')['terms']
    assert terms[0] == {'position': 0, 'n': -2, 'value': '-5'}
    assert terms[2]['value'] == '9007199254740993'
    found = catalog.match_terms(['-5', '0', '9007199254740993'])['results']
    assert found[0]['oeis_indices'] == [-2, -1, 0]
    assert not catalog.match_terms(['5', '0', '9007199254740993'])['results']
    assert not catalog.match_terms(['-5', '0', '9007199254740992'])['results']


def test_prefix_contiguous_and_subsequence_have_distinct_meanings(catalog):
    query = ['1', '2', '3']
    contiguous = {r['aid'] for r in catalog.match_terms(query)['results']}
    prefix = {r['aid'] for r in catalog.match_terms(query, mode='prefix')['results']}
    assert contiguous == {'A000002', 'A000004'} and prefix == {'A000004'}
    assert not catalog.match_terms(['2', '7', '13'])['results']
    match = catalog.match_terms(['2', '7', '13'], mode='subsequence')['results'][0]
    assert match['aid'] == 'A000003' and match['first_match_positions'] == [0, 3, 5]
    assert catalog.match_terms(['1', '1', '2'], mode='subsequence')['results'][0]['aid'] == 'A000002'
    assert not catalog.match_terms(['3', '2', '1'], mode='subsequence')['results']


def test_transformations_are_explicit_and_return_the_searched_values(catalog):
    result = catalog.match_terms(['1', '2', '3'], multiplier=2)
    assert result['searched_terms'] == ['2', '4', '6']
    assert result['results'][0]['aid'] == 'A000006'
    assert catalog.match_terms(['0', '1', '3', '6'], transform='differences')['searched_terms'] == ['1', '2', '3']
    assert catalog.match_terms(['1', '1', '2'], transform='partial_sums')['results'][0]['aid'] == 'A000007'
    assert catalog.match_terms(['1', '2', '3'], transform='negate')['results'][0]['aid'] == 'A000005'


def test_match_context_exposes_next_terms_at_the_actual_offset(catalog):
    hit = catalog.match_terms(['0', '9007199254740993', '9'])['results'][0]
    assert hit['context_before'] == [{'position': 0, 'n': -2, 'value': '-5'}]
    assert hit['context_after'] == [{'position': 4, 'n': 2, 'value': '16'}]


def test_compare_reports_first_disagreement_without_rounding(catalog):
    result = catalog.compare_terms('A000001', ['0', '9007199254740992', '9'], start_position=1)
    assert result['status'] == 'mismatch'
    assert result['matching_prefix_terms'] == 1 and result['compared_terms'] == 3
    assert result['first_mismatch'] == {'query_position': 1, 'position': 2, 'n': 0,
                                      'supplied': '9007199254740992', 'stored': '9007199254740993'}


def test_compare_distinguishes_storage_limits_from_mismatch_and_identity(catalog):
    result = catalog.compare_terms('A000001', ['9007199254740993', '9', '16', '123'], start_position=2)
    assert result['status'] == 'insufficient_data'
    assert result['matching_prefix_terms'] == 3 and result['unchecked_terms'] == 1
    assert result['first_mismatch'] is None
    mismatch = catalog.compare_terms('A000001', ['9', '17', '123'], start_position=3)
    assert mismatch['status'] == 'mismatch' and mismatch['unchecked_terms'] == 1
    empty = catalog.compare_terms('A000001', ['1', '2', '3'], start_position=20)
    assert empty['status'] == 'insufficient_data' and empty['compared_terms'] == 0
    assert catalog.compare_terms('A999999', ['1', '2', '3'])['status'] == 'not_found'


def test_compare_uses_explicit_transforms_and_positions(catalog):
    result = catalog.compare_terms('A000006', ['1', '2', '3'], multiplier=2)
    assert result['status'] == 'match' and result['first_oeis_index'] == 0
    assert result['searched_terms'] == ['2', '4', '6']
    assert result['transformation']['multiplier'] == 2
    assert catalog.compare_terms('A000005', ['1', '2', '3'], transform='negate')['status'] == 'match'
    assert catalog.compare_terms('A000004', ['2', '3', '4'])['status'] == 'mismatch'
    assert catalog.compare_terms('A000004', ['2', '3', '4'], start_position=1)['status'] == 'match'
    with pytest.raises(ValueError):
        catalog.compare_terms('A000001', ['1', '2', '3'], start_position=-1)


def test_matching_pagination_is_exact_and_rejects_stale_or_changed_cursors(catalog):
    first = catalog.match_terms(['1', '2', '3'], limit=1)
    second = catalog.match_terms(['1', '2', '3'], limit=1, cursor=first['next_cursor'])
    assert first['results'][0]['aid'] != second['results'][0]['aid']
    assert second['exhausted'] and second['next_cursor'] is None
    with pytest.raises(ValueError, match='cursor'):
        catalog.match_terms(['2', '3', '5'], cursor=first['next_cursor'])
    with pytest.raises(ValueError, match='cursor'):
        catalog.match_terms(['1', '2', '3'], cursor='invalid')


def test_hash_candidates_are_verified_even_if_the_index_contains_a_false_positive(catalog):
    from oeis_source import term_key
    with sqlite3.connect(catalog.database) as db:
        db.execute('INSERT INTO term_search(rowid,tokens) VALUES (?,?)',
                   (3, ' '.join(term_key(v) for v in ['7', '7', '7'])))
    assert not catalog.match_terms(['7', '7', '7'])['results']


def test_cross_reference_direction_and_mention_scope(catalog):
    outgoing = catalog.neighbors('A000001', direction='outgoing')['results']
    assert outgoing[0]['aid'] == 'A000002'
    assert catalog.neighbors('A000001', direction='incoming')['total'] == 0
    incoming = catalog.neighbors('A000001', direction='incoming', explicit_only=False)['results']
    assert incoming[0]['aid'] == 'A000002' and incoming[0]['fields'] == ['comments']


def test_bfile_pointer_missing_content_and_exact_values(catalog):
    assert catalog.bfile('A000001')['status'] == 'not_local'
    folder = catalog.mirror / 'files/A000'
    folder.mkdir(parents=True)
    path = folder / 'b000001.txt'
    path.write_text('version https://git-lfs.github.com/spec/v1\noid sha256:abc\nsize 999\n')
    assert catalog.bfile('A000001')['status'] == 'lfs_pointer'
    path.write_text('# a comment\n-2 9007199254740993\n-1 -9\n0 4\n')
    first = catalog.bfile('A000001', limit=2)
    assert first['terms'][0]['value'] == '9007199254740993'
    assert catalog.bfile('A000001', start_position=first['next_position'])['terms'] == [{'n': '0', 'value': '4'}]


def test_queries_are_read_only_and_missing_index_is_not_created(catalog, tmp_path):
    before = catalog.database.stat().st_mtime_ns
    catalog.search('example')
    catalog.get('A000001')
    catalog.match_terms(['1', '2', '3'])
    catalog.compare_terms('A000004', ['1', '2', '3'])
    assert catalog.database.stat().st_mtime_ns == before
    missing = OEIS(tmp_path / 'missing.sqlite3')
    assert missing.status()['status'] == 'missing_index'
    with pytest.raises(ValueError, match='missing'):
        missing.get('A000001')
    assert not missing.database.exists()


def test_failed_rebuild_preserves_previous_index(catalog):
    before = catalog.database.read_bytes()

    def broken():
        yield record('A000009', [1, 2, 3])
        raise RuntimeError('interrupted build')

    with pytest.raises(RuntimeError, match='interrupted'):
        create_database(catalog.database, broken(), {})
    assert catalog.database.read_bytes() == before
    assert not list(catalog.database.parent.glob('*.building'))


@pytest.mark.parametrize('value', ['1.0', '1e9', '', 'NaN', '1/2', 9007199254740993, True])
def test_noninteger_input_is_rejected(value):
    with pytest.raises(ValueError):
        integer(value)


def test_validation_prevents_unbounded_queries_and_paths(catalog):
    for identifier in ('../../x', 'A000001/../other', '123', 'A1234567'):
        with pytest.raises(ValueError):
            catalog.bfile(identifier)
    with pytest.raises(ValueError):
        catalog.search('x', fields=['unknown'])
    with pytest.raises(ValueError):
        catalog.search('x', limit=1000)
    with pytest.raises(ValueError):
        catalog.match_terms(['1', '2'])
    with pytest.raises(ValueError):
        catalog.match_terms(['1', '2', '3'], transform='eval')


def test_lab_links_join_docs_ledger_and_correct_lean_docstring(tmp_path, monkeypatch):
    monkeypatch.setattr('oeis_lab_links.shutil.which', lambda _: None)
    (tmp_path / 'formal/Problems').mkdir(parents=True)
    (tmp_path / 'docs/theory').mkdir(parents=True)
    (tmp_path / 'docs/theory/paper.md').write_text('An identity involving A000002.\n')
    (tmp_path / 'docs/claims/shared').mkdir(parents=True)
    (tmp_path / 'docs/claims/shared/example.json').write_text(json.dumps([
        {'source': 'docs/theory/paper.md', 'id': 'test-claim', 'statement': 'A000002 under a condition', 'tag': 'EXACT — HUMAN PROOF',
         'lean': 'Problems/Test.lean', 'decl': 'Math.fibonacci_count'}]))
    (tmp_path / 'formal/Problems/Test.lean').write_text('namespace Math\n'
        'theorem previous : True := trivial\n/-- A000002 interpretation. -/\n'
        'theorem fibonacci_count : True := trivial\nend Math\n')
    result = lab_links('A000002', root=tmp_path)
    assert len(result['lean_declarations']) == 1
    assert result['lean_declarations'][0]['qualified_name'] == 'Math.fibonacci_count'
    assert result['ledger_claims'][0]['id'] == 'test-claim'
    assert result['total_mentions'] == 3


def test_lab_links_include_and_prioritize_manuscripts_and_filter_before_paging(tmp_path, monkeypatch):
    monkeypatch.setattr('oeis_lab_links.shutil.which', lambda _: None)
    (tmp_path / 'docs/theory').mkdir(parents=True)
    (tmp_path / 'docs/problems').mkdir()
    (tmp_path / 'docs/negative_knowledge').mkdir()
    for file, source in {
        'theory/manuscript.tex': 'A000002 first citation\nA000002 second citation\n',
        'theory/manuscript.md': 'A000002 manuscript source\n',
        'theory/references.bib': 'A000002 bibliography\n',
        'theory/note.md': 'A000002 theory\n',
        'problems/known.md': 'A000002 CLOSE\n',
        'negative_knowledge/barrier.md': 'A000002 false identification\n',
    }.items():
        (tmp_path / 'docs' / file).write_text(source)
    result = lab_links('A000002', root=tmp_path, limit=1)
    assert result['mentions'][0]['kind'] == 'paper'
    assert result['mention_counts']['paper'] == 3
    assert result['mention_counts']['bibliography'] == 1
    first = lab_links('A000002', root=tmp_path, kinds=['negative_knowledge', 'dossier'], limit=1)
    second = lab_links('A000002', root=tmp_path, kinds=['negative_knowledge', 'dossier'],
                       limit=1, offset=first['next_offset'])
    assert first['filtered_mentions'] == 2 and first['total_mentions'] == 7
    assert first['mentions'][0]['kind'] == 'dossier'
    assert second['mentions'][0]['kind'] == 'negative_knowledge' and second['next_offset'] is None
    with pytest.raises(ValueError, match='Mention kinds'):
        lab_links('A000002', root=tmp_path, kinds=['typo'])


def test_lab_links_archive_scope_is_explicit_and_counted(tmp_path, monkeypatch):
    monkeypatch.setattr('oeis_lab_links.shutil.which', lambda _: None)
    (tmp_path / 'data').mkdir()
    (tmp_path / 'data/lab_scope.json').write_text(json.dumps({'archived_research': ['primes']}))
    (tmp_path / 'docs/problems').mkdir(parents=True)
    (tmp_path / 'docs/problems/juggler_example.md').write_text('A000002 active\n')
    (tmp_path / 'docs/problems/prime_example.md').write_text('A000002 archived\n')
    current = lab_links('A000002', root=tmp_path)
    assert current['total_mentions'] == 1 and current['all_scope_mentions'] == 2
    assert current['scope_counts'] == {'active': 1, 'archive': 1}
    old = lab_links('A000002', root=tmp_path, scope='archive')
    assert old['mentions'][0]['file'].endswith('prime_example.md')
    assert lab_links('A000002', root=tmp_path, scope='all')['total_mentions'] == 2


@pytest.mark.parametrize('fallback', [False, True])
def test_archive_reference_search_respects_gitignored_private_files(tmp_path, monkeypatch, fallback):
    import shutil
    import subprocess
    from oeis_lab_links import find_mentions
    if not shutil.which('rg') or not shutil.which('git'):
        pytest.skip('ripgrep and git are required for the ignore integration check')
    subprocess.run(['git', 'init', '--quiet', str(tmp_path)], check=True, capture_output=True)
    if fallback:
        which = shutil.which
        monkeypatch.setattr('oeis_lab_links.shutil.which', lambda name: None if name == 'rg' else which(name))
    (tmp_path / '.ignore').write_text('/src/research/primes/\n')
    (tmp_path / '.gitignore').write_text('*.private.json\n')
    (tmp_path / 'src/research/primes').mkdir(parents=True)
    (tmp_path / 'literature').mkdir()
    (tmp_path / 'src/research/primes/old.py').write_text('# A000002 historical citation\n')
    (tmp_path / 'literature/letter.private.json').write_text('{"sequence": "A000002"}\n')
    found = list(find_mentions('A000002', tmp_path))
    assert [file for file, _, _ in found] == ['src/research/primes/old.py']
