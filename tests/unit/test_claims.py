"""Canonical claims remain authoritative across edits, moves and invalid snapshots."""
import hashlib
import json
from pathlib import Path

import pytest

from research import claims


def row(identifier='J-example', **extra):
    return {'id': identifier, 'statement': 'A conditional statement.',
            'tag': 'EXACT — HUMAN PROOF', 'source': 'docs/theory/proof.md', **extra}


def write(root, records, topic='juggler/example.json'):
    path = root / claims.CLAIMS / topic
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(claims.render_json(records), encoding='utf-8')
    return path


def route(root, target=None):
    path = root / 'docs/theory/proof.md'
    path.parent.mkdir(parents=True, exist_ok=True)
    passage = '# Proof\nOriginal argument.\n'
    path.write_text(passage + '# End\n', encoding='utf-8')
    return {'id': 'written', 'method': 'written', 'coverage': 'complete',
            'notes': 'A recorded reading, not a proof certificate.',
            'source': {'path': 'docs/theory/proof.md', 'start': '# Proof', 'end': '# End',
                       'sha256': hashlib.sha256(passage.encode()).hexdigest()},
            'uses': [{'claim': target, 'kind': 'proof'}] if target else []}


def test_authority_identity_and_locations_survive_moves(tmp_path):
    original = row(custom_metadata={'exact': 'α/3'}, conditions=['A hypothesis'])
    topic = write(tmp_path, [original])
    export = tmp_path / claims.EXPORT
    export.parent.mkdir(parents=True)
    export.write_text('broken stale export', encoding='utf-8')
    first = claims.load_claims(tmp_path)
    assert first.get('J-example') == original
    assert first.location('J-example') == {'path': 'docs/claims/juggler/example.json', 'pointer': '/0'}
    first.entries[0]['custom_metadata']['exact'] = 'mutated'
    assert first.get('J-example') == original
    moved = topic.with_name('renamed.json')
    topic.rename(moved)
    second = claims.load_claims(tmp_path)
    assert second.entries == first.entries and second.snapshot != first.snapshot
    assert second.location('J-example')['path'].endswith('renamed.json')
    assert export.read_text() == 'broken stale export'
    moved.unlink()
    with pytest.raises(claims.ClaimError, match='No canonical claim files'):
        claims.load_claims(tmp_path, required=False)


@pytest.mark.parametrize('content,expected', [
    ('[{"id":"J-a","id":"J-b"}]', 'Duplicate JSON key'),
    ('[{"id":NaN}]', 'Nonfinite JSON'),
    ('{}', 'JSON array'),
    ('[null]', 'Claim must be an object'),
    (json.dumps([row(tests='tests/test.py')]), 'tests must be a list'),
])
def test_invalid_rows_fail_with_source_diagnostics(tmp_path, content, expected):
    path = write(tmp_path, [])
    path.write_text(content)
    with pytest.raises(claims.ClaimError, match=expected) as error:
        claims.load_claims(tmp_path)
    assert error.value.issues[0]['path'] == 'docs/claims/juggler/example.json'


def test_cross_file_duplicates_and_broken_dependencies(tmp_path):
    write(tmp_path, [row()])
    other = write(tmp_path, [row()], 'shared/other.json')
    with pytest.raises(claims.ClaimError, match='Duplicate claim ID'):
        claims.load_claims(tmp_path)
    other.unlink()
    write(tmp_path, [row(proof_routes=[route(tmp_path, 'C-other')])])
    with pytest.raises(claims.ClaimError, match='unknown dependency'):
        claims.load_claims(tmp_path)
    write(tmp_path, [row('C-other')], 'collatz/other.json')
    assert len(claims.load_claims(tmp_path).entries) == 2
    write(tmp_path, [row('C-other', proof_routes=[route(tmp_path, 'J-example')])], 'collatz/other.json')
    with pytest.raises(claims.ClaimError, match='Circular'):
        claims.load_claims(tmp_path)


def test_stale_pins_remain_discoverable_but_fail_audit(tmp_path):
    write(tmp_path, [row(proof_routes=[route(tmp_path)])])
    claims.load_claims(tmp_path, check_sources=True)
    (tmp_path / 'docs/theory/proof.md').write_text('# Proof\nChanged argument.\n# End\n')
    assert claims.load_claims(tmp_path).get('J-example')['tag'] == 'EXACT — HUMAN PROOF'
    with pytest.raises(claims.ClaimError, match='stale'):
        claims.load_claims(tmp_path, check_sources=True)


def test_snapshot_retries_membership_changes_and_rejects_continuous_edits(tmp_path, monkeypatch):
    write(tmp_path, [row()])
    original = claims._stamp
    calls = 0

    def change_once(paths):
        nonlocal calls
        calls += 1
        if calls == 1:
            write(tmp_path, [row('C-added')], 'collatz/added.json')
        return original(paths)

    monkeypatch.setattr(claims, '_stamp', change_once)
    assert len(claims.load_claims(tmp_path).entries) == 2
    assert calls >= 4
    monkeypatch.setattr(claims, '_stamp', lambda paths: object())
    with pytest.raises(claims.ClaimError, match='changed while reading'):
        claims.load_claims(tmp_path)


def test_renderer_checks_both_exports(tmp_path, monkeypatch):
    import render_theorem_ledger as renderer
    write(tmp_path, [row()])
    export = tmp_path / claims.EXPORT
    export.parent.mkdir(parents=True)
    markdown = export.with_suffix('.md')
    monkeypatch.setattr(renderer, 'ROOT', tmp_path)
    monkeypatch.setattr(renderer, 'JSON_PATH', export)
    monkeypatch.setattr(renderer, 'MD_PATH', markdown)
    assert renderer.main(['--check']) == 1
    assert renderer.main([]) == 0
    assert renderer.main(['--check']) == 0
    export.write_text('[]')
    assert renderer.main(['--check']) == 1
    renderer.main([])
    markdown.write_text('stale')
    assert renderer.main(['--check']) == 1


def test_repository_export_is_lossless():
    root = Path(__file__).resolve().parents[2]
    ledger = claims.load_claims(root, check_sources=True)
    assert (root / claims.EXPORT).read_text(encoding='utf-8') == claims.render_json(ledger.entries)


def test_optional_empty_checkout_cannot_hide_a_missing_claim_directory(tmp_path):
    assert claims.load_claims(tmp_path, required=False).entries == []
    export = tmp_path / claims.EXPORT
    export.parent.mkdir(parents=True)
    export.write_text('[]')
    with pytest.raises(claims.ClaimError, match='No canonical claim files'):
        claims.load_claims(tmp_path, required=False)
