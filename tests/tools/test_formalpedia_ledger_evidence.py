"""EXACT — LEAN VERIFIED rows must name declarations whose compiled axioms match their label."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))

from formalpedia_core import ledger_evidence as fp_evidence, workspace as fp_workspace  # noqa: E402

STANDARD = ['propext', 'Classical.choice', 'Quot.sound']


def _index(*names):
    return {'declarations': [
        {'id': f'N.{n}', 'name': n, 'qualified_name': f'N.{n}', 'source_name': f'N.{n}', 'namespace': 'N',
         'module': 'Problems.A', 'file': 'formal/Problems/A.lean', 'visibility': 'public', 'line': 1}
        for n in names]}


def _row(identifier, decl=None, trust='kernel', **extra):
    row = {'id': identifier, 'tag': fp_evidence.LABEL, 'statement': 's', 'lean': 'Problems/A.lean',
           'decl': decl, 'lean_trust': trust if decl else None}
    return dict(row, **extra)


def _baseline(tmp_path, rows):
    path = tmp_path / fp_evidence.BASELINE_NAME
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({'rows': rows}), encoding='utf-8')


def test_unnamed_rows_are_a_shrinking_baseline(tmp_path) -> None:
    ledger = [_row('held'), _row('new'), _row('named', 'a'), {'id': 'other', 'tag': 'CONJECTURE'}]
    _baseline(tmp_path, ['held', 'fixed'])
    kinds = {(p['kind'], p['row']) for p in fp_evidence.static_problems(ledger, fp_evidence.baseline(tmp_path))}
    assert kinds == {('lean_verified_without_declaration', 'new'), ('baseline_entry_resolved', 'fixed')}


def test_compiled_axioms_must_match_each_rows_trust_label() -> None:
    index = _index('a', 'b', 'c', 'd')
    ledger = [_row('kernel', 'a'), _row('sorry', 'b'),
              _row('mixed', ['c', 'd'], trust='mixed', compiler_decls=['d']),
              _row('ghost', 'missing')]
    axioms = {'Problems.A::N.a': STANDARD, 'Problems.A::N.b': STANDARD + ['sorryAx'],
              'Problems.A::N.c': STANDARD + ['Lean.ofReduceBool'],
              'Problems.A::N.d': STANDARD + ['Lean.ofReduceBool']}
    result = fp_evidence.compiled_problems(index, ledger, lambda ids: {i: axioms.get(i) for i in ids})
    found = {(p['kind'], p['row']) for p in result['problems']}
    assert found == {('axioms_exceed_label', 'sorry'), ('axioms_exceed_label', 'mixed'),
                     ('declaration_unresolved', 'ghost')}
    assert [p['unexpected_axioms'] for p in result['problems'] if p['row'] == 'mixed'] == [['Lean.ofReduceBool']]
    assert result['declarations_checked'] == 4


def test_declarations_outside_the_current_export_are_reported() -> None:
    result = fp_evidence.compiled_problems(_index('a'), [_row('r', 'a')], lambda ids: {i: None for i in ids})
    assert [p['kind'] for p in result['problems']] == ['not_in_current_export']


def test_a_missing_export_fails_only_when_required(tmp_path) -> None:
    _baseline(tmp_path, [])

    class Missing:
        def axioms(self, ids):
            raise ValueError('Semantic index is missing')
    ledger = [_row('r', 'a')]
    relaxed = fp_evidence.check(_index('a'), ledger, root=tmp_path, semantic=Missing())
    strict = fp_evidence.check(_index('a'), ledger, root=tmp_path, semantic=Missing(), require_compiled=True)
    assert relaxed['problems'] == [] and relaxed['compiled']['status'] == 'unavailable'
    assert [p['kind'] for p in strict['problems']] == ['compiled_export_unavailable']


def test_the_committed_ledger_matches_its_baseline_and_every_named_declaration_resolves() -> None:
    from formalpedia_catalog import Catalogue
    index, ledger, _ = Catalogue().snapshot()
    assert fp_evidence.static_problems(ledger, fp_evidence.baseline(fp_workspace.ROOT)) == []
    resolved = fp_evidence.compiled_problems(index, ledger, lambda ids: {i: list(STANDARD) for i in ids})
    assert resolved['problems'] == [] and resolved['declarations_checked'] > 1000
