"""Loogle search with hits checked against a pinned Mathlib; the service is never contacted."""
import json
from pathlib import Path
import sys
from urllib.error import URLError

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))

from formalpedia_core import mathlib as fp_mathlib  # noqa: E402


def _pinned_tree(tmp_path: Path) -> Path:
    formal = tmp_path / 'formal'
    (formal / '.lake/packages/mathlib/Mathlib/Order').mkdir(parents=True)
    (formal / 'lake-manifest.json').write_text(json.dumps(
        {'packages': [{'name': 'mathlib', 'rev': 'abc123'}]}), encoding='utf-8')
    (formal / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n', encoding='utf-8')
    (formal / '.lake/packages/mathlib/Mathlib/Order/Basic.lean').write_text(
        'namespace Nat\n\ntheorem succ_le_iff {m n : Nat} : succ m ≤ n ↔ m < n := sorry\n'
        'theorem foo_bar : True := trivial\n\nend Nat\n'
        'theorem Order.qualified : True := trivial\n', encoding='utf-8')
    return tmp_path


def _serve(payload):
    seen = []

    def fetch(url, timeout):
        seen.append(url)
        return payload
    return fetch, seen


def test_hits_are_checked_against_the_pinned_sources(tmp_path, monkeypatch) -> None:
    root = _pinned_tree(tmp_path)
    monkeypatch.setenv('ELAN_HOME', str(tmp_path / 'no-elan'))
    fetch, seen = _serve({'count': 6, 'header': 'Found 6 declarations', 'hits': [
        {'name': 'Nat.succ_le_iff', 'module': 'Mathlib.Order.Basic', 'type': 'm.succ ≤ n ↔ m < n'},
        {'name': 'Order.qualified', 'module': 'Mathlib.Order.Basic', 'type': 'True'},
        {'name': 'Nat.foo', 'module': 'Mathlib.Order.Basic', 'type': 'True'},
        {'name': 'Nat.gone', 'module': 'Mathlib.Order.Removed', 'type': 'True'},
        {'name': 'Nat.le_refl', 'module': 'Init.Prelude', 'type': 'n ≤ n'},
        {'name': 'X.y', 'module': 'Unknown.Lib', 'type': 'True'}]})
    result = fp_mathlib.search('Nat.succ, _ ≤ _', root=root, fetch=fetch)
    assert seen == [fp_mathlib.ENDPOINT + '?q=Nat.succ%2C+_+%E2%89%A4+_']
    assert result['status'] == 'found' and result['mathlib_pinned_rev'] == 'abc123'
    assert [h['pinned']['status'] for h in result['hits']] == [
        'declared', 'declared', 'not_declared_literally', 'module_missing', 'unchecked', 'unchecked']
    assert result['hits'][0]['pinned']['file'] == 'formal/.lake/packages/mathlib/Mathlib/Order/Basic.lean'


def test_limit_errors_and_unreachable_service_are_reported(tmp_path) -> None:
    root = _pinned_tree(tmp_path)
    fetch, _ = _serve({'count': 3, 'hits': [{'name': f'N.h{i}', 'module': 'Mathlib.Order.Basic'}
                                            for i in range(3)]})
    limited = fp_mathlib.search('N', root=root, fetch=fetch, limit=2)
    assert limited['returned'] == 2 and limited['total'] == 3
    fetch, _ = _serve({'error': 'Unknown identifier Rea.sqrt', 'suggestions': ['Real.sqrt']})
    bad = fp_mathlib.search('Rea.sqrt', root=root, fetch=fetch)
    assert bad['status'] == 'query_error' and bad['suggestions'] == ['Real.sqrt']

    def offline(url, timeout):
        raise URLError('Tunnel connection failed: 403 Forbidden')
    down = fp_mathlib.search('Real.sqrt', root=root, fetch=offline)
    assert down['status'] == 'unreachable' and 'loogle.lean-lang.org' in down['remedy']
    fetch, _ = _serve({'count': 0, 'hits': []})
    assert fp_mathlib.search('nothing', root=root, fetch=fetch)['status'] == 'no_hits'


def test_packages_that_are_not_installed_are_unchecked_not_missing(tmp_path) -> None:
    (tmp_path / 'formal').mkdir()
    fetch, _ = _serve({'count': 1, 'hits': [{'name': 'Nat.succ_le_iff', 'module': 'Mathlib.Order.Basic'}]})
    [hit] = fp_mathlib.search('Nat.succ_le_iff', root=tmp_path, fetch=fetch)['hits']
    assert hit['pinned']['status'] == 'unchecked'


def test_remote_modules_cannot_escape_package_and_core_sources_can_be_external(tmp_path, monkeypatch):
    root = _pinned_tree(tmp_path)
    for module in ('Mathlib/../../outside', 'Mathlib..outside', 'Mathlib.\\outside'):
        assert fp_mathlib.check_pinned('x', module, root)['status'] == 'unchecked'
    core = tmp_path / 'toolchain-source'
    (core / 'Init').mkdir(parents=True)
    (core / 'Init/Prelude.lean').write_text('theorem True.intro_test : True := trivial\n')
    monkeypatch.setattr(fp_mathlib, '_toolchain_source', lambda _: core)
    assert fp_mathlib.check_pinned('True.intro_test', 'Init.Prelude', root)['status'] == 'declared'
    for hits in ({'bad': 'shape'}, [None], [{'name': [], 'module': 'Init.Prelude'}]):
        fetch, _ = _serve({'hits': hits})
        assert fp_mathlib.search('x', root=root, fetch=fetch)['status'] == 'error'


def test_commented_names_are_not_reported_as_declared(tmp_path):
    root = _pinned_tree(tmp_path)
    path = root / 'formal/.lake/packages/mathlib/Mathlib/Order/Basic.lean'
    path.write_text('/- theorem Nat.fake : True := trivial -/\n')
    assert fp_mathlib.check_pinned('Nat.fake', 'Mathlib.Order.Basic', root)['status'] == 'not_declared_literally'


def test_short_name_in_a_different_namespace_is_not_a_match(tmp_path):
    root = _pinned_tree(tmp_path)
    assert fp_mathlib.check_pinned('Wrong.succ_le_iff', 'Mathlib.Order.Basic', root)['status'] == 'not_declared_literally'
    assert fp_mathlib.check_pinned('Nat.succ_le_iff', 'Mathlib.Order.Basic', root)['status'] == 'declared'
