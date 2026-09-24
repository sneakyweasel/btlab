"""Recorded axiom artifacts: parsing, consistency with their checks, and corpus coverage."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))

from formalpedia_core import audits as fp_audits, source as fp_source  # noqa: E402


KNOWN_MISSING_EXPECTED = fp_audits.KNOWN_MISSING_EXPECTED


def _write(root: Path, name: str, check: str, expected: str | None) -> None:
    formal = root / 'formal'
    formal.mkdir(exist_ok=True)
    (formal / f'{name}.lean').write_text(check, encoding='utf-8')
    if expected is not None:
        (formal / f'{name}.expected').write_text(expected, encoding='utf-8')


def test_wrapped_lists_primes_and_axiom_free_answers_parse() -> None:
    rows = fp_audits.parse_expected(
        "'A.b' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
        "'A.c'' depends on axioms: [propext]\n"
        "'A.d' does not depend on any axioms\n"
        "A.e : True\n")
    assert [(r['name'], r['axioms']) for r in rows] == [
        ('A.b', ['propext', 'Classical.choice', 'Quot.sound']),
        ("A.c'", ['propext']), ('A.d', [])]
    assert all(r['standard'] for r in rows)


def test_a_matching_artifact_reports_no_problem_and_answers_relative_names(tmp_path) -> None:
    _write(tmp_path, 'AxiomCheckGood', 'open A\n#print axioms b\n#print axioms A.d\n',
           "'A.b' depends on axioms: [propext]\n'A.d' does not depend on any axioms\n")
    result = fp_audits.scan(tmp_path)
    assert result['problems'] == []
    assert result['by_name']['A.b'] == [
        {'expected': 'formal/AxiomCheckGood.expected', 'axioms': ['propext'], 'standard': True}]


def test_stale_missing_and_nonstandard_artifacts_are_reported(tmp_path) -> None:
    _write(tmp_path, 'AxiomCheckStale', '#print axioms A.b\n#print axioms A.new\n',
           "'A.b' depends on axioms: [propext]\n")
    _write(tmp_path, 'AxiomCheckMissing', '#print axioms A.b\n', None)
    _write(tmp_path, 'AxiomCheckSorry', '#print axioms A.s\n',
           "'A.s' depends on axioms: [propext, sorryAx]\n")
    kinds = {(p['kind'], p.get('check', p.get('expected'))) for p in fp_audits.scan(tmp_path)['problems']}
    assert not any(p.get('known') for p in fp_audits.scan(tmp_path)['problems'])
    assert kinds == {('stale_expected', 'formal/AxiomCheckStale.lean'),
                     ('missing_expected', 'formal/AxiomCheckMissing.lean'),
                     ('nonstandard_axioms', 'formal/AxiomCheckSorry.expected')}


def test_a_reordered_artifact_is_stale_even_with_the_same_count(tmp_path) -> None:
    _write(tmp_path, 'AxiomCheckOrder', '#print axioms A.b\n#print axioms A.c\n',
           "'A.c' depends on axioms: [propext]\n'A.b' depends on axioms: [propext]\n")
    [problem] = fp_audits.scan(tmp_path)['problems']
    assert problem['kind'] == 'stale_expected' and problem['first_difference'] == 0


def test_committed_artifacts_match_their_checks_and_name_live_declarations() -> None:
    result = fp_audits.scan(ROOT)
    problems = result['problems'] + fp_audits.unresolved(result, fp_source.build())
    missing = {p['check'] for p in problems if p['kind'] == 'missing_expected'}
    assert missing <= KNOWN_MISSING_EXPECTED, sorted(missing - KNOWN_MISSING_EXPECTED)
    assert [p for p in problems if p['kind'] != 'missing_expected'] == []
    assert len(result['by_name']) > 1000


def test_unknown_or_empty_audit_selection_never_succeeds(monkeypatch):
    import axiom_audit
    import pytest
    monkeypatch.setattr(fp_audits, 'checks', lambda: [])
    for args in (['--run', '--only', 'Typo.lean'], ['--run', '--only']):
        with pytest.raises(SystemExit) as error:
            axiom_audit.main(args)
        assert error.value.code == 2
