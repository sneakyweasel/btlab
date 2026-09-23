"""Focused feedback must expose gaps rather than silently narrow acceptance gates."""
import pytest

from lab_selection import select_tests


def change(root, paths, links=None, uncertainties=()):
    for name in paths:
        file = root / name
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text('# fixture\n')
    links = links or {}
    return {'changed_files': paths, 'affected_tests': sorted({p for rows in links.values() for p in rows}),
            'test_links': links, 'uncertainties': list(uncertainties)}


def test_full_remains_default_policy_even_when_a_small_test_set_exists(tmp_path):
    data = change(tmp_path, ['src/app/one.py'], {'src/app/one.py': ['tests/test_one.py']})
    assert select_tests(tmp_path, data, 'full')['paths'] == ['tests']
    focused = select_tests(tmp_path, data, 'focused')
    assert focused['paths'] == ['tests/test_one.py'] and focused['mode'] == 'affected'
    assert 'Iteration only' in focused['basis']


@pytest.mark.parametrize('name', [
    'conftest.py', 'tests/nested/conftest.py', 'src/app/__init__.py',
    'pyproject.toml', 'tools/lab_selection.py', 'tools/requirements-lab.lock',
    'src/research/claims.py', 'src/research_engine/intervals.py',
    'src/research/experiments/provenance.py', 'formal/lake-manifest.json',
    '.github/workflows/ci.yml',
])
def test_shared_or_configuration_changes_force_full_suite(tmp_path, name):
    selected = select_tests(tmp_path, change(tmp_path, [name], {name: ['tests/test_one.py']}), 'focused')
    assert selected['mode'] == 'full'
    assert any(name in reason for reason in selected['fallback_reasons'])


def test_mixed_changes_cannot_hide_an_unmapped_file(tmp_path):
    data = change(tmp_path, ['src/app/mapped.py', 'src/app/orphan.py'],
                  {'src/app/mapped.py': ['tests/test_mapped.py']})
    result = select_tests(tmp_path, data, 'focused')
    assert result['paths'] == ['tests']
    assert any('orphan.py' in reason for reason in result['fallback_reasons'])
    data['changed_files'] = ['src/app/mapped.py']
    data['uncertainties'] = ['Cannot parse Python imports in tools/broken.py']
    assert select_tests(tmp_path, data, 'focused')['mode'] == 'full'


def test_deletion_unclassified_data_and_absent_tests_force_full_suite(tmp_path):
    data = change(tmp_path, ['src/app/gone.py'], {'src/app/gone.py': ['tests/test_one.py']})
    (tmp_path / 'src/app/gone.py').unlink()
    assert select_tests(tmp_path, data, 'focused')['mode'] == 'full'
    data = change(tmp_path, ['formal/certificate.json'], {'formal/certificate.json': ['tests/test_one.py']})
    assert select_tests(tmp_path, data, 'focused')['mode'] == 'full'
    assert select_tests(tmp_path, change(tmp_path, ['src/app/orphan.py']), 'focused')['mode'] == 'full'


def test_claim_edits_keep_evidence_tests_and_documentation_paths_do_not_duplicate_tests(tmp_path):
    names = ['tests/unit/test_claims.py', 'tests/unit/test_theorem_ledger.py', 'tests/integration/test_docs.py']
    change(tmp_path, names)
    data = change(tmp_path, ['docs/claims/juggler/example.json', 'docs/problems/juggler_example.md'],
                  {'docs/claims/juggler/example.json': ['tests/test_math.py', names[-1]]})
    selected = select_tests(tmp_path, data, 'focused')
    assert selected['mode'] == 'affected'
    assert set(selected['paths']) == {'tests/integration', *names[:2], 'tests/test_math.py'}


def test_long_argument_lists_fall_back_to_a_portable_full_suite_command(tmp_path):
    tests = [f'tests/long_directory_name/test_candidate_{i:04}.py' for i in range(500)]
    data = change(tmp_path, ['src/app/one.py'], {'src/app/one.py': tests})
    result = select_tests(tmp_path, data, 'focused')
    assert result['paths'] == ['tests']
    assert any('command-line budget' in reason for reason in result['fallback_reasons'])


def test_unknown_profile_is_rejected(tmp_path):
    with pytest.raises(ValueError, match='profile'):
        select_tests(tmp_path, {}, 'automatic')
