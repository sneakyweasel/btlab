"""Scope keeps transitive mathematics and makes historical discovery explicit."""
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))

from lab_scope import active_lean_modules, path_scope, policy, validate_scope


def test_active_graph_keeps_shared_imports_but_not_unrelated_projects():
    graph = {'modules': {
        'Problems.Juggler.Test': {'imports': ['BTCalculus.Fourier']},
        'Problems.Collatz.Test': {'imports': ['Problems.Engine.Counting']},
        'BTCalculus.Fourier': {'imports': ['Core.Basic']},
        'Problems.Engine.Counting': {'imports': ['Core.Basic']},
        'Core.Basic': {'imports': []},
        'Problems.Primes.Test': {'imports': ['Core.Basic']},
        'BTCalculus.Cubic': {'imports': []},
    }}
    assert active_lean_modules(graph) == set(graph['modules']) - {'Problems.Primes.Test', 'BTCalculus.Cubic'}


def test_policy_agrees_with_runtime_and_retains_dependency_seeds():
    from research.scope import ACTIVE_RESEARCH
    rules = policy()
    assert rules['active_research'] == list(ACTIVE_RESEARCH)
    assert 'engine_campaign' in rules['support_research']
    assert 'rewrite_calculus' in rules['archived_research']
    classified = rules['active_research'] + rules['support_research'] + rules['archived_research']
    assert len(classified) == len(set(classified))
    actual = {p.name for p in (ROOT / 'src/research').iterdir() if p.is_dir() and p.name != '__pycache__'}
    assert set(classified) == actual


def test_dossiers_and_source_scope_preserve_relevant_negative_knowledge():
    assert path_scope('docs/negative_knowledge.md') == 'active'
    assert path_scope('docs/problems/juggler_oeis_neighbourhood.md') == 'active'
    assert path_scope('src/research/collatz/core.py') == 'active'
    assert path_scope('src/research/engine_campaign/corpus.py') == 'active'
    assert path_scope('docs/theory/cubic_newton_stratum.md') == 'archive'
    assert path_scope('src/research/primes/sparse.py') == 'archive'
    assert path_scope('docs/problems/odd_residue_example.md',
                      rules={'archived_research': [], '_active_documents': ['docs/problems/odd_residue_example.md']}) == 'active'
    with pytest.raises(ValueError, match='scope'):
        validate_scope('typo')


def test_registry_defaults_to_four_programmes_and_exact_archive_lookup_survives(monkeypatch):
    from research.open_problems import get_problem, list_problems
    monkeypatch.delenv('BTLAB_INCLUDE_ARCHIVE', raising=False)
    assert {p.id for p in list_problems()} == set(policy()['active_research'])
    assert len(list_problems(include_archive=True)) > 40
    assert get_problem('rewrite_calculus').id == 'rewrite_calculus'


def test_cli_default_help_is_focused_and_archive_flag_is_local(monkeypatch, capsys):
    from cli.main import main
    monkeypatch.delenv('BTLAB_INCLUDE_ARCHIVE', raising=False)
    with pytest.raises(SystemExit) as result:
        main(['--help'])
    assert result.value.code == 0
    current = capsys.readouterr().out
    assert 'Juggler' in current and 'perfect-powers' not in current
    with pytest.raises(SystemExit):
        main(['--include-archive', '--help'])
    assert 'perfect-powers' in capsys.readouterr().out
    assert main(['status']) == 0
    assert 'active research problems: 4' in capsys.readouterr().out


def test_archive_inventory_preserves_publication_outputs_and_names_a_snapshot():
    archive = json.loads((ROOT / 'archive/inventory.json').read_text(encoding='utf-8'))
    assert archive['archive_revision'] == policy()['archive_revision']
    assert archive['retained_build_artifacts']
    assert all(row['path'].startswith('tmp/') for row in archive['removed_from_tracking'])
