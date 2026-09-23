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


def test_only_current_research_packages_remain():
    rules = policy()
    expected = set(rules['active_research'] + rules['support_research'])
    actual = {p.name for p in (ROOT / 'src/research').iterdir()
              if p.is_dir() and any(p.glob('*.py'))}
    assert actual == expected
    assert not rules['archived_research']
    assert not list((ROOT / 'src/visualization').rglob('*.py'))


def test_current_registry_and_cli_have_no_archive_or_ui_commands(capsys):
    from research.open_problems import get_problem, list_problems
    from cli.main import main
    assert {p.id for p in list_problems()} == set(policy()['active_research'])
    with pytest.raises(KeyError):
        get_problem('rewrite_calculus')
    with pytest.raises(SystemExit) as result:
        main(['--help'])
    assert result.value.code == 0
    help_text = capsys.readouterr().out
    assert 'collatz' in help_text
    assert '--include-archive' not in help_text and 'ui' not in help_text.split()
    assert main(['status']) == 0
    assert 'juggler_sequence' in capsys.readouterr().out
    for args in (['ui'], ['collatz', 'ui'], ['--include-archive', 'status']):
        with pytest.raises(SystemExit) as result:
            main(args)
        assert result.value.code == 2


def test_retained_python_imports_resolve_inside_the_checkout():
    import ast
    missing = []
    source = ROOT / 'src'
    local = {'bt', 'research', 'research_engine', 'cli'}
    for path in source.rglob('*.py'):
        for node in ast.walk(ast.parse(path.read_text(encoding='utf-8-sig'))):
            names = ([n.name for n in node.names] if isinstance(node, ast.Import) else
                     [node.module] if isinstance(node, ast.ImportFrom) and node.module and not node.level else [])
            for name in names:
                if name.split('.')[0] not in local:
                    continue
                target = source.joinpath(*name.split('.'))
                if not target.with_suffix('.py').is_file() and not (target / '__init__.py').is_file():
                    missing.append((path.relative_to(ROOT).as_posix(), name))
    assert missing == []


def test_retained_lean_imports_have_source_files():
    import re
    import formalpedia as fp
    missing = []
    for path in fp.sources():
        for name in re.findall(r'^import\s+(\S+)', path.read_text(encoding='utf-8'), re.M):
            if name.split('.')[0] in fp.LIBRARIES and not (fp.FORMAL / (name.replace('.', '/') + '.lean')).is_file():
                missing.append((path.name, name))
    assert missing == []
