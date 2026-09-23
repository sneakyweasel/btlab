"""A worktree command must never import another checkout's editable source."""
import json
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
import lab


def test_run_uses_selected_checkout_even_with_other_source_on_path(tmp_path, monkeypatch):
    root = tmp_path / 'selected checkout'
    other = tmp_path / 'other checkout'
    for directory in (root, other):
        package = directory / 'src/research'
        package.mkdir(parents=True)
        (package / '__init__.py').write_text('')
        (package / 'probe.py').write_text(
            'import json, os, pathlib, sys\n'
            'pathlib.Path("result.json").write_text(json.dumps({\n'
            '    "source": __file__, "cwd": str(pathlib.Path.cwd()), "args": sys.argv[1:],\n'
            '    "command": json.loads(os.environ["BTLAB_RUN_COMMAND"])\n'
            '}))\n', encoding='utf-8')
    monkeypatch.setenv('PYTHONPATH', str(other / 'src'))
    assert lab.run_python(['-m', 'research.probe', '--output', 'name with spaces'], root) == 0
    result = json.loads((root / 'result.json').read_text())
    assert Path(result['source']).is_relative_to(root)
    assert Path(result['cwd']) == root
    assert result['args'] == ['--output', 'name with spaces']
    assert result['command'] == ['python', 'tools/lab.py', 'run', 'research.probe', '--output', 'name with spaces']
    assert not (other / 'result.json').exists()


@pytest.mark.parametrize(('argv', 'expected'), [
    (['run', 'research.probe', '--check'], ['-m', 'research.probe', '--check']),
    (['test', '--', '-n', '0', 'tests/unit'], ['-m', 'pytest', '-n', '0', 'tests/unit']),
    (['test', 'tests/unit', '-q'], ['-m', 'pytest', 'tests/unit', '-q']),
])
def test_command_forwards_arguments_and_exit_status(monkeypatch, argv, expected):
    calls = []
    def run(arguments):
        calls.append(arguments)
        return 7
    monkeypatch.setattr(lab, 'run_python', run)
    assert lab.main(argv) == 7
    assert calls == [expected]
