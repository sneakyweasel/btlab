"""The React numerical producer runs without a plotting stack and keeps certificates."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from flint import ctx
import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import export_beatty_profile as profile  # noqa: E402


def test_cli_without_matplotlib_writes_only_certified_data(tmp_path):
    """A real CLI run retains exact endpoints, hash provenance and no image outputs."""
    output = tmp_path / 'profile.json'
    code = '''
import importlib.abc
import runpy
import sys
class RejectPlotting(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname == "matplotlib" or fullname.startswith("matplotlib."):
            raise AssertionError("The data producer must not import matplotlib")
sys.meta_path.insert(0, RejectPlotting())
sys.path.insert(0, sys.argv[1])
sys.argv = [sys.argv[2], "--depth", "64", "--sample-count", "7", "--output", sys.argv[3]]
runpy.run_path(sys.argv[0], run_name="__main__")
'''
    result = subprocess.run(
        [sys.executable, '-c', code, str(ROOT / 'tools'),
         str(ROOT / 'tools/export_beatty_profile.py'), str(output)],
        cwd=ROOT, capture_output=True, text=True, encoding='utf-8', timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    data = json.loads(output.read_text(encoding='utf-8'))
    manifest = json.loads(output.with_suffix('.research.json').read_text(encoding='utf-8'))
    assert data['orders'] == 40
    assert data['sample_orders'] == [34, 40]
    assert data['reference_counts_checked'] == 65
    assert Fraction(data['tail']['lower']) > 0
    assert Fraction(data['tail']['upper']) < Fraction(data['tail_strict_decimal_upper'])
    for core in data['certified_deleted_cores']:
        assert Fraction(core['lower']) < Fraction(core['upper'])
    assert len(manifest['outputs']) == 1
    assert manifest['outputs'][0]['sha256'] == hashlib.sha256(output.read_bytes()).hexdigest()
    assert 'matplotlib' not in manifest['generator']['parameters']
    assert {p.name for p in tmp_path.iterdir()} == {'profile.json', 'profile.research.json'}


def test_precision_is_local_and_integer_counts_are_reproducible():
    previous = ctx.prec
    low = profile.compute(64, 7, 192)
    high = profile.compute(64, 7, 256)
    assert ctx.prec == previous
    assert low['counts_sha256_hex_lines'] == high['counts_sha256_hex_lines']
    assert low['drawing'] == high['drawing']
    assert Fraction(low['tail']['lower']) <= Fraction(high['tail']['upper'])
    assert Fraction(high['tail']['lower']) <= Fraction(low['tail']['upper'])


@pytest.mark.parametrize('depth,samples,bits', [(0, 1, 256), (20001, 1, 256),
                                               (64, 0, 256), (64, 1, 128)])
def test_invalid_scope_fails_before_computing(depth, samples, bits):
    with pytest.raises(ValueError, match='Require depth'):
        profile.compute(depth, samples, bits)
