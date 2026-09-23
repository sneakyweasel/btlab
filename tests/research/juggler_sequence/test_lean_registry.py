"""Stable path consumers must not depend on the changing registration catalogue."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]


def test_numerical_certificate_import_does_not_load_registry():
    result = subprocess.run([sys.executable, '-c',
        'import sys; import research.juggler_sequence.negative_preimage_density; '
        'assert "research.juggler_sequence.lean_registry" not in sys.modules'],
        cwd=ROOT, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr


def test_paper_e_tracks_stable_paths_without_registry_churn():
    inputs = json.loads((ROOT / 'docs/theory/paper_e_release.json').read_text(encoding='utf-8'))['inputs']
    paths = {row['path'] for row in inputs}
    assert 'src/research/juggler_sequence/lean_paths.py' in paths
    assert 'src/research/juggler_sequence/lean_registry.py' not in paths


def test_registry_is_infrastructure_not_a_research_branch():
    from research.juggler_sequence.branch_index import INFRASTRUCTURE
    assert {'lean_paths', 'lean_registry'} <= INFRASTRUCTURE
