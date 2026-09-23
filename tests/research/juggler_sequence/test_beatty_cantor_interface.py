"""Compile the original-count Cantor consumers and audit their dependencies."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyCantorChecks.original_gap_decay",
    "Problems.Juggler.BeattyCantorChecks.original_count_cluster_dimension",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "certificateWeight_phase_asymptotic",
            "certificateWeight_three_halves_bounds",
            "volume_thickening_of_gap_lengths",
            "three_halves_tail_le",
            "truncated_sum_three_halves_bounds",
            "certificateClusterSet_tube_formula",
            "certificateClusterSet_tube_bounds",
            "certificateClusterSet_minkowski_dimension",
        )
    },
}


def test_original_count_cantor_consumers_compile():
    """The dimension concerns the actual cluster set and has only standard dependencies."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyCantor.lean"],
        cwd=ROOT / "formal", capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=600,
    )
    assert result.returncode == 0, (result.stdout + result.stderr)[-10000:]
    assert not result.stderr.strip(), result.stderr
    pattern = re.compile(
        r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]\s*$", re.MULTILINE,
    )
    records = pattern.findall(result.stdout)
    assert len(records) == len(EXPECTED), result.stdout
    assert {name for name, _ in records} == EXPECTED
    for name, dependencies in records:
        assert {value.strip() for value in dependencies.split(",")} <= STANDARD, name
    assert not pattern.sub("", result.stdout).strip(), result.stdout
