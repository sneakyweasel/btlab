"""Audit arithmetic-to-geometry consumers with all Diophantine premises exposed."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    *{
        f"Problems.Juggler.BeattyDiophantineChecks.{name}"
        for name in (
            "original_count_cluster_dimH_lower",
            "original_count_cluster_dimH_eq",
            "original_count_cluster_hausdorff_pos_finite",
        )
    },
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "rotation_hits_interval_of_rat_approx",
            "phaseHittingBound_of_diophantineLowerBound",
            "certificatePhase_hitting_of_diophantineLowerBound",
            "certificateClusterSet_dimH_lower_of_diophantineLowerBound",
            "certificateClusterSet_hausdorffMeasure_ne_zero_of_diophantineLowerBound",
            "certificateClusterSet_hausdorffMeasure_pos_finite_of_badApprox",
            "certificateClusterSet_dimH_eq_of_diophantine_family",
        )
    },
}


def test_original_count_diophantine_consumers_compile():
    """Kernel checks the consumers and their dependency sets, not their premises."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyDiophantine.lean"],
        cwd=ROOT / "formal", capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=600,
    )
    assert result.returncode == 0, (result.stdout + result.stderr)[-12000:]
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
