"""Audit Hausdorff consumers while retaining their explicit phase-hitting premises."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    *{
        f"Problems.Juggler.BeattyHausdorffChecks.{name}"
        for name in (
            "original_count_cluster_hausdorff_finite",
            "original_count_cluster_dimH_lower",
            "original_count_cluster_dimH_eq",
        )
    },
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "hausdorffMeasure_two_thirds_ne_top_of_tube_bound",
            "certificateClusterSet_hausdorffMeasure_ne_top",
            "certificateClusterSet_dimH_upper",
            "certificateCdf_image_clusterSet",
            "certificateCdf_holder_of_phaseHitting",
            "certificateClusterSet_dimH_lower_of_phaseHitting",
            "certificateClusterSet_hausdorffMeasure_ne_zero_of_phaseHitting",
            "certificateClusterSet_hausdorffMeasure_pos_finite_of_phaseHitting",
            "certificateClusterSet_dimH_eq_of_phaseHitting",
        )
    },
}


def test_original_count_hausdorff_consumers_compile():
    """Upper bounds are unconditional; lower-bound assumptions remain in the types."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyHausdorff.lean"],
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
