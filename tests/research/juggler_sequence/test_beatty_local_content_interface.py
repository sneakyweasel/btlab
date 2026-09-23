"""Compile the original-count local geometric-limit consumers and audit their axioms."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyLocalContentChecks.original_count_cluster_local_tail",
    "Problems.Juggler.BeattyLocalContentChecks.original_count_cluster_geometric_average",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "diagonalCount_nonneg_tendsto_of_sub_tendsto_zero",
            "certificate_tail_gapCount_asymptotic",
            "truncated_sum_asymptotic_of_gapCount_nonneg",
            "volume_thickening_inter_gap",
            "volume_thickening_tail_bounds",
            "tendsto_probabilityMeasure_of_tails",
            "tendsto_finiteMeasure_of_tails",
            "certificateLocalContent_mass",
            "certificateGeometricLaw_real",
            "certificateGeometricLaw_integral",
            "certificate_tail_truncated_asymptotic",
            "certificateClusterSet_local_tube_tail",
            "certificateScaledTubeMeasure_tendsto",
            "certificateTubeLaw_real",
            "certificateTubeLaw_integral",
            "certificateTubeLaw_tendsto",
            "certificateClusterSet_tube_average_tendsto",
        )
    },
}


def test_original_count_local_content_consumers_compile():
    """The full geometric limit applies to actual counts with standard dependencies."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyLocalContent.lean"],
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
