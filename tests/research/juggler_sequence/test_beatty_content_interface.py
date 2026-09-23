"""Compile the original-count Minkowski-content consumers and audit their axioms."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyContentChecks.original_gap_counting",
    "Problems.Juggler.BeattyContentChecks.original_count_cluster_content",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "diagonalCount_monotone_tendsto",
            "diagonalCount_tendsto_of_sub_tendsto_zero",
            "certificatePhase_shift_interval_frequency",
            "certificateWeight_two_thirds_phase_asymptotic",
            "certificateGapMoment_pos",
            "certificate_gapCount_asymptotic",
            "truncated_sum_eq_integral_gapCount",
            "truncated_sum_asymptotic_of_gapCount",
            "certificateGapMoment_eq_profile_moment",
            "certificateGapMoment_eq_law_moment",
            "certificateMinkowskiContent_pos",
            "certificateClusterSet_minkowski_content",
        )
    },
}


def test_original_count_content_consumers_compile():
    """The complete limit applies to actual counts and has only standard dependencies."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyContent.lean"],
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
