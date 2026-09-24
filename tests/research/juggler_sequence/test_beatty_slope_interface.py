"""Audit actual arbitrary-boundary counts and the unconditional tilted phase."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    f"Problems.Juggler.BeattySlopeChecks.{name}" for name in (
        "actual_count_partition", "actual_count_recurrence",
        "actual_count_recurrence_reciprocal", "actual_prefix_convention",
        "actual_crossing_edge", "actual_logarithmic_word_sets",
        "actual_weighted_recurrence", "actual_crossing_weight",
        "actual_weighted_renewal", "actual_weighted_phase_transfer", "actual_tilt_bounds",
        "actual_tilted_tail_majorant", "actual_tilted_tail_comparison",
        "actual_tilted_endpoint_limit", "actual_tilted_survivor_limit",
        "actual_tilted_survivor_reciprocal", "actual_tilted_phase_series", "actual_tilted_phase_bounds",
    )
}


def test_arbitrary_boundary_count_consumers():
    """Compile count/phase consumers and reject any nonstandard proof premise."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySlope.lean"],
        cwd=ROOT / "formal", capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=600,
    )
    assert result.returncode == 0, (result.stdout + result.stderr)[-16000:]
    assert not result.stderr.strip(), result.stderr
    pattern = re.compile(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]\s*$", re.MULTILINE)
    records = pattern.findall(result.stdout)
    assert len(records) == len(EXPECTED), result.stdout
    assert {name for name, _ in records} == EXPECTED
    for name, dependencies in records:
        assert {value.strip() for value in dependencies.split(",")} <= STANDARD, name
    assert not pattern.sub("", result.stdout).strip(), result.stdout
