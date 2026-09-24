"""Audit the actual-count geometry and law for the whole irrational slope family."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    f"Problems.Juggler.BeattySlopeGeometryChecks.{name}" for name in (
        "actual_logarithmic_profile", "actual_positive_crossings", "actual_positive_jump_weights",
        "actual_family_cluster_reciprocal", "actual_family_cantor", "actual_gap_endpoints",
        "actual_gap_avoidance", "actual_singular_empirical_law",
        "actual_profile_threshold_frequency", "actual_average_limit",
    )
}


def test_arbitrary_slope_geometry_consumers():
    """Compile expanded count/geometry consumers and reject any nonstandard proof premise."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySlopeGeometry.lean"],
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
