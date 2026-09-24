"""Audit the exact overlap criterion without promoting its unresolved premise."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyOverlapChecks.actual_density_overlap_criterion",
    *{f"Problems.Juggler.BeattyPhase.{name}" for name in (
        "lintegral_tsum_indicator_sq", "certificateJumpMultiplicity_measurable",
        "certificateJumpMultiplicity_lintegral_sq",
        "certificatePassageDensity_eq_kernel_mul_multiplicity",
        "certificatePassageDensity_lintegral_sq_lt_top_iff",
        "certificatePassageDensity_memLp_two_iff",
    )},
}


def test_gamma_overlap_consumer():
    """Check the expanded infinite pair sum and the exact allowed dependency set."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyOverlap.lean"],
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
