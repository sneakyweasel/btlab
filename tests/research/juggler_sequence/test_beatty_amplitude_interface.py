"""Check the exact Gamma-normalized count limit and its transitive dependencies."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyAmplitudeChecks.original_count_gamma_amplitude",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "gammaShiftRatio_bounds",
            "gammaShiftRatio_tendsto",
            "tendsto_rpow_unit_exponent",
            "certificateGammaScale_pos",
            "certificateGammaRatio_phase_asymptotic",
            "certificatePassageProfile_periodic",
            "certificateGammaRatio_periodic_asymptotic",
        )
    },
}


def test_original_count_gamma_amplitude():
    """Expose the integer counts and Gamma factors, then audit all dependencies."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyAmplitude.lean"],
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
