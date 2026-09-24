"""Audit concrete Gamma-law concentration, subcritical Lp and blowup geometry."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    *{
        f"Problems.Juggler.BeattyRegularityChecks.{name}"
        for name in (
            "arbitrary_set_concentration", "density_series_subcritical",
            "entire_blowup_geometry", "cdf_regularity",
        )
    },
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "certificateAmplitudeJump_length_le",
            "certificatePassageLaw_concentration",
            "certificatePassageLaw_cdf_holder",
            "certificatePassageDensity_weak_three_halves",
            "certificatePassageDensity_eq_zero_of_not_mem_envelope",
            "certificatePassageDensity_lintegral_rpow_lt_top",
            "certificatePassageDensity_memLp",
            "certificatePassageLaw_cdf_not_lipschitzOn",
            "certificateDensityBlowupSet_eq_infinite",
            "certificatePassageDensity_infinite_hausdorffMeasure_zero",
            "certificatePassageDensity_infinite_dimH_le",
        )
    },
}


def test_gamma_regularity_consumers():
    """Reject altered quantifiers, compilation warnings and extra proof axioms."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyRegularity.lean"],
        cwd=ROOT / "formal", capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=600,
    )
    assert result.returncode == 0, (result.stdout + result.stderr)[-16000:]
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
