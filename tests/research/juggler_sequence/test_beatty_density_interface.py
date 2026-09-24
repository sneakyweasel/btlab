"""Audit the full density and real-power moments for the original certificate law."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattyDensityChecks.original_count_density_limit",
    "Problems.Juggler.BeattyDensityChecks.explicit_jump_density",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "finiteJumpProfile_integral_chain",
            "finiteJumpProfile_occupation",
            "occupationPrimitive_sub_bound",
            "jumpProfile_occupation_hasSum",
            "jumpProfile_kernel_occupation_hasSum",
            "measure_eq_sum_logIntervalMeasure",
            "sum_logIntervalMeasure_eq_withDensity",
            "certificatePassageLaw_occupation",
            "certificatePassageLaw_eq_sum_logIntervalMeasure",
            "certificatePassageLaw_eq_withDensity",
            "certificatePassageDensity_lintegral",
            "certificatePassageDensity_ae_lt_top",
            "certificate_log_jump_normalization",
            "certificateAmplitudeJump_bounds",
            "certificatePassageLaw_ae_mem_envelope",
            "certificatePassageLaw_integrable_rpow",
            "certificatePassageLaw_endpoint_moment_hasSum",
            "certificatePassageLaw_moment_hasSum",
        )
    },
}


def test_original_count_density_consumers():
    """Reject altered quantifiers, compilation warnings and extra proof axioms."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattyDensity.lean"],
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
