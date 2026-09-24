"""Audit the original-count interval support and dense null density blowup."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    "Problems.Juggler.BeattySupportChecks.original_count_interval_cluster",
    "Problems.Juggler.BeattySupportChecks.density_blowup_geometry",
    *{
        f"Problems.Juggler.BeattyPhase.{name}"
        for name in (
            "lowerSemicontinuous_mul_monotone_of_tendsto_left",
            "intermediate_value_downward_of_lowerSemicontinuous",
            "ordConnected_image_Icc_of_equal_endpoints",
            "support_map_restrict_Ioc_eq_closure_image",
            "mapClusterPt_amplitude_iff",
            "support_sum_logIntervalMeasure",
            "certificatePhaseAmplitude_endpoints",
            "certificatePassageLaw_support_eq_closure_image",
            "certificatePassageLaw_support_eq_closure_jumps",
            "certificatePassageLaw_support_eq_Icc",
            "certificatePassage_endpoints_bounds",
            "certificateGammaRatio_cluster_iff_mem_Icc",
            "certificatePassageLaw_Ioo_pos",
            "certificatePassageLaw_cdf_strictMonoOn",
            "certificatePassageDensity_lowerSemicontinuous",
            "certificateJumpTail_inter_open_nonempty",
            "isGδ_certificateDensityBlowupSet",
            "closure_certificateDensityBlowupSet",
            "certificateDensityBlowupSet_subset_infinite",
            "volume_certificateDensityBlowupSet",
            "certificatePassageDensity_superlevel_pos",
            "certificatePassageDensity_no_ae_bounded_version",
        )
    },
}


def test_original_count_support_consumers():
    """Reject altered interfaces, compilation warnings and extra proof axioms."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySupport.lean"],
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
