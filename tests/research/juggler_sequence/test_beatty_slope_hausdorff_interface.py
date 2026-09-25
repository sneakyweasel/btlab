"""Audit the actual-count Hausdorff theorems for the irrational slope family."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    f"Problems.Juggler.BeattySlopeHausdorffChecks.{name}" for name in (
        "actual_family_hausdorff_finite", "actual_ae_hausdorff_dim",
        "actual_dio_hausdorff_pos", "actual_quadratic_hausdorff", "actual_golden_hausdorff",
        "actual_liouville_hausdorff", "actual_liouville_dim",
        "actual_hausdorff_pos_iff", "actual_exponent_dim",
        "actual_dim_class_lower", "actual_dim_two_thirds_iff",
        "actual_dim_spectrum", "actual_cf_regular_dim", "actual_packing_dim",
        "actual_star_dim", "actual_iso_dim", "actual_two_scale_dim",
        "actual_two_scale_low",
    )
}


def test_arbitrary_slope_hausdorff_consumers():
    """Compile expanded Hausdorff consumers and reject any nonstandard proof premise."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySlopeHausdorff.lean"],
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
