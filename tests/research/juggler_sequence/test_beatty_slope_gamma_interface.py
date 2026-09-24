"""Audit the actual-count Gamma-normalized law for the irrational family."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    f"Problems.Juggler.BeattySlopeGammaChecks.{name}" for name in (
        "actual_gamma_phase", "actual_gamma_cluster",
        "actual_gamma_law_type", "actual_gamma_regularity",
    )
}


def test_slope_gamma_consumers():
    """Compile expanded Gamma-law consumers and reject any nonstandard proof premise."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySlopeGamma.lean"],
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
