"""Audit the actual-count slope-continuity theorems for the irrational family."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    f"Problems.Juggler.BeattySlopeContinuityChecks.{name}" for name in (
        "actual_count_locally_constant", "actual_weights_l1",
        "actual_content_continuous", "actual_law_continuous",
    )
}


def test_slope_continuity_consumers():
    """Compile expanded slope-continuity consumers and reject any nonstandard proof premise."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySlopeContinuity.lean"],
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
