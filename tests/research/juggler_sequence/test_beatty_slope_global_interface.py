"""Audit the actual-count global empirical law for every real slope."""
from pathlib import Path
import re
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[3]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = {
    f"Problems.Juggler.BeattySlopeGlobalChecks.{name}" for name in (
        "actual_global_law", "actual_global_law_explicit",
        "actual_rational_law", "actual_right_phase", "actual_law_slope_map",
        "actual_law_dimension", "actual_law_dimension_liouville",
    )
}


def test_global_law_consumers():
    """Compile expanded global-law consumers and reject any nonstandard proof premise."""
    lake = shutil.which("lake")
    if lake is None:
        pytest.skip("no lake on PATH")
    result = subprocess.run(
        [lake, "env", "lean", "InterfaceCheckBeattySlopeGlobal.lean"],
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
