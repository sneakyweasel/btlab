"""Paper C's printed constants reproduce, and the audit itself is honest."""

from __future__ import annotations

import json
import math
from pathlib import Path

import pytest

from research.juggler_sequence.paper_c_audit import (
    DATA_DIR,
    PAPER,
    constants_table_checks,
    contagion_checks,
    exponent,
    residual,
    run_exponent,
    stratification_checks,
    summary,
    tao_checks,
)

GROUPS = {
    "contagion": contagion_checks,
    "tao": tao_checks,
    "constants_table": constants_table_checks,
    "stratification": stratification_checks,
}


@pytest.mark.parametrize("name", sorted(GROUPS))
def test_every_printed_constant_reproduces(name: str) -> None:
    checks = GROUPS[name]()
    assert checks
    bad = [(c["name"], c["printed"], c["computed"]) for c in checks if not c["ok"]]
    assert bad == [], f"{name}: {bad}"


def test_residual_root_is_the_printed_lambda_two_equation() -> None:
    """The residual and the note's printed lambda** equation are the same curve, not merely
    curves with the same root: multiplying by (1 - x) and using x(3/4)^L = (3/8)^L."""

    for lam in (0.1, 0.25, 0.4480, 0.5, 0.7, 0.9):
        x = 2.0**-lam
        printed = 2.0**-lam + (1 / 9) * (3 / 8) ** lam + (2 / 9) * (3 / 4) ** lam - 1.0
        assert residual(lam, 0.0, 2 / 3, 1.0) * (1 - x) == pytest.approx(printed, abs=1e-12)


def test_ladder_is_monotone_and_the_sweep_sits_below_the_ideal() -> None:
    present = [run_exponent(r, eta1=2 / 3) for r in (1, 2, 3, 4)]
    ideal = [run_exponent(r, eta1=1.0) for r in (1, 2, 3, 4)]
    assert present == sorted(present)
    assert ideal == sorted(ideal)
    assert all(p < i for p, i in zip(present, ideal))
    assert exponent(1.0, 1.0, 1.0) == pytest.approx(1.0, abs=1e-9)


def test_the_two_C_of_q_regimes_are_different_and_both_are_covered() -> None:
    """C(0.55) is 44 under lambda** and 39 under lambda***; Paper C quotes the second.

    The regime must be carried explicitly, or a value correct in one context looks like
    drift in the other -- the trap this audit exists to avoid."""

    by_name = {c["name"]: c for c in tao_checks()}
    assert by_name["C(0.55), lambda*** regime"]["computed"] == 39
    assert by_name["C(0.55), lambda** regime"]["computed"] == 44
    assert by_name["C(0.5), lambda*** regime"]["computed"] == 18
    assert by_name["C(0.5), lambda** regime"]["computed"] == 20


def test_paper_quotes_the_constants_the_audit_checks() -> None:
    """A guard against the audit drifting away from the manuscript it audits."""

    text = PAPER.read_text(encoding="utf-8")
    for token in ("0.4480", "0.5392", "0.4927", "0.5520", "0.4608", "0.574", "0.480",
                  "0.6247", "0.7180", "0.7095", "0.8414", "0.7516", "0.9121"):
        assert token in text, token
    assert "C(0.55)=39" in text.replace(" ", "").replace("\\(", "").replace("\\)", "")


def test_summary_is_clean_and_serialisable() -> None:
    result = summary()
    assert result["classification"]["failures"] == 0
    assert result["classification"]["total_checks"] >= 40
    assert result["classification"]["all_printed_constants_reproduce"]
    json.dumps(result)


def test_stored_summary_matches_a_fresh_run() -> None:
    stored = DATA_DIR / "summary.json"
    if not stored.is_file():
        pytest.skip("run python -m research.juggler_sequence.paper_c_audit first")
    data = json.loads(stored.read_text(encoding="utf-8"))
    assert data["classification"]["failures"] == 0
    assert data["N0"] == summary()["N0"]
