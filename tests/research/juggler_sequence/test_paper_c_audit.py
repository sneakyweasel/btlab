"""Paper C's printed constants reproduce, and the audit itself is honest."""

from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path

import pytest

from research.juggler_sequence.paper_c_audit import (
    DATA_DIR,
    PAPER,
    boundary_checks,
    constants_table_checks,
    contagion_checks,
    exponent,
    fiber_counterexample,
    floor_rational_power,
    rate_boundary_evidence,
    residual,
    run_exponent,
    summary,
    tao_checks,
)

GROUPS = {
    "contagion": contagion_checks,
    "tao": tao_checks,
    "constants_table": constants_table_checks,
    "statement_boundaries": boundary_checks,
}


def test_published_artifact_hashes_match_the_reviewed_files() -> None:
    entries = re.findall(
        r"^- `([^`]+)`\n\n  SHA-256: `([a-f0-9]{64})`$",
        PAPER.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    assert entries
    root = Path(__file__).resolve().parents[3]
    for relative, digest in entries:
        assert hashlib.sha256((root / relative).read_bytes()).hexdigest() == digest, relative


def test_local_release_retains_the_registered_publication_identity() -> None:
    root = Path(__file__).resolve().parents[3]
    release = json.loads((root / "docs/theory/paper_c_release.json").read_text(encoding="utf-8"))
    assert release["publication"] == {
        "doi": "10.5281/zenodo.22678165",
        "published_date": "2026-09-09",
        "version": "1.0.0",
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
    """C(0.55) is 41 under lambda** (V_6), 44 under pairing, 39 under lambda***.

    The regime must be carried explicitly, or a value correct in one context looks like
    drift in the other -- the trap this audit exists to avoid."""

    by_name = {c["name"]: c for c in tao_checks()}
    assert by_name["C(0.55), lambda*** regime"]["computed"] == 39
    assert by_name["C(0.55), lambda** regime"]["computed"] == 41
    assert by_name["C(0.55), pairing regime"]["computed"] == 44
    assert by_name["C(0.5), lambda*** regime"]["computed"] == 18
    assert by_name["C(0.5), lambda** regime"]["computed"] == 19
    assert by_name["C(0.5), pairing regime"]["computed"] == 20


def test_all_current_azuma_and_optimized_pressure_depths_are_guarded() -> None:
    """The live lambda** table must not silently revert to the older pairing threshold."""

    by_name = {c["name"]: c["computed"] for c in tao_checks()}
    qs = (0.5, 0.55, 0.6, 0.62)
    assert [by_name[f"C({q}), lambda** regime"] for q in qs] == [19, 41, 223, 1586]
    assert [by_name[f"pressure C({q}), lambda** regime"] for q in qs] == [19, 41, 214, 1496]


def test_1015_falsifies_only_the_collapsed_OEOEE_fiber() -> None:
    """Exact arithmetic separates the false 9/32 collapse from the nested identity in use."""

    row = fiber_counterexample()
    assert row["word"] == "OEOEE"
    assert row["orbit"] == [1015, 32336, 179, 2394, 48, 6]
    assert floor_rational_power(1015, 9, 32) == 7 != row["source"]
    assert not row["in_claimed_source_interval"]
    assert floor_rational_power(1015, 3, 4) == row["nested_3_4_floor"] == 179
    assert row["nested_source_condition"]


def test_old_A_condition_does_not_absorb_the_claimed_azuma_rate() -> None:
    row = rate_boundary_evidence()
    assert row["old_A_witness"] > row["C_azuma"] + 1
    assert row["additive_error_exponent"] < row["azuma_exponent"]
    assert row["C_azuma"] + row["azuma_exponent"] > row["old_A_witness"]


def test_KL_rate_occurs_only_at_the_optimizing_tilt() -> None:
    row = rate_boundary_evidence()
    assert row["optimized_tilt_rate"] == pytest.approx(row["kl_rate"], abs=1e-12)
    assert row["off_tilt_rate"] < row["kl_rate"]
    assert row["chernoff_exponent"] == pytest.approx(
        row["C_chernoff"] * row["kl_rate"] / math.log(2), abs=1e-12
    )


def test_paper_quotes_the_constants_the_audit_checks() -> None:
    """A guard against the audit drifting away from the manuscript it audits."""

    text = PAPER.read_text(encoding="utf-8")
    for token in ("0.4480", "0.4801", "0.4891", "0.4916", "0.4924", "0.4926", "0.5392", "0.4927", "0.5520",
                  "0.5199", "0.5109", "0.5084", "0.5076", "0.5074", "0.4608", "0.574", "0.480", "0.6247",
                  "0.7180", "0.7095", "0.8414", "0.7516", "0.9121"):
        assert token in text, token
    assert "C(0.55)=39" in text.replace(" ", "").replace("\\(", "").replace("\\)", "")
    assert r"1-\lambda^{**}=0.552" not in text
    assert r"A>C+1" not in text
    assert "1015" in text
    assert "collapsed-power fiber" in text


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
