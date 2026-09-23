"""Connect rigorous arithmetic to the paper/Lean constants and recorded scope."""
from fractions import Fraction as F
import json
import re

from flint import ctx
import pytest

import check_paper_c_intervals as audit
from research_engine.intervals import UnresolvedInterval, ball, signed_evaluation


@pytest.fixture(scope="module")
def report():
    return audit.certificate()


def test_models_match_the_lean_table_and_current_ooee_certificate():
    src = audit.LEAN.read_text(encoding="utf-8")

    def table(name):
        start = src.index(f"noncomputable def {name} : Fin 8 → ℝ")
        body = src[start:src.index("\n\n", start)]
        rows = dict(re.findall(r"\|\s*(\d)\s*=>\s*([0-9]+(?:\s*/\s*[0-9]+)?)", body))
        assert len(rows) == 8
        return [F(rows[str(i)].replace(" ", "")) for i in range(8)]

    assert audit.production_models()["V6"] == list(zip(table("productionCoeff"), table("productionRate")))
    note = audit.OOEE_NOTE.read_text(encoding="utf-8")
    assert r"\frac{33}{100}(3/4)^{5/8}" in note
    assert r"\frac{11}{100}(9/16)^{5/8}" in note


@pytest.mark.parametrize("name,printed", [
    ("pairing", "0.4480"), ("V2", "0.4801"), ("V3", "0.4891"),
    ("V4", "0.4916"), ("V5", "0.4924"), ("V6", "0.4926"),
    ("conditional_Appendix_C", "0.5392"), ("depth_two_ideal", "0.4927"),
    ("sweep", "0.138"), ("OOEE_limiting_model", "0.6327671418"),
])
def test_entire_root_bracket_rounds_to_the_printed_decimal(report, name, printed):
    text = (audit.PAPER if name != "OOEE_limiting_model" else audit.OOEE_NOTE).read_text(encoding="utf-8")
    assert printed in text
    half_unit = F(1, 2 * 10**len(printed.split(".")[1]))
    root = report["roots"][name]
    assert F(printed) - half_unit < F(root["lower"]) <= F(root["upper"]) < F(printed) + half_unit
    assert F(root["upper"]) - F(root["lower"]) <= F(1, 10**24)
    assert F(root["lower_residual"]["lower"]) > 0
    assert F(root["upper_residual"]["upper"]) < 0


def test_certified_current_and_historical_rate_crossings(report):
    depths = report["rate_crossings"]
    expected = {
        "V6": ([19, 41, 214, 1496], [19, 41, 223, 1586]),
        "Lean_baseline_100_203": ([19, 41, 214, 1496], [19, 41, 223, 1586]),
        "written_OOEE_5_8": ([16, 34, 168, 1135], [16, 34, 175, 1201]),
    }
    for regime, kinds in expected.items():
        for kind, values in zip(("Chernoff", "Azuma"), kinds):
            assert [row["least_integer_C"] for row in depths[regime][kind].values()] == values
    for kinds in depths.values():
        for rows in kinds.values():
            for row in rows.values():
                assert row["rejected_candidates"] == row["least_integer_C"] - 5
                assert F(row["gap_at_C"]["lower"]) > 0
                assert F(row["gap_at_previous_C"]["upper"]) < 0


def test_ooee_slack_does_not_retag_the_theorem(report):
    assert F(report["OOEE_slack_at_5_8"]["lower"]) > F(11, 50000)
    assert "No Lean proof" in report["scope"]
    assert "OOEE production theorem or its independent analytic review" in report["not_certified"]
    assert report["all_checks_passed"]


def test_inadmissible_drift_invalid_kind_and_budget_fail_closed():
    with ctx.workprec(128):
        assert audit.rate(5, F(31, 50), "Azuma") == 0
    for q, kind in [(F(7, 10), "Chernoff"), (F(1, 2), "bogus")]:
        with pytest.raises(ValueError):
            audit.least_depth(q, kind, F(5, 8))
    with pytest.raises(UnresolvedInterval):
        audit.least_depth(F(1, 2), "Chernoff", F(5, 8), max_C=15)
    # Verify the boundary independently at higher precision against exact 3/8.
    for C, expected in ((15, -1), (16, 1)):
        assert signed_evaluation(lambda: audit.rate(C, F(1, 2), "Chernoff") - ball("3/8"),
                                 bits=256)[0] == expected


def test_explicit_writer_creates_real_provenance(tmp_path, capsys):
    dest = tmp_path / "intervals.json"
    assert audit.main(["--output", str(dest)]) == 0
    report = json.loads(dest.read_text(encoding="utf-8"))
    assert b"\r\n" not in dest.read_bytes()  # Git stores LF; hashes must survive checkout.
    manifest = json.loads(dest.with_suffix(".research.json").read_text(encoding="utf-8"))
    assert report["all_checks_passed"]
    assert manifest["generator"]["parameters"]["version"] == audit.flint.__version__
    assert manifest["outputs"][0]["path"] == dest.name
    assert manifest["scope"] == audit.SCOPE
    assert len(manifest["inputs"]) == 3
    assert json.loads(capsys.readouterr().out)["schema"] == report["schema"]
