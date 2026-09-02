"""Odd-start image-parity discrepancy. Not a halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.odd_image_discrepancy import (
    CLASS_GREEN,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    analytic_majorant,
    anti_overclaim,
    cell_multiplicity,
    interval_census,
    lean_api_present,
    odd_image,
    odd_image_sign,
    scan,
    so_from_oo,
)
from research.juggler_sequence.parity_discrepancy import odd_start_count


def test_sign_convention_and_so_identity():
    assert odd_image(1) == 1
    assert odd_image_sign(1) == -1
    assert odd_image(7) == 18
    assert odd_image_sign(7) == 1
    census = interval_census(200)
    assert census["identity_ok"] is True
    assert census["S_O"] == so_from_oo(census["O_O"], 199)
    assert census["S_O"] == census["odd_starts"] - 2 * census["O_O"]
    assert abs(census["S_O"]) <= 2 * odd_start_count(200)


def test_cell_multiplicity_is_zero_or_one():
    seen = {0, 1}
    for m in range(1, 250):
        rec = cell_multiplicity(m)
        assert rec["c_m"] in seen
        assert rec["n_count"] <= 1
        if rec["c_m"] == 1:
            n = rec["lower_n"]
            assert n % 2 == 1
            assert odd_image(n) == m


def test_cell_sum_recovers_so():
    n_max = 120
    so = 0
    occupied = []
    for n in range(1, n_max + 1, 2):
        a = odd_image(n)
        occupied.append(a)
        so += odd_image_sign(n)
    rebuilt = sum((-1) ** m for m in occupied)
    assert rebuilt == so
    assert interval_census(n_max)["S_O"] == so


def test_pairing_is_linear_on_small_window():
    census = interval_census(2000)
    assert census["cells"]["c_m_max"] == 1
    assert census["cells"]["pair_variation_over_odds"] > 0.5
    assert census["max_abs"] <= analytic_majorant(2000)


def test_scan_keeps_frequency_flag_false():
    row = scan(
        n_max=400,
        n_spot=None,
        cell_prefix=80,
        word_n_max=80,
        image_n_max=80,
    )
    assert row["decision"]["classification"] == CLASS_GREEN
    assert row["decision"]["n13_promoted"] is False
    assert row["anti_overclaim"]["parity_frequency_theorem"] is False
    assert row["anti_overclaim"]["n13_is_a_theorem"] is False
    assert row["cells"]["c_m_le_1"] is True
    assert row["interval"]["identity_ok"] is True


def test_lean_and_anti_overclaim():
    lean = lean_api_present()
    assert lean["sorry_free"]
    assert lean["odd_preimage_unique"]
    assert lean["odd_preimage_iff"]
    anti = anti_overclaim()
    assert anti["parity_frequency_theorem"] is False
    assert anti["interval_bound_transfers_to_arbitrary_sets"] is False
    assert anti["weyl_engine"] is False


def test_records_park():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["decision"]["branch"] == "PARK"
    assert data["anti_overclaim"]["parity_frequency_theorem"] is False
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "PARK" in text.split("## Decision", 1)[1]
    assert "## Publication assessment" in text
    assert (DATA_DIR / "manifest.json").is_file()
    assert (DATA_DIR / "odd_image_discrepancy.csv").is_file()
    assert (DATA_DIR / "cell_counts.csv").is_file()
    assert (DATA_DIR / "cell_pair_differences.csv").is_file()
    assert (DATA_DIR / "structured_set_discrepancy.csv").is_file()
    assert (DATA_DIR / "counterexamples.jsonl").is_file()
