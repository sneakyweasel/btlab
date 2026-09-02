"""One-step parity-discrepancy transfer. Not a halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.odd_image_discrepancy import odd_image, odd_image_sign
from research.juggler_sequence.parity_discrepancy_transfer import (
    CLASS_COMPLEX,
    DATA_DIR,
    DOSSIER_PATH,
    JSON_PATH,
    PrefixTables,
    anti_overclaim,
    cell_sum_identity,
    differencing_identity,
    first_odd,
    gap_row,
    image_structure,
    interval_D_direct,
    last_odd,
    lean_api_present,
    odd_count_interval,
    scan,
    source_parity_sum,
)


def test_prefix_matches_direct_and_differencing():
    tables = PrefixTables(250)
    assert tables.interval_D(1, 99) == interval_D_direct(1, 99)
    assert tables.interval_D(10, 80) == interval_D_direct(10, 80)
    assert differencing_identity(tables, 1, 250)
    assert differencing_identity(tables, 7, 91)
    assert cell_sum_identity(1, 120)
    assert tables.interval_D(1, 99) != source_parity_sum(1, 99)


def test_cell_multiplicity_and_monotone_image():
    tables = PrefixTables(300)
    structure = image_structure(tables, 1, 299)
    assert structure["strictly_increasing"] is True
    assert structure["adjacent_occupied"] == 0
    assert structure["output_size"] == odd_count_interval(1, 299)
    assert structure["shape"] in {"highly_fragmented", "interval_with_holes", "few_intervals"}
    values = tables.image_values(5, 40)
    assert values == [odd_image(n) for n in range(5, 41, 2)]
    assert len(values) == len(set(values))
    rebuilt = sum((-1) ** image for image in values)
    assert rebuilt == sum(odd_image_sign(n) for n in range(5, 41, 2))


def test_gap_parity_controls_sign_flip():
    for n in (1, 7, 15, 99, 201):
        row = gap_row(n)
        left = odd_image_sign(n)
        right = odd_image_sign(n + 2)
        assert row["image_gap"] == odd_image(n + 2) - odd_image(n)
        assert (right == left) == (row["gap_parity"] == 0)
        assert row["floor_error"] == row["image_gap"] - row["derivative_approximation"]


def test_source_parity_is_not_image_parity():
    assert source_parity_sum(1, 20) == -odd_count_interval(1, 20)
    assert first_odd(10) == 11
    assert last_odd(10) == 9
    tables = PrefixTables(40)
    assert tables.interval_D(1, 21) == sum(odd_image_sign(n) for n in range(1, 22, 2))
    assert tables.interval_D(1, 21) != source_parity_sum(1, 21)


def test_scan_closes_without_overclaim():
    row = scan(n_max=400)
    assert row["identities"]["differencing"] is True
    assert row["identities"]["cell_sum"] is True
    assert row["identities"]["source_parity_not_D"] is True
    assert row["runs"]["max_run"] >= 1
    assert row["decision"]["classification"] == CLASS_COMPLEX
    assert row["decision"]["branch"] == "CLOSE"
    assert row["decision"]["flags"]["IMAGE_TRANSFER_GREEN"] is False
    assert row["decision"]["flags"]["INTERVAL_UNIFORM_GREEN"] is False
    assert row["anti_overclaim"]["parity_frequency_theorem"] is False
    assert row["anti_overclaim"]["weyl_engine"] is False
    assert row["anti_overclaim"]["interval_bound_is_transfer"] is False


def test_lean_and_anti_overclaim():
    lean = lean_api_present()
    assert lean["sorry_free"]
    assert lean["odd_preimage_unique"]
    anti = anti_overclaim()
    assert anti["parity_frequency_theorem"] is False
    assert anti["iterate_a_theorem"] is False
    assert anti["reopen_closed_branches"] is False


def test_records_close():
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_COMPLEX
    assert data["decision"]["branch"] == "CLOSE"
    assert data["anti_overclaim"]["parity_frequency_theorem"] is False
    smallest = data["decision"]["smallest_transfer"]
    assert smallest is not None
    assert smallest["kind"] == "Y"
    assert smallest["image_odd"] >= 20
    assert smallest["normalized_image_discrepancy"] >= 0.25
    text = DOSSIER_PATH.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "CLOSE" in text.split("## Decision", 1)[1]
    assert "## Publication assessment" in text
    assert (DATA_DIR / "manifest.json").is_file()
    assert (DATA_DIR / "interval_discrepancy.csv").is_file()
    assert (DATA_DIR / "record_intervals.csv").is_file()
    assert (DATA_DIR / "image_discrepancy.csv").is_file()
    assert (DATA_DIR / "gap_statistics.csv").is_file()
    assert (DATA_DIR / "weighted_discrepancy.csv").is_file()
    assert (DATA_DIR / "counterexamples.jsonl").is_file()
