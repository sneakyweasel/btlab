"""Fast checks for the square-seam cycle lemma. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.juggler_sequence.power_words import floor_power
from research.juggler_sequence.square_seam import (
    CLASS_REPARAM,
    DOSSIER_PATH,
    EXISTING_LEAN,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    NEW_LEAN_FILES,
    anti_overclaim,
    cyclemin_square_algebra,
    even_isolated_seam,
    finance_saving,
    fixture_nine,
    fixture_one_hundred,
    fixture_thirty_six,
    lean_api_present,
    odd_isolated_seam,
    parent_census,
    short_closure,
)

DOSSIER = Path("docs/problems/juggler_square_seam.md")


def test_fixture_nine_odd_seam() -> None:
    row = fixture_nine()
    assert row["state"] == 9
    assert row["image"] == 27
    assert floor_power(9) == 27
    assert row["crumb"] == 0
    assert row["exact"] is True
    assert row["isolated"] is True
    assert row["next_letter"] == "O"
    assert row["local_word"] == "*OO"


def test_fixture_thirty_six_even_seam() -> None:
    row = fixture_thirty_six()
    assert row["state"] == 36
    assert row["image"] == 6
    assert row["crumb"] == 0
    assert row["isolated"] is True
    assert row["next_letter"] == "E"
    assert row["local_word"] == "*EE"


def test_fixture_one_hundred_then_odd() -> None:
    row = fixture_one_hundred()
    assert row["state"] == 100
    assert row["image"] == 10
    assert row["isolated"] is True
    assert floor_power(10) == 3


def test_tower_sixteen_is_not_isolated() -> None:
    row = even_isolated_seam(4)
    assert row["state"] == 16
    assert row["image"] == 4
    assert row["isolated"] is False
    assert row["tower_square"] is True


def test_parent_cells_small() -> None:
    census = parent_census(max_root=40)
    assert census["all_exact"] is True
    assert census["odd_parent_unique"] is True
    assert census["even_width_is_cell"] is True
    assert census["all_odd_star_oo"] is True
    assert census["all_even_star_ee"] is True
    nine = odd_isolated_seam(3)
    assert nine["even_width"] == 2 * 9 + 1
    assert len(nine["odd_parents"]) <= 1


def test_cyclemin_square_is_d0_only() -> None:
    row = cyclemin_square_algebra(max_s=40)
    assert row["oo_suffix_holds"] is True
    assert row["last_even_is_standard_cell"] is True
    assert row["first_even_ge_n2"] is True
    assert row["extra_beyond_d0"] is False


def test_finance_is_not_a_leftover_mover() -> None:
    fin = finance_saving()
    assert fin["leftover_mover"] is False
    assert fin["odd_save"] < 1e-10
    assert fin["even_save_if_cyclemin_bound"] < 1e-7


def test_short_closure_finds_no_cycle() -> None:
    short = short_closure(max_root=20, max_len=3)
    assert short["no_short_cycle"] is True
    assert short["n_odd_hits"] == 0
    assert short["n_even_hits"] == 0


def test_anti_overclaim_and_no_atlas_lean() -> None:
    anti = anti_overclaim()
    assert anti["halt_theorem"] is False
    assert anti["paper_a_modified"] is False
    assert anti["n0_raised"] is False
    assert anti["atlas_recensus"] is False
    assert anti["exact_floor_impact_reopened"] is False
    assert anti["cyclic_seam_reopened"] is False
    assert anti["leftover_killer"] is False
    assert anti["dk_tightened"] is False
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False
    for path in NEW_LEAN_FILES:
        assert path.exists() is False
    source = Path("src/research/juggler_sequence/square_seam.py").read_text(encoding="utf-8")
    assert "research.juggler_sequence.atlas" not in source
    assert "gpu_census" not in source


def test_dossier_headings() -> None:
    text = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in text
    assert "## Decision" in text
    assert "## Publication assessment" in text
    assert "CLOSE" in text
    assert "Paper A" in text


def test_science_artifact_when_present() -> None:
    if not JSON_PATH.exists():
        return
    import json

    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_REPARAM
    assert summary["parents"]["all_exact"] is True
    assert summary["short_closure"]["no_short_cycle"] is True
    assert summary["finance"]["leftover_mover"] is False
    assert DOSSIER_PATH.exists()
