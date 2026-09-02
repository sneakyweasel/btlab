"""Second OO from an odd cube-corridor landing."""

from __future__ import annotations

import json

from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.odd_oooe_next import odd_oooe_next
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.second_oo_cube import (
    CLASS_GREEN,
    CONTRAST_EVEN_Q,
    EVEN_U_C1,
    EVEN_U_OOO,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    ODD_U,
    U_DEN,
    U_NUM,
    V_DEN,
    V_NUM,
    classify,
    lean_api_present,
    render_markdown,
    run_probe,
    scale_band,
    second_oo,
    t_lt_n,
    u_inherited_lt_generic,
    u_lt_fifth,
    u_lt_fourth,
    v_inherited_lt_generic,
    v_lt_seventh,
    v_lt_sixth,
    write_artifacts,
)


def test_envelopes():
    assert u_lt_fifth() is True
    assert u_lt_fourth() is False
    assert u_inherited_lt_generic() is True
    assert U_NUM < 5 * U_DEN
    assert U_NUM > 4 * U_DEN
    assert U_NUM < (9 * U_DEN) // 2
    assert v_lt_seventh() is True
    assert v_lt_sixth() is False
    assert v_inherited_lt_generic() is True
    assert V_NUM < 7 * V_DEN
    assert V_NUM > 6 * V_DEN
    assert V_NUM < (27 * V_DEN) // 4
    assert t_lt_n() is False
    assert 3**7 > 2**11
    assert square_cell_gap(9, 7) is False
    assert square_cell_gap(11, 7) is True


def test_even_u_second_ooo():
    row = second_oo(EVEN_U_OOO["n"])
    assert row is not None
    assert row["branch"] == "even_u"
    assert row["q"] == EVEN_U_OOO["q"]
    assert row["u"] == EVEN_U_OOO["u"]
    assert row["s"] == EVEN_U_OOO["s"]
    assert row["u_ge_n3"] and row["u_lt_n5"]
    assert row["u_band"] == 4
    assert row["s_even"] is False
    assert row["s_lt_n2"] is False
    assert row["s_ge_three_halves"]
    assert row["first"] == "even_odd_OOO"


def test_even_u_returns_to_c1():
    row = second_oo(EVEN_U_C1["n"])
    assert row is not None
    assert row["branch"] == "even_u"
    assert row["s"] == EVEN_U_C1["s"]
    assert row["s_even"] is True
    assert row["s_lt_n2"] is False
    assert row["t"] == EVEN_U_C1["t"]
    assert row["t_band"] == 1
    assert row["drop"] is False
    assert row["first"] == "even_even_c1"


def test_odd_u_continues_oo():
    row = second_oo(ODD_U["n"])
    assert row is not None
    assert row["branch"] == "odd_u"
    assert row["q"] == ODD_U["q"]
    assert row["u"] == ODD_U["u"]
    assert row["v"] == ODD_U["v"]
    assert row["u_ge_n3"] and row["u_lt_n5"]
    assert row["v_even"] is False
    assert row["v_lt_n7"]
    assert row["v_ge_nine_halves"]
    assert row["v_band"] == 6
    assert row["first"] == "odd_OOO"


def test_483_is_even_q_not_second_oo():
    assert second_oo(CONTRAST_EVEN_Q["n"]) is None
    row = odd_oooe_next(CONTRAST_EVEN_Q["n"])
    assert row is not None
    assert row["branch"] == "even_q"
    assert row["q"] == CONTRAST_EVEN_Q["q"]
    assert row["r"] == CONTRAST_EVEN_Q["r"]
    assert scale_band(row["r"], CONTRAST_EVEN_Q["n"]) == 1


def test_3989_not_inherited_corridor():
    raw = odd_oooe_next(3989)
    assert raw is not None
    assert raw["branch"] == "odd_q"
    assert raw["w_lt_sq"] is False or raw["q_lt_cube"] is False
    assert second_oo(3989) is None


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    window = scan["window"]
    assert scan["exponents_ok"] is True
    assert scan["u_sharper"] is True
    assert scan["v_sharper"] is True
    assert window["u_fail"] == 0
    assert window["v_fail"] == 0
    assert window["s_fail"] == 0
    assert window["firsts"]
    assert scan["graph"]["c1_return"] is True
    assert scan["length_eleven_census"] is False
    assert scan["residue_automaton"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "2187" in text
    from research.juggler_sequence.second_oo_cube import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_second_oo_cube"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["second_oo_in_c2_c3"] is False
    assert data["anti_overclaim"]["scale_automaton_acyclic"] is False
    assert data["anti_overclaim"]["even_u_always_drops"] is False
    assert data["anti_overclaim"]["defect_chain_constrained"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_second_oo_cube.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_odd_oooe_next.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "2187" in dossier
    assert "juggler_second_oo_cube" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
