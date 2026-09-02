"""Second-valley ≥ 281 does not kill leftover 84 at m≥3. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.conjectures import get_conjecture
from research.literature import get_reference
from research.juggler_sequence.cycle_ceiling_finance import FOCUS_EVEN, theta_of
from research.juggler_sequence.cycle_finance import EPS_CONST
from research.juggler_sequence.cycle_second_valley import (
    CLASS_CLOSED,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    EXISTING_LEAN,
    FORBIDDEN_LEAN_FILES,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    KILLING_N2,
    LEAN_CONST,
    LEAN_FLOOR,
    classify,
    later_circuit_rows,
    lean_api_present,
    mixed_height_rhs,
    mixed_inv_sum,
    odd_landing,
    probe_payload,
    render_markdown,
)
from research.juggler_sequence.cycle_ceiling_finance import (
    LEAN_LOG_CERT,
    peak_even_lower,
)
from research.juggler_sequence.cycle_position_finance import odd_run_heights

REPO = Path(__file__).resolve().parents[3]


def test_first_circuit_k12_lands_at_281():
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=12)
    m_min = peak_even_lower(heights, 12)
    r_odd, p_odd = odd_landing(m_min, n, FOCUS_EVEN - 2)
    assert r_odd == 7
    assert p_odd == KILLING_N2 == 281


def test_from_281_k12_lands_at_303():
    rows = later_circuit_rows(281, LEAN_FLOOR)
    worst = min((row for row in rows if row["feasible"]), key=lambda row: row["p_odd"])
    assert worst["k"] == 12
    assert worst["p_odd"] == 303


def test_adversarial_triple_misses_proved_constants():
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=24)
    theta = theta_of()
    need = theta * LEAN_LOG_CERT
    valleys = [261, 281, 303]
    six = mixed_height_rhs(
        n, 84, 53, valleys, const=EPS_CONST, heights=heights
    )
    one = mixed_height_rhs(
        n, 84, 53, valleys, const=LEAN_CONST, heights=heights
    )
    inv = mixed_inv_sum(n, 84, 53, valleys, heights=heights)
    assert one < theta
    assert six > theta
    assert inv > need
    assert 0.00242 < six < 0.00243
    assert 0.01186 < inv < 0.01187
    both = mixed_inv_sum(n, 84, 53, [261, 281, 281], heights=heights)
    assert both > need


def test_oe_263_requires_high_valley_and_dies():
    payload = probe_payload()
    witness = payload["scan"]["k1_witness"]
    assert witness["v"] == 1687
    assert witness["T_v"] == 69290
    assert witness["p_odd"] == 263
    assert payload["scan"]["kills_oe_six_fifths"] is True
    assert payload["scan"]["kills_oe_inv_sum"] is True


def test_probe_closes_and_adds_no_lean():
    payload = probe_payload()
    decision = classify(payload["scan"], payload["lean"])
    assert decision["classification"] == CLASS_CLOSED
    assert payload["scan"]["slogan_false"] is True
    assert payload["scan"]["adversarial_valleys"] == [261, 281, 303]
    assert payload["anti_overclaim"]["halt_theorem"] is False
    assert payload["anti_overclaim"]["new_lean"] is False
    assert payload["lean"]["sorry_free"] is True
    assert payload["lean"]["no_second_valley_lean"] is True
    assert payload["lean"]["not_in_paper_barrel"] is True
    for name in EXISTING_LEAN:
        assert payload["lean"][name] is True
    for name in FORBIDDEN_THEOREMS:
        assert payload["lean"][f"has_{name}"] is False
    for name in FORBIDDEN_NEW_API:
        assert payload["lean"][f"has_api_{name}"] is False
    for path in FORBIDDEN_LEAN_FILES:
        assert not path.is_file()
    markdown = render_markdown(payload)
    assert CLASS_CLOSED in markdown
    assert decision["classification"] != CLASS_GREEN
    assert decision["classification"] != CLASS_INCOMPLETE


def test_dossier_and_registry():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_second_valley.md"
    ).read_text(encoding="utf-8")
    paper = (REPO / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "juggler_second_valley_leftover_killer" in dossier
    assert "juggler_cycle_finance_note.md" in dossier
    assert "CycleSecondValley" not in paper
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    get_reference("simons-de-weger-2005-collatz-m-cycles")
    rec = get_conjecture("juggler_second_valley_leftover_killer")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
    lean = lean_api_present()
    assert lean["cycle_extrema_present"] is True
