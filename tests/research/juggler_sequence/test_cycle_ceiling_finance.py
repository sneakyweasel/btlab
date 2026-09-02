"""Upper-cell ceiling does not kill leftover 84 at m≥3. Not a halt test."""

from __future__ import annotations

from pathlib import Path

from research.conjectures import get_conjecture
from research.literature import get_reference
from research.juggler_sequence.cycle_ceiling_finance import (
    CLASS_CLOSED,
    CLASS_GREEN,
    CLASS_INCOMPLETE,
    EXISTING_LEAN,
    FOCUS_EVEN,
    FOCUS_LENGTH,
    FOCUS_ODD,
    FORBIDDEN_LEAN_FILES,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    LEAN_CONST,
    LEAN_FLOOR,
    LEAN_LOG_CERT,
    ceiling_inv_sum,
    ceiling_landing,
    ceiling_rhs,
    ceil_div,
    classify,
    lean_api_present,
    peak_even_lower,
    probe_payload,
    render_markdown,
    theta_of,
)
from research.juggler_sequence.cycle_finance import EPS_CONST
from research.juggler_sequence.cycle_position_finance import odd_run_heights

REPO = Path(__file__).resolve().parents[3]


def test_pigeonhole_k18_would_kill_and_is_not_the_worst():
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=18)
    m_min = peak_even_lower(heights, 18)
    r_max, p_min = ceiling_landing(m_min, n, FOCUS_EVEN - 2)
    theta = theta_of()
    six = ceiling_rhs(
        n, FOCUS_LENGTH, FOCUS_ODD, 3, p_min, const=EPS_CONST, heights=heights
    )
    inv = ceiling_inv_sum(n, FOCUS_LENGTH, FOCUS_ODD, 3, p_min, heights=heights)
    assert ceil_div(FOCUS_ODD, 3) == 18
    assert r_max == 10
    assert p_min == 3075
    assert six < theta
    assert inv < theta * LEAN_LOG_CERT


def test_adversarial_k24_misses_every_proved_constant():
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=24)
    m_min = peak_even_lower(heights, 24)
    r_max, p_min = ceiling_landing(m_min, n, FOCUS_EVEN - 2)
    theta = theta_of()
    one = ceiling_rhs(
        n, FOCUS_LENGTH, FOCUS_ODD, 3, p_min, const=LEAN_CONST, heights=heights
    )
    six = ceiling_rhs(
        n, FOCUS_LENGTH, FOCUS_ODD, 3, p_min, const=EPS_CONST, heights=heights
    )
    inv = ceiling_inv_sum(n, FOCUS_LENGTH, FOCUS_ODD, 3, p_min, heights=heights)
    assert r_max == 14
    assert p_min == 304
    assert one < theta
    assert six > theta
    assert inv > theta * LEAN_LOG_CERT
    assert 0.00249 < six < 0.00250
    assert 0.01212 < inv < 0.01214


def test_large_m_misses_at_pigeonhole_k():
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=14)
    theta = theta_of()
    need = theta * LEAN_LOG_CERT
    m4 = peak_even_lower(heights, 14)
    _, p4 = ceiling_landing(m4, n, FOCUS_EVEN - 3)
    six4 = ceiling_rhs(
        n, FOCUS_LENGTH, FOCUS_ODD, 4, p4, const=EPS_CONST, heights=heights
    )
    inv4 = ceiling_inv_sum(n, FOCUS_LENGTH, FOCUS_ODD, 4, p4, heights=heights)
    assert ceil_div(FOCUS_ODD, 4) == 14
    assert p4 == 569
    assert six4 > theta
    assert inv4 > need

    m2 = peak_even_lower(heights, 2)
    _, p2 = ceiling_landing(m2, n, 1)
    six31 = ceiling_rhs(
        n, FOCUS_LENGTH, FOCUS_ODD, 31, p2, const=EPS_CONST, heights=heights
    )
    assert p2 == 523
    assert six31 > theta


def test_probe_closes_and_adds_no_lean():
    payload = probe_payload()
    decision = classify(payload["scan"], payload["lean"])
    assert decision["classification"] == CLASS_CLOSED
    assert payload["scan"]["slogan_false"] is True
    assert payload["scan"]["k24"]["p_min"] == 304
    assert payload["scan"]["k18"]["p_min"] == 3075
    assert payload["scan"]["killing_p"]["six_fifths"] == 659
    assert payload["scan"]["killing_p"]["inv_sum"] == 367
    assert payload["anti_overclaim"]["halt_theorem"] is False
    assert payload["anti_overclaim"]["new_lean"] is False
    assert payload["anti_overclaim"]["floor_raise"] is False
    assert payload["anti_overclaim"]["leftover_word_census"] is False
    assert payload["lean"]["sorry_free"] is True
    assert payload["lean"]["no_ceiling_lean"] is True
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
        REPO / "docs" / "problems" / "juggler_cycle_ceiling_finance.md"
    ).read_text(encoding="utf-8")
    paper = (REPO / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**CLOSE**" in dossier
    assert "juggler_ceiling_finance_leftover_killer" in dossier
    assert "even_iter_lt_succ_pow" in dossier
    assert "CycleCeilingFinance" not in paper
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    get_reference("simons-de-weger-2005-collatz-m-cycles")
    rec = get_conjecture("juggler_ceiling_finance_leftover_killer")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]
    lean = lean_api_present()
    assert lean["cycle_extrema_present"] is True
