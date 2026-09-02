"""L-envelope versus long odd runs from T_L(n)."""

from __future__ import annotations

import json

from research.juggler_sequence.k5_post_l_ooe import WORD_W5
from research.juggler_sequence.oneshot_recovery import L_DEN, L_NUM, WORD
from research.juggler_sequence.parity_persist import LONG_RUN
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.l_odd_run_cap import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    l_envelope_never_drops,
    l_odd_run_compose_drops,
    lean_api_present,
    render_markdown,
    run_probe,
    slack,
    write_artifacts,
)


def test_envelope_never_drops():
    assert L_NUM == 2187
    assert L_DEN == 2048
    assert 2187 > 2048
    for k in range(17):
        assert l_odd_run_compose_drops(k) is False, k
        assert slack(k) > 0, k
        assert L_NUM * (3**k) > L_DEN * (1 << k)
    assert slack(0) == 139
    assert l_envelope_never_drops() is True


def test_33391_still_k5_not_w5():
    from research.juggler_sequence.cycle_itinerary import follows_itinerary

    assert follows_itinerary(LONG_RUN["n"], WORD)
    assert follows_itinerary(LONG_RUN["n"], WORD_W5) is False
    from research.juggler_sequence.parity_persist import l_row

    row = l_row(LONG_RUN["n"])
    assert row is not None
    assert row["run"] == 5


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["gaps"]["never_drops"] is True
    assert scan["gaps"]["drop0"] is False
    assert scan["long_run"]["run"] == 5
    assert scan["word_census"] is False
    assert scan["new_power_cell"] is False
    assert scan["p_adic_system"] is False


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
    assert CLASS_PARK in text
    assert "2187" in text
    from research.juggler_sequence.l_odd_run_cap import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_l_odd_run_cap"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["envelope_caps_k"] is False
    assert data["anti_overclaim"]["k_unbounded"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_l_odd_run_cap.md").read_text(
        encoding="utf-8"
    )
    parent = (repo / "docs" / "problems" / "juggler_parity_persist.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "2187" in dossier
    assert "juggler_l_odd_run_cap" in parent
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note
