"""The architecture table before Theorem 5.3 must keep agreeing with the proof.

A map that has drifted from the territory is worse than no map, and this one is the first
thing a referee will read.  So every component it names has to exist, every exponent it quotes
has to appear in the step that produces it, and its claim about which inequality binds P_0 has
to match what the certificate computes.
"""

from __future__ import annotations

import io
import re
from pathlib import Path

import pytest

from research.juggler_sequence import p0_certificate as P0

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"
MIRROR = ROOT / "juggler_review" / "juggler_parity_discrepancy_note.md"


def text() -> str:
    return io.open(PAPER, encoding="utf-8").read()


def table() -> str:
    src = text()
    start = src.index("### Architecture of the proof of Theorem 5.3")
    return src[start:src.index("**Theorem 5.3 (kernel cancellation).**", start)]


def proof() -> str:
    """Theorem 5.3's statement and proof, which the table describes."""
    src = text()
    start = src.index("**Theorem 5.3 (kernel cancellation).**")
    return src[start:src.index("## 5. Depth-four equidistribution", start)]


def test_table_sits_immediately_before_the_theorem() -> None:
    src = text()
    assert src.index("### Architecture of the proof of Theorem 5.3") < \
        src.index("**Theorem 5.3 (kernel cancellation).**")


@pytest.mark.parametrize("component", [
    "Lemma 5.1(i)", "Lemma 5.1(ii)", "Lemma 5.1(iii)", "Lemma 5.1(iv)",
    "Lemma 5.2(i)", "Lemma 5.2(ii)", "Lemma 5.2b", "Lemma 3.9", "Lemma 3.7", "Lemma 3.3",
])
def test_every_component_named_in_the_table_exists(component: str) -> None:
    """The table may only point at statements the paper actually makes."""
    assert component in table(), component
    label = component.split("(")[0].strip()
    assert re.search(r"\*\*%s" % re.escape(label), text()), label


@pytest.mark.parametrize("step", ["Step 1", "Step 2", "Step 3", "Step 4", "Step 5a",
                                  "Step 5b", "Step 6"])
def test_every_step_named_in_the_table_exists_in_the_proof(step: str) -> None:
    assert step in table(), step
    bare = step.replace("Step 5a", "(5a)").replace("Step 5b", "(5b)")
    assert bare in proof() or ("*%s (" % step) in proof(), step


@pytest.mark.parametrize("quantity,where", [
    (r"P^{1-1/96+\varepsilon}", "the theorem's own exponent"),
    (r"P^{23/24+\varepsilon}", "the wave-piece bottleneck"),
    (r"P^{15/16+\varepsilon}", "Step 5b's output"),
    ("H_1=P^{1/48}", "Step 1's first shift range"),
    ("H_2=P^{1/24}", "Step 1's second shift range"),
    ("J_2=P^{1/24}", "the carry truncation of Step 3"),
])
def test_quantities_quoted_by_the_table_appear_in_the_proof(quantity: str, where: str) -> None:
    assert quantity in table(), (quantity, where)
    assert quantity in proof(), (quantity, where)


def test_curvature_ranges_match_the_steps_they_come_from() -> None:
    """The two anchor curvature scales are the axis Step 5 classifies on."""
    t, pr = table(), proof()
    for scale in (r"[1.30,1.43]k\lvert j\rvert P^{-1/8}", r"[0.35,2.6]\,kh_1h_2P^{-5/8}"):
        assert scale.replace(" ", "") in t.replace(" ", ""), scale
    assert r"[1.30,\,1.43]\,k|j|P^{-1/8}" in pr
    assert r"[0.35,\,2.6]\,kh_1h_2P^{-5/8}" in pr


def test_step_5b_regimes_match_the_proof() -> None:
    t, pr = table(), proof()
    for cond in (r"60\mu\le\lambda_0", r"\mu\ge60\lambda_0"):
        assert cond in t, cond
        assert cond in pr, cond
    assert "anchor-dominant" in t and "mode-dominant" in t and "middle band" in t


def test_the_binding_site_claim_matches_the_certificate() -> None:
    """The table says P_0 binds at Step 5b's W <= c_7 S/2; the certificate must agree."""
    binding = P0.certificate()["binding"]
    assert "5b" in binding["tag"] and "c7S" in binding["tag"], binding
    t = table()
    assert r"W\le c_7S/2" in t
    assert "Step 5b" in t and "middle band" in t
    assert "c_7=1/232" in t


def test_the_table_states_where_the_exponent_is_inherited_from() -> None:
    """1/96 = (1/4)(1/24) traces to Lemma 5.2(ii)'s 23/24, and the proof says so too."""
    t = table()
    assert r"\tfrac1{96}" in t and r"\tfrac1{24}" in t
    assert "Lemma 5.2(ii)" in t
    assert "depth-2 strength" in t and "depth-2 strength" in proof()


def test_c5_dependency_is_stated_in_the_table() -> None:
    """(C5) is not implied by (C1)-(C4); the table says which step discharges it."""
    t = table()
    assert "(C5)" in t
    assert "does *not* follow from (C1)–(C4)" in t or "not implied by (C1)" in t
    assert r"\mu\le60\lambda_0" in t


def test_mirror_carries_the_table() -> None:
    assert text() == io.open(MIRROR, encoding="utf-8").read()
