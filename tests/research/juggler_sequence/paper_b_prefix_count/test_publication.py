"""Historical Paper B prefix audit: publication."""
from __future__ import annotations
import io
import re
import pytest
from research.juggler_sequence import paper_b_prefix_count as B

from .helpers import (
    DEPENDENTS,
    PAPER,
    ROOT,
)


def test_paper_quotes_the_table_this_module_computes() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    body = text[text.index("**Proposition 7.1"):text.index("Sections 3–5 prove")]
    rows = {r["d"]: r for r in B.table(24)}
    for d in (4, 5, 6, 8, 12, 16, 24):
        row = re.search(r"^\| \\\(%d\\\) \| \\\((\d+)\\\) \| \\\((\d+)\\\)" % d, body, re.MULTILINE)
        assert row, d
        assert int(row.group(1)) == rows[d]["N_d"], d
        assert int(row.group(2)) == rows[d]["endpoint_only"], d


@pytest.mark.parametrize("rel,role", sorted(DEPENDENTS.items()))
def test_dependents_state_the_exact_count(rel: str, role: str) -> None:
    """Five documents restate Proposition 7.1; the improvement has to reach all of them.

    The old closed form is still true -- Hoeffding remains valid and is kept as the bound on
    ``N_d`` -- so this is staleness, not error.  It is exactly the drift that a grep found once
    and would find again, which is why it is a test.
    """
    text = io.open(ROOT / rel, encoding="utf-8").read()
    assert "N_d" in text, (rel, role)
    for stale in ("2^d E_d(N)", "2^dE_d(N)", r"2^d E_d(N)", r"2^dE_d(N)"):
        assert stale not in text, (rel, stale)


def test_rendered_ledger_is_not_stale() -> None:
    """theorem_ledger.md is generated; the JSON edit has to be re-rendered."""
    import subprocess
    import sys

    r = subprocess.run([sys.executable, str(ROOT / "tools" / "render_theorem_ledger.py"),
                        "--check"], capture_output=True, text=True, cwd=ROOT)
    assert r.returncode == 0, r.stdout + r.stderr


def test_both_ledger_rows_cite_this_regression() -> None:
    import json

    rows = json.load(io.open(ROOT / "docs" / "theory" / "theorem_ledger.json", encoding="utf-8"))
    by_id = {r["id"]: r for r in rows}
    for rid in ("J-equidistribution-implies-density-one", "J-rate-free-density-one"):
        assert any("paper_b_prefix_count" in t for t in by_id[rid]["tests"]), rid


@pytest.mark.parametrize("d,o_rooted,surviving", [
    (5, 16, 4), (8, 128, 19), (16, 32768, 2114), (24, 8388608, 286581),
])
def test_the_remark_quantifies_what_is_not_used(d: int, o_rooted: int, surviving: int) -> None:
    """The proof needs N_d classes, not the 2^(d-1) an equidistribution statement covers."""
    assert 2 ** (d - 1) == o_rooted
    assert B.non_contracting(d) == surviving
    text = io.open(PAPER, encoding="utf-8").read()
    remark = text[text.index("The name of the proposition"):text.index("The exact count is worth")]
    assert str(surviving) in remark, surviving
    assert str(o_rooted) in remark, o_rooted


def test_only_two_standing_conditions_are_hypotheses() -> None:
    """(C3) and (C4) cap k, h_1, h_2 each at P^(1/24); (C1) and (C2) follow.

    (C1) is exactly the product of the three caps, tight at k = h_1 = h_2 = P^(1/24).
    (C2) needs only P >= 3^(12/5) = 14.  So an invocation verifies two inequalities, not four,
    and the lemma statements say so.
    """
    from fractions import Fraction as F

    cap = F(1, 24)
    assert cap * 3 == F(1, 8)                      # (C1), with equality
    assert cap * 2 == F(1, 12) and F(1, 12) < F(1, 2)
    assert abs(3 ** (12 / 5) - 14.0) < 0.1         # where (C2) starts to hold

    text = io.open(PAPER, encoding="utf-8").read()
    assert "Assume (C3) and (C4), write" in text          # Lemma 5.2
    assert r"Assume (C3) and (C4), \(j=0\)" in text       # Lemma 5.2b
    assert "(C1)\u2013(C4)" not in text and "(C1)--(C4)" not in text
    assert "checking two inequalities, not four" in text


def test_decoration_budget_is_a_ceiling_not_a_count() -> None:
    """Claim E forms five terms; Step 4's leftovers add two; the class allows nine.

    The number is never used quantitatively -- it appears only in the class definition and in
    the sentence that records the true maximum -- so the ceiling is documentation, not an
    estimate anything depends on.
    """
    text = io.open(PAPER, encoding="utf-8").read()
    assert "at most nine terms" in text                 # the class definition
    assert "seven is the largest decoration this paper forms" in text
    assert "not a count that is" in text
    # the number is documentation: it occurs as the ceiling and as the note, nowhere else
    # (the third "nine" in the paper is "nine orders of magnitude", a different subject)
    assert text.count("budget of nine") == 1
    assert text.count("at most nine terms") == 1
