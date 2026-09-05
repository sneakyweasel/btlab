"""The exact non-contracting count of Proposition 7.1, and Proposition 7.4's arc count.

Proposition 7.1 bounded the number of length-d words with no contracting prefix by Hoeffding
applied to the endpoint.  Two things were given away: the prefix constraint itself, and the
local-limit factor.  The count is a dynamic program over ``(t, o_t)``, so the exact number is
available; these tests check it against the paper's own figures and against the closed form it
replaces.
"""

from __future__ import annotations

import io
import math
import re
from pathlib import Path

import pytest

from research.juggler_sequence import paper_b_prefix_count as B

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"


def surviving_words(d: int) -> list[str]:
    out: list[str] = []

    def rec(w: str, o: int, t: int) -> None:
        if t == d:
            out.append(w)
            return
        for ch, s in (("O", 1), ("E", 0)):
            if B.survives(t + 1, o + s):
                rec(w + ch, o + s, t + 1)

    rec("", 0, 0)
    return out


# --- the count itself ---


def test_count_agrees_with_direct_enumeration() -> None:
    for d in range(1, 15):
        assert B.non_contracting(d) == len(surviving_words(d)), d


def test_depth_five_reproduces_corollary_6_4() -> None:
    """The four survivors give certificate density 7/8, which Corollary 6.4 reaches by
    counting contractors rather than words.  Two of the four are the open OOOO* split."""
    words = surviving_words(5)
    assert words == ["OOOOO", "OOOOE", "OOOEO", "OOEOO"]
    assert 1 - len(words) / 2 ** 5 == 7 / 8
    assert sum(1 for w in words if w.startswith("OOOO")) == 2


def test_depth_six_buys_nothing_without_depth_five() -> None:
    """All eight children of the depth-five survivors survive, so the density is 7/8 again."""
    assert B.non_contracting(6) == 8
    assert 1 - 8 / 2 ** 6 == 7 / 8


def test_every_e_rooted_word_contracts_immediately() -> None:
    """The step the proposition opens with: 3^0 < 2."""
    for d in range(1, 12):
        assert all(w.startswith("O") for w in surviving_words(d))


# --- the closed form it replaces is still a valid bound, and how lossy ---


def test_hoeffding_is_an_upper_bound_at_every_depth() -> None:
    for d in range(1, 41):
        assert B.non_contracting(d) <= B.hoeffding_bound(d), d


def test_two_losses_compound_and_neither_touches_the_rate() -> None:
    rows = {r["d"]: r for r in B.table(40)}
    # loss 1: dropping the prefix constraint
    assert abs(rows[5]["endpoint_only"] / rows[5]["N_d"] - 1.50) < 0.01
    assert abs(rows[24]["endpoint_only"] / rows[24]["N_d"] - 4.44) < 0.01
    # both together
    for d, want in ((5, 6.7), (10, 11.4), (40, 43.6)):
        got = rows[d]["density_hoeffding"] / rows[d]["density_exact"]
        assert abs(got - want) < 0.1, (d, got)
    # the exponential rate is essentially unchanged
    assert abs(2 * B.chernoff_rate() - 1.9318) < 5e-4
    assert abs(2 * math.exp(-B.HOEFFDING_C) - 1.9326) < 5e-4
    assert 2 * B.chernoff_rate() < 2 * math.exp(-B.HOEFFDING_C)
    # and N_d is far below its own asymptote in the operative range
    assert abs(rows[40]["N_d"] ** (1 / 40) - 1.7586) < 1e-3


def test_the_discarded_factor_is_polynomial_of_order_three_halves() -> None:
    """``N_d/2^d ~ C rho^d d^(-3/2)`` with ``C`` about 11.

    That exponent is the content of the improvement: ``d^(-1/2)`` for staying nonnegative
    under the zero-drift tilt, and a further ``d^(-1)`` because the tilted endpoint sits at
    height ``~sqrt(d)`` rather than at the origin.  The test is that the sequence converges;
    a wrong exponent would make it drift by a power of ``d``.
    """
    c = B.meander_constant((400, 800, 1600))
    assert all(8 < x < 13 for x in c), c
    assert c == sorted(c), c                       # increasing towards its limit
    assert (c[2] - c[1]) < (c[1] - c[0])           # and the increments are shrinking


def test_observed_rate_matches_the_theorem_ledger() -> None:
    """The ledger records this count independently at d = 200; the two agree.

    Row ``J-rate-free-density-one`` states "never-negative word count C_200/2^200 = 3.06e-6
    (empirical rate 0.0635/letter, Hoeffding majorizes at 0.0343)".  Both numbers are the
    polynomial factor at work, not a different exponential rate.
    """
    assert abs(B.non_contracting(200) / 2 ** 200 - 3.06e-6) < 0.01e-6
    assert abs(B.observed_rate(200) - 0.0635) < 5e-5
    for d, want in ((24, 0.1696), (1600, 0.0401)):
        assert abs(B.observed_rate(d) - want) < 5e-4, d
    # monotone decrease towards the asymptote, never below it
    rates = [B.observed_rate(d) for d in (24, 50, 100, 200, 400, 800, 1600)]
    assert rates == sorted(rates, reverse=True)
    assert rates[-1] > -math.log(B.chernoff_rate())


def test_error_term_improvement_is_the_same_factor() -> None:
    """Proposition 7.1's error term carries N_d, not 2^d."""
    for d, factor in ((5, 8.0), (16, 31.0)):
        assert abs(2 ** d / B.non_contracting(d) - factor) < 0.05, d


# --- Proposition 7.4: two arcs on the circle, not three ---


@pytest.mark.parametrize("seed", [0, 1, 2])
def test_off_diagonal_integral_obeys_the_two_arc_bound(seed: int) -> None:
    """``A{x+l} - B{y+l}`` has three pieces on [0,1) but two arcs on the circle.

    The first and last pieces carry the same linear branch -- their constants differ by
    exactly the slope -- so the bound is ``2/(pi|A-B|)``, not ``3/(pi|A-B|)``.
    """
    import numpy as np

    rng = np.random.default_rng(seed)
    n = 200_000
    lam = (np.arange(n) + 0.5) / n
    worst = 0.0
    for _ in range(40):
        a, b = rng.uniform(-500, 500, 2)
        if abs(a - b) < 1:
            continue
        x, y = rng.random(2)
        phase = a * ((x + lam) % 1.0) - b * ((y + lam) % 1.0)
        worst = max(worst, abs(np.exp(2j * np.pi * phase).mean()) * abs(a - b))
    assert worst <= 2 / math.pi + 1e-3, worst


def test_paper_quotes_the_table_this_module_computes() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    body = text[text.index("**Proposition 7.1"):text.index("Sections 3–5 prove")]
    rows = {r["d"]: r for r in B.table(24)}
    for d in (4, 5, 6, 8, 12, 16, 24):
        row = re.search(r"^\| \\\(%d\\\) \| \\\((\d+)\\\) \| \\\((\d+)\\\)" % d, body, re.MULTILINE)
        assert row, d
        assert int(row.group(1)) == rows[d]["N_d"], d
        assert int(row.group(2)) == rows[d]["endpoint_only"], d


def test_paper_no_longer_states_the_old_constants() -> None:
    text = io.open(PAPER, encoding="utf-8").read()
    assert r"e^{-cd}\,N+2^dE_d(N)" not in text
    assert r"\frac6\pi" not in text
    assert r"most three arcs" not in text
    assert r"Neither loss touches the" not in text


# --- the change has to reach every document that restates the proposition ---


DEPENDENTS = {
    "docs/theory/theorem_ledger.json": "the canonical row",
    "docs/theory/theorem_ledger.md": "rendered from the JSON",
    "docs/theory/juggler_cycle_itinerary_structure_note.md": "imports it as Proposition 6.1",
    "docs/problems/juggler_k3_rate_free.md": "derives the rate-free reduction from it",
    "docs/research/juggler_two_step_parity_lemma.md": "the source note",
}


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
