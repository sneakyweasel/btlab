"""The Paper B constants sweep, as a regression.

A comparison of two powers whose exponents differ by `g`, carrying a constant `c`, does not
hold until `P >= c^(1/g)`.  A gap of `1/36` turns a constant of `2.52` into `2.8e14`; a gap of
`4/96` turns `10.25` into `1.8e24`.  Both defects this sweep found were of that shape, and so
were the two found earlier in Theorem 6.3.  This test keeps the manuscript free of new ones.
"""

from __future__ import annotations

from research.juggler_sequence import p0_certificate as C
from research.juggler_sequence import paper_b_constants_sweep as S


def test_claim_D_is_the_binding_row() -> None:
    """The sweep's headline finding: P_0 is set by Claim D, not by the Lemma 3.9 balance."""
    cert = C.certificate()
    assert cert["binding"]["tag"] == "claimD-shift"
    assert abs(cert["P0"] - 2.52**36) / cert["P0"] < 1e-6
    assert 2.8e14 < cert["P0"] < 2.9e14


def test_claim_D_fails_at_the_superseded_P0() -> None:
    """It misses by 3% at 8.95e13 -- which is why an obsolete comparison hid it."""
    old = 8.9458e13
    assert 2.52 * old ** (7 / 72) > old ** (1 / 8)
    assert old ** (1 / 36) < 2.52
    assert 2.4 < old ** (1 / 36) < 2.45


def test_step_3a_flat_cost_is_inside_the_right_budget() -> None:
    """23 P^(19/24) is inside P^(23/24) from 1.5e8, and not inside P^(7/8) until 2.2e16."""
    assert 23.0**6 < 1.5e8
    assert 23.0**12 > 2.1e16
    P0 = C.certificate()["P0"]
    assert 23 * P0 ** (19 / 24) <= P0 ** (23 / 24)
    assert 23 * P0 ** (19 / 24) > P0 ** (7 / 8)          # the superseded claim is false at P_0


def test_sweep_finds_nothing_new_above_P0() -> None:
    """Shape A is clean; shape B flags only Claim D, which is P_0 by definition."""
    import io
    import re

    lines = io.open(S.PATH, encoding="utf-8").read().split("\n")
    bad_a, bad_b = [], []
    for i, line in enumerate(lines):
        ts = S.terms_with_pos(line)
        ctx = " ".join(lines[max(0, i - 2): i + 3])
        for k, (c, e, st, en, s) in enumerate(ts):
            if c > 1.0 and e < 0 and re.search(r"dominated|inside|to0|o\(1\)|negligible", ctx):
                if (c / 0.25) ** (1 / float(-e)) > S.P0:
                    bad_a.append((i + 1, c, str(e)))
            if c <= 1.0:
                continue
            for (c2, e2, st2, en2, _s) in ts[k + 1:]:
                if not S.CMP.search(s[en:st2]):
                    continue
                if c2 != 1.0 or e2 <= e or float(e2 - e) > 0.5:
                    break
                if c ** (1 / float(e2 - e)) > S.P0:
                    bad_b.append((i + 1, c, str(e), str(e2)))
                break
    assert sorted({b[1] for b in bad_a}) == [], bad_a
    assert sorted({b[1] for b in bad_b}) == [2.52], bad_b   # Claim D only, and that row IS P_0


def test_findings_are_recorded() -> None:
    f = {x["site"]: x for x in S.findings()}
    assert abs(f["Claim D"]["threshold"] - 2.52**36) < 1e6
    assert abs(f["Thm 5.3 St.3(a)"]["threshold"] - 23.0**12) < 1e10
