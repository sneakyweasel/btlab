"""The Paper B constants sweep, as a regression.

A comparison of two powers whose exponents differ by `g`, carrying a constant `c`, does not
hold until `P >= c^(1/g)`.  A gap of `1/36` turns a constant of `2.52` into `2.8e14`; a gap of
`4/96` turns `10.25` into `1.8e24`.  Both defects this sweep found were of that shape, and so
were the two found earlier in Theorem 6.3.  This test keeps the manuscript free of new ones.
"""

from __future__ import annotations

from research.juggler_sequence import p0_certificate as C
from research.juggler_sequence import paper_b_constants_sweep as S


def test_claim_D_would_have_been_the_binding_row() -> None:
    """The sweep found Claim D carrying 16 P^(1/24); the fix was to carry 3 P^(1/24).

    With the loose bound the row is 16^12 = 2.8e14 and binds; with the sharp one it is
    3^12 = 5.3e5 and the Lemma 3.9 balance binds again at 8.9e13.
    """
    cert = C.certificate()
    assert cert["binding"]["tag"] == "5b-W<=c7S"
    assert 8.9e13 < cert["P0"] < 9.0e13
    loose, sharp = 16.0**12, 3.0**12
    assert loose > cert["P0"] * 3            # would have raised P_0 by over 3x
    assert sharp < cert["P0"] / 1e7          # as carried, it is nowhere near binding
    row = {r["tag"]: r["P_min"] for r in cert["thresholds"]}["claimD-shift"]
    assert sharp <= row < 1e6


def test_the_loose_bound_fails_at_P0_and_the_sharp_one_holds() -> None:
    """At 8.95e13 the loose constant misses by 3%; the sharp one clears by 60%."""
    P0 = 8.9458e13
    assert 2.52 * P0 ** (7 / 72) > P0 ** (1 / 8)      # loose: fails
    assert 1.45 * P0 ** (7 / 72) <= P0 ** (1 / 8)     # sharp: holds
    assert 2.4 < P0 ** (1 / 36) < 2.45                # the miss is only 3%


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
    # Shape B is clean: since Claim D carries |t| <= 3 P^(1/24), no printed containment of one
    # power in another hides a constant above P_0.
    assert bad_b == [], bad_b
    # Shape A flags exactly one term, and its target is not a margin: Theorem 6.3's per-point
    # flat cost 11 P^(-11/96) is never compared to 1/4 -- it is multiplied by the block length
    # and compared to P^(1-1/96), which is the probe's t63-flat row at 5.5e9.
    assert sorted({b[1] for b in bad_a}) == [11.0], bad_a


def test_findings_are_recorded() -> None:
    f = {x["site"]: x for x in S.findings()}
    assert abs(f["Claim D"]["threshold"] - 2.52**36) < 1e6
    assert abs(f["Thm 5.3 St.3(a)"]["threshold"] - 23.0**12) < 1e10
