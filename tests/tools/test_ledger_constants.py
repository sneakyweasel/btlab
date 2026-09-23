"""Decimals written into the ledger must match the constants they name.

The ledger is prose, and prose carries numbers by hand. On 20 September 2026
`J-paper-b-sturmian-zero-law-is-the-empty-window` was found recording
`rho = 0.9659065532355213`, wrong from the twelfth significant digit. The
code was never wrong -- `chernoff_rate()` returns the right value and so does
plain double precision -- so it was a transcription, which is exactly the
kind of error no computational gate sees.

This scans the ledger for long decimals, matches each against the closed-form
constants of this cluster, and requires that a match be a correct rounding or
truncation of the true value.
"""

from __future__ import annotations

from research.claims import load_claims
import re
from pathlib import Path

from mpmath import log, mp, mpf, power

REPO = Path(__file__).resolve().parents[2]
LEDGER = REPO / "docs" / "theory" / "theorem_ledger.json"

mp.dps = 40

BETA = log(2) / log(3)
ENTROPY = -(BETA * log(BETA, 2) + (1 - BETA) * log(1 - BETA, 2))

#: Closed-form constants this cluster quotes by name.
CONSTANTS = {
    "beta = log2/log3": BETA,
    "lambda = log2 3": 1 / BETA,
    "eta (Lagarias Theorem D)": 1 - ENTROPY,
    "theta = rho (survivor rate)": power(BETA, -BETA) * power(1 - BETA, BETA - 1) / 2,
    "H(beta)": ENTROPY,
    "gamma = H(beta)/beta": ENTROPY / BETA,
    "c = eta/beta": (1 - ENTROPY) / BETA,
    "log2(3/2)": log(mpf(3) / 2, 2),
}

#: Decimals that sit near one of the above and are a DIFFERENT quantity.
#: Each needs saying why, because "it is something else" is also what a typo
#: looks like from the outside.
NEAR_MISSES = {
    "0.584967": (
        "the tail ratio (1-s)/s at the RATIONAL slope s = 306/485, which is "
        "179/306 = 0.5849673. At the exact slope BETA the same quantity is "
        "1/BETA - 1 = log2(3/2) = 0.5849625, hence the near match. Different "
        "barrier, correctly computed -- see "
        "J-tail-spectral-gap-closes-like-one-over-root-q."
    ),
    "1.5849625007211563": (
        "Hikawa's own float literal for LAMBDA, quoted verbatim from his "
        "toolkit in J-hikawa-september-preprint-located. Not this "
        "laboratory's value and not to be silently corrected."
    ),
}

#: Decimals quoted BECAUSE they are wrong. This laboratory's convention is to
#: leave a corrected value visible next to its correction rather than silently
#: overwrite it, so the gate needs a name for "yes, that is the bad number, on
#: purpose". Each entry says which correction it belongs to.
QUOTED_AS_WRONG = {
    "0.9659065532355213": (
        "the value J-paper-b-sturmian-zero-law-is-the-empty-window recorded "
        "for rho before 20 September 2026, kept as the subject of its own "
        "correction."
    ),
    "0.9659065532530513": (
        "1/(1.0352968376), computed in that same correction to rule it out as "
        "the provenance of the wrong digits. Quoted to be rejected."
    ),
}

#: How close a decimal must be to a constant before we hold it to that
#: constant's digits. Wide enough to catch a wrong digit, narrow enough that
#: unrelated quantities are not dragged in.
CLAIM_WINDOW = mpf(10) ** -5


def _agrees(literal: str, true: "object") -> bool:
    """True if `literal` is a correct rounding OR truncation of `true`."""
    places = len(literal.split(".")[1])
    value = mpf(literal)
    if abs(value - true) <= mpf(10) ** (-places) / 2 * mpf("1.0001"):
        return True
    # a truncation is also honest: 0.630929753 for 0.6309297535...
    return abs(value - true) < mpf(10) ** (-places)


#: `theorem_ledger.md` is rendered FROM the json, so scanning both would
#: report every finding twice and make the exception lists look twice as long
#: as the problem.
RENDERED = {"theorem_ledger.md"}


def _ledger_decimals() -> list[tuple[str, str]]:
    rows = load_claims(REPO).entries
    out = []
    for row in rows:
        for match in re.finditer(r"(?<![\d.])(\d\.\d{6,}|0\.\d{6,})", row["statement"]):
            out.append((match.group(1), row["id"]))
    return out


def _manuscript_decimals() -> list[tuple[str, str]]:
    """The same scan over the prose manuscripts, which face a referee.

    Clean when this was written, on 20 September 2026 -- the only hits in
    `docs/theory` were the rendered ledger's copies of the four cases already
    classified below. The gate exists to keep it that way, since a constant
    mistyped in a manuscript is read by someone who will check it.
    """
    out = []
    for path in sorted((REPO / "docs" / "theory").glob("*.md")):
        if path.name in RENDERED:
            continue
        text = path.read_text(encoding="utf-8")
        for match in re.finditer(r"(?<![\d.])(\d\.\d{6,}|0\.\d{6,})", text):
            out.append((match.group(1), path.name))
    return out


def test_ledger_decimals_match_the_constants_they_name() -> None:
    """A decimal near a named constant must be that constant's digits.

    Covers the ledger json and every prose manuscript under `docs/theory`.
    """
    wrong = []
    for literal, row_id in _ledger_decimals() + _manuscript_decimals():
        if literal in NEAR_MISSES or literal in QUOTED_AS_WRONG:
            continue
        value = mpf(literal)
        for name, true in CONSTANTS.items():
            if abs(value - true) < CLAIM_WINDOW:
                if not _agrees(literal, true):
                    wrong.append(
                        f"    {row_id}: {literal} claims {name}, "
                        f"true {mp.nstr(true, len(literal) + 2)}"
                    )
                break
    assert not wrong, (
        "decimal(s) in the ledger disagree with the constant they name:\n"
        + "\n".join(wrong)
        + "\n\nFix the digits, or add the literal to NEAR_MISSES with the "
        "reason it is a different quantity."
    )


def test_the_corrected_rho_stays_corrected() -> None:
    """The specific value this gate was written for."""
    rows = load_claims(REPO).entries
    row = next(
        r for r in rows if r["id"] == "J-paper-b-sturmian-zero-law-is-the-empty-window"
    )
    assert "0.9659065532355213" in row["statement"]  # kept, as the correction's subject
    assert "0.96590655323343772361" in row["statement"]
    assert "CORRECTED 2026-09-20" in row["statement"]


def test_near_misses_are_still_near_and_still_misses() -> None:
    """An entry that stops being near, or becomes correct, should be removed."""
    stale = []
    for literal, reason in NEAR_MISSES.items():
        value = mpf(literal)
        near = [n for n, t in CONSTANTS.items() if abs(value - t) < CLAIM_WINDOW]
        if not near:
            stale.append(f"{literal}: no longer near any constant")
        elif all(_agrees(literal, CONSTANTS[n]) for n in near):
            stale.append(f"{literal}: now agrees with {near}, so it is not a miss")
    assert not stale, stale
