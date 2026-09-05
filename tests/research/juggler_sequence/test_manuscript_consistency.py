"""Cross-document consistency for Papers A, B and C.

Every defect found in several iterations of work on these papers was the same species: a change
to a manuscript that silently invalidated prose elsewhere.  Extending Theorem 5.8's window to
q_14 falsified an Appendix A row, a glossary entry, six passages in the reviewer packet, a
constant in the companion app, and -- worst -- a line in the app's NOT_CLAIMED list, which
asserted the opposite of the new text.  Replacing Proposition 7.1's Hoeffding step left five
documents restating the superseded bound.  None of it was covered by a test, because prose is
not executable.

These tests make that class checkable.  They do not verify mathematics; they verify that the
manuscripts, the certificates, the review materials and the app agree about the numbers they
all quote, and that each manuscript's own numbering is in document order.

The invariants that hold for every paper are parametrized over ``MANUSCRIPTS``; anything that
depends on one paper's content lives in its own section below.  Two lessons from earlier
versions of this file are worth keeping in view, because both were cases of a test being wrong
about the paper rather than the reverse.  Global uniqueness of item numbers fails, because
Paper A's Appendix D deliberately restates the Section 3 theorems above their proofs.  And "one
expression, one value" fails, because Paper B deliberately carries two readings of ``c_7``.
The invariants below are the narrower ones that actually hold.
"""

from __future__ import annotations

import io
import re
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from research.juggler_sequence import p0_certificate as P0
from research.juggler_sequence import paper_a_audit as A

ROOT = Path(__file__).resolve().parents[3]

PAPER = ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md"
MIRROR = ROOT / "juggler_review" / "juggler_finite_dynamics_note.md"
PACKET = ROOT / "juggler_review" / "juggler_finite_dynamics_reviewer_packet.md"
README = ROOT / "juggler_review" / "README.md"
FORMALIZATION = ROOT / "juggler_review" / "juggler_finite_dynamics_formalization.md"
APP_CONSTANTS = ROOT / "web" / "juggler-companion" / "src" / "juggler" / "constants.ts"
APP_CLAIMS = ROOT / "web" / "juggler-companion" / "src" / "content" / "claims.ts"
APP_GLOSSARY = ROOT / "web" / "juggler-companion" / "src" / "content" / "glossary.ts"

PAPER_B = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note.md"
MIRROR_B = ROOT / "juggler_review" / "juggler_parity_discrepancy_note.md"
LEDGER_B = ROOT / "docs" / "theory" / "paper_b_audit_ledger.md"
LEDGER_B_MIRROR = ROOT / "juggler_review" / "paper_b_audit_ledger.md"

PAPER_C = ROOT / "docs" / "theory" / "juggler_fate_almost_all_note.md"
MIRROR_C = ROOT / "juggler_review" / "juggler_fate_almost_all_note.md"

REVIEW_DOCS = [PACKET, README, FORMALIZATION]

ITEM = r"^\*\*(?:Theorem|Lemma|Corollary|Proposition|Conjecture|Remark|Claim) "


@dataclass(frozen=True)
class Manuscript:
    """A paper and the documents that must agree with it."""

    name: str
    path: Path
    mirror: Path
    ordered_sections: tuple[str, ...]
    """Sections whose items must appear in numeric order.

    Paper A's Section 3 is deliberately not among them: Lemma 3.21b states the canonical run
    form early, where it is used, and Lemma 3.21a states the case split late, next to
    Theorem 3.22.  Both are out of numeric order on purpose.
    """

    satellites: tuple[Path, ...] = field(default_factory=tuple)


MANUSCRIPTS = (
    Manuscript("A", PAPER, MIRROR, ("5",), (PACKET, README, FORMALIZATION)),
    Manuscript("B", PAPER_B, MIRROR_B, ("3", "4", "5", "6", "7"), (LEDGER_B,)),
    Manuscript("C", PAPER_C, MIRROR_C, tuple(str(k) for k in range(2, 11))),
)
IDS = [m.name for m in MANUSCRIPTS]


def read(p: Path) -> str:
    return io.open(p, encoding="utf-8").read()


SUFFIX = r"[a-z'′]?"
"""Two conventions for a companion item, both sorting after the bare number: a letter
(Paper B's Lemma 5.2b, Paper A's Remark 5.8a) and a prime (Paper C's Lemma 4.1')."""


def item_key(label: str) -> tuple[int, int, str]:
    m = re.match(r"(\d+)\.(\d+)(" + SUFFIX + r")", label)
    return int(m.group(1)), int(m.group(2)), m.group(3)


# --- invariants that hold for every manuscript ---


@pytest.mark.parametrize("ms", MANUSCRIPTS, ids=IDS)
def test_items_are_in_document_order(ms: Manuscript) -> None:
    """Regression: Propositions 5.15/5.16 once sat between Theorems 5.8 and 5.9 of Paper A."""
    text = read(ms.path)
    for sec in ms.ordered_sections:
        pat = ITEM + r"(" + re.escape(sec) + r"\.\d+" + SUFFIX + r")"
        found = re.findall(pat, text, re.MULTILINE)
        keys = [item_key(f) for f in found]
        assert keys == sorted(keys), (ms.name, sec, found)


@pytest.mark.parametrize("ms", MANUSCRIPTS, ids=IDS)
def test_every_numbered_item_is_unique_in_the_body(ms: Manuscript) -> None:
    """Uniqueness holds in the body only: Paper A's Appendix D deliberately restates the
    Section 3 theorems above their proofs, which is not a numbering defect."""
    text = read(ms.path)
    cut = text.find("## Appendix")
    body = text if cut < 0 else text[:cut]
    found = re.findall(ITEM + r"(\d+\.\d+" + SUFFIX + r")", body, re.MULTILINE)
    assert len(found) == len(set(found)), (ms.name, [f for f in found if found.count(f) > 1])


@pytest.mark.parametrize("ms", MANUSCRIPTS, ids=IDS)
def test_no_number_is_used_for_two_different_items(ms: Manuscript) -> None:
    """The real numbering invariant, given that appendices both restate and introduce.

    Paper A's Appendix D restates the Section 3 theorems above their proofs (same number, same
    title -- fine), and its Appendix C introduces Theorems 2.4-2.7 continuing Section 2's
    numbering (new number, not in the body -- also fine).  What must never happen is one number
    carrying two different titles.
    """
    pat = ITEM + r"(\d+\.\d+" + SUFFIX + r") \(([^)]*)\)"
    pairs = re.findall(pat, read(ms.path), re.MULTILINE)
    titles: dict[str, set[str]] = {}
    for num, title in pairs:
        titles.setdefault(num, set()).add(title.strip().rstrip("."))
    clashes = {n: t for n, t in titles.items() if len(t) > 1}
    assert not clashes, (ms.name, clashes)


@pytest.mark.parametrize("ms", MANUSCRIPTS, ids=IDS)
def test_review_mirror_matches_the_manuscript(ms: Manuscript) -> None:
    assert read(ms.path) == read(ms.mirror), f"{ms.name}: juggler_review mirror is stale"


@pytest.mark.parametrize("ms", MANUSCRIPTS, ids=IDS)
def test_no_mangled_latex_escapes(ms: Manuscript) -> None:
    """A tab in a manuscript is always a LaTeX escape eaten by a shell heredoc.

    Three got in this way and survived several revisions: `\\theta` in Paper A's Section 5,
    `\\to` in its Section 3, and `\\theta(L)` in the reviewer packet, each rendered as a literal
    tab plus the rest of the macro name.  No legitimate tab exists in these documents, so the
    check is exact rather than heuristic.
    """
    for doc in (ms.path, ms.mirror, *ms.satellites):
        bad = [i for i, line in enumerate(read(doc).splitlines(), 1)
               if any(c in line for c in MANGLED_ESCAPES)]
        assert not bad, (ms.name, doc.name, bad[:5])


#: control characters a non-raw Python string produces from a LaTeX macro.  AGENTS.md lists
#: the escape-initial letters as `a b f n r t v 0 x`; six of them land on a character that
#: cannot legitimately appear in these documents:
#:   \a -> BEL  (\approx, \alpha, \asymp)      \b -> BS   (\beta, \bigl)
#:   \f -> FF   (\frac)                        \t -> TAB  (\theta, \text, \to)
#:   \v -> VT   (\varepsilon, \varphi)         \0 -> NUL
#: `\n` and `\r` are not detectable this way -- both become line breaks, and Python's
#: universal-newline decoding erases the difference.  That gap is why the check is a floor
#: and not a proof.
MANGLED_ESCAPES = ("\a", "\b", "\f", "\t", "\v", "\0")

#: documents outside the manuscript set that carry the same LaTeX and the same hazard
OTHER_LATEX_DOCS = (
    ROOT / "AGENTS.md",
    ROOT / "docs" / "juggler_branch_ledger.md",
    ROOT / "docs" / "negative_knowledge.md",
    ROOT / "docs" / "theory" / "juggler_fate_contagion_note.md",
    ROOT / "docs" / "theory" / "juggler_flight_note.md",
    ROOT / "docs" / "theory" / "juggler_tao_reduction_note.md",
)


LEAN_LAYER = ROOT / "formal" / "Problems" / "Juggler"
TACTICS = ("native_decide", "decide +kernel", "norm_num")
_DECL = re.compile(r"^\s*(?:theorem|lemma|def)\s+([A-Za-z_][A-Za-z_0-9'.]*)", re.M)
_IMPORT = re.compile(r"^import Problems\.Juggler\.(\w+)", re.M)


def _lean_layer() -> tuple[dict[str, str], dict[str, str], dict[str, set[str]]]:
    """Module text, identifier -> defining module, and the intra-layer import graph."""
    text: dict[str, str] = {}
    decls: dict[str, str] = {}
    imports: dict[str, set[str]] = {}
    for p in LEAN_LAYER.glob("*.lean"):
        body = read(p)
        text[p.stem] = body
        imports[p.stem] = set(_IMPORT.findall(body))
        for name in _DECL.findall(body):
            decls.setdefault(name, p.stem)
    return text, decls, imports


def _import_closure(mod: str, imports: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = [mod]
    while stack:
        for m in imports.get(stack.pop(), ()):
            if m not in seen:
                seen.add(m)
                stack.append(m)
    return seen


def test_tactics_the_manuscripts_name_are_the_tactics_the_layer_uses() -> None:
    """A sentence naming both a tactic and a Lean identifier must be telling the truth.

    Converting 305 proofs from `native_decide` to `decide +kernel` silently invalidated
    sixteen sentences of Paper A, which went on describing the Section 3 finite tables as
    `native_decide` evaluations.  The cross-quotation guard could not see it: the drift was
    a method name, not a constant.  The tactic is looked for in the identifier's own module
    and in everything that module imports inside the layer, because the paper attributes an
    evaluation to the theorem that consumes it (`no_cycle_itinerary_oooeoe` in
    `LeftoverShort`) while the tactic sits in the module that performs it (`LeftoverEval`).
    """
    text, decls, imports = _lean_layer()
    bad: list[tuple[str, str, str, str]] = []
    checked = 0
    for doc in (PAPER, PAPER_B, PAPER_C):
        body = " ".join(read(doc).split())
        for sentence in re.split(r"(?<=\.)\s+", body):
            for tactic in TACTICS:
                if f"`{tactic}`" not in sentence:
                    continue
                for ident in re.findall(r"`([A-Za-z_][A-Za-z_0-9'.]*)`", sentence):
                    if ident in TACTICS or ident not in decls:
                        continue
                    mod = decls[ident]
                    scope = {mod} | _import_closure(mod, imports)
                    checked += 1
                    if not any(tactic in text[m] for m in scope):
                        bad.append((doc.name, tactic, ident, mod))
    assert checked >= 20, f"guard went blind: only {checked} claims matched"
    assert bad == [], bad[:8]


def test_no_mangled_latex_escapes_outside_the_manuscripts() -> None:
    """The same hazard, in the documents the per-manuscript check does not reach.

    AGENTS.md carried `L\\approx` as `L` + BEL for some time -- the very defect its own
    "LaTeX and Python strings" section warns about -- because the existing guard tested
    only for TAB and only on the three papers.
    """
    for doc in OTHER_LATEX_DOCS:
        if not doc.is_file():
            continue
        bad = [i for i, line in enumerate(read(doc).splitlines(), 1)
               if any(c in line for c in MANGLED_ESCAPES)]
        assert not bad, (doc.name, bad[:5])


# --- Paper A: the window, which is what actually drifted ---


def test_window_endpoint_agrees_everywhere() -> None:
    """The extended window must read the same in the paper, the review docs and the app."""
    hi = str(A.WINDOW_HI)
    assert hi in read(PAPER)
    for doc in REVIEW_DOCS:
        assert hi in read(doc), doc.name
    assert "WALK_WINDOW_HI = 16_785_921" in read(APP_CONSTANTS)


def test_no_document_still_quotes_the_old_window_as_the_window() -> None:
    """301994 is legitimate as q_13 and in the fan arithmetic, but not as a window endpoint."""
    bad = re.compile(r"\[\s*50508\s*,\s*301994\s*\)")
    for doc in [PAPER, MIRROR, PACKET, README, FORMALIZATION, APP_CLAIMS, APP_GLOSSARY]:
        assert not bad.search(read(doc)), doc.name


def test_contagion_exponent_quoted_by_paper_a_is_the_current_one() -> None:
    """Paper A quotes Paper C's exponent; it must be lambda**, not the superseded sweep root.

    ``block_average_plus_sweep`` (0.4051) was lambda** before the OE-fiber constant was
    sharpened from 1/7 to 1/3; ``block_average_plus_third`` (0.4480) replaced it, and the
    Tao rate threshold moved from 0.595 to 1 - lambda** = 0.552."""

    from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root

    lam = lambda_root(RECURSIONS["block_average_plus_third"])
    assert abs(lam - 0.4480) < 1e-3
    assert abs((1.0 - lam) - 0.5520) < 1e-3
    text = read(PAPER)
    assert "0.4480" in text and "0.448" in text
    assert "0.552" in text
    # the superseded pair must not appear as Paper C's exponent or as the rate threshold
    assert "0.4050" not in text
    assert re.search(r"\(\\log x\)\^\{0\.405\}", text) is None
    assert re.search(r"e>0\.595", text.replace(" ", "")) is None


@pytest.mark.parametrize(
    "regime,lam,rate,depth",
    [
        ("block_average_plus_third", 0.4480, 0.5520, 20),   # unconditional, lambda**
        ("block_third_plus_ooeee", 0.5392, 0.4608, 18),     # with Hypothesis L, lambda***
        ("depth_two_ideal", 0.4927, 0.5073, 19),            # the method's ideal ceiling
    ],
)
def test_rate_and_depth_pairs_quoted_anywhere_are_the_computed_ones(
    regime: str, lam: float, rate: float, depth: int
) -> None:
    """Any (rate, depth) pair a manuscript quotes must satisfy least_C(rate) == depth.

    The three regimes are the only ones the papers use: lambda** unconditional, lambda***
    under Hypothesis L, and the depth-two ideal ceiling.  Paper B's ``e>0.508, C>=19`` and
    Paper C's ``0.4608, C>=18`` and ``0.5520, C=20`` all sit on this invariant; pairing a
    rate from one regime with a depth from another would break it."""

    from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root
    from research.juggler_sequence.tao_reduction import least_C

    assert abs(lambda_root(RECURSIONS[regime]) - lam) < 1e-3
    assert abs((1.0 - lam) - rate) < 1e-3
    assert least_C(rate) == depth


def test_paper_a_pins_the_seed_sum_from_both_sides() -> None:
    """Section 6.1 states Corollary 4.4c as the floor beside the trivial cap."""

    text = read(PAPER)
    assert "6.83\\cdot10^{-5}" in text and "2.23\\cdot10^{-3}" in text
    assert "J-lachesis-basin-inverse-sum" in text


def test_window_covers_the_whole_fan() -> None:
    """The window's endpoint is exactly the last fan member: q_14 = L_55."""
    assert A.WINDOW_HI == A.fan_length(A.FAN_LEN - 1) == 16785921


@pytest.mark.parametrize("name,value", [
    ("PAPER_FLOOR", 1_000_000), ("PAPER_PERIOD", 25_781),
    ("LAB_FLOOR", 26_254_995), ("LAB_PARITY_PERIOD", 50_508),
    ("LAB_WALK_PERIOD", 176_251),
    ("PRINTED_FLOOR", 162_849_448), ("PRINTED_PERIOD", 478_245),
])
def test_app_constants_match_the_certificate(name: str, value: int) -> None:
    src = read(APP_CONSTANTS)
    m = re.search(rf"export const {name} = ([\d_]+);", src)
    assert m, name
    assert int(m.group(1).replace("_", "")) == value


def test_certified_floors_and_bounds_match_the_audit() -> None:
    """The four (floor, period) pairs the paper prints are the audit's FLOORS table."""
    pairs = {(n0, bound) for n0, bound, _site in A.FLOORS}
    assert (10**6, 25781) in pairs
    assert (26254995, 50508) in pairs
    # the paper writes floors in LaTeX (10^6, 26254995, ...), so match either form
    text = read(PAPER)
    for n0, _bound, _ in A.FLOORS:
        plain = str(n0)
        latex = "10^{%d}" % len(plain[1:]) if plain[0] == "1" and set(plain[1:]) == {"0"} else None
        assert plain in text or (latex and latex in text), n0


def test_fan_endpoints_quoted_in_the_paper() -> None:
    for k in (0, 1, 2):
        assert str(A.fan_length(k)) in read(PAPER)
    assert str(A.fan_length(55)) in read(PAPER)


def test_appendix_A_mentions_the_fan_law_module() -> None:
    """Regression: FanLaw.lean was registered and built but absent from Appendix A."""
    text = read(PAPER)
    appendix = text[text.index("## Appendix A"):]
    assert "FanLaw.lean" in appendix
    for name in ("fanLambda_affine", "fan_positive_iff", "fanLambda_55_pos"):
        assert name in appendix, name


# --- Paper B: the threshold P_0, quoted at two precisions, and the two readings of c_7 ---


def test_p0_agrees_between_the_certificate_the_manuscript_and_the_ledger() -> None:
    """The manuscript rounds to two significant figures, the audit ledger keeps five.

    Both must be roundings of what ``p0_certificate.certificate()`` actually computes; a change
    to the certificate that moves either rounding has to move the prose with it.
    """
    p0 = P0.certificate()["P0"]
    mantissa = p0 / 10 ** 13
    assert 1 <= mantissa < 10, p0
    assert f"P_0={mantissa:.1f}" + r"\cdot10^{13}" in read(PAPER_B)
    assert f"P_0={mantissa:.4f}" + r"\cdot10^{13}" in read(LEDGER_B)


def test_manuscript_quotes_p0_consistently_wherever_it_appears() -> None:
    """Every numeric occurrence of P_0 in Paper B is the same two-figure value."""
    quoted = set(re.findall(r"P_0\s*=\s*([\d.]+)\\cdot10\^\{(\d+)\}", read(PAPER_B)))
    assert quoted == {("8.9", "13")}, quoted


def test_binding_site_named_in_the_ledger_is_the_computed_one() -> None:
    """The ledger says P_0 binds at Step 5b's W <= c_7 S/2; the certificate must agree."""
    binding = P0.certificate()["binding"]
    assert "5b" in binding["tag"] and "c7S" in binding["tag"], binding
    assert r"W\le c_7S/2" in read(LEDGER_B)


def test_both_readings_of_c7_are_present_with_the_sentence_that_explains_them() -> None:
    """Paper B deliberately carries two values, so "one expression, one value" is not the
    invariant here.  The sharp constant 1/232 is the l-infinity operator norm of the Step 5b
    inverse and is what the P_0 appendix uses; 1/288 is the l-1 norm, a weaker value the proof
    of Step 5b keeps.  Both appear, and so must the sentence saying why -- otherwise the
    manuscript reads as self-contradictory.
    """
    text = read(PAPER_B)
    assert abs(P0.certificate()["c7"] - 1 / 232) < 1e-15
    assert r"c_7=1/232" in text and r"c_7=1/288" in text
    assert "we keep the" in text and "which remains valid" in text
    # the two consequent values of c_7/8, each with its own reading
    assert r"\tfrac1{1856}" in text and "1/2304" in text


def test_certificate_densities_agree_with_their_corollary_titles() -> None:
    """13/16 at depth four and 7/8 at depth five, in the titles and in the prose.

    Anchored on the corollary titles rather than on the bare fractions: Paper B also writes
    ``c_7/8`` and ``P^{7/8}``, so a substring test on "7/8" is meaningless.
    """
    text = read(PAPER_B)
    assert r"**Corollary 4.9 (certified-descent density \(13/16\)).**" in text
    assert r"**Corollary 6.4 (certified-descent density \(7/8\)).**" in text
    assert r"density \(13/16\) (Corollary 4.9)" in text
    assert r"density \(7/8\) (Corollary 6.4)" in text


def test_audit_ledger_mirror_matches() -> None:
    assert read(LEDGER_B) == read(LEDGER_B_MIRROR), "paper_b_audit_ledger mirror is stale"
