"""Core notation regressions and the explicit scope of later local symbols.

The original envelope, itinerary, finance and walk arguments distinguish
the even count, branch exponent, floor loss and suffix exponent. Later
return sections and appendices define their own local notation. The Paper B
checks below still concern the historical 2026-09-04 snapshot.
"""

from __future__ import annotations

import io
import re
from pathlib import Path

import pytest

from research.juggler_sequence.notation_audit import letter_sites

ROOT = Path(__file__).resolve().parents[3]
PAPER = ROOT / "docs" / "theory" / "juggler_finite_dynamics_note.md"
MIRROR = ROOT / "juggler_review" / "juggler_finite_dynamics_note.md"

MATH = re.compile(r"\\\(.*?\\\)|\\\[.*?\\\]", re.DOTALL)


def text() -> str:
    return io.open(PAPER, encoding="utf-8").read()


def body() -> str:
    """The paper with Section 1.3 removed.

    Local-notation documentation is tested separately from formula uses.
    """
    src = text()
    start = src.index("### 1.3 Notation")
    return src[:start] + src[src.index("\n## 2.", start):]


def math_spans(src: str) -> list[str]:
    return [m.group(0) for m in MATH.finditer(src)]


def section(start: str, end: str) -> str:
    source = text()
    begin = source.index(start)
    return source[begin:source.index(end, begin)]


def core_estimates() -> str:
    """Envelope/early exclusions, finance/walk, and exact defect appendix.

    Later return sections define local gap/carry/word symbols. They do not
    change the branch-exponent convention in these original estimates.
    """
    return "\n".join((section("## 2. Envelope", "### 3.10"),
                       section("## 4. Cycle finance", "## 6. Limitations"),
                       section("## Appendix C.", "## Appendix D.")))


def stale_branch_exponents(source: str) -> list[str]:
    bad = []
    for span in math_spans(source):
        if (re.search(r"(?<![A-Za-z\\])e_(?!\{\\mathrm)", span)
                or re.search(r"\^[ed](?![A-Za-z0-9_])", span)):
            bad.append(" ".join(span.split()))
    return bad


def test_core_even_count_does_not_replace_the_branch_exponent() -> None:
    """The original e_a, x^e and x^d collisions remain forbidden locally."""
    assert stale_branch_exponents(core_estimates()) == []


@pytest.mark.parametrize("stale", [r"\(e_a\)", r"\(x^e\)", r"\(x^d\)"])
def test_core_branch_collision_guard_detects_regressions(stale: str) -> None:
    assert stale_branch_exponents(core_estimates() + stale)


@pytest.mark.parametrize("sym,least,role", [
    ("G", 25, "Lemma 3.3's constant, was e_a"),
    ("h", 5, "the per-step exponent, was e"),
    ("T", 8, "the backward exponent of a suffix, was 2^s/3^l"),
])
def test_the_replacement_symbols_are_actually_used(sym: str, least: int, role: str) -> None:
    assert len(letter_sites(text(), sym)) >= least, (sym, role)


def test_branch_exponent_has_its_defined_values_in_finance_and_defect() -> None:
    """The obsolete global d-depth census is replaced by the actual formulas."""
    for source in (section("## 4. Cycle finance", "## 5."),
                   section("## Appendix C.", "## Appendix D.")):
        compact = re.sub(r"\s+", "", source)
        assert "x^h" in compact
        assert r"h=\begin{cases}1,&x" in compact
        assert r"3,&x" in compact


def test_s_and_l_no_longer_carry_the_suffix_shape() -> None:
    """`2^s/3^l` became `T(u)`, which frees `s` for the digit sum `s(L)`."""
    src = body()
    for stale in (r"2^{s}/3^{l}", r"2^s/3^l", r"s=|u|", r"3^{\,a+l}", r"2^{\,a+s}"):
        assert stale not in src, stale
    assert r"T(u)\ =\ \frac{2^{|u|}}{3^{\#O(u)}}" in text()
    assert "s(L)=\\sum_j b_j" in src          # the digit sum still means what it meant


def test_walk_exponent_is_subscripted_so_u_is_free_for_a_suffix() -> None:
    """`W = 2^u` collided with the suffix `u` of Section 3.9; its neighbours were already
    subscripted, so it is now `2^{u_k}` too."""
    src = text()
    assert r"W=2^{u_k}=3^{a_k}/2^k" in src
    assert r"W=2^u=3^a/2^k" not in src


# --- the table itself ---


def table() -> str:
    src = text()
    start = src.index("### 1.3 Notation")
    return src[start:src.index("\n## 2.", start)]


def test_notation_table_exists_and_precedes_the_mathematics() -> None:
    src = text()
    assert src.index("### 1.3 Notation") < src.index("\n## 2.")


@pytest.mark.parametrize("sym", [
    "J", "n", "N_0", "x_k", "w", "v", "u", "O", "E", "L", "o", "e", "a", "b", "c",
    "r", "h", "G_a", "B(u)", "T(u)", "\\theta", "\\Lambda", "\\mu", "u_k", "w_k",
    "n'", "C_L", "C_*", "g", "q_j", "b_j", "s(L)", "n_{\\max}(L)",
])
def test_every_recurring_symbol_is_in_the_table(sym: str) -> None:
    assert sym in table(), sym


def test_table_distinguishes_core_and_locally_defined_notation() -> None:
    t = table()
    assert "Euler's number" in t
    assert "integration variable" in t
    assert "local notation" in t
    assert "No other symbol in the paper is bound twice." not in t
    for symbol in (r"I_b", r"m,M", r"Q(s)", r"U,V,P,Q", r"e_W(x)"):
        assert symbol in t


def test_return_symbols_are_explicitly_defined_in_their_own_sections() -> None:
    order = section("### 3.10", "### 3.11")
    boundary = section("### 3.11", "### 3.12")
    terminal = section("### 3.13", "## 4.")
    loss = section("## Appendix F.", "## 7.")
    assert r"c_0=m<c_1<\cdots<c_{L-1}=M" in order
    assert r"I_b=\{b,b+1,\ldots,b^3-1\}" in order
    assert r"Let \(Q(s)\) denote the greatest odd integer not exceeding \(s\)." in boundary
    assert r"return stage with words \(U,V\)" in terminal
    assert r"UV=P\,OE\,Q,\qquad VU=P\,EO\,Q" in terminal
    assert r"e_W(x):=x^p-F_W(x)=" in loss


def test_mirror_carries_the_renames() -> None:
    assert text() == io.open(MIRROR, encoding="utf-8").read()


# --- Paper B, Section 7: the model problem has its own letters ---


PAPER_B = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note_2026_09_04.md"
MIRROR_B = ROOT / "juggler_review" / "juggler_parity_discrepancy_note_2026_09_04.md"


def section_7() -> str:
    src = io.open(PAPER_B, encoding="utf-8").read()
    return src[src.index("## 7. The Terras-style reduction"):
               src.index("## 8. Relation to the Juggler map")]


def section_7_body() -> str:
    """Section 7 without the sentence that explains its letters.

    That sentence names the symbols it is distinguishing itself from -- Lemma 3.9's `S` and its
    curvature triple `A,B,C` -- so the "no bare letters" check must not read it, exactly as the
    Paper A checks must not read the notation table.
    """
    sec = section_7()
    start = sec.index("Its objects carry script letters")
    return sec[:start] + sec[sec.index("Stripping every", start):]


def test_model_problem_uses_script_letters() -> None:
    """S, A and B in Section 7 were the sum, the amplitude and the phase, while elsewhere in
    the paper they are Lemma 3.9's size and its curvature triple.  Section 7's are script."""
    sec = section_7_body()
    for sym, least in ((r"\mathcal S", 7), (r"\mathcal A", 40), (r"\mathcal B", 5)):
        assert sec.count(sym) >= least, (sym, sec.count(sym))
    bad = []
    for m in MATH.finditer(sec):
        span = " ".join(m.group(0).split())
        stripped = span
        for repl in (r"\mathcal S", r"\mathcal A", r"\mathcal B", r"\tau"):
            stripped = stripped.replace(repl, "")
        for letter in ("S", "A", "B", "T"):
            if re.search(r"(?<![A-Za-z\\])" + letter + r"(?![A-Za-z])", stripped):
                bad.append("%s in %s" % (letter, span[:70]))
    assert not bad, bad[:5]


def test_epsilon_means_one_thing_in_section_7() -> None:
    """Conjecture 7.3 uses `P^varepsilon`; Proposition 7.4's exceptional measure is now eta.

    Before, both were `varepsilon`, forty lines apart in the same section -- the worst kind of
    collision, since a reader holds both at once.
    """
    sec = section_7()
    assert sec.count(r"\varepsilon") == 1, sec.count(r"\varepsilon")
    assert r"k\le P^{\varepsilon}" in sec
    assert sec.count(r"\eta") >= 5


def test_kernel_weight_and_hoeffding_constant_are_distinct() -> None:
    """Both were `c` in Section 7: the weight of Lemma 7.2 and Proposition 7.1's rate.

    The weight is now `varrho`, which leaves `c` to the constants -- c_2, c_3, c_4, c_7 and
    Hoeffding's rate -- where an unsubscripted `c` for a constant matches the family and an
    unsubscripted `c` for a function of n did not.
    """
    sec = section_7()
    assert r"\varrho=\tfrac{3k}4z^{1/2}" in sec
    assert r"\varrho(n)" in sec
    assert r"c=2\bigl(\tfrac{\log2}{\log3}-\tfrac12\bigr)^2>0.0342" in sec
    assert r"c=\tfrac{3k}4z^{1/2}" not in sec


def test_section_7_says_why_its_letters_are_script() -> None:
    assert "script letters" in section_7()


def test_markov_threshold_is_not_the_truncation_T() -> None:
    """Lemma 3.7 truncates at `T = P^{1/2}`; Proposition 7.4's Markov threshold is now tau."""
    sec = section_7()
    assert r"\tau=(L/\eta)" in sec
    assert r"\{|\mathcal S_\lambda|^2>\tau\}" in sec


def test_paper_b_mirror_carries_the_section_7_renames() -> None:
    assert io.open(PAPER_B, encoding="utf-8").read() == io.open(MIRROR_B, encoding="utf-8").read()
