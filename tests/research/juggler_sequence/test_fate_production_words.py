"""Paper C's six production words, and the prefix-freeness it asserts three times.

Paper C builds Theorem 1 out of six finite productions ``V_k = (OE)^(k-1) OEE``, ``1 <= k <= 6``,
and uses their prefix-freeness as a load-bearing step: "Production words must be prefix-free" when
the candidate list is drawn up, "These six words are prefix-free" when the six are fixed, and, at
the close of Appendix D, "Finally the prefix-free words give disjoint source sets, and the
subtraction in (5.9) proves (5.10)."

Until 19 September 2026 the assertion was written only and the words were not defined anywhere
under ``formal/``.  ``Problems/Juggler/FateProductionWords.lean`` now defines them and proves
prefix-freeness for the whole family, not just the six.  These tests hold the same facts
independently of Lean, and tie the module to the manuscript sentences that need it: if the paper
stops asserting prefix-freeness, or the module stops proving it, one of them fails.

The disjointness of the *source sets* is NOT tested here and is not proved in Lean.  It follows
from prefix-freeness only together with Appendix D's analytic layer, which is a written proof.
"""
from __future__ import annotations

import io
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
PAPER_C = ROOT / "docs" / "theory" / "juggler_fate_almost_all_note.md"
MODULE = ROOT / "formal" / "Problems" / "Juggler" / "FateProductionWords.lean"
UMBRELLA = ROOT / "formal" / "Problems" / "Juggler.lean"
BARREL = ROOT / "formal" / "Problems" / "JugglerFatePaper.lean"

#: ``V_k = (OE)^(k-1) OEE`` for ``1 <= k <= 6``, as the paper writes them.
WORDS = {k: "OE" * (k - 1) + "OEE" for k in range(1, 7)}


def read(path: Path) -> str:
    return io.open(path, encoding="utf-8").read()


def flat(path: Path) -> str:
    """The manuscript with its line wrapping collapsed, so a sentence can be matched whole."""
    return " ".join(read(path).split())


def test_the_six_words_are_the_ones_the_paper_prints() -> None:
    """``V_1 = OEE`` and each step prepends ``OE``; the paper prints ``V_k = (OE)^(k-1) OEE``."""
    assert WORDS[1] == "OEE"
    assert WORDS[2] == "OEOEE"
    assert WORDS[6] == "OE" * 5 + "OEE"
    assert r"V_k=(OE)^{k-1}OEE" in flat(PAPER_C).replace(" ", "")


def test_lengths_and_odd_counts() -> None:
    """``|V_k| = 2k + 1`` and ``V_k`` carries ``k`` odd letters, which is Lean's
    ``Vword_length`` and ``Vword_oddCount`` at ``i = k - 1``."""
    for k, w in WORDS.items():
        assert len(w) == 2 * k + 1, (k, w)
        assert w.count("O") == k, (k, w)
        assert w.count("E") == k + 1, (k, w)


def test_the_six_words_are_prefix_free() -> None:
    """The assertion Paper C makes three times, checked directly."""
    for i, u in WORDS.items():
        for j, v in WORDS.items():
            if i == j:
                continue
            assert not v.startswith(u), (i, j, u, v)


@pytest.mark.parametrize("n", [6, 20, 60])
def test_prefix_freeness_holds_for_the_whole_family(n: int) -> None:
    """Lean proves it for every pair of indices, not only the six: ``Vword_prefix_iff``.

    The reason is uniform in ``k``: ``V_i`` closes with its second ``E`` exactly where ``V_j``,
    for ``j > i``, opens another ``OE``.  So the family stays prefix-free however far it runs,
    and the six are not a lucky initial segment.
    """
    family = {k: "OE" * (k - 1) + "OEE" for k in range(1, n + 1)}
    for i, u in family.items():
        for j, v in family.items():
            if i != j:
                assert not v.startswith(u), (i, j)


def test_the_first_divergence_is_where_the_word_closes() -> None:
    """For ``j > i`` the two agree up to position ``2i``, then ``V_i`` has ``E`` and ``V_j`` ``O``.

    This is the content of the induction in ``Vword_prefix_iff``, as a statement about indices.
    """
    for i in range(1, 7):
        for j in range(i + 1, 7):
            u, v = WORDS[i], WORDS[j]
            assert u[: 2 * i] == v[: 2 * i], (i, j)
            assert u[2 * i] == "E" and v[2 * i] == "O", (i, j)


def test_the_manuscript_still_asserts_what_the_module_proves() -> None:
    """Three sentences.  If the paper drops them, this module stops being load-bearing."""
    text = flat(PAPER_C)
    assert "Production words must be prefix-free" in text
    assert "These six words are prefix-free" in text
    assert "the prefix-free words give disjoint source sets" in text


def test_the_lean_module_exists_states_the_theorem_and_is_registered() -> None:
    """The module carries the general statement, no open proof, and is in the inventory."""
    body = read(MODULE)
    for token in ("sorry", "admit", "axiom"):
        assert token not in body, token
    assert "def Vword" in body
    assert "theorem Vword_prefix_iff" in body
    assert "theorem Vword_length" in body
    assert "theorem Vword_oddCount" in body
    assert "import Problems.Juggler.FateProductionWords" in read(UMBRELLA)

    from research.juggler_sequence.lean_registry import AUXILIARY_MODULES, LAYERS

    # Wired into Paper C on 19 September 2026.  The module was deliberately parked in
    # AUXILIARY_MODULES when it landed, because wiring a new module into the barrel and into
    # Appendix A belonged with the pass that fixed Appendix A's "thirty modules named here"
    # while naming 29.  That pass has now run: the module is a Paper C barrel module like
    # every other Fate* module, so it sits in LAYERS and the barrel imports it.
    assert "FateProductionWords" in LAYERS
    assert "FateProductionWords" not in AUXILIARY_MODULES
    assert "import Problems.Juggler.FateProductionWords" in read(BARREL)


def test_it_does_not_claim_the_analytic_layer() -> None:
    """The module is the combinatorial step; Appendix D's asymptotics are not in Lean.

    A guard against the one overclaim available here: prefix-freeness gives disjoint SOURCE sets
    only with the analytic layer, and the module says so rather than asserting the consequence.
    """
    body = read(MODULE)
    assert "is written proof and is untouched here" in body
    assert "does not formalise" in body
