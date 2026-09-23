"""Formalpedia trust regressions; live corpus snapshots are isolated by conftest."""
from __future__ import annotations


from formalpedia_core import (
    graph as fp_graph,
)


JUGGLER_COMPILER_TRUST: set[str] = set()
"""Nothing in the Juggler Lean layer runs off the kernel, as of 14 September 2026.

It was two.  `greedy_eq_ostro_below_window` scanned all 301994 lengths to identify the
fold-form digits with the function-form ones; they are the same algorithm written twice,
so `greedy_eq_ostro` proves it structurally for every `L` and the scan is a corollary.
Then `window_digit_scan`, which sharpened the Ostrowski digit cap from the structural 47
to 37 over 251486 window lengths: nothing consumed the 37, so `window_digit_cap` was
reproved from `greedyDigitSum_le` at 47 and the scan retired.  `window_digit_max` still
records, kernel-checked, that 37 is attained at L = 275632.

Keep this empty.  A name here is a compiler-trust assumption inside a deposited paper's
surface; it belongs in the paper's prose before it belongs in this set."""


PAPER_A_OFF_KERNEL: list[str] = []
"""Paper A's current trust boundary is kernel-checked throughout the layer.
The former Ostrowski scan has been replaced by a structural proof."""


PAPER_A_COMPILER_DEPENDENT: list[str] = []
"""What rests on the compiler, as opposed to what runs it.

Section 1.2's sentence is about proofs that call ``native_decide``, and none does any
more.  A reader asking the other question -- which of Paper A's theorems would fall if
the compiler were wrong -- used to get a second name, ``window_digit_cap``, because it
cited the scan.  With ``window_digit_scan`` retired on 14 September 2026 both answers are
empty and the two sentences coincide.
"""


def test_the_corpus_carries_no_sorry(corpus_index) -> None:
    index = corpus_index
    open_ = [d["name"] for d in index["declarations"] if d["trust"] == "open"]
    assert open_ == [], open_


def test_the_juggler_layer_keeps_nothing_off_the_kernel(corpus_index) -> None:
    index = corpus_index
    found = {
        d["name"]
        for d in index["declarations"]
        if d["trust"] == "compiler" and d["module"].startswith("Problems.Juggler")
    }
    assert found == JUGGLER_COMPILER_TRUST, found


def test_paper_a_keeps_nothing_off_the_kernel(paper_surfaces) -> None:
    surface = paper_surfaces["Paper A"]
    assert surface["present"], "Problems.JugglerPaper is missing from the index"
    assert surface["compiler_trusted"] == PAPER_A_OFF_KERNEL, surface["compiler_trusted"]


def test_paper_a_rests_on_the_compiler_nowhere(paper_surfaces) -> None:
    surface = paper_surfaces["Paper A"]
    assert surface["compiler_dependent"] == PAPER_A_COMPILER_DEPENDENT, (
        surface["compiler_dependent"]
    )
    trusted, dependent = set(surface["compiler_trusted"]), set(surface["compiler_dependent"])
    if trusted:
        assert trusted < dependent, (
            "if these ever agree while something is off the kernel, the transitive pass "
            "has stopped finding anything and the syntactic label would say the same "
            "thing more cheaply"
        )
    else:
        assert not dependent, (
            "nothing runs the compiler, so nothing may rest on it either: a citation "
            "without a caller means the transitive pass is reading a stale index"
        )


def test_paper_b_is_kernel_checked_throughout(paper_surfaces) -> None:
    surface = paper_surfaces["Paper B"]
    assert surface["present"], "Problems.JugglerParityPaper is missing from the index"
    assert surface["compiler_trusted"] == [], surface["compiler_trusted"]


def test_paper_b_is_kernel_checked_transitively_too(paper_surfaces) -> None:
    """Paper B's claim is the stronger one, so it is the one worth testing both ways: no
    declaration it reaches runs ``native_decide``, and none cites anything that does."""
    surface = paper_surfaces["Paper B"]
    assert surface["compiler_dependent"] == [], surface["compiler_dependent"]


def test_paper_c_is_kernel_checked_transitively(paper_surfaces) -> None:
    """Paper C's root is `Problems.JugglerFatePaper`; its Lean column says the exact layer is
    checked without `sorry` or `native_decide`, so nothing it reaches may run the compiler and
    nothing it reaches may cite anything that does."""
    surface = paper_surfaces["Paper C"]
    assert surface["present"], "Problems.JugglerFatePaper is missing from the index"
    assert surface["compiler_trusted"] == [], surface["compiler_trusted"]
    assert surface["compiler_dependent"] == [], surface["compiler_dependent"]
    assert surface["modules"] >= 8, surface["modules"]


def test_no_paper_reaches_a_sorry(paper_surfaces) -> None:
    """A `sorry` anywhere under a paper root would make its verification claim false."""
    for label, surface in paper_surfaces.items():
        if surface["present"]:
            assert surface["open"] == [], f"{label}: {surface['open']}"


def test_paper_reachability_is_not_the_same_set_as_the_directory(corpus_index) -> None:
    """Why the paper roots matter: the Juggler directory holds modules no paper imports, so a
    directory count answers a different question than a trust sentence does.  If these ever
    coincided the distinction would be free, and the roots could be dropped."""
    index = corpus_index
    reach = fp_graph.reachable(index)
    root = fp_graph.PAPER_ROOTS["Paper A"]
    reached = reach.get(root, set()) | {root}
    in_dir = {m for m in index["modules"] if m.startswith("Problems.Juggler")}
    assert in_dir - reached, "every Juggler module is now reachable from Paper A"
    assert reached & in_dir, "Paper A reaches no Juggler module at all"
