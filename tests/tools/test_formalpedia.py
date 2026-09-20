"""The theorem index, and the two invariants it exists to keep honest.

The corpus is sorry-free and all but a named handful is kernel-checked.  Both facts are
asserted in the manuscripts, so both are worth a test that reads the Lean rather than the
prose: Paper A's Section 1.2 states the trust boundary positively, and a new
``native_decide`` slipping in anywhere would make that sentence false.
"""

from __future__ import annotations

import io
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TOOLS = REPO / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import formalpedia as fp

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


def test_the_index_covers_the_libraries_and_not_the_build_output() -> None:
    paths = fp.sources()
    assert paths, "no Lean sources found"
    assert not any(".lake" in p.parts for p in paths)


def test_every_declaration_carries_its_location_and_trust() -> None:
    index = fp.build()
    assert index["totals"]["declarations"] > 3000
    for d in index["declarations"]:
        assert d["name"] and d["module"] and d["file"]
        assert d["line"] >= 1
        assert d["trust"] in {"kernel", "compiler", "open"}


def test_the_corpus_carries_no_sorry() -> None:
    index = fp.build()
    open_ = [d["name"] for d in index["declarations"] if d["trust"] == "open"]
    assert open_ == [], open_


def test_the_juggler_layer_keeps_nothing_off_the_kernel() -> None:
    index = fp.build()
    found = {
        d["name"]
        for d in index["declarations"]
        if d["trust"] == "compiler" and d["module"].startswith("Problems.Juggler")
    }
    assert found == JUGGLER_COMPILER_TRUST, found


def test_a_docstring_belongs_to_the_declaration_it_sits_above() -> None:
    """Regression: reaching backwards for any earlier ``/--`` gave one paragraph to many."""
    text = "/-- First. -/\ntheorem a : True := trivial\n\ntheorem b : True := trivial\n"
    assert fp._docstring(text, text.index("theorem a")) == "First."
    assert fp._docstring(text, text.index("theorem b")) == ""


def test_dependents_reverses_the_import_graph() -> None:
    index = fp.build()
    rev = fp.dependents(index)
    for target, importers in rev.items():
        for name in importers:
            assert target in index["modules"][name]["imports"]


def test_impact_of_a_leaf_is_a_superset_of_its_direct_importers() -> None:
    index = fp.build()
    rev = fp.dependents(index)
    for module in list(index["modules"])[:40]:
        assert set(rev.get(module, [])) <= set(fp.transitive(rev, module))


def test_the_claim_graph_is_acyclic_and_reduced() -> None:
    """A DAG is only useful if it is both: cycles make it unreadable, redundancy makes it long."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    g = fp.dag(index, ledger)
    edges = {name: set(node["depends_on"]) for name, node in g["nodes"].items()}

    # acyclic: a depth-first walk never revisits a node on its own stack
    state: dict[str, int] = {}

    def visit(n: str) -> None:
        state[n] = 1
        for d in edges.get(n, ()):
            assert state.get(d) != 1, f"cycle through {n} -> {d}"
            if state.get(d) is None:
                visit(d)
        state[n] = 2

    for n in edges:
        if state.get(n) is None:
            visit(n)

    # reduced: no edge is implied by a two-step path already in the graph
    for n, ds in edges.items():
        for d in ds:
            assert not (edges.get(d, set()) & ds), f"{n} -> {d} is implied by another path"

    assert g["totals"]["edges"] < g["totals"]["edges_before_reduction"]


def test_every_graph_node_carries_at_least_one_ledger_row() -> None:
    """The graph is over claims, not over the whole corpus; a node with no row is noise."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    g = fp.dag(index, ledger)
    empty = [n for n, node in g["nodes"].items() if not node["ledger"]]
    assert empty == [], empty


def test_proposals_are_never_written_into_the_ledger() -> None:
    """The queue is advisory. Its own calibration is why: 86% precision is one wrong mapping
    in seven, fine for a list a person reads and wrong for a ledger whose purpose is making a
    claim checkable."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    out = fp.propose(index, ledger)
    proposed = {r["id"] for r in out["rows"]}
    resolved = {r["id"] for r in ledger if r.get("decl")}
    assert not (proposed & resolved), sorted(proposed & resolved)[:5]
    for r in out["rows"]:
        assert r["confidence"] in {"review", "low"}


def test_every_proposed_candidate_lives_in_the_row_s_own_file() -> None:
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    by_file = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    for r in fp.propose(index, ledger)["rows"]:
        lean = r.get("lean")
        if not (isinstance(lean, str) and lean.endswith(".lean")):
            continue
        names = by_file.get(fp.lean_key(lean), set())
        for c in r["candidates"]:
            assert c["decl"] in names, f"{r['id']}: {c['decl']} not in {lean}"


PAPER_A_OFF_KERNEL: list[str] = []
"""Paper A's Section 1.2 states the trust boundary positively: kernel-checked throughout the
layer except the one Ostrowski scan.  This is that sentence, as an assertion."""


def test_paper_a_keeps_nothing_off_the_kernel() -> None:
    surface = fp.paper_surface(fp.build())["Paper A"]
    assert surface["present"], "Problems.JugglerPaper is missing from the index"
    assert surface["compiler_trusted"] == PAPER_A_OFF_KERNEL, surface["compiler_trusted"]


PAPER_A_COMPILER_DEPENDENT: list[str] = []
"""What rests on the compiler, as opposed to what runs it.

Section 1.2's sentence is about proofs that call ``native_decide``, and none does any
more.  A reader asking the other question -- which of Paper A's theorems would fall if
the compiler were wrong -- used to get a second name, ``window_digit_cap``, because it
cited the scan.  With ``window_digit_scan`` retired on 14 September 2026 both answers are
empty and the two sentences coincide.
"""


def test_paper_a_rests_on_the_compiler_nowhere() -> None:
    surface = fp.paper_surface(fp.build())["Paper A"]
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


def test_paper_b_is_kernel_checked_throughout() -> None:
    surface = fp.paper_surface(fp.build())["Paper B"]
    assert surface["present"], "Problems.JugglerParityPaper is missing from the index"
    assert surface["compiler_trusted"] == [], surface["compiler_trusted"]


def test_paper_b_is_kernel_checked_transitively_too() -> None:
    """Paper B's claim is the stronger one, so it is the one worth testing both ways: no
    declaration it reaches runs ``native_decide``, and none cites anything that does."""
    surface = fp.paper_surface(fp.build())["Paper B"]
    assert surface["compiler_dependent"] == [], surface["compiler_dependent"]


def test_paper_c_is_kernel_checked_transitively() -> None:
    """Paper C's root is `Problems.JugglerFatePaper`; its Lean column says the exact layer is
    checked without `sorry` or `native_decide`, so nothing it reaches may run the compiler and
    nothing it reaches may cite anything that does."""
    surface = fp.paper_surface(fp.build())["Paper C"]
    assert surface["present"], "Problems.JugglerFatePaper is missing from the index"
    assert surface["compiler_trusted"] == [], surface["compiler_trusted"]
    assert surface["compiler_dependent"] == [], surface["compiler_dependent"]
    assert surface["modules"] >= 8, surface["modules"]


def test_no_paper_reaches_a_sorry() -> None:
    """A `sorry` anywhere under a paper root would make its verification claim false."""
    for label, surface in fp.paper_surface(fp.build()).items():
        if surface["present"]:
            assert surface["open"] == [], f"{label}: {surface['open']}"


def test_paper_reachability_is_not_the_same_set_as_the_directory() -> None:
    """Why the paper roots matter: the Juggler directory holds modules no paper imports, so a
    directory count answers a different question than a trust sentence does.  If these ever
    coincided the distinction would be free, and the roots could be dropped."""
    index = fp.build()
    reach = fp.reachable(index)
    root = fp.PAPER_ROOTS["Paper A"]
    reached = reach.get(root, set()) | {root}
    in_dir = {m for m in index["modules"] if m.startswith("Problems.Juggler")}
    assert in_dir - reached, "every Juggler module is now reachable from Paper A"
    assert reached & in_dir, "Paper A reaches no Juggler module at all"


def test_declares_requires_the_name_to_end_at_the_match() -> None:
    """The corpus names helper lemmas by extending their main theorem, so 519 of 4,528 names
    are a proper prefix of another. A substring check cannot tell them apart; this one can."""
    text = (
        "theorem power_bound_compensated_contracts_follows (h : True) : True := trivial\n"
    )
    assert not fp.declares(text, "power_bound_compensated_contracts")
    assert fp.declares(text, "power_bound_compensated_contracts_follows")


def test_declares_finds_a_real_declaration_in_the_corpus() -> None:
    path = fp.ROOT / "formal" / "Problems" / "Juggler" / "CycleFinance.lean"
    text = path.read_text(encoding="utf-8")
    assert fp.declares(text, "cycleMin_finance")
    assert not fp.declares(text, "cycleMin_financ")
    assert not fp.declares(text, "cycleMin_finance_extra_suffix")


def test_the_prefix_collision_surface_is_real_and_measured() -> None:
    """If this ever drops to zero the `declares` boundary stops mattering and can go."""
    names = {d["name"] for d in fp.build()["declarations"]}
    shadowed = {n for n in names if any(o != n and o.startswith(n) for o in names)}
    assert len(shadowed) > 100, len(shadowed)


def test_review_digest_pairs_each_row_with_its_candidate_s_prose() -> None:
    """The digest exists so a person can decide; deciding needs the docstring beside the row."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.review_digest(index, ledger)
    assert "# Declaration review queue" in text
    assert "rows below, of" in text
    # every entry carries a candidate line and a quoted docstring block
    entries = text.count("\n## ")
    assert entries > 0
    assert text.count("**Candidate.**") == entries
    assert text.count("**Row.**") == entries


def test_review_digest_warns_about_both_part_for_whole_failures() -> None:
    """Neither is scored, and both record a part as the whole: a row broader than its
    candidate, and a candidate narrower than its row. The digest names a worked example of
    each, because a reviewer cannot see either one in the numbers."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.review_digest(index, ledger)
    assert "record a part as the whole" in text
    assert "BTC-select3" in text                      # row broader than candidate
    assert "BTN-sdrg-lambda1-interval" in text        # candidate narrower than row


def test_proposals_never_offer_a_declaration_another_row_already_claims() -> None:
    """Two rows on one declaration is rejected by the ledger's own collision test, so a queue
    that offers a taken declaration spends a reviewer's judgement on a foregone answer.
    Two of the 43 confident entries did exactly that before this filter."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    taken = {(r["lean"], name) for r in ledger for name in fp.row_decls(r)}
    offered = [
        f"{row['id']} -> {c['decl']}"
        for row in fp.propose(index, ledger)["rows"]
        for c in row["candidates"]
        if (row["lean"], c["decl"]) in taken
    ]
    assert offered == [], offered


def test_signature_returns_the_statement_without_the_proof() -> None:
    index = fp.build()
    decl = next(d for d in index["declarations"] if d["name"] == "cycleMin_finance")
    sig = fp.signature(decl)
    assert sig.startswith("theorem cycleMin_finance")
    assert ":=" not in sig and "by" not in sig.split("\n")[-1]


def test_every_digest_entry_shows_a_docstring_or_a_signature() -> None:
    """An entry offering only a name cannot be answered. Nine of the confident candidates
    carry no docstring, so the digest falls back to the statement the docstring would have
    paraphrased."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.review_digest(index, ledger)
    entries = text.count("\n## ")
    assert text.count("> ") + text.count("```lean") >= entries
    assert "(no docstring)" not in text


def test_definitions_are_ranked_apart_from_theorems() -> None:
    """Merging them into one ranking displaces the true answer on rows already resolved --
    measured at 3 of 103 -- so a row that means a `def` gets its own short list instead."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    kinds = {d["name"]: d["kind"] for d in index["declarations"]}
    for row in fp.propose(index, ledger)["rows"]:
        for c in row["candidates"]:
            assert kinds.get(c["decl"]) in ("theorem", "lemma"), c["decl"]
        for d in row.get("definitions", []):
            assert kinds.get(d["decl"]) in ("def", "abbrev"), d["decl"]


def test_the_digest_computes_its_precision_rather_than_asserting_one() -> None:
    """A hardcoded figure goes stale silently: 96% was quoted for twenty-five ticks after the
    calibration set had outgrown the easy rows it was measured on. The real number was 86%.

    Calibration measures the scorer, and the scorer proposes one declaration, so it runs on
    the rows that name exactly one. A row naming its whole inventory has no single answer to
    be scored against and would only dilute the figure.
    """
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    cal = fp.calibrate(index, ledger)
    assert cal["resolved"] == sum(1 for r in ledger if len(fp.row_decls(r)) == 1)
    assert cal["resolved"] < sum(1 for r in ledger if fp.row_decls(r))
    assert 0 < cal["correct"] <= cal["fires"]
    text = fp.review_digest(index, ledger)
    assert f"all {cal['resolved']} single-declaration rows" in text
    assert "96%" not in text


def test_digest_flags_a_top_candidate_that_extends_a_runner_up() -> None:
    """Helper and special-case lemmas are named by extending their main theorem, so a longer
    top candidate beside a shorter runner-up is the shape that cost two wrong answers:
    q_eq_iff_of_same_bal over q_eq_iff, and predecessor_on_F over unique_predecessor."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.review_digest(index, ledger)
    flagged = 0
    for row in fp.propose(index, ledger)["rows"]:
        if row["confidence"] != "review" or len(row["candidates"]) < 2:
            continue
        top = row["candidates"][0]["decl"]
        if any(top != c["decl"] and top.startswith(c["decl"]) for c in row["candidates"][1:]):
            flagged += 1
    assert text.count("Careful:") == flagged


#: Every file this tool writes is committed, and until 14 September 2026 nothing
#: compared any of them to a rebuild.  All four had drifted.  The index did not
#: know InformationField's ninety declarations, still listed `window_digit_scan`
#: after that scan was retired, and still placed `window_digit_cap` in
#: OstrowskiSandwich after the declaration had moved to OstrowskiNumeration.  The
#: claim DAG was missing 58 of its 177 modules and 68 ledger-row placements, which
#: is the graph that answers "what does changing this module rebuild".  Four rows
#: in the proposal queue pointed at a declaration that was no longer the best
#: match.  And the review digest had lost its first 48 bytes -- its `# Declaration
#: review queue` title and the opening words of the first sentence -- to the
#: tool's own "wrote ..." success message, which is what a shell redirect onto a
#: file the tool already writes itself does: the shell truncates, the tool writes
#: the document, the banner lands back at offset 0.
#:
#: The failure was not that any one of these went stale.  It is that every other
#: test in this file calls fp.build() fresh, so the artifacts on disk -- the ones
#: a session actually reads -- were the only thing nobody checked.  A gate over
#: one of the four would have left the same hole three times over.
#:
#: All four rebuild deterministically across hash seeds in about 1.4 seconds
#: together, so the comparison is exact bytes and covers the whole set.
def _generated() -> list[tuple[str, Path, str]]:
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    return [
        ("build", fp.INDEX, fp.render(index)),
        ("propose", fp.PROPOSALS, fp.render(fp.propose(index, ledger))),
        ("dag", fp.DAG, fp.render(fp.dag(index, ledger))),
        ("review", fp.REVIEW, fp.review_digest(index, ledger)),
    ]


def test_every_committed_artifact_matches_a_fresh_build() -> None:
    stale = []
    for cmd, path, fresh in _generated():
        committed = path.read_text(encoding="utf-8").replace("\r\n", "\n")
        if committed != fresh.replace("\r\n", "\n"):
            rel = path.relative_to(REPO).as_posix()
            stale.append(f"  {rel}: rebuild with `python tools/formalpedia.py {cmd}`")
    assert not stale, (
        "formalpedia artifacts on disk disagree with a fresh build:\n"
        + "\n".join(stale)
        + "\n\nThese are what the formalpedia skill tells a session to consult before "
        "touching formal/. A stale one does not go quiet -- it answers wrong."
    )


def test_the_review_digest_still_opens_with_its_own_title() -> None:
    """The specific corruption above, named so it cannot come back quietly.

    Regenerating fixes it, but `formalpedia.py review > <the file it writes>` puts
    it straight back, and the result still looks like a plausible document.
    """
    first = fp.REVIEW.read_text(encoding="utf-8").lstrip().splitlines()[0]
    assert first.startswith("# "), (
        f"{fp.REVIEW.name} starts with {first!r}, not a Markdown title. "
        "It was most likely written by redirecting the tool's stdout into the "
        "same file the tool writes itself, which drops the opening bytes."
    )
