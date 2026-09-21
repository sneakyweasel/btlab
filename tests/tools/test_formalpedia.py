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


def test_the_index_holds_the_declarations_written_with_an_attribute() -> None:
    """``@[simp] theorem foo`` is a declaration, and 70 in ``formal/`` are written that way.

    The pattern had no room for ``@[...]`` in front of the keyword, so all 70 were absent
    from the index outright -- not mislabelled, not mis-filed, simply not there. A missing
    declaration is the quietest failure this index has: ``jev-propose`` cannot offer it,
    ``jev-coverage`` cannot score it, and both ledger gates that look a row's ``decl`` up
    here ``continue`` when the name is absent, so a row naming one would be checked by
    nothing at all while every gate stayed green.
    """
    decls = {(d["file"], d["name"]) for d in fp.build()["declarations"]}
    for rel, name in (
        ("formal/BTCalculus/OpFragSemantic.lean", "signFactor_true"),
        ("formal/BTCalculus/OpFragSemantic.lean", "signFactor_false"),
        ("formal/Problems/Engine/InformationField.lean", "informationCost_id"),
    ):
        source = (fp.ROOT / rel).read_text(encoding="utf-8")
        assert f"@[simp] theorem {name}" in source, f"{name} is no longer written this way"
        assert (rel, name) in decls, f"{name} is declared in {rel} and the index omits it"


def test_no_declaration_in_the_index_is_prose_from_a_comment() -> None:
    """A wrapped docstring line is not a declaration, and six of them were indexed as one.

    ``formal/`` writes long docstrings, and when one wraps so that ``theorem``, ``lemma`` or
    ``instance`` lands at column 0 the pattern reads the next English word as a name. That
    put declarations called ``of``, ``at``, ``needs`` and ``nothing`` in the index, with a
    kind, a line and a trust level, indistinguishable from real ones to everything
    downstream. The ``^`` anchor was the only thing holding this back, which is why comments
    are blanked before the scan rather than indentation simply being allowed: permitting an
    indented declaration without blanking first adds a seventh, ``beats``, from the module
    docstring of ``FateTaoReduction.lean``.
    """
    names = {d["name"] for d in fp.build()["declarations"]}
    for word in ("of", "at", "needs", "nothing", "beats"):
        assert word not in names, f"{word!r} is English prose, not a declaration"


def test_the_declaration_pattern_reads_lean_and_not_prose_about_it() -> None:
    """The pattern, against the three forms it missed and the one it must keep missing."""
    sample = (
        "/-- A docstring whose line wraps so that a keyword lands at column 0, the way\n"
        "the contagion\n"
        "theorem beats a bound; and again, indented, so the\n"
        "  lemma pretends to be a declaration. -/\n"
        "@[simp] theorem tagged_thing : True := trivial\n"
        "section Inner\n"
        "  theorem indented_thing : True := trivial\n"
        "end Inner\n"
        "-- a line comment mentioning theorem commented_thing\n"
        "private noncomputable def modified_thing : Nat := 0\n"
    )
    found = {m.group("name") for m in fp.DECL.finditer(fp.blank_comments(sample))}
    assert found == {"tagged_thing", "indented_thing", "modified_thing"}, found


def test_a_docstring_above_an_attribute_declaration_still_reaches_it() -> None:
    """The scan runs on blanked text and the docstring is sliced from the original at the
    offset it reports, reading backwards from the match. The match now opens at the start of
    the line rather than at the keyword, so an attribute must not come between the two.

    None of the 70 in ``formal/`` carries prose today -- ``@[simp]`` lemmas here are written
    without it -- so asserting this on the corpus would pass without exercising anything.
    """
    text = (
        "/-- Negating a trit twice returns it. -/\n"
        "@[simp] theorem negate_negate : True := trivial\n"
    )
    hits = list(fp.DECL.finditer(fp.blank_comments(text)))
    assert [m.group("name") for m in hits] == ["negate_negate"]
    assert fp._docstring(text, hits[0].start()) == "Negating a trit twice returns it."


def test_blanking_comments_moves_no_byte_and_keeps_every_line() -> None:
    """Offsets have to survive it: the scan runs on the blanked text and the docstring and
    trust of each declaration are sliced from the original at the same positions. A blanker
    that shortened the text would report every line number after the first comment wrong."""
    for path in fp.sources():
        text = path.read_text(encoding="utf-8")
        blanked = fp.blank_comments(text)
        assert len(blanked) == len(text), path
        assert blanked.count("\n") == text.count("\n"), path


def test_declares_reads_the_forms_a_declaration_is_actually_written_in() -> None:
    """``declares`` guards deletions, so a form it cannot read reports a live theorem gone.

    It took a bare keyword with no room for either an attribute or a modifier, so
    ``@[simp] theorem foo`` and ``private theorem foo`` both answered False -- the answer
    that means "this theorem is no longer here".
    """
    assert fp.declares("@[simp] theorem tagged_thing : True := trivial\n", "tagged_thing")
    assert fp.declares("private theorem hidden_thing : True := trivial\n", "hidden_thing")
    assert fp.declares("theorem plain_thing : True := trivial\n", "plain_thing")
    assert fp.declares("  theorem indented_thing : True := trivial\n", "indented_thing")
    # And still answers False for a name that is not declared, which is the point of it.
    assert not fp.declares("@[simp] theorem tagged_thing : True := trivial\n", "tagged")
    assert not fp.declares("theorem plain_thing : True := trivial\n", "plain_thing_more")


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


def _fake_ask(*, confidence: float = 0.95, pick: dict[str, str] | None = None,
              none_for: set[str] = frozenset(), seen: list | None = None):
    """An ``ask`` that answers from the criteria it is offered and never touches the network.

    Default answer: the alphabetically first theorem offered.  ``pick`` overrides per row,
    including names the file does not offer, which is how the known-bad path is exercised;
    ``none_for`` answers "none of these" for those rows; ``seen`` collects every question.
    """
    def ask(state, instructions, criteria):
        if seen is not None:
            seen.append((state, criteria))
        names = sorted(n for n in criteria if n != fp.JEV_NONE)
        rid = state["ledger_id"]
        if rid in none_for:
            choice = fp.JEV_NONE
        elif pick and rid in pick:
            choice = pick[rid]
        else:
            choice = names[0]
        rest = (1.0 - confidence) / max(1, len(criteria) - 1)
        probs = {n: rest for n in criteria}
        probs[choice] = confidence
        return {"choice": choice, "confidence": confidence, "probabilities": probs,
                "model": "jev-test", "input_tokens": 100}
    return ask


def _queue_ids(index, ledger) -> set[str]:
    return {row["id"] for row, cands, _ in fp._queue(index, ledger) if cands}


def test_jev_propose_asks_each_unresolved_row_about_its_own_file_and_nothing_else() -> None:
    """Jev is offered exactly the theorems the scorer may propose: the row's own file, minus
    declarations another row already claims, plus the option that none of them is the claim.
    The tests above pin those two rules for the scorer; this pins them for the offer."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    seen: list = []
    record = fp.jev_propose(index, ledger, _fake_ask(seen=seen), workers=1)
    asked = {state["ledger_id"] for state, _ in seen}
    assert asked == _queue_ids(index, ledger) == set(record["rows"])
    by_file: dict[str, set[str]] = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    taken = {(fp.lean_key(r.get("lean")), n) for r in ledger for n in fp.row_decls(r)}
    rows = {r["id"]: r for r in ledger}
    for state, criteria in seen:
        assert fp.JEV_NONE in criteria
        key = fp.lean_key(rows[state["ledger_id"]]["lean"])
        for name in criteria:
            if name == fp.JEV_NONE:
                continue
            assert name in by_file[key], f"{state['ledger_id']}: {name} is not in {key}"
            assert (key, name) not in taken, f"{state['ledger_id']}: {name} is already claimed"
        assert len(criteria) - 1 <= fp.JEV_SHORTLIST
    for verdict in record["rows"].values():
        fields = {"key", "model", "asked", "choice", "confidence", "shortlist", "in_file"}
        assert fields <= set(verdict)
    assert record["totals"]["asked_now"] == len(seen) == record["totals"]["answered"]


def test_jev_propose_reuses_a_verdict_until_the_row_or_its_offer_changes() -> None:
    """A verdict costs tokens and can differ between runs, so an unchanged row keeps the
    answer it has.  The key covers the statement, the file and the names offered: any of
    those moving re-asks that row alone, ``refresh`` re-asks them all, a row resolved since
    is dropped rather than carried, and ``limit`` leaves the rows it does not reach as they
    were instead of forgetting them."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    first = fp.jev_propose(index, ledger, _fake_ask(), workers=1)
    n = first["totals"]["answered"]
    assert n > 0
    seen: list = []
    again = fp.jev_propose(index, ledger, _fake_ask(seen=seen), cached=first, workers=1)
    assert seen == [] and again["rows"] == first["rows"]
    assert again["totals"] == {"answered": n, "asked_now": 0, "reused": n, "input_tokens": 0}
    seen = []
    fp.jev_propose(index, ledger, _fake_ask(seen=seen), cached=first, refresh=True, workers=1)
    assert len(seen) == n
    moved = json.loads(json.dumps(first))
    victim = next(iter(moved["rows"]))
    moved["rows"][victim]["key"] = "0000000000000000"
    moved["rows"]["A-row-resolved-since"] = dict(moved["rows"][victim])
    seen = []
    third = fp.jev_propose(index, ledger, _fake_ask(seen=seen), cached=moved, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]
    assert "A-row-resolved-since" not in third["rows"]
    seen = []
    capped = fp.jev_propose(index, ledger, _fake_ask(seen=seen), cached=first, refresh=True,
                            limit=3, workers=1)
    assert len(seen) == 3 and capped["totals"]["answered"] == n


def test_propose_routes_a_confident_jev_pick_to_review_and_leaves_the_candidates_alone() -> None:
    """Jev's answer is a field beside the scorer's candidates, never a substitute: candidates
    and definitions are identical with and without it.  What it may change is the routing,
    and only upward: a pick at or above JEV_REVIEW lists the row; a pick below it and a
    "none of these" leave the scorer's verdict as it was."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    ids = sorted(_queue_ids(index, ledger))
    none_for = set(ids[::3])
    sure = fp.jev_propose(index, ledger, _fake_ask(confidence=0.95, none_for=none_for),
                          workers=1)
    unsure = fp.jev_propose(index, ledger, _fake_ask(confidence=0.4), workers=1)
    plain = fp.propose(index, ledger, jev={})
    base = {r["id"]: r for r in plain["rows"]}
    by_file: dict[str, set[str]] = {}
    for d in index["declarations"]:
        by_file.setdefault(d["file"], set()).add(d["name"])
    for record, routes in ((sure, True), (unsure, False)):
        merged = fp.propose(index, ledger, jev=record)
        assert merged["jev"]["answered"] == len(record["rows"])
        assert merged["jev"]["picks"] + merged["jev"]["none"] == merged["jev"]["answered"]
        for r in merged["rows"]:
            b = base[r["id"]]
            assert r["candidates"] == b["candidates"]
            assert r.get("definitions") == b.get("definitions")
            assert r["confidence"] in {"review", "low"}
            jv = r.get("jev")
            if jv is None:
                assert r["id"] not in record["rows"]
                assert r["confidence"] == b["confidence"]
            elif jv["verdict"] == "none":
                assert r["id"] in none_for and jv["decl"] is None
                assert r["confidence"] == b["confidence"]
            else:
                assert jv["verdict"] == "pick"
                assert jv["decl"] in by_file[fp.lean_key(r["lean"])]
                assert r["confidence"] == ("review" if routes else b["confidence"])
                assert jv["routed"] == (routes and b["confidence"] == "low")
    assert fp.propose(index, ledger, jev=sure)["worth_reviewing"] > plain["worth_reviewing"]
    assert fp.propose(index, ledger, jev=unsure)["worth_reviewing"] == plain["worth_reviewing"]


def test_propose_ignores_a_jev_pick_that_the_file_does_not_offer() -> None:
    """The known-bad input.  A cached name that is not in the offer -- claimed by another
    row since, renamed, or invented -- is recorded as not_a_candidate and routes nothing;
    the digest says so and never renders it as a candidate."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    plain = fp.propose(index, ledger, jev={})
    shown = next(r for r in plain["rows"] if r["confidence"] == "review" and r["candidates"])
    hidden = next(r for r in plain["rows"] if r["confidence"] == "low" and r["candidates"])
    bad = fp.jev_propose(
        index, ledger,
        _fake_ask(confidence=0.99,
                  pick={shown["id"]: "no_such_theorem", hidden["id"]: "no_such_theorem"}),
        workers=1)
    merged = {r["id"]: r for r in fp.propose(index, ledger, jev=bad)["rows"]}
    for rid, before in ((shown["id"], "review"), (hidden["id"], "low")):
        jv = merged[rid]["jev"]
        assert jv["verdict"] == "not_a_candidate" and jv["decl"] is None
        assert merged[rid]["confidence"] == before
    text = fp.review_digest(index, ledger, jev=bad)
    assert "which this file does not offer; ignored" in text
    assert "`no_such_theorem`" in text
    assert "**Jev's candidate.** `no_such_theorem`" not in text


def test_propose_marks_a_verdict_stale_once_the_row_or_the_offer_moved() -> None:
    """A verdict answers one wording of the claim against one offer.  When either changes,
    the cached answer is shown as stale and routes nothing until jev-propose re-asks."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    record = fp.jev_propose(index, ledger, _fake_ask(confidence=0.99), workers=1)
    plain = {r["id"]: r for r in fp.propose(index, ledger, jev={})["rows"]}
    victim = next(rid for rid in record["rows"] if plain[rid]["confidence"] == "low")
    stale = json.loads(json.dumps(record))
    stale["rows"][victim]["key"] = "0000000000000000"
    merged = {r["id"]: r for r in fp.propose(index, ledger, jev=stale)["rows"]}
    assert merged[victim]["jev"]["verdict"] == "stale"
    assert merged[victim]["confidence"] == "low"
    fresh = {r["id"]: r for r in fp.propose(index, ledger, jev=record)["rows"]}
    assert fresh[victim]["jev"]["verdict"] == "pick"
    assert fresh[victim]["confidence"] == "review" and fresh[victim]["jev"]["routed"] is True


def test_review_digest_shows_jev_beside_the_scorer_and_quotes_its_stored_calibration() -> None:
    """Each listed entry carries Jev's answer next to the scorer's candidate; a disagreement
    prints Jev's declaration in full so the reviewer reads both; and the figures in the
    opening come from the stored, dated calibration record, never from a constant."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    record = fp.jev_propose(index, ledger, _fake_ask(confidence=0.9), workers=1)
    record["calibration"] = {
        "asked": "2026-09-21", "model": "jev-test", "sampled": 30, "top1": 19, "top3": 26,
        "confident": 21, "confident_correct": 16, "scorer_top1": 16,
    }
    text = fp.review_digest(index, ledger, jev=record)
    merged = fp.propose(index, ledger, jev=record)
    listed = [r for r in merged["rows"] if r["confidence"] == "review" and r["candidates"]]
    assert text.count("**Jev.**") == sum(1 for r in listed if r.get("jev"))
    disagreeing = [r for r in listed if r["jev"]["verdict"] == "pick"
                   and r["jev"]["decl"] != r["candidates"][0]["decl"]]
    assert len(disagreeing) > 0
    assert text.count("**Jev's candidate.**") == len(disagreeing)
    assert "first 19 times, in its top three 26 times" in text
    assert "right 16 of 21 times at or above 0.7" in text
    entries = text.count("\n## ")
    assert text.count("**Candidate.**") == entries == text.count("**Row.**")
    assert "rows below, of" in text


def test_jev_calibrate_scores_the_recorded_answer_on_the_scorer_s_own_population() -> None:
    """Same rows as calibrate(): one recorded declaration, in a file offering at least two.
    A fake that always answers the recorded name scores every row; one that never does
    scores none, and the misses list names the rows it got wrong."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    truth = {r["id"]: fp.row_decls(r)[0] for r in ledger if len(fp.row_decls(r)) == 1}
    oracle = fp.jev_calibrate(index, ledger, _fake_ask(pick=truth, confidence=0.9),
                              sample=12, seed=1, workers=1)
    assert oracle["sampled"] == 12 and oracle["top1"] == 12 == oracle["top3"]
    assert oracle["confident"] == 12 == oracle["confident_correct"] and oracle["misses"] == []
    assert oracle["resolved"] == fp.calibrate(index, ledger)["resolved"]
    assert oracle["eligible"] <= oracle["resolved"]
    blind = fp.jev_calibrate(index, ledger, _fake_ask(none_for=set(truth)),
                             sample=12, seed=1, workers=1)
    assert blind["top1"] == 0 and blind["none"] == 12 and len(blind["misses"]) == 12
    assert {m["id"] for m in blind["misses"]} <= set(truth)


def test_jev_key_tracks_the_statement_the_file_and_the_offer() -> None:
    row = {"id": "X", "statement": "a claim", "lean": "Problems/X.lean"}
    offer = [{"name": "a"}, {"name": "b"}]
    key = fp.jev_key(row, offer)
    assert key != fp.jev_key({**row, "statement": "a claim."}, offer)
    assert key != fp.jev_key(row, offer[:1])
    assert key != fp.jev_key({**row, "lean": "Problems/Y.lean"}, offer)
    assert key == fp.jev_key(dict(row), list(offer))


def _fake_nouls(answer: dict[str, dict[str, float]] | None = None, *, seen: list | None = None):
    """An ``AskNouls`` that rates every row covered -- 0.9 for coverage, 0.1 for each failure
    mode -- unless ``answer`` maps a ledger id to the probabilities to return instead."""
    def ask(state, questions):
        if seen is not None:
            seen.append((state, questions))
        nouls = {"covers": 0.9, "claim_broader": 0.1, "decl_narrower": 0.1,
                 "different_result": 0.05}
        nouls.update((answer or {}).get(state["ledger_id"], {}))
        return {"nouls": {q: nouls[q] for q in questions}, "model": "jev-test",
                "input_tokens": 100}
    return ask


def test_jev_coverage_asks_every_resolved_row_with_all_the_declarations_it_names() -> None:
    """The retag rule is about the declarations a row names, all of them: a row joined to a
    list is asked about the list, and the four questions are the constant ones.  The offer
    verdicts and the calibration already in the record survive the run untouched."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    offers = fp.jev_propose(index, ledger, _fake_ask(), workers=1)
    offers["calibration"] = {"asked": "2026-09-21", "model": "jev-test", "sampled": 1,
                             "top1": 1, "top3": 1, "confident": 1, "confident_correct": 1,
                             "scorer_top1": 1}
    seen: list = []
    record = fp.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=offers, workers=1)
    resolved = {r["id"]: fp.row_decls(r) for r in ledger
                if fp.row_decls(r) and r["tag"] != "REFUTED"}
    assert any(fp.row_decls(r) and r["tag"] == "REFUTED" for r in ledger)  # the exclusion bites
    assert {s["ledger_id"] for s, _ in seen} == set(resolved) == set(record["coverage"]["rows"])
    for state, questions in seen:
        assert [d["name"] for d in state["declarations"]] == resolved[state["ledger_id"]]
        assert all(d["statement"] for d in state["declarations"])
        assert list(questions) == list(fp.JEV_COVERAGE_QUESTIONS)
    for verdict in record["coverage"]["rows"].values():
        assert set(fp.JEV_COVERAGE_QUESTIONS) <= set(verdict)
        assert {"key", "model", "asked", "decls"} <= set(verdict)
    assert record["rows"] == offers["rows"] and record["calibration"] == offers["calibration"]
    assert record["coverage"]["totals"]["asked_now"] == len(seen) == len(resolved)
    assert record["coverage"]["totals"]["unfound"] == 0


def test_jev_coverage_lists_a_known_bad_row_and_clears_the_covered_ones() -> None:
    """The known-bad input.  A row Jev rates as broader than its declaration is filed as not
    covered with that reading; a row with doubtful coverage and no mode above half is listed
    under the doubtful mark and says so; a row rated covered is left off even when a failure
    mode is high, because coverage alone lists; a record of all-covered rows lists nothing."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    ids = [r["id"] for r in ledger if fp.row_decls(r) and r["tag"] != "REFUTED"]
    broad, doubtful, covered = ids[0], ids[-1], ids[1]
    answer = {broad: {"covers": 0.1, "claim_broader": 0.9},
              doubtful: {"covers": 0.3},
              covered: {"covers": 0.55, "decl_narrower": 0.8}}
    record = fp.jev_coverage(index, ledger, _fake_nouls(answer), workers=1)
    rows = {r["id"]: r for r in fp.coverage_rows(index, ledger, record)}
    assert rows[broad]["flagged"] and rows[broad]["reading"] == "claim_broader"
    assert rows[broad]["band"] == "not_covered"
    assert rows[doubtful]["flagged"] and rows[doubtful]["reading"] is None
    assert rows[doubtful]["band"] == "doubtful"
    assert not rows[covered]["flagged"] and rows[covered]["band"] == "covered"
    assert rows[covered]["reading"] == "decl_narrower"
    assert sum(r["flagged"] for r in rows.values()) == 2
    text = fp.coverage_digest(index, ledger, jev=record)
    assert text.startswith("# Coverage review queue")
    assert text.count("\n## ") == 2
    first, mark, second = (text.index(f"`{broad}`"), text.index("**Doubtful from here"),
                           text.index(f"`{doubtful}`"))
    assert first < mark < second                                       # lowest coverage first
    assert "Reads as: the claim asserts more than the declarations state (0.9)" in text
    assert "coverage itself is doubtful" in text
    assert f"resolved rows: {len(ids) - 2} covered," in text
    assert "1 doubtful, 1 not covered; 2 are" in text
    statement = next(r["statement"] for r in ledger if r["id"] == broad)
    assert ("likeliest mis-joins" in text) == (len(statement) < 150)
    assert text.count("```lean") == len(fp.row_decls(next(r for r in ledger if r["id"] == broad))) \
        + len(fp.row_decls(next(r for r in ledger if r["id"] == doubtful)))
    clean = fp.coverage_digest(index, ledger, jev=fp.jev_coverage(index, ledger, _fake_nouls(),
                                                                  workers=1))
    assert "\n## " not in clean and "0 are\nlisted below" in clean
    assert "Doubtful from here" not in clean


def test_jev_coverage_reuses_verdicts_until_the_row_or_its_declarations_change() -> None:
    """The key covers the statement and the declarations' text, so a row is re-asked when
    either moves and otherwise keeps its answer; ``only`` asks the named rows and keeps the
    rest; ``limit=0`` asks nothing; a changed row shows as stale and is not listed."""
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    first = fp.jev_coverage(index, ledger, _fake_nouls(), workers=1)
    n = first["coverage"]["totals"]["answered"]
    seen: list = []
    again = fp.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=first, workers=1)
    assert seen == [] and again["coverage"]["rows"] == first["coverage"]["rows"]
    victim = next(iter(first["coverage"]["rows"]))
    seen = []
    some = fp.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=first,
                           refresh=True, only={victim}, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]
    assert some["coverage"]["totals"]["answered"] == n
    seen = []
    none = fp.jev_coverage(index, ledger, _fake_nouls(seen=seen), cached=first,
                           refresh=True, limit=0, workers=1)
    assert seen == [] and none["coverage"]["totals"]["answered"] == n
    moved = json.loads(json.dumps(ledger))
    row = next(r for r in moved if r["id"] == victim)
    row["statement"] = row["statement"] + " And one more claim."
    rows = {r["id"]: r for r in fp.coverage_rows(index, moved, first)}
    assert rows[victim]["verdict"] == "stale" and not rows[victim]["flagged"]
    assert "need a rerun" in fp.coverage_digest(index, moved, jev=first)
    seen = []
    fp.jev_coverage(index, moved, _fake_nouls(seen=seen), cached=first, workers=1)
    assert [s["ledger_id"] for s, _ in seen] == [victim]


def test_coverage_digest_says_so_when_jev_has_not_been_asked() -> None:
    index = fp.build()
    ledger = json.load(io.open(fp.LEDGER, encoding="utf-8"))
    text = fp.coverage_digest(index, ledger, jev={})
    assert "has not been asked yet" in text and "\n## " not in text


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
        ("jev-coverage --limit 0", fp.COVERAGE, fp.coverage_digest(index, ledger)),
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
