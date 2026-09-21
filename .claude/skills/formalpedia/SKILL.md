---
name: formalpedia
description: Query the Lean theorem index at tools/formalpedia.py before touching anything under formal/. Use this whenever you are about to edit, add, rename or delete a Lean declaration; before proving a lemma that may already exist; when asked what a change would break or what depends on a module; when checking whether a proof is kernel-checked or rests on native_decide; or when connecting a theorem-ledger id to the declaration behind it. Several Claude sessions work this repository at once, so "who else depends on this?" is a question worth answering before the edit rather than after.
---

# formalpedia

`tools/formalpedia.py` indexes every Lean declaration the laboratory defines — 4,570 of them
across 189 modules — and joins them to the 597-row theorem ledger. It reads the sources
directly, so it is current the moment you rebuild it and never needs `lake`.

```bash
python tools/formalpedia.py build            # rebuild the index (~1s)
python tools/formalpedia.py search <text>    # match a name or docstring
python tools/formalpedia.py show <name>      # one declaration, in full
python tools/formalpedia.py impact <target>  # what a change here would rebuild
python tools/formalpedia.py jev-propose      # ask Jev which theorem each unresolved row means
python tools/formalpedia.py jev-calibrate    # score Jev on rows whose theorem is recorded
python tools/formalpedia.py jev-coverage     # does a recorded theorem cover its row? (the retag rule)
```

`<target>` accepts a module (`Problems.Juggler.CycleFinance`), a repo path, or a path
fragment (`Problems/Juggler/CycleFinance.lean`).

## Jev beside the scorer

The proposal queue (`propose`, `review`) joins ledger rows that name no declaration to the
theorems of their file by word overlap, and hands the confident ones to a person. Jev,
TypeSafe's typed-judgment model, answers the same question from the statements themselves:
`jev-propose` offers it every unresolved row's own theorems, docstring and header each, plus
"none of these", and caches its pick and confidence in
`data/research/formalpedia/jev_verdicts.json`. `propose` merges a cached verdict onto its row
as a `jev` field beside the scorer's candidates, and a pick at or above `JEV_REVIEW` (0.7)
lists the row in the digest whatever the scorer thought. Candidates are never replaced, and
nothing is written into the ledger: Jev is a second opinion for the reviewer.

```bash
pip install -e ".[jev]"                       # typesafe-sdk; needs TYPESAFE_API_KEY
python tools/formalpedia.py jev-calibrate --sample 40   # measure before trusting
python tools/formalpedia.py jev-propose                # ~130 rows, a few cents
```

Both commands rewrite the verdict record and the two artifacts that merge it,
`decl_proposals.json` and `formalpedia_decl_review.md`; commit the three together. A
verdict is keyed on the row's statement, its file and the names offered, so a row that
changes is asked again on the next run and shows as stale until then; `--refresh` re-asks
everything, `--limit N` asks N rows now and keeps the rest. Calibration is stored with its
date, model and sample in the record, and the digest quotes those figures, not a constant:
on 21 September 2026, thirty resolved rows, Jev put the recorded declaration first 19 times
and in its top three 26, against 16 for the scorer, and 16 of its 21 answers at or above 0.7
were right. Most of what it got "wrong" were composite rows, where "none of these" is a fair
reading, or a better join than the recorded one; read a disagreement before ruling on it.

### The retag rule, asked

`EXACT — LEAN VERIFIED` is allowed only when the Lean theorem covers the English statement,
and nothing checked that. `jev-coverage` asks it of every resolved row as four Nouls over the
claim and every declaration the row names: covers, claim broader than the declarations,
declaration narrower than the claim, different result. Rows with coverage below 0.5 are
listed in `docs/research/formalpedia_coverage_review.md`, lowest first, filed as not covered
below 0.25 and doubtful between, each with the statement and every declaration in full and
the failure mode Jev rates highest as the reading to check first. The questions set the
row's provenance, trust remarks and disclaimers aside and judge the declarations together;
the first wording did neither and listed nine rows in ten. Before retagging one row, ask
about that row alone:

```bash
python tools/formalpedia.py jev-coverage --rows J-my-row-id
```

The verdict is keyed on the statement and the declarations' text, so an edit to either
re-asks that row and shows it as stale until then; `--limit 0` rewrites the digest from the
cache without asking. The remedies are the ledger's own: extend `decl` to the declarations
that together state the claim, narrow the statement, or retag to `EXACT — HUMAN PROOF`.

## Before editing a Lean file, run `impact`

This is the habit worth forming. Several agents work this repository concurrently, and the
collisions are never mathematical — they are two sessions changing things that turn out to be
connected, discovered only when something downstream fails.

```
$ python tools/formalpedia.py impact Problems/Juggler/OstrowskiSandwich.lean
Problems.Juggler.OstrowskiSandwich (29 declarations)
  imported directly by 4, transitively by 5
     Problems
   * Problems.Juggler
   * Problems.Juggler.FanLaw
   * Problems.Juggler.OstrowskiNumeration
   * Problems.JugglerPaper
```

Entries marked `*` import the module directly; the rest arrive through the graph. A module
reaching `Problems.JugglerPaper` is load-bearing for a manuscript, which raises the bar for
changing its statements as opposed to its proofs.

Read the result as a scope estimate, not a permission slip. A wide blast radius is a reason to
say what you are about to touch before you touch it, and to prefer adding a lemma over
restating an existing one.

## Before proving something, search for it

The corpus is large enough that reproving something already present is a live risk, and the
duplicate is worse than the wasted effort — it gives the same fact two names, and the next
reader cannot tell which one the manuscripts cite.

```
$ python tools/formalpedia.py search "finance"
cycleMin_finance  [kernel]  formal/Problems/Juggler/CycleFinance.lean:210
    **Cycle finance inequality.** For any cycle taken at its minimum: `n log n (3^o - 2^L) ...
```

Search covers names and docstrings. Only about 28% of declarations carry a docstring, so a
miss is weak evidence of absence — try the name of the object as well as the name of the
result, and look at the module you would put it in before concluding it is not there.

## `show` gives the whole row

```
$ python tools/formalpedia.py show cycleMin_finance
{
  "doc": "**Cycle finance inequality.** For any cycle taken at its minimum: ...",
  "file": "formal/Problems/Juggler/CycleFinance.lean",
  "kind": "theorem",
  "ledger": ["J-cycle-finance-inequality", "J-lachesis-basin-inverse-sum"],
  "line": 210,
  "module": "Problems.Juggler.CycleFinance",
  "name": "cycleMin_finance",
  "trust": "kernel"
}
```

The `ledger` ids are inherited from the file, not resolved per declaration — the ledger's
`lean` field names a file in 321 of 322 rows. Treat them as "this file backs these claims",
and check the ledger row itself before quoting one as the statement of this theorem.

## Trust levels are claims the papers make

Each declaration is classified by reading its proof body:

| level | meaning |
|---|---|
| `kernel` | checked by Lean's kernel |
| `compiler` | rests on `native_decide`; the compiler is trusted, not the kernel |
| `open` | carries a `sorry` |

Two facts here are asserted in the manuscripts, so changing them changes a paper: the corpus
carries **no `sorry`**, and the Juggler layer keeps exactly **one** proof off the kernel —
`window_digit_scan`, the Ostrowski scan that Paper A's Section 1.2 names.
`tests/tools/test_formalpedia.py` fails if either stops being true, which is the point: a
second `native_decide` in that layer would silently falsify a published sentence.

It was two. `greedy_eq_ostro_below_window` was the other until it became a corollary of
`greedy_eq_ostro` rather than a scan, and it now carries no compiler-trust assumption;
Paper A's Section 1.2 records that transition. A reader asking the different question —
which of Paper A's theorems would *fall* if the compiler were wrong — gets a second name,
`window_digit_cap`, which cites the scan. Both sentences are true and the ledger carries
both.

If you add one deliberately, update Paper A's Section 1.2 and the test together.

## Keeping the index current

The committed index at `data/research/formalpedia/index.json` goes stale as soon as anyone
adds a declaration. It costs about a second to rebuild, so rebuild before trusting a search
that matters, and commit the result alongside Lean changes that add or remove declarations.

If a search returns nothing surprising and you suspect the index rather than the corpus, run
`build` first and search again before concluding anything.

### Check `git status` before you commit a rebuild

`formalpedia` reads the **working tree**, not `HEAD`. That is what makes `impact` useful
before an edit, and it is what makes committing a rebuild from a shared checkout unsafe:
several sessions work this repository at once, and a rebuild will quietly bake their
*uncommitted* declarations into an index you then commit.

```bash
git status --porcelain formal/     # only your own .lean should be dirty
```

If someone else's Lean is modified, do not commit the artifacts. Either wait for them to
land, or make your source change and say plainly that the rebuild is owed — your docstring
can wait a commit; their unfinished work appearing in a committed index cannot be undone
quietly, and they may not find out.

This happened on 19 September 2026: a one-line docstring change triggered a rebuild that
committed seven of a peer's unlanded window-empty declarations (`4a6240e9`, backed out in
`00466925`), hours after the same session had warned a third session about it. Twice is a
pattern, which is why it is written here rather than left to memory.

Note the incentive, because it points the wrong way.
`test_every_committed_artifact_matches_a_fresh_build` also compares against the working
tree, so committing the contaminated artifacts turns it **green** and backing them out
turns it **red** until the peer lands. Red is the correct state. A green gate bought by
describing someone else's unfinished work is a false statement about the repository, and
false in a way no one can see. Leave it red and say why in the commit message.
