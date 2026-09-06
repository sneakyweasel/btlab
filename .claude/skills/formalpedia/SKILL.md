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
```

`<target>` accepts a module (`Problems.Juggler.CycleFinance`), a repo path, or a path
fragment (`Problems/Juggler/CycleFinance.lean`).

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
carries **no `sorry`**, and the Juggler layer keeps exactly two proofs off the kernel —
`greedy_eq_ostro_below_window` and `window_digit_scan`, the Ostrowski scans that Paper A's
Section 1.2 names. `tests/tools/test_formalpedia.py` fails if either stops being true, which
is the point: a third `native_decide` in that layer would silently falsify a published
sentence.

If you add one deliberately, update Paper A's Section 1.2 and the test together.

## Keeping the index current

The committed index at `data/research/formalpedia/index.json` goes stale as soon as anyone
adds a declaration. It costs about a second to rebuild, so rebuild before trusting a search
that matters, and commit the result alongside Lean changes that add or remove declarations.

If a search returns nothing surprising and you suspect the index rather than the corpus, run
`build` first and search again before concluding anything.
