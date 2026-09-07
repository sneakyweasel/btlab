# Agent guide

This is the **Balanced Ternary Mathematical Laboratory**: a
problem-independent core (`bt`) plus independent research applications
(`research.*`). The active application is the **Juggler map**
\(T(n)=\lfloor\sqrt n\rfloor\) (\(n\) even), \(\lfloor n\sqrt n\rfloor\)
(\(n\) odd).

```text
cli, visualization          application edges
research.*                  problem-specific mathematics
research_engine             problem-independent experimental dynamics
bt.*                        problem-independent BT mathematics
```

`bt.*` must never import `research.*` or `research_engine`. Architecture:
[docs/architecture/overview.md](docs/architecture/overview.md).

## Juggler (live application)

Full reading path, state of the problem, file map, and registration:
[attacks/juggler/AGENT.md](attacks/juggler/AGENT.md). Branch lookup:
[attacks/juggler/index.json](attacks/juggler/index.json).

**Floors.** No nontrivial cycle of period \(<780239\) at
\(N_0=350000000\). Do not raise \(N_0\). Next useful floor
\(5.54\cdot 10^8\) is PARK.

**Live frontiers.** Cycles: Diophantine near-convergents (Paper D;
laboratory-kill CLOSE). Termination: exported exponent-pair leftover,
not a Juggler construction. Fates: contagion \(\lambda^{**}=0.4926\);
Tao reduction is conditional. Flights: descriptively terminal.

**Do not reopen.** Local attacks (Collision Factorization); Baker/SdW;
Paper A×B merge; DK-arch free-kill; floor-Hardy reformulations; kernel
localize; harvest counting; slogan halt theorems. Search
[docs/negative_knowledge.md](docs/negative_knowledge.md) first.

Claim labels: [docs/README.md](docs/README.md).
Research method: [docs/methodology.md](docs/methodology.md).
BT-core theory (STRUCTURAL, parked): `docs/theory/balanced_ternary_calculus.md`,
`cubic_newton_stratum.md`; the rewrite-calculus note remains ready to send
for external review.

## How a direction runs

`explore → distill → prove/refute → decide`. Before substantial
implementation, output a triage block:

```text
Mathematical target     one precise question
Novelty hypothesis      what could possibly be new
Falsifier               the observation that kills the idea
Existing machinery      what the platform already provides
Maximum Phase-0 scope   the smallest experiment that answers the target
Promotion criterion     what would justify PROMOTE
Stop criterion          what forces PARK or CLOSE
```

Implement only that scope. Search [docs/negative_knowledge.md](docs/negative_knowledge.md), `conjectures/refuted/`, the branch
ledger, and the `REFUTED` ledger rows before re-testing a hypothesis.

At the end of a phase, report:

```text
What was learned      3–7 concise points
Strongest theorem     one statement
Strongest refutation  one false hypothesis or counterexample, if any
Reusable machinery    what enters the platform
Branch status         PROMOTE | PARK | CLOSE
Why                   one short paragraph
Best next question    exactly one
```

Then stop. Machinery gravity — new structure, new CLI, new visualization,
no new mathematical consequence — means stop implementing, find the
invariant or obstruction, and decide. Every branch ends in `PROMOTE`,
`PARK`, or `CLOSE`; do not auto-open the next one. Do not raise \(N_0\),
reopen finance, or edit Paper A from a Phase-0 branch. Do not
generate nearby reformulations of the floor-Hardy composition.

## Where non-Juggler math goes

Trit / `D` / jets / `≡_k` → `src/bt/calculus/`; cubic strata →
`src/research/residuals/`; Collatz → `src/research/collatz/`; generic Lean
→ `formal/BTCalculus/`. No `bt.calculus` shims, no compatibility packages.
New research area: [docs/problems/TEMPLATE.md](docs/problems/TEMPLATE.md)
plus `src/research/<id>/`.

## Commands

```powershell
python -m pip install -e ".[dev,ui]"
pytest                                              # fast suite
pytest tests/research/juggler_sequence -q           # Juggler only
pytest --runslow
python -m research.juggler_sequence.<branch>        # run a probe
python tools/render_theorem_ledger.py --check
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd formal; lake build                               # no sorry / admit
python -m research.juggler_sequence.branch_index --check
```

## Adding a Lean module or a probe (checklist)

Juggler Lean modules and probes: follow the registration sections in
[attacks/juggler/AGENT.md](attacks/juggler/AGENT.md), then rebuild
`attacks/juggler/index.json`. Lab-wide ledger and link gates stay below.

## Environment notes for agents

- Shell is PowerShell: no `head`/`tail`/heredocs (`<<'EOF'` fails);
  use `Select-Object -First/-Last`, `Select-String`, and write
  multi-line scripts to a temp file. `rg` globs like `dir/*.lean`
  fail on Windows paths — use `rg -g "*.lean" dir`; parentheses in
  `rg` patterns must be escaped or avoided.
- **LaTeX and Python strings.** The papers hold 2639 macros across 42
  names that a *non-raw* Python string silently corrupts — `\tfrac`
  (675), `\nu` (199), `\theta` (195), `\beta` (179), `\rfloor` (145),
  `\varepsilon` (144), `\frac` (123), `\text`, `\asymp`, `\alpha`,
  `\rho`, `\to`, `\bigl` … Any macro starting with `a b f n r t v 0 x`
  is an escape: `"\theta"` is TAB + `heta`, `"\nu"` is NEWLINE + `u`,
  `"\approx"` is BEL + `pprox`, `"\frac"` is FF + `rac`. **This is
  Python, not the shell** — a quoted heredoc (`<<'PY'`) passes the text
  through untouched; the damage happens in the string literal on the
  far side, so blaming "heredoc mangling" sends you to the wrong fix.
  Therefore:
  1. To change a file containing LaTeX, use the Edit/Write tools.
     There is no string layer, so there is nothing to escape.
  2. If a script is genuinely needed, write it to a file with Write and
     then run it. Not `python <<'PY'`, not `python -c "…"`.
  3. If a Python string must carry LaTeX, make it raw: `r"\theta"`.
  4. Symptoms: a literal tab or a stray line break inside a `.md`; a
     regex that quietly stops matching; `SyntaxWarning: invalid escape
     sequence`. Three real defects reached the manuscripts this way
     (`\theta` in Paper A §5, `\to` in §3, `\theta(L)` in the reviewer
     packet) and survived several revisions.
  `test_manuscript_consistency.py::test_no_mangled_latex_escapes`
  catches the tab case — no legitimate tab exists in these documents.
  It cannot catch a stray *newline*, so prefer assertions whose target
  string fits on one line.
- Floats: `10.0**1000` overflows; work in `log y`.
- The fast suite (`pytest`, xdist) takes ≈ 3.5 min; the research-control
  tests regenerate `docs/research/*.json` artifacts (harmless
  churn). The working tree may be auto-committed by the host between
  turns; check `git log -1` before assuming files are uncommitted.
- Mathlib names used here: `Nat.eq_sqrt`, `Nat.le_sqrt`, `Nat.sqrt_lt`,
  `Nat.pow_le_pow_iff_left`, `Function.iterate_fixed`,
  `Function.iterate_mul`, `Function.iterate_add_apply`.
- **`lake build` does not build everything.** `defaultTargets` is
  `BTCalculus` and `Problems`, and the two paper barrels
  `Problems.JugglerPaper` / `Problems.JugglerParityPaper` are not
  imported by `Problems.lean`, so a plain `lake build` leaves them
  untouched. After any toolchain change build them by name, or
  `AxiomCheckPaperB.lean` fails on a stale olean with *incompatible
  header* and `test_manuscript_self_audit.py` reports it as a
  manuscript defect. `.lake/build` also carries orphan oleans whose
  sources were deleted (37 at the v4.33.1 bump); they are inert, but
  they make any stale-artifact sweep look alarming.

## prove2.me and Formalpedia (external platform)

- **What it is.** https://prove2.me is a Lean 4 theorem platform:
  missions, server-side kernel verification, permanent attribution.
  Every proved statement enters *Formalpedia*
  (https://prove2.me/formalpedia), a public library of ~58k theorems
  that later proofs can import. This is **not** the laboratory's
  `tools/formalpedia.py` (the local index over `formal/`), which keeps
  its name and its habits (`impact` before editing, `search` before
  proving).
- **Client.** `python tools/prove2me.py {whoami,envs,search,show,fetch,
  missions,leaves,verify,status}`; standard library only. The skill
  `.claude/skills/prove2me/SKILL.md` is the full guide.
- **Key.** User environment variable `PROVE2ME_API_KEY` (set with
  `setx`; open a new shell) and `~/.prove2me/credentials.json`. Prefix
  `p2m_`, valid 30 days (the current key expires 2026-10-07; a new one
  comes from the account menu on the site). Exchanged by the client for
  one-hour tokens at `POST /agent/refresh`. Never commit it, never send
  it to any domain other than prove2.me; `.env`, `credentials.json` and
  `prove2me_workspace/` are gitignored and
  `tests/tools/test_prove2me.py` fails if any tracked file carries a
  key-shaped string.
- **Environments match.** Both the platform default and `formal/` are
  Lean v4.33.1 + Mathlib `0df444a3…` (aligned 2026-09-07). Mathlib's
  source is identical either way, so proof text ports unchanged apart
  from imports and a solution that compiles here compiles there.
  Cross-environment *imports* remain impossible and a submitted
  solution may import only `Theorems.Thm_*` / `Definitions.Def_*`, so a
  Formalpedia hit is still a statement to port, not a module to import.
  Check `envs` before trusting the pin.
- **Submitting.** `theorem solution` at top level with the target's
  exact type; never import the target; sorry-free; `autoImplicit`
  false; targeted imports (no `import Mathlib`); explanation in
  Markdown + KaTeX, ≤ 50k chars. Verify locally in
  `$HOME/prove2me_workspace` (clone
  https://github.com/prove2me/prove2me_workspace and read its
  `SKILL.md`) before spending a server round trip; ≤ 100 pending
  submissions.
- **Publishing is irreversible.** Ask the human before any
  `submit-problem`, `submit-definition`, `verify` on a public theorem,
  or mission proposal, and say exactly what will be sent. A full upload
  of `formal/` results follows `references/upload_full_project.md`;
  axioms must be within `propext`/`Classical.choice`/`Quot.sound`, so
  the two `native_decide` proofs are excluded.
- **Docs.** `https://prove2.me/start.md`, `https://prove2.me/skill.md`
  (v0.9.7), `https://prove2.me/references/*.md`.

## Remarks

If you're Fable don't spend ages fixing tests - focus on the math.

You have access to a Windows 11 machine with an AMD Ryzen 9 3900X (12C/24T), 64 GB RAM, and an RTX 5090 (32 GB VRAM, CUDA 13.3), so don't be afraid to use it.

Persistent policy lives in [.cursor/rules/](.cursor/rules/). Streamlit work uses
[.agents/skills/developing-with-streamlit/SKILL.md](.agents/skills/developing-with-streamlit/SKILL.md).
