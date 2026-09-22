# Agent guide

This is the **Juggler–Collatz Mathematical Laboratory**. Active research is
Juggler and the signed Collatz maps, supported by exact arithmetic (`bt`) and
shared experimental machinery. Independent earlier projects are frozen in the
[archive](archive/README.md), outside the default research scope.
The **Juggler map** is
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
laboratory-kill CLOSE); the closure threshold is a minimum lower bound
\(n\gg L^{5.1163051}\), never below \(L^{2}\)
(`J-cyclemin-closure-threshold`). Termination: exported exponent-pair leftover,
not a Juggler construction. Fates: contagion is now unconditional at
\(\lambda=5/8\), with the actual OOEE production and source cutoff
proved in Lean (`J-ooee-contagion-five-eighths`);
Tao reduction is still conditional on a rate, now at \(e>3/8\).
Flights: descriptively terminal.

**Do not reopen.** Local attacks (Collision Factorization); Baker/SdW;
Paper A×B merge; DK-arch free-kill; floor-Hardy reformulations; kernel
localize; harvest counting; slogan halt theorems. Search
[docs/negative_knowledge.md](docs/negative_knowledge.md) first.

Claim labels: [docs/README.md](docs/README.md).
Research method: [docs/methodology.md](docs/methodology.md).
Earlier BT-core, cubic-stratum and rewrite research is archived. Retain its
sources and negative knowledge for citations; do not develop it as a parallel
frontier without an explicit user request.

## How a direction runs

`explore → distill → prove/refute → decide`. Emit the triage block from
`.cursor/rules/methodology.mdc` (including `Already killed by?`). Do not
reprint it here. Then stop; do not auto-open the next branch.

## Shared mathematics and Collatz

Trit / `D` / jets / `≡_k` → `src/bt/calculus/`; cubic strata →
`src/research/residuals/`; Collatz → `src/research/collatz/`; generic Lean
→ `formal/BTCalculus/`. No `bt.calculus` shims, no compatibility packages.
New applications outside Juggler/Collatz require an explicit scope change.
Within scope, use [docs/problems/TEMPLATE.md](docs/problems/TEMPLATE.md).
The [scope policy](data/lab_scope.json) preserves imported dependencies even
when their historical names refer to balanced ternary.

## Commands

```powershell
python -m pip install -e ".[dev,ui]"
pytest                                              # fast suite
pytest tests/research/juggler_sequence -q           # Juggler only
pytest --runslow
python -m research.juggler_sequence.<branch>        # run a probe
python -m research.juggler_sequence.branch_index --check
python -m research.juggler_sequence.branch_index show <id>
python -m research.juggler_sequence.branch_index search <query>
python -m research.juggler_sequence.branch_index new <id>
python tools/render_theorem_ledger.py --check
python tools/branch_drift.py                        # results stranded on branches
zgrep -m1 "^A094683 " data/external/oeis/names.gz    # local OEIS, no network
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
python tools/lab.py build                          # active Lean graph; no sorry / admit
```

`pytest --include-archive` and `python tools/lab.py build --include-archive`
check the historical library. Formalpedia search and OEIS laboratory links
default to active scope; request `scope=archive` or `scope=all` for old projects.
Exact theorem/claim lookups and the global OEIS database remain unrestricted.
Package names and the paper-pinned Lake file retain their historical names.

## OEIS, locally

`data/external/oeis/` holds `stripped.gz` (all terms) and `names.gz` (all
names), gitignored, refetched with `curl -o <name> https://oeis.org/<name>`.
The full internal-format records -- comments, links, formulas, programs --
are a shallow clone of `oeis/oeisdata` outside the repository; its `files/`
tree is Git LFS pointers, so b-files are not local. Some sessions have
`oeis.org` refused by egress policy and this is the way in for them.

Before sweeping it, read
[juggler_oeis_neighbourhood](docs/problems/juggler_oeis_neighbourhood.md): the
Juggler corner is already swept, and a second session repeated the whole of it.

Use the local `btlab-oeis` MCP for indexed full-text and exact term searches,
published comments, cross-references and laboratory links. Its
[operating guide](docs/architecture/oeis_discovery.md) covers offsets,
subsequence matching and provenance. `python tools/oeis_index.py` rebuilds the
ignored index from the local mirror's committed snapshot; MCP queries are
read-only and never fetch files or submit edits. Use `oeis_status` for coverage
and export freshness, and `oeis_bfile` to distinguish content from LFS pointers.

## Adding a Lean module or a probe (checklist)

Juggler Lean modules and probes: follow the registration sections in
[attacks/juggler/AGENT.md](attacks/juggler/AGENT.md), then rebuild
`attacks/juggler/index.json`. Lab-wide ledger and link gates stay in
`.cursor/rules/environment.mdc`.

## prove2.me

External Lean 4 platform (https://prove2.me), distinct from the local
`tools/formalpedia.py` index. Full guide:
[`.claude/skills/prove2me/SKILL.md`](.claude/skills/prove2me/SKILL.md).
Ask the human before any public submit or verify.

## Remarks

If you're Fable don't spend ages fixing tests - focus on the math.

You have access to a Windows 11 machine with an AMD Ryzen 9 3900X (12C/24T), 64 GB RAM, and an RTX 5090 (32 GB VRAM, CUDA 13.3), so don't be afraid to use it.

Persistent policy lives in [.cursor/rules/](.cursor/rules/). Streamlit work uses
the `developing-with-streamlit` skill, which ships with the `streamlit`
dependency rather than living in this repository: after
`pip install -e ".[dev,ui]"` it is at
`<site-packages>/streamlit/.agents/skills/developing-with-streamlit/SKILL.md`.
`.agents/` is a gitignored convenience symlink to it and is absent from a
fresh clone, so do not link it as a repository path.
