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

`explore → distill → prove/refute → decide`. Emit the triage block from
`.cursor/rules/methodology.mdc` (including `Already killed by?`). Do not
reprint it here. Then stop; do not auto-open the next branch.

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
python -m research.juggler_sequence.branch_index --check
python -m research.juggler_sequence.branch_index show <id>
python -m research.juggler_sequence.branch_index search <query>
python -m research.juggler_sequence.branch_index new <id>
python tools/render_theorem_ledger.py --check
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd formal; lake build                               # no sorry / admit
```

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
[.agents/skills/developing-with-streamlit/SKILL.md](.agents/skills/developing-with-streamlit/SKILL.md).
