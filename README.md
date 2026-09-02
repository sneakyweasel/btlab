# Balanced Ternary Mathematical Laboratory

An exact-arithmetic **research platform**. Balanced ternary mathematics is
the core. Research problems are independent applications. The active
application is the **Juggler map**
\(T(n)=\lfloor\sqrt n\rfloor\) (\(n\) even),
\(\lfloor n\sqrt n\rfloor\) (\(n\) odd).

This repository does **not** claim a solution of the Collatz conjecture or
of any other open problem. Finite checks are never presented as proofs.
Claims are labelled **EXACT — HUMAN PROOF**, **EXACT — LEAN VERIFIED**,
**COMPUTATIONALLY VERIFIED**, **CONJECTURE**, **OBSERVATION**,
**REFUTED**, or **REPARAMETERIZATION**. See
[docs/README.md](docs/README.md).

## What balanced ternary is

Every integer has a unique canonical expansion


n = \sum_i a_i 3^i,\qquad a_i \in -1,0,+1


with no leading zeros (except n=0). Display uses `-`, `0`, `+`
(most-significant digit first). Mathematical positions are indexed from
the least-significant digit a_0.

## Why this repository exists

To keep a **problem-independent** encoder, arithmetic, operators,
polynomials, automata, and transducers, and to attach new open problems
as modules that import `bt` but never the reverse. Experimental dynamics
that are not BT-specific live in `research_engine` and are imported by
problem adapters, not by the core.

## How research is done here

Each direction runs the loop **explore → distill → prove/refute →
decide**, under a written budget that fixes the target, the novelty
hypothesis, and the falsifier before implementation starts. Every branch
ends in exactly one decision — `PROMOTE`, `PARK`, or `CLOSE` — and a
closed branch stays documented so it is not rediscovered. Machinery is a
means: reusable primitives are welcome, taxonomies without a
theorem-level payoff are not.

See [docs/methodology.md](docs/methodology.md).

## Core (`bt`)

Representation, arithmetic, normalization, operators (`S`, `N`, `D`,
`W`, `M2`, `H2`, …), the trit calculus (`D`, `I_a`, `cmp3`, `select3`,
rewrite), metrics, support, polynomials P_n with
P_n(3)=n, generic automata, and generic transducers.

```python
from bt import decode, encode

word = encode(42)
assert decode(word) == 42
```



## Research applications (`research`)

The live publication task is the Juggler programme: Paper A
([cycle-length lower bounds](docs/theory/juggler_finite_dynamics_note.md))
and Paper B
([parity discrepancy](docs/theory/juggler_parity_discrepancy_note.md)).
Reviewer snapshot: [juggler_review/](juggler_review/). Companion:
[web/juggler-companion/](web/juggler-companion/). Reading path:
[AGENTS.md](AGENTS.md). This is not a halt theorem and not a
Collatz-style solution claim.

The rewrite-calculus note remains ready to send
([draft](docs/theory/rewrite_calculus_note.md),
[reviewer packet](docs/theory/rewrite_calculus_reviewer_packet.md)).
The cubic Newton stratum is the last promoted BT-core theory; it is
parked. Full table:
[docs/architecture/research_modules.md](docs/architecture/research_modules.md).


| Module                                         | Status          |
| ---------------------------------------------- | --------------- |
| `research.juggler_sequence`                    | PAPER_CANDIDATE |
| `research.rewrite_calculus`                    | PAPER_CANDIDATE |
| `research.residuals`                           | STRUCTURAL      |
| `research.collatz`                             | STRUCTURAL      |
| `research.ostrowski`                           | STRUCTURAL      |
| `research.regular_output_preimages`            | STRUCTURAL      |
| `research.residual_complexity`                 | STRUCTURAL      |
| `research.monna_endpoint_spectra`              | STRUCTURAL      |
| `research.lifting`                             | EXPLORATORY     |
| `research.additive_combinatorics`              | EXPLORATORY     |
| `research.perfect_powers`                      | EXPLORATORY     |
| `research.primes`                              | EXPLORATORY     |
| `research.sparse_polynomials`                  | EXPLORATORY     |
| `research.operator_dynamics`                   | EXPLORATORY     |
| `research.balanced_ternary_digit_sum_dynamics` | ARCHIVED        |
| `research.balanced_ternary_weight_dynamics`    | ARCHIVED        |
| `research.balanced_ternary_weight_drift`       | ARCHIVED        |
| `research.balanced_digit_sum_polynomials`      | EXPLORATORY     |
| `research.erdos_distinct_subset_sums`          | EXPLORATORY     |
| `research.kabelian_complexity`                 | ARCHIVED        |
| `research.stabilization`                       | ARCHIVED        |
| `research.padic_dynamics`                      | ARCHIVED        |
| `research.cerny_bt`                            | ARCHIVED        |
| `research.misere_quotients`                    | ARCHIVED        |


```python
from research.juggler_sequence.power_itineraries import floor_power

assert floor_power(3) == 5
```



## Formal verification

Lean 4 + Mathlib under `formal/`. No `sorry` or `admit`.

```powershell
cd formal
lake update
lake exe cache get
lake build
```

See [formal/README.md](formal/README.md) and
[docs/architecture/formalization.md](docs/architecture/formalization.md).

## Current open problems and conjectures

The Juggler cycle programme is terminal on the laboratory side:
no nontrivial cycle of period \(<478245\) at the certified floor
\(N_0=162849448\). Further period progress is Diophantine (partial
quotients of \(\log 2/\log 3\)), not a new floor campaign. Closed
and refuted Juggler hypotheses stay under `conjectures/refuted/`
and [docs/juggler_branch_ledger.md](docs/juggler_branch_ledger.md).
Parked BT-core registry entries remain in `conjectures/`.

```powershell
btlab conjectures list
btlab status
```



## Quick start

Python 3.11 or newer:

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -e ".[dev,ui]"
pytest
```

Optional Parquet experiment I/O: `pip install -e ".[experiments]"`.

## CLI

The command is `btlab`. Leaf commands stay for encoding and analysis;
namespaces group operators, calculus, research, and Collatz.

```powershell
btlab encode 42
btlab bt encode 42
btlab operators apply S 42
btlab calculus eval 42
btlab research analyze ostrowski
btlab research reproduce D
btlab collatz analyze 27
btlab status
```

Research UI (optional extra `ui`). Canonical launcher:

```powershell
btlab ui
```

`btlab collatz ui` and `btlab calculus explorer` remain aliases.

## Tests and Lean

```powershell
pytest
pytest --runslow
cd formal
lake build
```

`pytest` skips the slow marker (k>10 residual censuses, million-range identities, Streamlit AppTests) and runs in parallel. Full suite: `pytest --runslow`. Serial: `pytest -n 0`.

## How to add a new research problem

1. Copy [docs/problems/TEMPLATE.md](docs/problems/TEMPLATE.md) to
  `docs/problems/<id>.md`.
2. Copy `src/research/template/` to `src/research/<id>/` and fill
  `problem.py`.
3. Import only `bt.*` plus shared experiment/registry utilities.
4. Register conjectures in `conjectures/` and literature in `literature/`.
5. Add tests under `tests/research/` and witnesses under `tests/regression/`.
6. Do not edit core arithmetic to introduce the problem.

Every new problem starts from a branch budget and ends in a decision:
[docs/methodology.md](docs/methodology.md).

Architecture: [docs/architecture/overview.md](docs/architecture/overview.md).
Documentation map: [docs/README.md](docs/README.md).
Journal: [docs/research_journal.md](docs/research_journal.md).

## The Ballad of the Hug Word

*A laboratory song, to be hummed while `lake build` runs.*

> **Verse 1**
> Oh the Juggler takes you up on odd, and down when you are even,
> Root three-halves of what you were, no cycle worth believin'.
> We set the floor at four hundred million, watched the orbits fall —
> But one shy word at four-seven-eight still wouldn't die at all.
>
> **Chorus**
> Hug the wall, hug the wall, cheapest walk of all,
> Every cycle pays its debt in logs before the fall.
> One point two per floor you lose, the ledger keeps the score —
> And Lean has signed the bottom line: *you can't afford the tour.*
>
> **Verse 2**
> The finance man says three-to-the-o must cover two-to-the-L,
> The hug word walks the rotation line and charges you like hell.
> Denjoy and Koksma hold the coats, the digits stay below —
> Forty-seven, structurally, wherever the quotients go.
>
> **Final chorus, ritardando**
> Hug the wall, hug the wall, the envelope is tight,
> Transport to the reduced base and read the logs at night.
> No `sorry` in the ledger, no cycle in the ring —
> Just one Diophantine blocker left, and the partial quotients sing.