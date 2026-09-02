# Juggler even-run scale barriers

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

How strongly does minimality constrain even runs on a hypothetical
minimal non-terminating orbit? In particular, the orbit is **not**
known to be all-odd.

## Exact statement

Assume a minimal positive \(n_*\) with \(\neg\mathrm{ReachesOne}\,n_*\).
Minimality is quantified over \(m\ge 1\). Then every even run
\(m\xrightarrow{E^r}m_r\) that occurs on the orbit of \(n_*\) satisfies

\[
n_*^{2^r}\le m.
\]

The start \(n_*\) is odd and at least \(12\). The first image is odd.
Later even states are allowed once they lie at scale \(\ge n_*^2\).
Do not prove totality. Do not prove that the orbit is all-odd.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite `ReachesOne` interval \(\{1,\ldots,11\}\) and even residuals
  below \(144\) — **EXACT — LEAN VERIFIED**.
- `even_itinerary_contracts`, first-even freeze, changing-family capture —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. Minimality is turned into a
numerical lower bound on even-run entries. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     E^r on a minimal non-1 orbit implies entry >= n^{2^r}
Novelty hypothesis      Minimality plus even square-root gives a scale barrier
Falsifier               An even run with exit >= n but entry < n^{2^r}
Existing machinery      ReachesOne closure, even_itinerary_contracts, even_run identities
Maximum Phase-0 scope   MinimalNonTerm; barrier; normal form; short pattern census
Promotion criterion     Proved scale barrier, or a packaged finite-prefix normal form
Stop criterion          Halt; all-odd claim; PowerHeight; infinite paths; Q0/grammar programme
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `MinimalNonTerm` —
  **EXACT — LEAN VERIFIED**
- `even_run_scale_barrier` —
  **EXACT — LEAN VERIFIED**
- `minimal_nonterm_even_ge_sq` / first-even entry \(\ge n^2\) —
  **EXACT — LEAN VERIFIED**
- orbit stays \(\ge n\); no descent below \(n\); no capture —
  **EXACT — LEAN VERIFIED**
- first image odd; `OE` at the start is descent —
  **EXACT — LEAN VERIFIED**
- changing-family towers cannot lie on the orbit —
  **EXACT — LEAN VERIFIED**
- `minimal_counterexample_normal_form` —
  **EXACT — LEAN VERIFIED**
- even entries above the start occur on ordinary orbits —
  **COMPUTATIONALLY VERIFIED**
- all-odd orbit — not claimed
- global halt — not claimed
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.even_scale_barrier`
- Records: [juggler_even_scale_barrier.md](../research/juggler_even_scale_barrier.md),
  [juggler_even_scale_barrier.json](../research/juggler_even_scale_barrier.json)
- Tests: `tests/research/juggler_sequence/test_even_scale_barrier.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the scale barrier. Realized even runs on \(n\le 80\) obey
\(T^r(m)^{2^r}\le m\), and whenever the exit stays \(\ge n\) they also
obey \(n^{2^r}\le m\). Terminating orbits do collapse below their start;
that is compatible because those starts are not `MinimalNonTerm`.

The all-odd claim is already false as a necessary statement: ordinary
orbits visit even states above the start (e.g. \(3\to\cdots\to 36\)).

## Formalization

`formal/Problems/Engine/MinimalNonTerm.lean`, above
`FloorPower`. Added:

- `MinimalNonTerm`
- `minimal_nonterm_ge_of_not_reachesOne`
- `even_run_pow_le` / `even_run_exit_ge` / `even_run_scale_barrier`
- `minimal_nonterm_even_ge_sq` / `minimal_nonterm_first_even_ge_sq`
- `minimal_nonterm_avoid_even_lt_sq_twelve`
- `even_tower_not_on_minimal`
- `minimal_nonterm_oe_descent` / `minimal_nonterm_odd_image_odd`
- `minimal_counterexample_normal_form`

`FloorPower` is not rewritten. No `sorry`. No halt theorem. No
`PowerHeight`. No infinite-path type. Basin remains \(\{1\}\).

## Results

Classification **MINIMAL_NORMAL_FORM_GREEN**, with
**EVEN_SCALE_BARRIER_GREEN**.

A hypothetical minimal non-1 orbit stays at or above \(n_*\), never
hits a `ReachesOne` state, cannot capture, and cannot begin with `OE`.
Every even run of length \(r\) has entry at least \(n_*^{2^r}\). Even
states below \(144\) are already impossible. Changing-family collapses
to \(1\) cannot occur on the orbit.

Odd steps still increase; even runs are permitted only after the state
has financed the required scale. That is the accounting, not an
all-odd theorem.

## Open questions

Answered in [juggler_repeated_oe.md](juggler_repeated_oe.md): \(r\)
consecutive `OE` blocks on a minimal non-1 orbit require
\(n_*^{4^r}\le x^{3^r}\), and \((\texttt{OE})^r\) cannot start at
\(n_*\). The remaining question lives there.

## Decision

**PROMOTE** the even-run scale barrier and the finite-prefix normal
form. Do not claim that the orbit is all-odd. Do not claim that every
even collapse is impossible. Do not claim termination.

Best next question: after the first odd run has grown past \(n_*^2\),
must the first even residual fall below \(n_*\), or can it land in
\([n_*,\infty)\)?

## Publication assessment

Status: `EXPLORATORY`. A conditional scale obstruction, not a paper
candidate and not a Juggler totality result.
