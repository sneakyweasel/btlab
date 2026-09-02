# Juggler odd-run financing

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

How much odd expansion is required to finance the first legal even
residual on a hypothetical minimal non-terminating orbit, and what
does the same accounting say for a later block \(O^aE^b\)?

## Exact statement

Assume `MinimalNonTerm n`. If a later orbit state \(x\) realizes
\(O^aE\), the even residual \(x_a=T^a(x)\) satisfies \(x_a\ge n^2\),
and the itinerary envelope gives \(x_a^{2^a}\le x^{3^a}\). Therefore

\[
n^{2^{a+1}}\le x^{3^a}.
\]

The same argument with an even run of length \(b\) yields

\[
n^{2^{a+b}}\le x^{3^a}.
\]

At the start \(x=n>1\), this reduces to \(2^{a+1}\le 3^a\), whose
smallest solution is \(a=2\). The first even residual of a minimal
counterexample cannot occur before `OOE`.

Do not claim that every later odd run has length at least \(2\). A
sufficiently large later entry can finance \(a=1\). Do not prove an
odd-run frequency theorem. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope \(T_w(n)^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED**.
- Even-run scale barrier \(m\ge n_*^{2^r}\) —
  **EXACT — LEAN VERIFIED**.
- Repeated-`OE` scale budget \(n_*^{4^r}\le x^{3^r}\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The itinerary envelope and the even-run
barrier are multiplied into one integer-power financing law. Totality
remains unclaimed.

## Branch budget

```text
Mathematical target     MinimalNonTerm n and O^a E from x => n^{2^{a+1}} <= x^{3^a}
Novelty hypothesis      Odd growth finances the first legal even residual
Falsifier               Envelope fail, or xa>=n^2 with n^{2^{a+1}} > x^{3^a}
Existing machinery      power_bound_word, even_run_scale_barrier, follows
Maximum Phase-0 scope   Financing inequality; O^a E^b; start a>=2; later a=1 census
Promotion criterion     Proved financing law, or start a>=2, or O^a E^b block theorem
Stop criterion          Halt; frequency; log energy; lower envelope; moduli programme; repeated-block engine
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `odd_run_even_residual` —
  **EXACT — LEAN VERIFIED**
- `odd_run_financing_scale_barrier` —
  **EXACT — LEAN VERIFIED**
- `odd_even_block_scale_barrier` —
  **EXACT — LEAN VERIFIED**
- \(2^{a+1}\le 3^a\) iff \(a\ge 2\); first even residual at the start
  cannot occur before `OOE` —
  **EXACT — LEAN VERIFIED**
- realized \(O^aE^b\) blocks obey the envelope; legal even residuals
  obey the financing inequality —
  **COMPUTATIONALLY VERIFIED**
- later \(a=1\) occurs (e.g. \(77\): \(1523\xrightarrow{\mathrm{OE}}243\)) —
  **OBSERVATION** / **SCALE_FINANCING_COUNTEREXAMPLE** for an absolute
  later lower bound on \(a\)
- closest legal even residual on \(n\le 80\): \(5\xrightarrow{\mathrm{OO}}36\)
  against \(5^2=25\); among \(n\ge 12\): \(33\xrightarrow{\mathrm{OO}}2598\)
  against \(33^2=1089\) —
  **OBSERVATION**
- a coarse odd-step lower bound \(x_a\ge x_0\) does not improve
  \(x_a\ge n^2\) at the start; no extra modulus programme —
  **OBSERVATION**
- odd-run frequency — not claimed
- global halt — not claimed
- `PowerHeight` / log energy / lower envelope — not added

## Experiments

- Probe: `research.juggler_sequence.odd_run_financing`
- Records: [juggler_odd_run_financing.md](../research/juggler_odd_run_financing.md),
  [juggler_odd_run_financing.json](../research/juggler_odd_run_financing.json)
- Tests: `tests/research/juggler_sequence/test_odd_run_financing.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the envelope, the financing inequality, or the block form on
\(n\le 80\). A later `OE` block can occur after growth
(\(77\): \(1523\xrightarrow{\mathrm{OE}}243\), even residual
\(59436\ge 77^2\)). That refutes an absolute later bound \(a\ge 2\)
and does not refute the scale inequality
\(77^{4}\le 1523^{3}\).

Start-`OE` on ordinary orbits (\(13\xrightarrow{\mathrm{OE}}6\)) is
descent and is already forbidden for a minimal counterexample.

## Formalization

`formal/Problems/Engine/OddRunFinancing.lean`, above `RepeatedOE`.
Added:

- `oddEvenBlock` / `follows_of_append_right` / `odd_run_even_residual`
- `odd_run_power_bound`
- `odd_even_block_scale_barrier`
- `odd_run_financing_scale_barrier`
- `two_pow_succ_le_three_pow_iff` / `initial_even_not_before_ooe`

`FloorPower`, `MinimalNonTerm`, and `RepeatedOE` are not rewritten. No
`sorry`. No halt theorem. No `PowerHeight`. No infinite-path type. No
odd-run automaton.

## Results

Classification **ODD_RUN_FINANCING_GREEN**, with
**ODD_RUN_MINIMUM_GREEN** at the start and **BLOCK_FINANCING_GREEN**
for \(O^aE^b\). The stronger claim that every later odd run has
length at least \(2\) is **SCALE_FINANCING_COUNTEREXAMPLE**.

Odd expansion must finance the next allowed even collapse. That is a
conditional scale law, not a grammar of all parity itineraries.

## Open questions

Answered in [juggler_repeated_block.md](juggler_repeated_block.md):
\((O^aE^b)^r\) on a minimal non-1 orbit requires
\(n^{2^{r(a+b)}}\le x^{3^{ar}}\). Formally contracting blocks cannot
start at \(n_*\). Expanding repetition can stay above the start
(\(69\xrightarrow{(OOE)^2}212\)). Repetition alone is not a global
obstruction.

## Decision

**PROMOTE** the odd-run financing law and the \(O^aE^b\) block
theorem. Do not claim that later odd runs have length at least \(2\).
Do not claim that every orbit contains many odd or even steps. Do not
claim termination.

Best next question: answered in
[juggler_repeated_block.md](juggler_repeated_block.md).

## Publication assessment

Status: `EXPLORATORY`. A conditional growth-pays-for-collapse
accounting law, not a paper candidate and not a Juggler totality
result.
