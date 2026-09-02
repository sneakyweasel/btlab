# Juggler excursions and first-return induction

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can realized first-return-below words be certified by the existing
finite-itinerary envelope and defect calculus, and do leftover weak returns
form a small exact family with a candidate smaller canonical state?

## Exact statement

For \(n\ge 2\) write

\[
\tau_<(n)=\min\{k\ge 1:T^k(n)<n\}
\]

when the minimum exists, and keep \(\tau_\le\), the first peak time, and
the peak-to-return suffix as separate objects. Let \(w(n)\) be the
realized itinerary of length \(\tau_<(n)\). Phase 0 asks whether \(w(n)\) on
\(2\le n\le 2000\), together with the hard starts
\(9,37,49,69,77,173\), admits a **non-tautological** certificate:

- exponent gap \(2^k>3^o\);
- first-defect compensation \(\delta_{\mathrm{first}}>\mathrm{formal\_gap}\)
  when the gap is formable;
- peak/return split: \(P^{3^q}<n^{2^s}\) by exact integer comparison.

Full-word \(\Delta>n^{3^o}-n^{2^k}\) is equivalent to \(T_w(n)<n\) once
\(\Delta\) is formed. It is **not** a certificate on a completed return.
A search-horizon miss is not a bound \(L\). This is not a halt theorem.

`FiniteProgress` via `Descent` is already the global spine. A
`MinimalNonTerm` has no finite excursion. The census studies terminating
\(n\), where \(\tau_<\) exists.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope, equality rigidity, first-defect, and
  compensated contraction — **EXACT — LEAN VERIFIED**.
- Automatic `FiniteProgress` off the odd-odd class —
  **EXACT — LEAN VERIFIED**.
- Escape-state margin — closed as `ESCAPE_STATE_COMPLEX`
  (2026-08-27).
- Odd-odd residual scalars — closed as `ODD_ODD_RESIDUAL_COMPLEX`.
- Prefix-NC arithmetic admissibility — closed as
  `PREFIX_NC_ARITHMETIC_COMPLEX`.
- Cycle Diophantine peak identities — closed as
  `DIOPHANTINE_REPACKAGING`.
- Residual `first_return` is orbit period \(T^k(n)=n\), not
  \(\tau_<\). Residual `O^a E^b` excursions are not this object.

Project relationship: **extended**. The unit is a complete
first-return-below excursion, not another local rewrite of \(T\ge n\).
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Can first-return-below words be certified by the
                        existing envelope/defect calculus, or do weak
                        returns refuse a canonical smaller state?
Novelty hypothesis      The complete excursion (not one step, not
                        ResidualStep, not prefix-NC) is the right
                        FiniteProgress unit
Falsifier               Leftover COMPUTED_ONLY grazers with no shared
                        structure, or every new invariant is T<n rewritten
Existing machinery      power_bound_word, power_bound_contracts,
                        power_bound_eq_iff_extremal, first-defect,
                        compensated contraction, cmp_pow, FiniteProgress
Maximum Phase-0 scope   Definitions; n=2..2000 + HARD_STARTS; persist;
                        classify; lemma A–D checks; decide. No Lean file.
                        No new engine.
Promotion criterion     A peak-return inequality or a small exact
                        hard-excursion family with a candidate M
Stop criterion          EXCURSION_INDUCTION_COMPLEX; ResidualStep /
                        CycleDiophantine / prefix-NC reopen; PowerHeight;
                        halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\tau_<(n)\) first return strictly below the start — **OBSERVATION**
- \(\tau_\le(n)\) first return at or below the start — **OBSERVATION**
- Peak/return split \((r,o_u,s,q)\) — **OBSERVATION**
- Exponent-gap certificate on the first-return word — existing
  **EXACT — LEAN VERIFIED** applied to \(w(n)\)
- First-defect certificate — existing **EXACT — LEAN VERIFIED**,
  non-tautological only when \(\mathrm{formal\_gap}\) is formable
- Peak-suffix comparison \(P^{3^q}<n^{2^s}\) — **OBSERVATION** in
  Phase 0; not named as a theorem
- Full-word \(\Delta>\mathrm{formal\_gap}\) on a completed return —
  **REPARAMETERIZATION** of \(T<n\)
- Canonical measure \(M\) for a minimal-counterexample law — not
  claimed in Phase 0
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.excursions`
- Records: [juggler_excursions.md](../research/juggler_excursions.md),
  [juggler_excursions.json](../research/juggler_excursions.json)
- Dataset: `data/research/juggler/excursions/`
- Tests: `tests/research/juggler_sequence/test_excursions.py`
- CLI: `python -m research.juggler_sequence.excursions {init,run,resume,status,summarize}`
- The Research Engine control layer is not modified.
- `ResidualStep` is not extended. `CycleDiophantine` is not reopened.
- No `PowerHeight`. No excursion automaton.

## Conjectures

None opened.

## Counterexamples

- Lemma A stated for every start: even \(n\) has first-return word
  \(E\), which is extremal. **REFUTED** as a universal claim.
- Lemma A for odd \(n\ge 3\): no all-odd first-return word in
  \(2\le n\le 2000\). **COMPUTATIONALLY VERIFIED** on the window.
- A first-return word with \(3^o\ge 2^k\): none in the window.
  Not a refutation of existence outside the window.
- Minimal-counterexample measure \(M\): return value \(<n\) is
  the definition of \(\tau_<\), not a new state. **REPARAMETERIZATION**
  if treated as \(M\).

## Formalization

None added. Envelope and compensated contraction already live in
`formal/Problems/Engine/FloorPower.lean`. No `Excursions.lean`.
`ResidualChain.lean` is not rewritten. Candidate names
`first_return_envelope`, `excursion_peak_bound`, and
`first_return_contraction` stay unclaimed. No `sorry`. No ledger row.

## Results

Classification **EXCURSION_ENVELOPE_GREEN**.

On \(2\le n\le 2000\), every start returns below \(n\) before the
horizon. The 1999 first-return words all satisfy \(2^k>3^o\).
By the existing Lean theorem `power_bound_contracts`, that gap
already forces \(T_w(n)<n\) for \(n\ge 2\). First-defect and
peak-suffix never certify a return that the exponent gap misses.
No `COMPUTED_ONLY` leftover. No unfinished start.

Because \(G>0\) on a realized prefix already contracts, the first
return in this window is exactly the first formally contracting
realized prefix. That is **COMPUTATIONALLY VERIFIED**, not a
theorem that every orbit realizes such a prefix.

Lemma B holds on the window: an all-odd itinerary does not return.
Lemma D shapes are many: first-defect compensation is not needed
and does not constrain the peak split. No candidate \(M\) for a
minimal-counterexample route.

No Lean file. No halt theorem.

## Open questions

The missing theorem is not another local residual. It is: does
every \(n\ge 2\) eventually realize a finite prefix with
\(3^o<2^k\)? If yes, `FiniteProgress` follows from
`power_bound_contracts`. An infinite itinerary that stays
prefix-noncontracting would be a non-terminator. Do not reopen
backward prefix-NC admissibility, ResidualStep, escape-state
margins, or peak Diophantine identities.

## Decision

**PARK** the excursion branch as `EXCURSION_ENVELOPE_GREEN`. The
window shows that completed first-return words are formally
contracting, so the existing envelope already certifies those
returns. That is not a proof that \(\tau_<\) is finite, not a
peak-return inequality beyond the full-word gap, and not a
well-founded measure \(M\). Keep the probe and the dataset. Do
not add Lean. Do not claim termination.

Best next question: prove or refute that every \(n\ge 2\)
realizes a finite prefix with \(3^o<2^k\).

## Publication assessment

Status: `EXPLORATORY`. A window-level envelope observation, not a
paper candidate and not a Juggler totality result.
