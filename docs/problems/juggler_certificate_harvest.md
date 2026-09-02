# Juggler leftover-class certificate harvest

Status: **EXPLORATORY**

Standalone computational phase on the Juggler floor-power map. It
adapts the parked Word Atlas GPU engine into a first-descent sieve.
It is **not** a Word Atlas recensus, not a new atlas language tag,
not a Research Engine control-layer experiment, not Paper A or
Paper B, and not a claim that every positive integer reaches 1.

## Problem

Among \(n\le X\), what first contracting words fire on the complement
of \(\{E, OE, OOEE\}\), and does that leftover dictionary drift with
scale?

## Exact statement

A **certificate** is the first realized word \(w\) with
\(T_{|w|}(n)<n\). Coarse bins are

- \(E\) — even \(n\ge 2\) (Paper A Theorem 4.1)
- \(OE\) — odd-to-even (Theorem 4.1)
- \(OOEE\) — first descent is exactly `OOEE`
- leftover — first descent is none of the above

The leftover-class histogram is the count of leftover starts by
first contracting packed word. Absence under a bound is
`NOT OBSERVED WITHIN SEARCH BOUND`. This is not a halt theorem.

## Current literature

- Uniform short certificates \(E\) / \(OE\) —
  **EXACT — LEAN VERIFIED** (Paper A Theorem 4.1)
- `OOEE` as a uniform contracting class —
  Paper B / two-step parity harvest
- Word Atlas —
  **PARK** as machinery
  ([juggler_word_atlas.md](juggler_word_atlas.md))
- Published totality through \(7{,}110{,}200\) —
  `derneueschwan-2026-juggler`; through \(10^6\) — Weisstein
- Every start reaches 1 — not claimed

Project relationship: **extended**. A leftover-class census on
existing certificates. Do not reopen
`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`.

## Branch budget

```text
Mathematical target     Among n ≤ X, what first contracting words fire
                        on the complement of {E, OE, OOEE}, and does
                        that leftover dictionary drift with scale?
Novelty hypothesis      A short stable leftover list (or a persistent
                        bias vs product density) that is invisible at
                        the published 7e6 totality bound.
Falsifier               Histogram is only OOOO* until an even letter,
                        with no new shape and no scale drift — then
                        the sieve is a verification bound.
Existing machinery      Atlas Kernel A + Wide8 floor_power; packed
                        O/E words; trajectory_until_drop; Theorem 4.1
                        (E / OE); Paper B OOEE class
Maximum Phase-0 scope   Harvest kernel; leftover-word histogram;
                        coarse counts; overflow CPU merge; science
                        at 10^9; optional 10^10 slabs. No Lean, no
                        new atlas language, no per-n storage.
Promotion criterion     Stable leftover dictionary whose frequencies
                        match or stably bias Paper B product densities
Stop criterion          Only “still reaches 1”; machinery gravity
                        (Nsight, PE recensus, CLI/UI, automata)
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- first contracting word —
  **COMPUTATIONALLY VERIFIED** as a bounded observation
- coarse split \(E\) / \(OE\) / \(OOEE\) / leftover —
  **COMPUTATIONALLY VERIFIED** as a bounded observation
- leftover `run_signature` grouping —
  **OBSERVATION**
- scale-split total variation of leftover shares —
  **OBSERVATION**
- global halt — not claimed
- new atlas language — not added

## Experiments

- Probe: `research.juggler_sequence.certificate_harvest`
- Native: `juggler-atlas-census --mode harvest`
- Records: [juggler_certificate_harvest.md](../research/juggler_certificate_harvest.md),
  [juggler_certificate_harvest.json](../research/juggler_certificate_harvest.json)
- Dataset: `data/research/juggler/certificate_harvest/`
- Tests: `tests/research/juggler_sequence/test_certificate_harvest.py`

Science window: \(2\le n\le 10^9\), \(k\le 20\), scale split at
\(10^8\). Tests use \(n\le 400\). Optional \(10^{10}\) only if
overflow and uncapped stay rare. No Lean. No new `LANGUAGE_IDS`.

## Conjectures

None opened.

## Counterexamples

- “the leftover histogram is only `OOOO*` until an even letter” —
  at \(n\le 10^9\) the two leading leftover words are `OOOEE`
  (unary) and `OOEOE` (mixed), each about \(21\%\) of the
  \(k\le 20\) leftover mass. Unary \(O^+E^+\) is only \(0.29\) of
  that mass; `OOOO*` is \(0.08\).
- “leftover word shares drift with scale” — total variation
  between \([2,10^8]\) and \((10^8,10^9]\) is \(0.013\).
- “overflow stays rare out to \(10^9\)” — \(3.50\cdot 10^7\)
  Wide8 overflows and \(4.06\cdot 10^6\) uncapped starts.
  The optional \(10^{10}\) slab was not run.

## Formalization

None added. Existing `FiniteProgress`, `even_finiteProgress`, and
`odd_even_finiteProgress` already contain the uniform certificates.
No `CertificateHarvest.lean`. No `sorry`. Paper A is unchanged.

## Results

Classification **CERTIFICATE_HARVEST_PARK**.

On \(2\le n\le 10^9\), CUDA, \(k\le 20\), histogram only
(**COMPUTATIONALLY VERIFIED** as a bounded observation):

- Coarse: \(E=5.00\cdot 10^8\), \(OE=2.50\cdot 10^8\),
  \(OOEE=6.25\cdot 10^7\), leftover-with-word \(1.48\cdot 10^8\),
  uncapped \(4.06\cdot 10^6\), overflow \(3.50\cdot 10^7\).
  The unfinished plus leftover-with-word mass is \(3/16\) of the
  window, the complement of \(\{E,OE,OOEE\}\).
- Leading leftover words: `OOOEE` and `OOEOE`, then a
  length-\(7/8\) octet at about one-quarter of that mass. Shares
  match a product-density split. Scale-split TV \(0.013\).
- \(3081\) leftover types at \(k\le 20\); mass is concentrated in
  the short \(O/E\)-block list. CPU merge of overflow/uncapped
  was skipped after those lists exploded at \(10^8\).
- No new atlas language. No Lean. No halt theorem.

## Open questions

None from this histogram. The leftover first-contracting
dictionary is a scale-stable mixed \(O/E\)-block list, not a new
grammar and not an `OOOO*`-only kernel.

## Decision

**PARK**. The sieve is a reusable verification bound: a short
stable leftover dictionary with product-like frequencies and no
scale drift. It does not promote a density theorem and does not
kill a withdrawn Paper B claim. Do not run \(10^{10}\). Do not
auto-open \(K_3\) sums or inverse-cell search.

Best next question: none from this leftover-class histogram.

## Publication assessment

Status: `EXPLORATORY`. A leftover-class histogram, not a paper
candidate and not a Juggler totality result.
