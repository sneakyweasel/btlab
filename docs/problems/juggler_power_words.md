# Juggler fixed-itinerary power inequalities

Status: **EXPLORATORY**

Standalone application probe on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a thaw of
frozen v2.3, and not a claim that every positive integer reaches 1.

## Problem

Do fixed Juggler parity-word compositions admit exact integer-power
inequalities \(T^k(n)^a \lessgtr n^b\) whose exponents depend only on
word length and odd-count, as suggested by the formal exponent
\(3^{\#O}/2^{|w|}\)?

## Exact statement

For a parity itinerary \(w\) of length \(k=\lvert w\rvert\) with \(o=\#O(w)\),
and for every positive integer \(n\) whose first \(k\) Juggler parities
equal \(w\), does the canonical comparison

\[
T^k(n)^{2^k}\lessgtr n^{3^o}
\]

hold with the sign of \(3^o\) versus \(2^k\), independently of the order
of the letters of \(w\)? Separately: does the one-sided floor composition

\[
T^k(n)^{2^k}\le n^{3^o}
\]

hold for every such realizing \(n\)?

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. Computational table.
  Project relationship: **known**. Totality is not claimed.
- Phase-12 local block: if \(n\ge 2\) follows `OOOEE`, then \(T^5(n)<n\),
  Lean `floorPower_oooee_five_step_lt`, via \(n_5^{32}\le n^{27}\).
  **extended** here by asking whether those exponents are the general
  \((k,o)\) shadow.
- Pickover juggler map: even \(\lfloor\sqrt{n}\rfloor\), odd
  \(\lfloor n^{3/2}\rfloor\). **reproduced** as `math.isqrt` only.

## Branch budget

```text
Mathematical target     Do fixed parity-word compositions obey the canonical
                        integer-power comparison T^k(n)^{2^k} ≶ n^{3^o} with
                        the sign of 3^o vs 2^k, independently of letter order?
Novelty hypothesis      The OOOEE exponents 32 vs 27 are the general (k,o)
                        shadow of floor-power composition, not a lucky word.
Falsifier               A realizing n whose first |w| bits are w and whose
                        power comparison has the opposite sign; or two words
                        with the same (k,o) and different behaviour.
Existing machinery      math.isqrt Juggler step; FloorPower.lean (OE, OO,
                        OOOEE); Phase-12 calibration on n in {3,25,39}.
Maximum Phase-0 scope   Exhaustive |w|<=8 on 1<=n<=10^6, plus a targeted
                        (k,o)=(9,6) scan for 729/512. No engine-control edits.
Promotion criterion     A near-critical contracting itinerary survives, Lean
                        proves one new exact inequality beyond OOOEE, and
                        the result is classified without termination claims.
Stop criterion          Machinery gravity; any global frequency/termination
                        claim; rewriting the Research Engine; a general-word
                        Lean theorem.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. Balanced-ternary digit structure is not used.

## Candidate operations / invariants

- Formal itinerary exponent \(3^{\#O(w)}/2^{|w|}\) — **OBSERVATION** (heuristic)
- One-sided floor composition \(T_w(n)^{2^k}\le n^{3^o}\) —
  **COMPUTATIONALLY VERIFIED** on \(1\le n\le 10^6\), \(|w|\le 8\), plus
  the \((k,o)=(9,6)\) family; **EXACT — LEAN VERIFIED** for `OOOEE` and
  `OOOEEEOO`
- Two-sided exponent-only law (expanding reverse inequality) — **REFUTED**
- Strict contracting comparison on pure-even words — **REFUTED** as a
  strict inequality on the infinite family of even perfect squares
- Same-count permutation independence of the one-sided bound — **OBSERVATION**
  (H1 on the tested domain)

## Experiments

- Probe: `research.juggler_sequence.power_itineraries`
- Range: \(1\le n\le 10^6\), exhaustive \(|w|\le 8\), targeted \(729/512\)
  family at \(k=9\), \(o=6\)
- Exact comparison: integer `cmp_pow`; float logarithms are a filter only
- Records: [juggler_power_itineraries.md](../research/juggler_power_itineraries.md),
  [juggler_power_itineraries.json](../research/juggler_power_itineraries.json)
- Tests: `tests/research/juggler_sequence/test_power_itineraries.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. Computational survival of the one-sided bound is not a
conjecture that it holds for all \(n\), and is not a totality statement.

## Counterexamples

- Two-sided expanding law: `O` at \(n=3\) gives \(5^2=25<3^3=27\); `OO`
  at \(n=3\) gives \(11^4=14641<3^9=19683\). **REFUTED**.
- Strict pure-even contraction: `E` at every even square (\(n=4\):
  \(2^2=4\)); `EE` at \(n=16\); `EEE` at \(n=256\). Equality, infinite
  family. **REFUTED** as a strict inequality.
- One-sided upper bound: no counterexample on the tested domain.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. New primitives
`floorPower_even_sq_le`, `floorPower_odd_sq_le_cube`, `pow_sq_le`,
`pow_sq_le_cube`, `pow_lt_of_two_le`. New block theorem
`floorPower_oooeeeoo_eight_step_lt`: if \(n\ge 2\) follows `OOOEEEOO`,
then \(T^8(n)^{256}\le n^{243}\) and \(T^8(n)<n\). Existing
`floorPower_oooee_five_step_lt` is unchanged. No `sorry`. No ledger row
(elementary floor arithmetic, same policy as the prior FloorPower lemmas).

## Results

Classification **POWER_WORD_COUNTEREXAMPLE** for the stated two-sided
exponent-only hypothesis. Permutation analysis is **H1** on both the
two-sided and one-sided comparisons: ordering does not change the
canonical direction inside a fixed \((k,o)\).

The one-sided floor composition \(T^k(n)^{2^k}\le n^{3^o}\) held for
every realizing \(n\) in range, including all \(\binom{5}{3}\) words of
ratio \(27/32\) and all realized length-8 words of ratio \(243/256\).
`OE` and `EO` both obey \(T^2(n)^4\le n^3\) with strict \(<\). Near-critical
expanding families \(9/8\), \(81/64\), and \(729/512\) fail the reverse
inequality at the first realizing \(n>1\).

Lean: if \(n\ge 2\) follows `OOOEEEOO`, then \(T^8(n)<n\). Calibration:
`OOOEE` at \(\{3,25,39\}\) still satisfies \(T^5(n)<n\).

`OOOEE` is therefore one instance of the one-sided power-composition
principle, not an isolated lucky word. It is not evidence for a
two-sided exponent law, a frequency theorem, or termination.

## Open questions

Can the one-sided floor-power chain be packaged as a composition lemma
indexed by a finite itinerary, without a general-word tactic and without a
parity-frequency theorem?

## Decision

**PROMOTE** the one-sided floor-power composition as a local block
language, together with the Lean `OOOEEEOO` eight-step contraction.
**Record** the two-sided exponent-only hypothesis as
`POWER_WORD_COUNTEREXAMPLE`. Do not register an attack. Do not claim
termination, divergence, or that every trajectory contains `OOOEEEOO`.
Stop rather than write a general-word theorem.

Best next question: can the one-sided floor-power chain be packaged as
a composition lemma indexed by a finite itinerary, without a general-word
tactic and without a parity-frequency theorem?

## Publication assessment

Status: `EXPLORATORY`. Local exact block lemmas, not a paper candidate
and not a Juggler totality result.
