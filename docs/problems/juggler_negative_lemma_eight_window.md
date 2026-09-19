# The negative Lemma 8 window

Status: **CLOSE** (the floor is sign-symmetric, tight at every known
cycle, and slack exactly at the leftovers; three corollaries recorded)

Standalone arithmetic phase on the Collatz bridge, and the complement of
[Lemma 8 on the exponent](juggler_exponent_valuation_mirror.md). Not a
cycle exclusion, not a termination theorem, not a floor raise, and not a
reopen of Paper A, of the finance mirror, or of the near-convergent
Diophantine branch.

## Problem

The 19 September negative-knowledge entry names the Juggler's missing
pointwise odd-run bound as the door. The laboratory's own bridge says the
Juggler's cycle words *are* the negative Collatz cycle words, letter for
letter. On that side the pointwise 2-adic fact is available in full. What
is it worth there, and where does it stop?

## Exact statement

Let \(a\) be the number of consecutive odd states from \(x\) under the
shortcut map. Lemma 8's congruence holds over \(\mathbb Z\):
\(x\equiv -1\pmod{2^a}\). Hence \(x\ge 2^a-1\) for \(x\ge 1\), and for
\(x\le -2\),

\[
x\le -(2^a+1),\qquad\text{that is}\qquad |x|\ge 2^a+1 .
\]

Paired with `neg_cycle_finance` — kernel-checked, on a cycle at
\(x\le -2\) read at its least \(|x|\):
\(2(|x|-1)(3^o-2^K)\le (K-o)3^o\) — this is a window on \(|x|\) per word.
Question: how many words of the shared shape does the window empty, is it
subsumed by Paper A's census bound on even letters, and how does the
implied run bound behave at the record near-convergent lengths?

## Current literature

- `hercher-2023-collatz-m-cycles`, Lemma 8. **known**; the negative
  restatement is two lines of integer arithmetic from the same
  congruence and is not claimed as new mathematics.
- `terras-1976-stopping-time`, `lagarias-1990-rational-cycles`. **known**.
- Laboratory: `neg_cycle_finance`, `neg_cycle_word_is_juggler_shape`,
  `neg_prefix_noncontracting` in `Problems/Juggler/CollatzBridge.lean`,
  and the rational-cycle census of
  [juggler_collatz_bridge.md](juggler_collatz_bridge.md), which already
  settles every length to 24 by exhibiting the cycles. **extended**: the
  window is a criterion, valid at every length, where the census is a
  computation valid to 24.
- Paper A Theorem 3.31, \(e\ge 8\) by a census of run forms. Compared
  here on the shared word shape, not combined with it.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     What is the pointwise 2-adic floor worth on the side
                        where it exists -- the negative Collatz cycles, whose
                        words are the Juggler's cycle words?
Novelty hypothesis      The floor is sign-symmetric and tight at every known
                        cycle, so it is not what discriminates; paired with
                        the kernel-checked finance ceiling it is a per-word
                        sieve whose strength can be measured.
Falsifier               The window excludes a word that is a known cycle, or
                        it is subsumed by Paper A's e >= 8, or it stays sharp
                        at the leftover lengths.
Already killed by?      No. The finance mirror reproduced the Collatz period
                        bounds and did not touch the valuation; the p-adic
                        cycle coupling asked about 3^o - 2^L and refuted; the
                        exponent-valuation mirror closed on the Juggler side
                        of the same fact. This is the measurement none of them
                        made, and it excludes nothing not already excluded.
Existing machinery      neg_cycle_finance, neg_cycle_word_is_juggler_shape,
                        the cycle equation, the CycleMin word shape, the
                        rational-cycle census.
Maximum Phase-0 scope   One probe: the known cycles against their floors, the
                        window over shape words to length 22, the comparison
                        with e >= 8, the run bound at the leftovers.
Promotion criterion     A word excluded at a leftover length, or a criterion
                        that survives theta_J -> 0.
Stop criterion          The bound goes slack at the leftovers, which is a
                        CLOSE with a number attached.
```

## Balanced-ternary formulation

None required. Integer arithmetic on \(\mathbb Z\) and on \(O/E\) words.

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- \(x\le -(2^a+1)\) for \(x\le -2\) with \(a\) consecutive odd states —
  **EXACT — HUMAN PROOF**, two lines from Lemma 8's congruence
- every nontrivial cycle of the \(\mathbb Z\) map attains its own floor,
  and \(|x+1|=2^a\) exactly at the extremal point —
  **COMPUTATIONALLY VERIFIED** on all three
- equivalently the odd part of the word's even-charge is
  \(|2^K-3^o|\) — **COMPUTATIONALLY VERIFIED** on all three
- the window \(2^a+1\le |x|\le 1+e3^o/(2(3^o-2^K))\) —
  **EXACT — HUMAN PROOF** given `neg_cycle_finance`
- emptiness is \(2^{a+1}\theta_J>e\), so a negative cycle word has
  \(a\le \log_2(e/\theta_J)-1\) — **EXACT — HUMAN PROOF**
- the sieve's strength and its slack at the leftovers —
  **COMPUTATIONALLY VERIFIED** to length 22

## Experiments

`python -m research.juggler_sequence.negative_lemma_eight_window` writes
`data/research/juggler/negative_lemma_eight_window/summary.json` and
[juggler_negative_lemma_eight_window.md](../research/juggler_negative_lemma_eight_window.md).
All expanding prefix-noncontracting words to length 22; the four known
cycles of the \(\mathbb Z\) map; the run bound at lengths 3, 11, 19, 84,
569 and 1054.

## Conjectures

None. The tightness at all three cycles is an observation on three
objects and is recorded as such, not as a conjecture.

## Counterexamples

None fired. Neither known cycle word is excluded by the window, which is
the falsifier that mattered.

## Formalization

No new Lean module. The ceiling is already `neg_cycle_finance`; the floor
is the negative branch of a congruence the bridge carries as
`two_pow_mul_iter_add_one_int`. A Lean statement of the window would be a
corollary of two existing theorems and is not the branch's content.

## Results

- **The floor is sign-symmetric, and the sign costs exactly two.**
  \(x\ge 2^a-1\) on the positive side, \(|x|\ge 2^a+1\) on the negative.
  The negative floor is the larger, and the negative side is the one that
  has cycles, so the valuation is not what separates the signs. The
  linear form is: \(2^K-3^o>0\) small forces \(K\) enormous, while
  \(3^o-2^K>0\) is \(1\) at \(K=3\) and \(139\) at \(K=11\).
- **Every nontrivial cycle of the \(\mathbb Z\) map sits on its floor.**
  \(\{1,2\}\) at \(a=1\) with \(x=1=2^1-1\); \(-5\) at \(a=2\) with
  \(|x|=5=2^2+1\); \(-17\) at \(a=4\) with \(|x|=17=2^4+1\). Equivalently
  \(x+1=-2^a\) at both negative cycles, equivalently the odd part of the
  even-charge is \(|2^K-3^o|\). A bound tight at every object it is meant
  to exclude is not the exclusion.
- **Floor and ceiling meet, and for `OOE` they pin the cycle.** The
  window at `OOE` is \([5,5.5]\), so \(-5\) is the unique realization,
  with no search. At the \(-17\) word it is \([17,32.47]\) and the cycle
  sits at the bottom.
- **The sieve is strong on short words, and the honest number is
  smaller.** Of the 198891 expanding prefix-noncontracting words of
  length at most 22 the window excludes 84.7 per cent and empties the
  lengths 1, 2, 4, 5, 7, 8, 10, 13 and 16 — but Paper A's Theorem 3.31
  already excludes every shape word shorter than 22, since \(e\ge 8\)
  with \(3^o>2^K\) forces \(o\ge 14\). The comparison begins at
  \(K=22\), and there: 93222 shape words, 17637 admissible to
  \(e\ge 8\), of which the window kills 4787 — **27.1 per cent**.
  Every word it kills has leading run at least 6; every survivor has run
  at most 5. That is what the missing Juggler floor would buy at the
  first length Paper A allows a cycle word: a cap of 5 on the leading odd
  run, and a quarter of the candidates.
- **And it goes slack exactly at the leftovers.** The implied run bound
  is \(a\le\log_2(e/\theta_J)-1\), and \(\theta_J\) is the record
  near-convergent defect: 2.17 at \(L=3\), 4.98 at 11, 8.02 at 19, 12.86
  at 84, 16.59 at 569, 22.09 at 1054, against 5 at \(L=22\). The
  leftovers are by definition the lengths where \(\theta_J\) is a record
  minimum, hence exactly the lengths where this sieve permits the longest
  runs, while the words that would have to be excluded need only a short
  leading run to pass.

## Open questions

Whether any criterion built from the pointwise floor can survive
\(\theta_J\to 0\). The measurement here says the answer is no for this
pairing, because the ceiling carries \(1/\theta_J\) and the floor does
not.

## Decision

**CLOSE**. The branch answers its target with a number: on the mirror
side, where the pointwise 2-adic floor exists in full, it is worth most
of the short word list, it is independent of Paper A's census bound, and
it is worth nothing at the leftover lengths. That prices the door named
on 19 September more sharply than the earlier argument did — it would
deliver the starting line and stop before the first leftover — and it
closes the question rather than opening a route.

Best next question: none from this branch. The near-convergent
Diophantine frontier keeps its own placement.

## Publication assessment

Status: `STRUCTURAL`. A measurement and two restatements, belonging next
to the finance mirror rather than in a manuscript.
