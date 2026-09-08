# Juggler run-type packing: what rests on it, and what it costs

Status: **AUDIT** (Paper A Theorems 4.7--4.8)

A fragility audit of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md), not a new
paper and not a refutation. Theorem 4.7 needs one hypothesis it does
not state --- the itinerary contains no `EE` --- established over four
earlier ledger entries. This branch asks the two questions those
entries never asked: *which of Paper A's claims actually depend on
Theorem 4.7*, and *how much `EE` does it take to void the claim that
does*. Not a halt theorem, not a floor raise, not a leftover census.

## Problem

The `EE` gap was found and named, but never priced. A gap in a
supporting comparison and a gap under a headline floor are different
kinds of problem, and nothing in the ledger said which this was.

## What Corollary 4.5 actually charges

The first finding is a misreading corrected, and it is the one the
rest depends on. Corollary 4.5's "length-only parity charge" is not a
two-class parity split (odds at \(n\), evens at \(n^2\)). Read
`cycle_finance.parity_rhs` and `paper_a_audit.parity_holds`:

\[
\theta\ \le\ \frac65\Bigl[\frac{e}{n\log n}+\frac{o-e}{t\log t}
+\frac{e}{2n^{2}\log n}\Bigr],\qquad t=\lfloor n^{3/2}\rfloor,
\]

which is the **three-class bound**, with the internal odds at \(t\).
That is Lean as `threeTerm_bound` (`FinanceTransfer.lean`) and, unlike
the packing, it needs no hypothesis about `EE`: the coarse form never
splits valleys into cheap and expensive, and the split is the only
place `EE` does damage.

`test_three_term_rhs_is_corollary_4_5s_charge` pins the identification
against `parity_holds` itself, so it cannot drift.

**Consequence.** The cutoff \(25781\), the \(141\)-length set
\(\mathcal E\), Theorem 5.2's floor \(50508\), Theorem 5.9's
\(176251\), Corollaries 5.10--5.11 and Corollary 5.14 are all
downstream of the three-term charge. **No period bound in Paper A
depends on Theorem 4.7.** Its only consumers are Theorem 4.8 --- the
\(42\) lengths \(56347+1054k\) and the set
\(\mathcal E_{\mathrm{run}}\) of \(99\) --- and Proposition 4.9's
*identification* with \(\mathcal E_{\mathrm{run}}\), the arithmetic of
which is Lean and unaffected. The manuscript already calls 4.7 "a
supporting comparison at the same floor"; that is now checked rather
than asserted.

## The refinement's entire budget is one constant

At every one of the \(42\) lengths, at \(n=10^6+1\),

\[
\frac{\text{three-term RHS}}{\text{packed RHS}}=1.4048,
\]

uniformly. To leading order this is \(e/(o-e)\) --- the packing moves
the \(n\)-scale charge from \(e\) valleys to \(o-e\) --- with the
\(t\)- and \(n^{2}\)-scale terms pulling it down about a third of a
percent. Since a smaller majorant is a stronger constraint and
\(n_{\max}\) is near-linear in it, the whole refinement is worth a
factor \(1.4\) in \(n_{\max}\), never an order of magnitude.

Every one of the \(42\) dies with margin
\(\theta/\text{packed} \in [1.0033,\ 1.3535]\) --- necessarily inside
that budget, since each survives the three-term charge.

## Pricing the missing hypothesis

With \(m\) cyclic `EE` adjacencies the even letters form \(e-m\)
maximal runs, so

\[
\#\text{valleys}=e-m,\quad
\#\text{internals}=o-e+m,\quad
\#\text{cheap}\le\min(o-e+m,\ e-m),
\]

and \(\#\text{cheap}\le o-e\), the form Theorem 4.7 displays, holds
only at \(m=0\). The counting is checked cyclically on explicit words
by `ee_model_holds`, including the ledger's own counterexample
`OOEEOOE`, where \(\#\text{cheap}\le 2>o-e=1\).

**The second cap is what makes the answer interesting.** \(\#\text{cheap}\)
is bounded by the lemma's \(o-\#\text{blocks}\) *and* by the valley
count it is part of. The two cross at \(m=e-o/2\), where both equal
\(o/2\); past the crossing the valleys themselves run out and the
majorant falls again. So `EE` cannot inflate the \(n\)-scale charge
beyond \((o/2)/(o-e)=1.2047\) however much of it a word carries.

## Result: the 42 split 18 / 24

\(\theta/\text{packed}\) rises monotonically along the progression and
crosses the ceiling between \(L=74265\) (\(1.1982\)) and \(L=75319\)
(\(1.2068\)):

| | lengths | verdict |
|---|---|---|
| \(56347+1054k\), \(k\le 17\) | 18 | **voided by `EE`** --- some admissible `EE` count defeats the exclusion |
| \(56347+1054k\), \(k\ge 18\) | 24 | **robust** --- no `EE` count does, by the cap crossing |

The \(18\) need between \(50\) and \(3925\) `EE` adjacencies. A word
with its evens placed uniformly carries \(e(e-1)/(L-1)\approx
7675\)--\(10116\) of them, so **every one of the \(18\) is voided by
less `EE` than an ordinary word already has** --- \(L=56347\) by a
factor of \(150\). `EE` is realized and common: it occurs in
\(12543\) of the \(29999\) at-or-above excursions below \(6\cdot10^4\).

So dropping the unstated hypothesis leaves \(117\) survivors below
\(10^5\), not \(99\).

## The reopen condition, tested and failed

The PARK below originally said this would reopen on a proof that closure
at \(o_{\min}(L)\) caps the `EE` density below the \(50\)-adjacency
threshold at \(L=56347\). **It does not, and cannot.**

Impose every constraint Paper A proves about a cycle-minimum itinerary and
nothing else: above-anchor prefixes (\(3^{a_j}\ge2^j\) for all \(j\)),
Theorem 3.29's run cap
(\(\lfloor(e-i)\log2/\log(3/2)\rfloor\)), \(o=o_{\min}(L)\), and the
\(\mathtt{OO}\ldots\mathtt{E}\) shape of `cycleMin_word_shape`. At all
\(18\) fragile lengths there is an admissible word carrying more than
enough `EE` to void the exclusion.

**The witness keeps runs of length at most two** --- the packing's *own*
extremal shape. It is the Beatty interleaving of `OOE` and `OE` blocks
over \(e-k\) evens followed by a tail of \(k\) evens. So no run-structure
claim is violated; what breaks is the block/even-letter correspondence,
which is the whole of the `EE` gap. That closes the route rather than
leaving it open: even granting the packing's extremality claim about runs
in full, the counting still fails.

One structural fact came out of it, and it is not a coincidence.
\(o_{\min}\) is defined by \(o\log(3/2)>e\log2\) and the run cap uses the
same constant, so at every one of the \(42\) lengths

\[
\Big\lfloor e\cdot\tfrac{\log 2}{\log(3/2)}\Big\rfloor = o_{\min}-1 ,
\]

i.e. **the one-block word \(\mathtt{O}^{o}\mathtt{E}^{e}\) is forbidden by
exactly one letter.** Two blocks are admissible, and already carry
\(e-2\) adjacencies.

## What this does and does not say

It is a statement about the *proof*, not about cycles. A voided
exclusion does not make a cycle of that length exist; it means Theorem
4.8's argument does not rule one out. Nor is Theorem 4.8 refuted: the
theorem is true as stated *with* the no-`EE` hypothesis, and \(24\) of
its \(42\) exclusions survive without it.

The model also treats \(m\) as free, whereas a realized word's `EE`
count is fixed by the dynamics. It assumes the only effect of `EE` is
the recount --- if an `EE` forced extra height relations, some of the
\(18\) could come back. That is the open direction here.

## Branch budget

Phase 0 only, and spent. One probe, `cycle_packing_fragility`, over the
existing three-class charge; the six-class packing it prices is Lean
(`cycleMin_sixTerm`). No new estimate and no new floor. Closed, so the
budget is not renewed.

## Decision

**PARK.** The question asked is answered and the answer is sharp: 4.7
carries no floor, its budget is \(1.4048\), and its missing hypothesis
costs \(18\) of \(42\) exclusions --- each of which an admissible word
with runs of length at most two actually voids.

The obvious reopener is now closed rather than open. Recovering the
no-`EE` hypothesis needs a constraint that is **floor-sensitive**: every
constraint used above is exponent bookkeeping, which is exact for the
multipliers and blind to the floors, and the witness satisfies all of
them. Nothing about run structure can help, since the witness already has
the run structure the packing wants. Reopen only on a genuinely new
constraint of that kind --- not on a sharper version of these.

## Files

- Probe: `src/research/juggler_sequence/cycle_packing_fragility.py`
- Test: `tests/research/juggler_sequence/test_cycle_packing_fragility.py`
- Data: `data/research/juggler/cycle_finance/packing_fragility.json`

## Publication assessment

Status: `MEASUREMENT`. Belongs in Paper A as the price attached to
Theorem 4.7's hypotheses -- the 24/18 split of Theorem 4.8 and the
"packing hypothesis and its price" subsection of section 4. Not a
theorem of its own and not a halt theorem.
