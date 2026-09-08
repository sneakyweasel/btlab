# Juggler: what the two exclusion mechanisms can reach

Status: **PARK** (Paper A §6.2)

Not a halt theorem, not a floor raise, not a refutation. It asks what
Paper A's two exclusion mechanisms reach *in the limit* and answers with
numbers, so that effort stops being spent on directions with a measured
ceiling.

## Problem

Every result in Sections 4 and 5 is a period bound: exclude \(L\) when
\(n_{\max}(L)\le N_0\). Section 3's results are floor-free and
length-free but stop at seven even letters. Neither family has ever been
asked what it converges to.

## The floor route diverges

Along the convergents \(p_k/q_k\) of \(\log2/\log3\), the surplus is
\(\theta\approx\log3/q_{k+1}\), so

\[
n_{\max}(q_k)\log n_{\max}(q_k)\ \approx\ c\,q_k q_{k+1},\qquad c\approx0.45,
\]

flat to within a factor \(1.3\) over \(q_k=19,84,1054,50508,176251\).
`paper_a_audit.convergent_invariant` is the table. Since \(q_{k+1}\) is
unbounded, so is \(n_{\max}\): **every length carries its own descent
floor, and the floors are unbounded.** No finite computation excludes
all lengths — intrinsic to using a floor, not a defect of a table.

Measured, raising \(N_0\) buys period \(\approx N_0^{0.59}\) by finance
and \(\approx N_0^{0.69}\) with the walk charge. Neither exponent
matters: the target recedes faster than any of them closes.

## The shape route is exponential

Section 3 kills *words*, not lengths, so it is the only family here that
could close the problem uniformly. Counting what it faces: writing the
itinerary as \(O^{a_0}E\cdots O^{a_{e-1}}E\), the shapes admissible at
the least odd count — \(a_0\ge2\), each run within Theorem 3.31's cap,
every prefix above the anchor — are

| \(e\) | 7 | 10 | 13 | 16 | 20 |
|---|---|---|---|---|---|
| shapes | 2651 | \(5.3\cdot10^{5}\) | \(7.2\cdot10^{7}\) | \(1.1\cdot10^{10}\) | \(1.1\cdot10^{13}\) |

about \(6\times\) per even letter. The first surviving length
\(L=25781\) has \(e=9515\). So Theorem 3.31's \(e\le7\) is not a stage on
the way to \(e\le8\); it is the end of that method.

The count is a dynamic program rather than a search: the above-anchor
condition after block \(i\) depends only on the cumulative odd count,
because the walk rises inside a run and dips only at even letters. State
\((\text{block},\ \text{odds used})\), so the numbers are exact.

## What is actually missing

The only proved relation between a cycle's minimum and its period runs
one way. Finance bounds the minimum above, \(n\log n\lesssim L^{\mu}\)
with \(\mu\) the effective irrationality measure of \(\log2/\log3\); and
\(\mu\ge2\) for *every* irrational, so even a perfect measure leaves
\(n\lesssim L^{2}\). Nothing bounds the minimum below in terms of the
period: the descent floor is a constant, not a function of \(L\), and
counting the \(L\) distinct states yields no window, since a cycle's
states are not confined to one — the confinement finance does supply is
finance itself, so that argument is circular.

Survivors sit at \(L\approx n^{0.59}\), that is \(n\approx L^{1.7}\),
inside the band \([L, L^{2}]\) that a one-sided bound cannot empty.

## Decision

**PARK.** Reopen only on one of two things, neither of which has a
visible mechanism: a lower bound on the cycle minimum in terms of the
period, or an argument uniform over shapes rather than an enumeration of
them. Do not reopen on a bigger floor, a sharper per-length charge, or a
longer enumeration; all three have ceilings measured here.

## Files

- Probe: `src/research/juggler_sequence/cycle_method_ceilings.py`
- Test: `tests/research/juggler_sequence/test_cycle_method_ceilings.py`
- Data: `data/research/juggler/cycle_finance/method_ceilings.json`
