# Juggler: what Paper A's exclusion mechanisms can reach

Status: **PARK** (Paper A §6.2)

Not a halt theorem, not a floor raise, not a refutation. It asks what
Paper A's exclusion mechanisms reach *in the limit* and answers with
numbers, so that effort stops being spent on directions with a measured
ceiling. Four are priced: the descent floor, the trailing-evens bound,
the charge family, and the shape enumeration.

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

Inverting that, raising \(N_0\) buys
\(\text{period}\asymp\sqrt{N_0\log N_0}\) by finance and
\(\asymp\sqrt{N_0}\log N_0\) with the walk charge, the second carrying
one more logarithm because the walk charge shrinks the charge by
\(0.44\log n'\). The walk coefficient is \(2.014,1.982,2.120\) at the
three published instances, constant to \(7\%\). Quoting these as
\(N_0^{0.59}\) and \(N_0^{0.69}\) fits a power to a square root: those
fits drift by a factor \(3\) across the same floors. Doubling the period
costs roughly quadrupling the floor, and no exponent helps because the
target recedes.

## The charge family is exhausted where it is length-only

A charge seeing only \((n,L,o)\) must bound every configuration those
numbers allow, and nothing proved forbids \(e\) valleys at
\(n,n+2,\ldots\); so it is at least \(\sim e/(n\log n)\) and the best
possible threshold is \(0.336\,q_kq_{k+1}\), against the
\(0.41\)--\(0.53\) Corollary 4.5 achieves. The ratio is \(1.21\) at the
large convergents — the \(6/5\) unroll and nothing else. **Finance is the
optimal length-only charge to within the coefficient it advertises**; no
sharper counting of valleys, internals and evens is worth more than
\(20\%\) in \(n_{\max}\), \(12\%\) in period. Theorem 4.7's
\(1.4048\) exceeds this only because no-\(\mathtt{EE}\) forbids the
extremal configuration. The room that remains is *orbit-dependent*
information, which is what the walk charge reads; Remark 5.8a prices it
at \(0.44\log n'\) and names its limiter as the shape of the charge.

## The trailing-evens bound is not independent

`cycle_trailing_evens_lt` is the one constraint whose strength reads
\((1+1/n)^{2^r}\) rather than \(\theta\), so it looks like the
floor-sensitive lever the prohibition below leaves open. It is not. The
window at the cut has log width \(2^r\log(1+1/n)\) and the \(r\) square
roots divide the log by exactly \(2^r\), so the transported width is
\(\log(1+1/n)\) at every \(r\): the constraint at any depth is the
\(r=1\) one carried back, and \(r=1\) is `cycle_last_even_interval`,
from which Theorem 4.4 is derived.

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

### And the law is empty where it matters

Feasibility is not the real obstruction. Theorem 3.26 says the whole word
expands while no proper tail beginning with an odd letter does.
Complementing tail to prefix, that reads
\(3^{o_p}/2^{|p|}\ge3^{o}/2^{L}=1/(1-\theta)\): the law **is** the anchor
condition, raised from \(1\) to \(1+\theta\). Its entire strength over the
anchor is the surplus.

| \(e\) | \(\Lambda\) | killed by the law |
|---|---|---|
| \(10\) | \(3.7\cdot10^{-1}\) | \(41.4\%\) |
| \(16\) | \(2.6\cdot10^{-1}\) | \(37.7\%\) |
| \(31\) | \(2.1\cdot10^{-3}\) | \(0\) |
| \(210\) | \(1.1\cdot10^{-3}\) | \(0\) |
| \(389\) | \(4.4\cdot10^{-5}\) | \(0\) |

At \(e=389\) the counts are equal as integers, all three hundred digits.
And \(\Lambda=\log(3/2)\,(1-\{e\cdot C\})\) is small exactly when
\(e\cdot C\) sits just under an integer, which is what makes a length
survive finance. Survivors have
\(\Lambda\in[3.6\cdot10^{-6},6.9\cdot10^{-5}]\).

**These mechanisms therefore fail for one reason.** Finance weakens as
\(\theta\to0\) because \(n_{\max}\sim1/\theta\); the run--suffix law
weakens as \(\theta\to0\) because it is the anchor tightened by
\(1+\theta\). The lengths where one is weak are exactly the lengths where
the other is, so they cannot be played against each other.

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
period: the descent floor is a constant, not a function of \(L\).

The counting route is priced rather than dismissed. A *primitive* cycle
has pairwise distinct orbit states (`cyclePrimitive_orbit_injOn`), so the
\(e\) valleys are distinct odd integers at least \(n\) — at least
\(n,n+2,\ldots,n+2(e-1)\), not all at \(n\). That refinement is real
and worth \(O(e/n)\): at the floor where each length matters it is
\(3.8\cdot10^{-4}\) at \(L=25781\), \(6.5\cdot10^{-5}\) at
\(176251\), and shrinking, since \(n_{\max}\sim q_kq_{k+1}\) outgrows
\(e\approx0.37L\). Distinctness is available, and empty.

Survivors sit at \(L\approx n^{0.59}\), that is \(n\approx L^{1.7}\),
inside the band \([L, L^{2}]\) that a one-sided bound cannot empty.

## Branch budget

Phase 0 only, and spent. Two probes -- `cycle_method_ceilings` for the
reach scalings and shape counts, `cycle_packing_fragility` for the
run-packing side -- over the existing finance and walk-charge machinery.
No new estimate, no new floor, no Lean. The branch is closed, so the
budget is not renewed: the reopen conditions in "What is actually
missing" are the only spend that would be justified.

## Decision

**PARK.** Reopen only on one of two things, neither of which has a
visible mechanism: a lower bound on the cycle minimum in terms of the
period, or an argument uniform over shapes rather than an enumeration of
them. Do not reopen on a bigger floor, a sharper per-length charge, or a
longer enumeration, or the trailing-evens bound; all have ceilings
measured here.

Sharper, and the standing instruction: **do not open a direction whose
kill criterion is a function of the surplus \(\theta\).** Every mechanism
in the paper is, and all are therefore empty at exactly the lengths a
cycle could occupy. The trailing-evens bound looked like the exception
and is not. A new idea has to be measured by something else.

## Files

- Probe: `src/research/juggler_sequence/cycle_method_ceilings.py`
- Test: `tests/research/juggler_sequence/test_cycle_method_ceilings.py`
- Data: `data/research/juggler/cycle_finance/method_ceilings.json`

## Publication assessment

Status: `MEASUREMENT`. Belongs in Paper A section 6 as the priced
ceiling, which is where it now sits: the floor-route reaches and the
length-only optimality are section 6.2, and the general statement is
Proposition 6.2a. Not a theorem of its own, not a halt theorem, and not
a Paper B object.
