# The barrier word: the one-sided hypothesis demands an 84-order deficit

Status: **PROMOTE** (a structural finding about Paper C's
\(\mathrm H_q(C,A)\): at large scales an explicit bad cylinder is
parity-constant, so the hypothesis survives only if that cylinder is
astronomically below its fair share).

## Problem

Whether the parity-constant bad cylinders found by
[bad-cylinder excess](juggler_bad_cylinder_excess.md) persist at the scales
where Paper C's hypotheses are asserted, and what they demand.

## Exact statement

The **barrier word** is \(w=OE^{t-1}\): one odd letter, then even letters
until the value sits just above the certified floor. Its prefix walk is
\(u_s=\log_23-s\), so it is \(L(y)\)-bad exactly while \(t<L(y)+\log_23\);
\(t\) is taken maximal, a depth of order \(L(y)\), far inside the window
\(t<d(y)=\lceil CL(y)\rceil\). On its cylinder the map is the plain
composite \(G(n)=\lfloor\cdot^{1/2}\rfloor^{t-1}\lfloor n^{3/2}\rfloor\),
because the letters say exactly that the intermediates are even, and \(G\)
is monotone. Questions: what is the image \(G((y,2y])\); is it a single
value; and what does \(\mathrm H_q(C,A)\) then demand of \(\#[w]\)?

## Current literature

`extended`. The absorbed-cylinder obstruction
([juggler_absorbed_cylinder.md](juggler_absorbed_cylinder.md),
`J-absorbed-cylinder`) refutes the all-word cylinder bound with starts that
have reached \(1\); this branch is the same shape for the *bad* words, with
a start that hovers just above the floor instead of being absorbed. Direct
predecessors: [cylinder energy, measured](juggler_cylinder_energy_measure.md)
and [bad-cylinder excess](juggler_bad_cylinder_excess.md). No external
result is claimed.

## Branch budget

- **Target:** at scales beyond enumeration, is the barrier cylinder
  parity-constant, and what deficit does \(\mathrm H_q(C,A)\) demand?
- **Novelty hypothesis:** the barrier value is bounded independently of
  \(y\), so the computation is small even when \(y\) is not.
- **Falsifier:** the barrier value growing with \(y\), or the image
  staying wide, would leave the hypothesis untouched.
- **Already killed by?:** none. `J-absorbed-cylinder` kills a different
  (all-word) statement.
- **Existing machinery:** `floor_power`; the walk criterion of Lemma 8.1;
  big-integer `isqrt`; the forward measurements of the two predecessors.
- **Maximum Phase-0 scope:** the value range and the exact level-set
  weights at a dozen scales up to \(10^{20000}\), plus one constructed
  witness. No sampling, no Lean.
- **Promotion criterion:** a bad cylinder, inside the window, shown
  parity-constant at a scale where the hypothesis is asserted.
- **Stop criterion:** the falsifier.

## Balanced-ternary formulation

Not used. The objects are integer square roots and parities.

## Why BT may be relevant

Not relevant here; no claim.

## Candidate operations / invariants

The barrier depth; the composite \(G\) and its monotonicity; the image
interval \([G(y+1),G(2y)]\); the exact level-set weights by bisection; the
constructed witness. All **COMPUTATIONALLY VERIFIED**.

## Experiments

`python -m research.juggler_sequence.barrier_collapse` writes
`data/research/juggler/barrier_collapse/summary.json`: per scale
\(y=10^k\), \(k\) from \(7\) to \(20000\), the barrier depth, its minimum
prefix walk and badness, \(d(19)\) for comparison, the value range and its
width, whether the value lies in the floor band, the fair share
\(2^{-t}\), the exact odd share of the next letter, the exponent it
permits, and the deficit \(\mathrm H_q(C,A)\) demands; plus a witness.

## Conjectures

None registered. The refutation of \(\mathrm H_q(C,A)\) is not asserted:
it needs a lower bound on \(\#[w]\), which is not proved here.

## Counterexamples

The witness at \(y\approx10^{19999}\): an explicit \(20000\)-digit odd
start whose first \(14\) letters are \(OE^{13}\), whose \(14\)th iterate is
\(4593\), and whose word is \(L(y)\)-bad (minimum prefix walk
\(-12.415\) against \(-L(y)=-13.016\)) at depth \(14\) against
\(d(19)=248\). Reproduced by `witness` in the probe and checked forward by
iterating the map.

## Formalization

None new. The hypothesis at issue is `OneSided.OneSidedBound` in
`formal/Problems/Juggler/FateOneSidedCorollary.lean`, which feeds
`OneSided.one_sided_implies_conjecture`, `Energy.energy_implies_conjecture`
and `OneSided.exc_implies_conjecture`. Those theorems are implications and
remain correct; what this branch bears on is whether their hypothesis is
satisfiable. Nothing here is proved about the map.

## Results

**COMPUTATIONALLY VERIFIED** (14 September 2026; exact big-integer
arithmetic, no sampling).

*The barrier value is bounded, at every scale.* It lies strictly between
the floor \(N_0=260\) and its square at all twelve scales tested, from
\(v_0=421\) at \(10^7\) to \(4593\) at \(10^{20000}\): one more even letter
would cross the floor, one fewer leaves the value below its square. So the
object to compute is small however large \(y\) is, which is what makes the
backward computation possible.

*The image narrows to a point.* The number of values the barrier cylinder
sits over is \(126,\,91,\,6760,\,3271,\,1609,\,799,\,3,\,3,\,2,\,3,\,1\) at
\(k=7,15,25,50,100,200,435,1000,2000,5000,20000\). It follows
\(V\approx v_0\log v_0/\log y\) with \(v_0\) bounded, so it tends to zero:
past some scale every start of \((y,2y]\) with the barrier word has the
same \(t\)-th iterate.

*At \(10^{20000}\) the cylinder is parity-constant.* There
\(G(y+1)=G(2y)=4593\), an odd number, so every member of \([OE^{13}]\) has
next letter \(O\): the exact odd share is \(1\), not \(\tfrac12\). The word
is bad and sits at depth \(14\) against a window reaching \(248\). An
explicit member is constructed.

*So the hypothesis demands a deficit that grows without bound.* With
\(\#[wO]=\#[w]\), \(\mathrm H_q(C,A)\) requires
\((1-q)\#[w]\le y(\log y)^{-A}\). At \(A=C=19\) and \(q\) at the paper's
ceiling, that allows \(\#[w]\le10^{-88}y\) against a fair share of
\(2^{-14}=6.1\cdot10^{-5}\): a deficit of \(84\) orders of magnitude. The
deficit at the twelve scales is \(21.6,27.6,31.8,37.2,42.6,48.1,53.9,60.4,
65.9,73.1,84.0\) — monotone, and growing without bound. Read the other
way: the exponent the barrier word permits is
\(2.91,2.90,\dots,1.20,0.97\), tending to \(1\), while the criteria need
\(A>C\ge19\).

*What is not established.* \(\#[w]\) itself. Counting the starts whose
thirteen intermediates are all even is an equidistribution statement of
exactly the kind Proposition 4.4 is about, and none is available. The
finding is therefore conditional on the barrier cylinder being within
\((\log y)^{18}\) of its fair share — a mild demand, confirmed exactly at
the scales where enumeration is possible (at \(10^7\) each bad word of
length \(4\) holds \(0.125y\), its fair share to three digits), but not
proved.

## Open questions

A lower bound \(\#[OE^{t-1}]\gg y(\log y)^{-c}\) for some fixed \(c\), at
the barrier depth \(t\approx L(y)\). Any such bound with \(c<A\) turns this
branch into a refutation of \(\mathrm H_q(C,A)\). Note the depth is only
\(O(\log\log y)\) and the conditions are \(t-1\) parities of nested floors,
so this is a bounded-depth statement, closer to Paper B's five-step
certificates than to Proposition 4.4's block average.

## Decision

**PROMOTE.** The target was met at a scale where the hypothesis is
asserted: an explicit bad word, well inside the depth window, whose
cylinder is parity-constant, with the deficit it demands growing without
bound. This does not refute \(\mathrm H_q(C,A)\) — that needs the cylinder
size — but it removes any presumption that the hypothesis holds, and it
does so by the same mechanism as `J-absorbed-cylinder`, transplanted from
absorbed starts to starts hovering above the floor. The one-sided criteria
in the Lean layer stay correct as implications and should carry the
warning. Do not reopen as a search for other words: the barrier word is
extremal by construction. Best next question: a lower bound on the barrier
cylinder's size, which is a bounded-depth nested-floor parity count.

## Publication assessment

Status: `STRUCTURAL`. Belongs in Paper C beside the absorbed-cylinder
obstruction of Section 8.3, as the corresponding remark for the one-sided
form of Section 9.1: the bad-word restriction removes the absorbed starts
but not the starts that hover just above the floor, and those make an
explicit bad cylinder parity-constant at large scales. Not a theorem, not
a refutation, and not a halt theorem.
