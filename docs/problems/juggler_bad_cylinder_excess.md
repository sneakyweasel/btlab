# Is the one-sided hypothesis satisfiable? The excess of the bad cylinders

Status: **PARK** (the question is now a single decaying quantity, and the
scales that would decide it are out of reach by forward enumeration; a
backward computation could reach them).

## Problem

Paper C's Section 9 criteria are implications from hypotheses nobody has
proved. This branch measures the quantity those hypotheses bound, to see
whether they are satisfiable at all.

## Exact statement

\(\mathrm H_q(C,A)\) at the scale \(y\) says that every \(L(y)\)-bad word
\(w\) of length \(1\le t<d(y)=\lceil CL(y)\rceil\) obeys
\(\#[wO]\le q\#[w]+y(\log y)^{-A}\). So it holds exactly when

\[
\mathrm{excess}(t,q)=\max_{w\ \text{bad},\,|w|=t}\bigl(\#[wO]-q\#[w]\bigr)
\ \le\ y(\log y)^{-A}
\]

at every such depth. The question: what is \(\mathrm{excess}\), exactly, for
\(y\in\{10^4,\dots,10^7\}\) and every depth up to \(32\); how does the
largest \(A\) it permits move with \(y\); and how does it compare with what
a fair coin would produce from the same cylinder sizes?

## Current literature

`extended`. The absorbed-cylinder obstruction
([juggler_absorbed_cylinder.md](juggler_absorbed_cylinder.md),
`J-absorbed-cylinder`) refutes the all-word member of the same family, which
is why Paper C states \(\mathrm H(C,A)\) and \(\mathrm H_q(C,A)\) on the
bad words; this branch asks the same question of the restricted versions.
[Cylinder energy, measured](juggler_cylinder_energy_measure.md) found the
collapse mechanism and is the direct predecessor. Paper C Section 11
measures sampled tilted shares, not per-cylinder quantities. No external
result is claimed.

## Branch budget

- **Target:** does the largest excess of a bad cylinder, over the paper's
  own depth window, permit an \(A\) that grows with \(y\)?
- **Novelty hypothesis:** the hypotheses of Section 9 have never been
  measured against the quantity they bound.
- **Falsifier:** the permitted \(A\) growing with \(y\) at least as fast as
  the fair-coin baseline would make the hypotheses look satisfiable and the
  branch uninteresting; it not growing makes them doubtful.
- **Already killed by?:** none. `J-absorbed-cylinder` kills the all-word
  version, which is a different statement.
- **Existing machinery:** `floor_power`; the itinerary words; the
  \(L(y)\)-bad criterion of Lemma 8.1; the enumeration of
  `cylinder_energy_measure`.
- **Maximum Phase-0 scope:** one exact enumeration of every odd start of
  \((y,2y]\) to depth \(32\) at four scales, two shares, no sampling, no
  Lean.
- **Promotion criterion:** the permitted \(A\) tracking or beating the
  fair-coin baseline across the four scales.
- **Stop criterion:** the falsifier, or a mechanism that makes the
  measurable range unrepresentative.

## Balanced-ternary formulation

Not used. The statistic is a parity count on the integer orbit.

## Why BT may be relevant

Not relevant here; no claim.

## Candidate operations / invariants

The per-depth maximum excess and the largest \(A\) it permits; the
standardised bias \(z_w=(\#[wO]-\#[w]/2)/\sqrt{\#[w]/4}\) against the
fair-coin maximum \(\sqrt{2\log W}\); the collapse alphabet (cylinders
\(W\), distinct iterates \(V\), pairs \(P\), and \(P/W\)); the largest
cylinder. All **COMPUTATIONALLY VERIFIED** on the recorded ranges.

## Experiments

`python -m research.juggler_sequence.bad_cylinder_excess` writes
`data/research/juggler/bad_cylinder_excess/summary.json`: per scale, per
depth, the bad mass fraction, \(W\), \(V\), \(P\), \(P/W\), the largest
cylinder, \(z_{\max}\), the fair-coin baseline, the maximum excess at
\(q\in\{0.5,0.55\}\) with the \(A\) it permits, the fair-coin excess with
the \(A\) *it* would permit, and the cylinder-bound excess; plus a verdict
per scale for \(C\in\{19,30\}\) over the window \(1\le t<d(y)\). Runtime
\(175\) s at \(10^7\).

## Conjectures

None. Computational observations are not conjectures.

## Counterexamples

None found: nothing here refutes either hypothesis. The observed failures
are at scales where the hypotheses are not asserted.

## Formalization

None new. The hypotheses measured are
`OneSided.OneSidedBound` and `CylinderBound` in
`formal/Problems/Juggler/FateOneSidedCorollary.lean` and
`FateChernoff.lean`; the criteria they feed are in
`FateOneSidedCorollary.lean`, `FatePressureCorollary.lean` and
`FateProduction.lean`. Nothing in this branch is proved about the map.

## Results

**COMPUTATIONALLY VERIFIED** (14 September 2026, exact enumeration, every
odd start of \((y,2y]\), no sampling).

*The additive error is dead at computable scales, so the measurement is
against a fair coin.* With \(A\ge32\), \(y(\log y)^{-A}\) is below
\(10^{-38}\) at \(y=10^7\): the hypothesis there degenerates to an exact
share bound that no finite sample obeys, and a bare comparison would be
meaningless. The scale-honest question is whether the map does worse than a
fair coin with the same cylinder sizes, whose largest excess is
\(\sqrt{2\log W\cdot n_{\max}}/2\).

*The permitted exponent does not grow, and falls behind a fair coin.*
Over the window \(1\le t<d(y)\) at \(C=19\), the largest \(A\) the measured
excess permits is \(2.62\), \(2.84\), \(2.61\), \(1.59\) at the four
scales, while the fair-coin baseline over the same cylinder sizes is
\(2.62\), \(2.86\), \(3.10\), \(3.34\). The gap is
\(-0.01,\ -0.01,\ -0.49,\ -1.74\): at \(10^4\) and \(10^5\) the map is
indistinguishable from a coin on this statistic, and at \(10^6\) and
\(10^7\) it is measurably worse. At \(C=30\) the window is longer and the
figures are identical, the binding depth being shallow in both cases.

*At fixed shallow depth the map is fair, and gets fairer.* The three
largest bad cylinders at depth \(4\) have odd shares \(0.53,0.53,0.52\) at
\(10^4\) and \(0.5001,0.4994,0.5008\) at \(10^7\). The deviation of a
cylinder's share from \(\tfrac12\) is governed by the number of distinct
iterates it sits over, which widens with \(y\) at fixed depth: at depth
\(4\) the word \(OEE\!\cdot\) sends \((y,2y]\) to about \(y^{3/8}\), a range
of about \(125\) integers at \(10^7\) and about \(10^{37}\) at \(10^{100}\).
Fixed-depth failures are therefore a small-scale artifact, and the drop in
the permitted exponent at \(10^7\) is one: it comes from depth \(4\), where
two even letters already collapse the value because \(L(10^7)=1.6\).

*At the top of the paper's own window the cylinders are parity-constant, at
every scale.* The number of distinct iterates per bad cylinder at the last
depth of the window, \(t=d(y)-1\) with \(C=19\), is \(1.14\), \(1.02\),
\(1.01\), \(1.00\) at the four scales: a bad cylinder there sits over a
single value, so all of its members share a next letter whatever the map
does, and its share is \(0\) or \(1\). This is not a small-scale artifact —
it holds at every scale measured, and the depth at which it sets in tracks
\(d(y)\) rather than lagging it.

*So the hypotheses reduce to one decaying quantity.* A parity-constant bad
cylinder of \(n\) members has excess \((1-q)n\), so \(\mathrm H_q(C,A)\)
requires the largest such \(n\) to be below \(y(\log y)^{-A}/(1-q)\) with
\(A>C\). Measured as a fraction of the starts, the largest cylinder at
\(t=d(y)-1\) is \(2.0\cdot10^{-3}\), \(6.8\cdot10^{-4}\),
\(4.6\cdot10^{-4}\), \(1.6\cdot10^{-3}\): order \(10^{-3}\) with no visible
decay across three decades, against an allowance of \(10^{-23}\) at
\(C=19\) and \(y=10^7\). Whether that fraction decays like
\((\log y)^{-A}\) is exactly the survival of \(\mathrm H_q(C,A)\), and three
decades of \(y\) cannot see a \((\log y)^{-19}\).

## Open questions

Does the mass fraction of the largest parity-constant bad cylinder decay
like \((\log y)^{-A}\) with \(A>C\)? Two things make this reachable without
enumerating \((y,2y]\). A parity-constant cylinder is a fiber of a small
value \(v\) along a word \(w\), and the preimage of \(v\) under an even step
is an interval, so the fiber can be computed backwards, from \(v\) and
\(w\), at any scale — including \(y=10^{25}\) or \(10^{100}\), where
\(L(y)\) is \(3\) or \(5.4\) and the early-collapse artifact is gone. And
the number of values a cylinder sits over, which governs its share, is
computable the same way. A backward computation of the largest fiber over
the words that reach the barrier is the experiment this branch could not
run forwards.

## Decision

**PARK.** The falsifier fired in the weak sense — the permitted exponent
did not grow, and fell below the fair-coin baseline at the two largest
scales — but the mechanism behind the fall at \(10^7\) is an artifact of
\(L(y)=1.6\), so the measurement does not decide the asymptotic question
and does not refute anything. What it establishes is sharper than a
verdict: the deep end of the paper's own depth window is parity-constant at
every scale measured, so the hypotheses stand or fall on the mass of the
largest such cylinder, one quantity with a known form. Do not reopen as a
larger forward enumeration (three decades of \(y\) cannot see a
\((\log y)^{-19}\)), a sampled run (the statistic is a maximum), or another
normalisation. Best next question: compute the largest parity-constant bad
cylinder backwards, from the value and the word, at scales where
\(L(y)\ge3\).

## Publication assessment

Status: `STRUCTURAL`. Belongs as an observation beside Paper C Section 11
and the absorbed-cylinder obstruction of Section 8.3: the bad-word
restriction removes the absorbed starts but not the collapsed ones, and at
the top of the depth window the surviving cylinders are parity-constant at
every computable scale. Not a theorem, not a refutation, and not a halt
theorem.
