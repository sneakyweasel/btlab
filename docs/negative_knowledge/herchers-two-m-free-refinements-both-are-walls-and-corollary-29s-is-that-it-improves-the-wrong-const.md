# Hercher's two m-free refinements: both are walls, and Corollary 29's is that it improves the wrong constant

Recorded 21 September 2026, after reading Hercher 2023 at Theorem 27, Lemma 26 and
Corollary 29 from the arXiv PDF. Both were proposed as ways to strengthen Paper D without
raising the verification floor, both were measured against what this side needed, and
neither reached. The proposal was mine and it was too optimistic; the measurement was the
correction.

**Amended twice on 21 September 2026.** The first shortfall was measured against the bound
Paper D 1.0.0 used. Version 1.1.0's valley count moved the first open value from \(m=59\)
to \(m=62\) and the shortfall with it, and the first verdict did not survive that: against
the refined bound, closing \(m=62\) needs \(0.30\) bits of effective floor and \(m=63\)
needs \(0.62\), against Corollary 29's \(1.30\), so it was reclassified `OPEN, WORTH
TRYING`. The guard in the pinned test was written to fire exactly there and did not, because
it went on measuring the old shortfall while the paper moved. The second amendment is the
transposition actually attempted, below; it is a wall again, for a reason that does not
depend on the size of any floor gain.

**Corollary 29, residue-class tracking.** He tracks the local minimum modulo powers of two
across the Lemma 26 cases and drops any case whose residue class has its least member above
the bound he needs, so a verified floor of \(1536\cdot2^{60}\) does the work of
\(3781\cdot2^{60}\). That is a factor \(2.46\), or \(1.30\) bits of effective floor.

*Both halves of the mechanism do transpose, and the first amendment was wrong to doubt it.*
Lemma 26's case analysis has an exact negative-side statement. The note's Lemma 1 makes the
run exact, so the run from a local minimum \(y\) with \(u=y-1\) and \(a=v_2(u)\) contributes
\(T(y)=\sum_{k<a}1/(3g^k(y)-1)<\kappa(a)/u\) with \(\kappa(a)=1-(2/3)^a\) — the factor the
note's Lemma 2 discards, and the same factor his Remark 7 carries as \(3(1-(2/3)^k)/n\). The
relation between consecutive minima is
\(u_i=(2/3)^{a_i}\bigl(2^{r_i}(u_{i+1}+1)-1\bigr)\) here against his
\(n_i=(2/3)^{k_i}(2^{\ell_i}n_{i+1}+1)-1\): the same shape with the sign flipped, so his one,
two and three-run averaging carries over case for case and with the same rationals
(\(1/4\) at \(a=1\), \(5/8\) at \(a=2\), \(19/27\) at \(a=3\)). The residue-class drop is
available too, and in a sharper form: Lemma 1 is the run congruence and Lemma 5 makes each
case word a residue class, and because every minimum of a window is above the floor, the
drop uses the least member of the class *above the floor* rather than the least positive
member, and the later minima of the window pull it further up.

*What does not transpose is the size, because it is the size of a different constant.*
Corollary 29 improves the m-free constant of Theorem 27. Paper D's open values are not
decided by any m-free bound. At \(m=62\) the chaining display of Theorem 8, which is the
one a finance constant moves, clears by \(41.4\) bits; what holds the row open is Lemma 6's
valley cap, and the cap is minimised with only **four** minima at the floor at \(m=62\) and
five at \(m=63\). An averaging argument can act on nothing but that block.

*Measured on this side, at the floor \(2^{51}\), against version 1.1.0's bound.* Closing
\(m=62\) needs those four minima to average \(0.8137\) of Lemma 2's own one-per-valley;
four consecutive local minima above \(2^{51}\) attain \(0.9013\), at the start
\(2255557997555713\), whose runs are \(12,7,5,6\). Closing \(m=63\) needs five to average
\(0.6509\); five attain \(0.8689\), at \(2266848965985921\), runs \(7,5,7,5,6\). So the
refinement is worth at most \(0.150\) bits where \(0.297\) are needed and \(0.203\) where
\(0.619\) are needed: **just over half of what \(m=62\) asks and a third of what \(m=63\)
asks, and the shortfall widens with \(m\).** Those figures charge the method no boundary
loss at all — a real lemma would have to pay for the ends of the block — and the starts are
concrete integers walked on the map, so they are lower bounds on what any averaging argument
can ever give here, not estimates, and the verdict rests on them alone. The search that
found them is a branch-and-bound over residue classes, Corollary 29's own mechanism run on
this side; it closes within a part in ten thousand of each witness, so the windows are not
an artifact of looking in the wrong place. What it closes is the least prefix average, which
is what a greedy block partition consumes; it does not bound the block average from above,
and for this verdict it does not need to.

*The scope of that verdict, stated exactly.* The witnesses are windows of an orbit, not of a
known cycle — no cycle above the floor is known, which is the point of the whole argument —
so they refute the method rather than the conclusion. Lemma 26 and Corollary 29 use only the
floor and the local step relations along at most a few consecutive runs; they never use the
cycle's closure. Every such bound is at the mercy of any window that satisfies those local
constraints, and these do: they are real orbit segments, their minima all lie above
\(2^{51}\), and their runs sum to thirty against an \(o\) of \(5.2\cdot10^{13}\), so
Lemma 6's odd-step count does not touch them either. To beat them one would need an
ingredient neither refinement has.

*Why the block is short, and what would lengthen it.* A single minimum gives nothing at all:
\(y=2^{51}+1\) has \(a=51\) and \(\kappa\) within \(10^{-9}\) of one, so the one-valley
constant is \(0.999999999\). The gain comes only from consecutive minima, and it grows with
the block — two average \(0.989\), four \(0.901\), seven \(0.770\), which is \(0.376\)
bits — because a block of \(d\) minima near the floor has to fit its run and halving lengths into
the floor's \(51\) bits, which forces short runs and short runs waste \(\kappa\). Lemma 6
puts only four there at \(m=62\). The block grows with \(m\) and with the floor, and so does
the demand, and the two do not stay this far apart. At the floor \(2^{60}\) of the note's
Table 2 the row \(m=76\) has a block of eight and demands \(0.7535\), and an eight-minimum
window above \(2^{60}\) attains \(0.7579\): short by \(0.008\) bits rather than by half. The
row \(m=75\) there has a block of seven and demands \(0.8611\), and the best seven-minimum
window found above \(2^{60}\) attains only \(0.7996\) — so **at that floor nothing measured
rules the transposition out**, and it would take a bound on the block average from above,
which this branch-and-bound does not give, to say whether it reaches. This wall is a
measurement against a floor as well as against a bound, and it is a much thinner wall at
\(2^{60}\) than at \(2^{51}\).

**Theorem 27, the m-free averaging.** In the normalisation of this side it reads
\(\Lambda<\tfrac14 o/X_0\), a constant of \(0.1577\) per unit of total cycle length
against the laboratory's \(0.1845\). It is therefore \(0.23\) bits tighter than what this
side already has — and what this side already has is kernel-checked (`neg_cycle_finance`,
\(2(y-1)(3^o-2^K)\le(K-o)3^o\)), where his needs a case analysis over one, two or three
consecutive runs. Transposing it would buy \(0.23\) bits at the cost of reproving a case
analysis. Worse, it buys nothing at all in practice: the m-free period bound is unchanged at
\(85137581\) under the tighter constant, because the surviving lengths are near-convergents
of \(\log2/\log3\) and sit far apart, so a seventeen per cent change of the window removes
none of them.

Kind: `METHOD WALL` for both, at the measured size, not `REFUTED`. Theorem 27 is correct on
its own side and would work here, it is simply too small and buys nothing where it is
applied. Corollary 29 transposes — the case analysis and the residue drop both have
negative-side statements, and the drop is sharper here — but the constant it improves is
not the constant Paper D's open values turn on, and applied to the one they do turn on it
delivers between a third and a half of what is needed. This supersedes the `OPEN, WORTH
TRYING` of the first amendment, which was a verdict on \(1.30\) borrowed bits rather than on
a measurement.

Do not reopen: Theorem 27 as a route to a better period bound, at any floor near
\(2^{51}\). Corollary 29 as a route to \(m=62\) or \(m=63\) at the floor \(2^{51}\), unless
Lemma 6's minimising block at the first open value grows past about eight minima, which is
where the window constant is worth half a bit. Do not quote the \(4.18\)-bit shortfall, or
the \(1.30\)-bit gain, without saying which paper version and which of the two constants it
belongs to.

Worth trying: the same window measurement at \(2^{56}\) and \(2^{60}\) before those floors
are run, since the wall is thinner there, and the window constants themselves for their own
sake — they are a statement about consecutive local minima of \(3n-1\) above a floor that
nothing else in the laboratory measures.

Done since: the valley arrangement behind his Main Theorem 21 was transposed and is Lemma 6
of Paper D 1.1.0. His Lemma 8 was already the note's Lemma 1. His Lemma 26 now has a
negative-side statement, recorded above and implemented in
`research.juggler_sequence.negative_valley_windows`; it is not in the manuscript, because it
changes no number there.

The general lesson, which is the reason this entry was amended twice rather than left
standing: a `METHOD WALL` is a measurement against a bound, and it expires when the bound
improves. An entry recording one should name the bound it was measured against, and the test
pinning it should measure the current shortfall rather than the one that was current when it
was written. The first version passed green while the condition it guarded had already
arrived. The second lesson is narrower and worth as much: when a refinement is quoted as
worth so many bits, the bits belong to a constant, and the constant has to be the one the
open case turns on. Here it was not, and the two were a factor of forty apart in slack.

Pinned: [tests/research/juggler_sequence/test_negative_m_cycles.py](../../tests/research/juggler_sequence/test_negative_m_cycles.py),
`test_herchers_corollary_29_transposes_but_improves_the_wrong_constant`,
`test_herchers_lemma_26_transposes_and_its_window_bound_spares_the_real_cycles` and
`test_a_stronger_run_factor_excludes_the_cycles_that_exist`.
