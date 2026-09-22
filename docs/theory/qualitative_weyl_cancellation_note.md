# Qualitative cancellation from fixed-shift correlations

22 September 2026. Formalization of a classical van der Corput argument.
The source is [WeylCancellation.lean](../../formal/BTCalculus/WeylCancellation.lean),
which imports the laboratory's [finite differencing inequality](finite_weyl_differencing_note.md).
This proves a general analytic tool; it does not prove cancellation for
Paper E's particular power phases.

## Exact statement

Let z be a complex sequence and C a positive real number with
|z(n)| <= C for every natural n. Suppose, for every fixed positive
natural d,

\[
 \frac{1}{N}\sum_{n=0}^{N-1}z(n+d)\overline{z(n)}\longrightarrow0
 \qquad(N\longrightarrow\infty).
\]

Then

\[
 \frac{1}{N}\sum_{n=0}^{N-1}z(n)\longrightarrow0.
\]

Only positive shifts occur in the hypothesis. No uniform rate in d is
assumed. The auxiliary definition `average` gives zero at N=0; this has
no effect on a limit at infinity.

## Boundary conversion

First suppose |z(n)| <= 1. Write

\[
 T_{N,d}=\sum_{0\le n<N-d}z(n+d)\overline{z(n)},
\]

where natural subtraction makes the sum empty if d>N. The full shifted
sum differs from T by the final N-(N-d) terms. Each has modulus at most
one, so `correlation_boundary_bound` proves that the difference has norm
at most d for every N and d, including N<d.

After division by N the error tends to zero for each fixed d.
`tendsto_overlap_zero_of_shifted` therefore transfers the stated full-sum
limit to |T_(N,d)|/N -> 0. The overlap is not silently replaced by a
periodic or full-length correlation.

## Limit argument

For 1<=H<=N, `normalized_van_der_corput` proves

\[
 \left(\frac{|\sum_{n<N}z(n)|}{N}\right)^2
 \le \frac{2}{H}+\frac{4}{H}\sum_{1\le d<H}\frac{|T_{N,d}|}{N}.
\]

Given epsilon>0, first choose a fixed H with 2/H<epsilon^2. The finite
sum on the right tends to zero as N tends to infinity. Eventually the
whole right side is less than epsilon^2, so the normalized norm is less
than epsilon. The Lean proof follows this order of quantifiers and
proves convergence directly, without assuming a limsup exists.

`tendsto_average_zero_of_shifted_correlations` gives the complex limit
for unit-bounded sequences. Scaling by C gives
`tendsto_average_zero_of_bounded_correlations`: the correlation averages
scale by C^2 and the sequence averages scale by C.

For any real-valued sequence f, the unit-modulus identity for
phase(t)=exp(2*pi*i*t) identifies the correlations with phase(f(n+d)-f(n)).
`tendsto_phase_average_zero_of_differences` packages exactly this
specialization, retaining the difference-phase cancellation hypotheses.

## Proof audit and scope

[AxiomCheckWeylCancellation.lean](../../formal/AxiomCheckWeylCancellation.lean)
audits the nine public theorems. The expected logical dependencies are
only propext, Classical.choice, and Quot.sound. No analytic estimate is
introduced as a logical assumption: correlation cancellation is an
explicit hypothesis of the implication.

The separate advisory prose-to-declaration review remains pending: the
configured review service could not be reached from this environment.
The ledger therefore keeps its pending-review label despite the successful
Lean build and dependency audit.

This is a foundation for [Paper E's Theorem 4.1](juggler_signed_collatz_note.md),
not a proof of its `BoxRecurrence` premise. The remaining obligations are:

1. Prove exponential cancellation for every nonzero integer combination
   of the fixed rational-power coordinates along s=1+2Mt. A differencing
   proof must handle the actual shifted differences, which need not be
   finite sums of pure powers of s.
2. Convert those joint Fourier limits into arbitrarily large visits to
   the specified positive-volume fractional-part box.
3. Supply that recurrence to `theorem41_of_box_recurrence` and audit the
   resulting unconditional statement.

No growing-depth uniformity, shrinking-target estimate, or quantitative
rate is proved here. The Paper E version 0.3.0 release and its selected
32-declaration audit retain their existing scope; this later foundation
has its own audit and does not change the manuscript's theorem status.
