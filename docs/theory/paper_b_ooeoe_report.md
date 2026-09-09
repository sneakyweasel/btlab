# Paper B: four-step audit, OOEOE repair, and kernel assessment

9 September 2026. Version: 2026-09-09-ooeoe-repair.

## Outcome

The OOEOE split is proved in the revised manuscript:
\[
\#OOEOE(N)=N/32+O(N^{47/48}).
\]
The disjoint certificate prefixes E, OE, OOEE, and OOEOE therefore
form a class of natural density **27/32**. This is a specified subset
of the starts with a five-step power-envelope certificate. It does
not assert that the entire five-step certificate set has density
27/32, or that every start terminates.

The full five-step density **7/8** now requires only the remaining
correlation hypothesis for OOOEE. The general decorated kernel and
its short-interval version remain unproved.

## Audit of the four-step proof

The written-proof audit found no additional gap in Lemmas 4.3–4.4,
Theorem 4.5, Corollary 4.6, or their use in Theorem 5.2. It checked:

- The sawtooth convention at integer inputs and the ambient-scale
  discrepancy used to count the Fourier error.
- The exact carry identity before truncation, with real half-integer
  coefficients allowed throughout.
- The derivative of the smooth A_h term and curvature dominance for
  every nonzero carry frequency.
- The zero-mode boundary term after summing every gap cell.
- Both signs and zero coordinates in the mixed-mode estimate.
- The pointwise root comparison, dyadic cutoffs, and disjoint
  certificate prefixes used to obtain density 13/16.

This was a further audit by the same assistant, not independent
mathematical peer review. Exact tests check algebra and bookkeeping;
they do not prove exponential-sum cancellation.

## The new identity

Put X=n^(3/2), m=floor(X), Y=m^(3/2), v=floor(Y), U=sqrt(v),
w=floor(U), theta={X}, and xi={U}. Taylor's theorem gives
\[
w^{3/2}=n^{27/16}-\tfrac98\theta n^{3/16}
-\tfrac32n^{9/16}\xi+O(P^{-9/16})
\]
on a dyadic block. For the fifth-letter Fourier index k, use the
smooth coefficient B=(3k/4)n^(9/16), freeze its integer part N,
and expand only its bounded fractional part beta=B-N.

For the resulting fixed frequency R=r-N+ell/2, the first-floor
coefficient satisfies the exact cancellation
\[
\tfrac{9k}{16}n^{3/16}+\tfrac34Rn^{-3/8}
=\tfrac34n^{-3/8}(r+\beta+\ell/2).
\]
With |r| at most P^(1/8), this remainder is small enough to delete.
No frequency is differentiated while varying with n. This avoids
the extra growing sawtooth in the historical proof.

## The interval cost

There are O(|k|P^(9/16)) frequency intervals, of length
O(P^(7/16)/|k|). Lemma 4.8 applies the carry argument on their
intersections with every gap cell. The additional differenced-sum
boundary cost is
\[
O(|k|P^{15/16}h^{-1/2}).
\]
After Cauchy–Schwarz and one van der Corput differencing, it contributes
|k|P^(31/16)H^(-1/2) to the squared bound. At H=P^(1/12) and
|k| at most P^(1/48), this is P^(23/12), exactly within the
available budget. The other largest costs have the same exponent.
Carry errors are summed once over the disjoint input intervals;
no global exceptional set is rescaled by interval length.

Theorem 4.9 thus proves all required four-coordinate mixed modes,
including mixed signs and zero coordinates. Corollary 4.10 gives
all sixteen formal sign classes and the actual OOEOE/OOEOO split.
Theorem 5.3 states the resulting 27/32 subfamily. The remaining
conditional full five-step result is now Theorem 5.4.

## Bounded kernel assessment

The basic collision model passes a useful exponent check. In
Proposition 7.6, an integer collision frequency w>=1 implies
uh is bounded below by a constant times P^(1/4). Together with
h<=P^(1/8) and uh<=P^(1/2), every term in (7.5) is O(P^(7/8)).
Thus the repaired model itself does not exhaust the power saving.

The full expansion still needs an audit of its actual frequency
supports and majorants. One concrete issue occurs in the historical
Lemma 5.2 Stage 6(D2)(a): the invoked Fourier decomposition has both
a continuous-part cutoff T=P^(1/2) and a sawtooth cutoff
J=P^(5/16). The printed curvature discussion restricts the produced
indices using J; it does not separately account for continuous-part
modes between J and T. The coefficient formula in the historical
Lemma 3.7 bounds their mass by O(|B|/J) when J is larger than |B|.
With |B|=O(khP^(1/8)), its crude full-block cost can be as large
as O(P^(47/48)) over the printed parameter range. This is a
possible weaker estimate, not the printed wave bound; its effect
through all differencing stages has not been proved here.

The slow branch variables F also need their own uniform Fourier-error
counts on the changing branch partitions. The single-floor X
discrepancy and the U discrepancy proved here do not provide those
counts automatically. A bound on smooth curvature alone does not
complete these error estimates.

Decision for the general kernel: **PARK** after this feasibility pass.
No counterexample to the desired kernel bound is asserted. The next
kernel question is whether the full D2 expansion, including both
frequency ranges and its majorants, retains a positive saving after
all required differencing.

## Validation and publication status

The two previous exact validators pass. The new standalone validator
checks 1,275 exact centering identities, the frozen-frequency curvature
coefficient 243/512, five squared-sum exponents, ten strict exponent
comparisons, and the certificate fractions. The manuscript contains
the analytic proofs and clearly identifies the remaining hypothesis.

Decision for this paper extension: **PROMOTE** the OOEOE estimate and
the 27/32 certificate subfamily. Best next question: can the remaining
OOOEE correlation be proved with a fully controlled D2 expansion?

No new Lean formalization, independent peer review, Zenodo deposit,
or public upload is claimed.
