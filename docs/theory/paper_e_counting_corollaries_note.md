# Paper E: counting and prescribed-residue corollaries

22 September 2026. **EXACT — HUMAN PROOF**, with compiled Lean counterparts;
independent statement coverage and external novelty review remain separate.

## Fixed-parameter statements

Fix natural a,b,M>0 with 3^a>2^(a+b), put d=2^(a-1), and s=1+2Mt.
Keep exactly the ReturnBox parameters with s>=2^(2^(b+1)). Their natural
density in t is delta=1/(2^(b+1)M). The number of distinct constructed
starts s^d<=X is asymptotic to X^(1/d)/(2^(b+2)M^2). For each fixed
epsilon>0, every sufficiently large (X,(1+epsilon)X] contains one.

Every retained start has actual itinerary O^a E^b, remains at least its
start throughout the prefix, ends strictly above it, and starts and ends
at residue 1 modulo 2M. The count is for this explicit family, not for
all starts having those orbit properties.

For any vector r_0,...,r_b in {0,...,2M-1}, even before the final index
and with r_b=1, impose at every j the half-open interval
fract(s^(3^a/2^(j+1))/(2M)) in [r_j/(2M),(r_j+1)/(2M)). The parameters
beyond the same threshold have density (2M)^(-(b+1)); they give infinitely
many distinct starts above every bound with J^(a+j)(n)=r_j modulo 2M.

## Proof architecture

1. The existing mixed-power theorem kills every nonzero Fourier mode.
   Uniform approximation therefore gives the Haar average of every
   continuous function on the finite torus.
2. Normalize the first N+1 Dirac masses as an empirical probability
   measure. The continuous-function criterion proves weak convergence.
   Portmanteau gives convergence on sets with Haar-null frontier.
3. A half-open circle arc is its open arc plus its left endpoint. Its
   volume is its length, including endpoints zero and one. Its frontier
   is contained in its two endpoints; Haar singletons have measure zero.
   The frontier of a finite box lies in the union of coordinate endpoint
   sets, all null by the product measure. Thus box frequency is volume.
4. Specialize the exponents and scales to the original return box or the
   prescribed residue box. Removing the finite size-threshold exceptions
   preserves frequency by a Cesaro argument on the indicator difference.
5. For X>=1 the exact number of possible parameter positions is
   floor((X^(1/d)-1)/(2M))+1. Dividing by X^(1/d) gives limit 1/(2M).
   The map t to (1+2Mt)^d is strictly increasing. Consequently parameter
   count equals distinct-start count and the leading constant is
   delta/(2M). A positive limiting difference between counts at cX and X
   proves the fixed-relative-interval assertion for every c>1.
6. Fractional-part membership determines the integer floor modulo 2M.
   The existing exact nested-root identities identify these floors with
   actual iterates once the even-source guards hold. Even r_j provide
   precisely those guards. The existing expansion threshold proves every
   inequality in (4.1). Positive parameter density and strict increase give
   infinitely many distinct starts above every prescribed bound.

## Formal source map

- [FourierBoxCounting.lean](../../formal/BTCalculus/FourierBoxCounting.lean):
  empirical measures, weak convergence, half-open arcs and null frontiers,
  and tendsto_fract_box_count.
- [PowerBoxCounting.lean](../../formal/BTCalculus/PowerBoxCounting.lean):
  power-box frequency, finite changes, exact cutoffs, strict increase,
  tendsto_powerStarts_card, and eventually_powerStarts_interval.
- [PaperECorollaries.lean](../../formal/Problems/Juggler/PaperECorollaries.lean):
  return and signature frequencies, their thresholded forms, actual orbit
  properties, the exact sparse-start asymptotic, relative intervals,
  and signature_returns_infinite.

The separate [audit](../../formal/AxiomCheckPaperECorollaries.lean) covers
all 32 public theorems in these modules; its saved expected output is
[AxiomCheckPaperECorollaries.expected](../../formal/AxiomCheckPaperECorollaries.expected).
The paper's selected audit grows from 37 to 49 declarations.
Only propext, Classical.choice, and Quot.sound are permitted dependencies.

## Scope and decision

**PROMOTE** Corollaries 4.2 and 4.3. They require no new analytic hypothesis.
The counting constant concerns a sparse perfect-power family, while the
residue density is measured in its parameter t. All word lengths, moduli,
residues, and relative-interval widths are fixed before taking a limit.

No first-witness bound, effective discrepancy, shrinking-target estimate,
growing-parameter statement, or orbit-concatenation theorem is proved.
No actual cycle or divergent orbit follows. The closed denominator-coupling
attack remains closed. Equidistribution is classical; specialist priority
review is needed before claiming external novelty for these consequences.
Stop at the two authorized corollaries; do not open an effective-bound branch.
