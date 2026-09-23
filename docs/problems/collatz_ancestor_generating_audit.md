# Ancestor generating functions retain the source term and the harmonic-mass problem

23 September 2026. **REPARAMETERIZATION**: known pullback and weighted-series
identities, with a shared kernel-checked source-equation interface.

## Problem

Can published generating-function rigidity supply the missing fixed-root
harmonic lower bound, and thereby help count the varying inverse words
left open by the [fixed-block theorem](collatz_fibre_word_tail.md)?

## Exact statement

For a self-map T and a nonperiodic target a, put

    b_a(n)=1 if T^d(n)=a for some d>=0, and 0 otherwise.

With coefficient pullback F(b)(n)=b(T(n)), the correct equation is

\[
 b_a(n)=b_a(T(n))+1_{n=a}.
\]

In particular b_a is not a fixed point. It is the least nonnegative real
solution of this source equation. For every nonnegative weight w,

\[
 \exists g\ge0:\quad g-g\circ T=1_{\{a\}},\quad
 \sum_n w(n)g(n)^2<\infty
 \quad\Longleftrightarrow\quad
 \sum_n w(n)b_a(n)<\infty.
\]

The result applies to either signed shortcut, either odd accelerated map
on its invariant positive odd domain, or Juggler as self-maps. It supplies
no dynamical estimate for any of them. The analytic comparisons below use
the signed shortcut maps on positive integers.

For positive integer ancestors and w(n)=1/(n+1), the right side is
equivalent to reciprocal summability, since
1/(2n)<=1/(n+1)<=1/n for n>=1. Thus excluding nonnegative Bergman solutions
of the source equation is precisely the harmonic-mass problem in a new
formulation, not an independently weaker arithmetic premise.

## Current literature

- `neklyudov-2021-collatz-functional-analysis`: [Section 4](https://arxiv.org/html/2106.11859#S4), Proposition 4.2 and the proof of Theorem 4.4 establish expansiveness of the coefficient pullback on the Hardy space H^2 and that its H^2 fixed points are constants. Theorem 4.5 records the resolvent viewpoint. The paper's pushforward operator is different; its fixed points cannot be substituted for pullback fixed points.
- `bell-lagarias-2015-inverse-orbit-natural-boundaries`: [Theorems 1.2 and 1.3](https://arxiv.org/html/1408.6884#S1.SS1) give natural boundaries for the plus inverse-orbit generating function outside the possible exceptions 1,2,4,8, and for every positive minus target. This concerns analytic continuation, not reciprocal mass.

The source equation and the norm distinction are **KNOWN** elementary
consequences, reproduced here to audit applicability. No mathematical
priority or new complex-analytic theorem is claimed.

## Branch budget

- **Target:** can these generating-function results supply the harmonic lower bound?
- **Novelty hypothesis:** analytic rigidity might control a fixed integer's mass.
- **Falsifier:** a norm mismatch, a missing source term, or an actual finite-mass counterexample.
- **Already killed by?:** the known signed dyadic ray is a candidate counterexample; this analytic use was unaudited.
- **Existing machinery:** shared inverse-generation Lean lemmas and the signed backward-ray theorem.
- **Maximum Phase-0 scope:** the source equation and the two primary papers above.
- **Promotion criterion:** an applicable estimate forcing harmonic divergence at unit roots.
- **Stop criterion:** close the shortcut if it only reformulates the open lower bound.

## Balanced-ternary formulation

None is needed. The coefficient sequence uses ordinary integer ancestors;
their membership cannot be replaced by residue-class membership.

## Why BT may be relevant

The shared inverse-generation module already distinguishes a fixed target
from a full fate class. That distinction, rather than digit notation, is
what the source term records.

## Candidate operations / invariants

If n!=a, reaching a from n is equivalent to reaching a from T(n). At n=a,
depth zero contributes one and no positive iterate returns. This proves
the source equation. For any nonnegative solution g, the equation gives
g(a)>=1 and g(n)>=g(T(n)); following a path to a gives g(n)>=b_a(n).
Since b_a is zero or one, b_a(n)<=g(n)^2. Multiplying by w and summing
proves the forward implication in the displayed equivalence; g=b_a proves
the reverse implication. These coefficient statements are in Lean.

For G(z)=sum b_n*z^n, orthogonality on circles and integration in radius give

\[
 \|G\|_{H^2}^2=\sum_n|b_n|^2,\qquad
 \|G\|_{A^2}^2=\sum_n\frac{|b_n|^2}{n+1},
\]

where A^2 uses normalized area measure. For an indicator, the first norm
counts ancestors; the second measures their harmonic mass up to a factor
two. The analytic norm identifications here are written standard proofs,
not additional Lean declarations.

## Experiments

No census or floating-point experiment. The executable Lean audit checks
two exact unit-target controls: T_plus(n)=7 iff n=14, and T_minus(n)=47
iff n=94. Thus the respective coefficient pullbacks send z^7 to z^14
and z^47 to z^94. Their Bergman square norms decrease from 1/8 to 1/15,
and from 1/48 to 1/95. The rational inequalities are also kernel-checked.

## Conjectures

No new conjecture. Fixed-root harmonic divergence and the stronger
dyadic-depth lower target remain open at nonperiodic unit roots.

## Counterexamples

The unit monomials above refute Bergman expansiveness. They do not refute
the published Hardy statement or the existence of some other analytic estimate.

For both signed shortcut maps, the exact ancestor set of 3 is
{3*2^k:k>=0}: every multiple of three has its double as unique predecessor,
and iterated halving reaches 3 from every ray point. Its reciprocal mass
is 2/3 by the already checked
[BackwardMass.lean](../../formal/Problems/Collatz/BackwardMass.lean).
The generating function sum z^(3*2^k) has a natural boundary by either
applicable Bell-Lagarias theorem, despite this finite harmonic mass.
This is an actual signed-map example, not an artificial coefficient model.
Its root is divisible by three, so it does not refute the unit-root target.

## Formalization

[PreimageGenerations.lean](../../formal/BTCalculus/PreimageGenerations.lean)
now includes `ancestorIndicator`, `ancestorIndicator_eq`,
`ancestorIndicator_not_fixed`, `ancestorIndicator_le_of_source_eq`, and
`exists_summable_source_iff`. The last theorem uses ordinary real Summable
series and arbitrary nonnegative weights, without assuming convergence
before the equivalence.

The [executed audit](../../formal/AxiomCheckAncestorSource.lean) and
[saved output](../../formal/AxiomCheckAncestorSource.expected) cover all
four new theorems and the exact unit-preimage controls. The operator-space
identifications and the cited natural-boundary theorems remain written
literature inputs. No external advisory request is made.

The active Lean graph passes all 9,032 build jobs; the four new theorems
use only propext, Classical.choice and Quot.sound. The existing seventeen
generation-mass audit outputs remain unchanged. The final shared source
also compiles after a docstring clarification. The style gate reports no
new violations and all five new declaration references resolve. All 68
selected mathematical, ledger, documentation and Paper E release checks
pass. The release tests were rerun in a fresh workspace temporary directory
after Windows denied access to pytest's default temporary directory.

## Results

The Hardy fixed-point theorem applies neither to the relevant norm nor to
the source equation. Natural boundaries coexist with finite harmonic mass
even for actual signed inverse orbits. The nonnegative finite-energy
source criterion is exactly equivalent to weighted ancestor summability.
No lower count, coefficient divergence, Juggler pressure or termination
claim is obtained from this translation.

## Open questions

What arithmetic lower estimate for genuinely varying actual words can
establish the fixed-root dyadic-depth bound? The generating-function
language does not yet supply one. Juggler's actual stopped-pressure rate
r-eta>3/8 is still a separate open input.

## Decision

**CLOSE** treating these published analytic statements or the source
reformulation as an automatic harmonic-mass lower bound. Retain the exact
shared source interface and literature distinction. The best next question
remains the direct depth-averaged actual-word estimate above. Stop this
bounded reading and formalization phase; no new analytic branch is opened.

## Publication assessment

Status: `ARCHIVED`. A checked applicability audit of known machinery,
not a new research theorem or a manuscript revision.
