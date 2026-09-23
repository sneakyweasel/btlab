# Subcritical weights: the missing bound at a fixed integer

23 September 2026. **EXACT — HUMAN PROOF** for the conditional implications,
with kernel-checked declarations; advisory statement coverage remains pending.
The eight finite certificates are **COMPUTATIONALLY VERIFIED** in exact
Python arithmetic, not kernel-checked data.

## Problem

Can a family of periodic lower bounds approach the critical rate without
losing too much of its leading constant at one fixed ordinary integer?
This targets the open coefficient count left by
[fixed-class transport](collatz_fibre_lower_transfer.md).

## Exact statement

For sign s in {1,-1}, let C_d^s=L_s^d 1 be the complete all-source inverse
coefficient. A level-r weight h on residues modulo 3^r is extended periodically.
The complete transfer is

\[
 (L_s h)(a)=\sum_{\substack{e\ge1\\3\mid 2^e a-s}}
       \frac3{2^e}h\left(\frac{2^e a-s}{3}\bmod3^r\right).
\]

If 0<=h<=1, q>=0, and L_s h>=q h at every refined residue modulo 3^(r+1),
then for every positive integer a and depth d,

\[
 C_d^s(a)\ge q^d h(a\bmod3^r).                       \tag{1}
\]

Now let h_i have levels r_i and rates 0<=q_i<1, with q_i tending to one.
Suppose all satisfy the preceding transfer inequality and normalization.
At a single fixed positive root a, it suffices that one constant c>0 satisfies

\[
 h_i(a\bmod3^{r_i})\ge c(1-q_i)\qquad\hbox{for every }i.       \tag{2}
\]

Then sum_d C_d^s(a) diverges. Neither a limiting family nor (2) is constructed
here. The theorem does not require a uniform lower bound over all unit roots.
There is no requirement on how densely the rates approach one.

For a positive odd nonperiodic root, the existing
[unit comparison](collatz_fibre_unit_comparison.md) and actual-mass results
turn this conditional coefficient divergence into divergence of the sum of
reciprocals of its distinct odd ancestors. This does not by itself exclude
a forward fate or give a Juggler pressure estimate.

## Current literature

The inverse recurrence and the Syracuse cell problem are **KNOWN**;
`tao-2019-almost-all-collatz` and Tao's
[2020 inverse-density note](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/)
are the primary references. Subexponential normalized-cell decay, even if
proved, need not make a depth series nonsummable.

The newly located preprint
[`nikpour-rabbani-2026-certified-density`](../../literature/nikpour-rabbani-2026-certified-density.json)
was posted on SSRN on 11 August 2026. Its
[primary abstract](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7239062)
claims a certified ancestor-count exponent 0.914947 and the smallest-atom
bound c_n >> (3t)^(-n), with t=10449/10000. **Only the abstract and metadata
were accessible; the paper and certificate have not been independently
checked.** These are attributed claims, not new verified inputs here.

Even accepting that advertised atom estimate, multiplying by 3^n gives a
lower bound proportional to t^(-n), a summable geometric sequence. It does
not discharge our divergence premise. Our complete-transfer calculation
below is separate; no equality with the authors' full Krasikov–Lagarias
operator is asserted without reading its definitions. Positivity and the
geometric-series limiting argument are standard methods; no priority is claimed.

## Branch budget

- **Target:** can near-critical coefficient lower bounds retain enough of their leading constants to force divergence?
- **Novelty hypothesis:** a controlled family may succeed where every individual exponential bound is summable.
- **Falsifier:** the leading constants collapse too quickly relative to the decay rates.
- **Already killed by?:** critical finite periodic reproduction is closed; strictly subcritical families are not covered by that obstruction.
- **Existing machinery:** complete signed transfer, exact geometric exponent sums and actual predecessor identities.
- **Maximum Phase-0 scope:** levels 1–4 only, exact certificate checks and a Lean proof of the limiting criterion.
- **Promotion criterion:** a proved family with rates tending to one and sufficient control of the leading constants.
- **Stop criterion:** park the route if only finitely many certificates and a conditional criterion are obtained.

## Balanced-ternary formulation

Each h_i is a finite ternary table. Balanced digits give another notation for
its classes. The relevant distinction is between evaluating the table at a
fixed integer's successive residues and taking its minimum over all residues.

## Why BT may be relevant

The finite tables expose the loss under each additional ternary digit.
Changing the digit convention supplies no lower estimate by itself.

## Candidate operations / invariants

Normalize max h=1 and set h=0 on multiples of three. For M=3^r and P=2M,
the congruence 2^P=1 modulo 3M folds all positive exponents into one period.
The denominator is D=2^P-1. At each unit target a modulo 3M the integer row
has coefficient 3*2^(P-e) at child (2^e*a-s)/3 modulo M, for every admissible
e in 1..P. Thus each infinite transfer inequality has an exact integer check.
Targets divisible by three have no admissible exponent and both sides vanish.

The candidate search applies the minimum of the three refined rows above
each coarse class, normalizes the image, and damps the update by averaging.
Floating arithmetic only proposes weights. Rounding weights to integer
scale 10^9 is followed by an exact worst-row calculation and downward rounding
of the rate. No optimality or spectral-radius claim is made.

The quantity relevant to (2) is h_i(a)/(1-q_i), not q_i alone. A uniform
minimum over every unit residue is stronger than the fixed-root requirement.

## Experiments

Run `python tools/lab.py run research.collatz.fibre_critical_minorants`.
The probe is hard-capped at both signs and levels one through four, with
20,000 candidate iterations per case. Its saved
[certificate data](../../data/research/collatz/fibre_critical_minorants.json)
include integer weights, exact rational rates, integer slacks, global minimum
weights, and the separate root values at plus 7 and minus 47.

The [ten controls](../../tests/research/collatz/test_fibre_critical_minorants.py)
check every refined unit residue at every saved level. An independent
implementation constructs ordinary positive odd children, verifies the period,
and sums its infinite geometric repetitions using rational arithmetic.
An overlarge rate is rejected in every case. Hand controls prove that the
level-one weights (0,1,2), or (0,2,1) for minus, accept the exact rate 2/7
with zero slack and reject 13/45. Nonzero weight at a nonunit is rejected.

## Conjectures

No new registered conjecture. Existence of a family satisfying both the limit
and (2) remains an explicit research question, not an inference from four levels.

## Counterexamples

Rates approaching one are insufficient without control of the leading
constants: for 0<epsilon<=1, the summable sequence f_d=1/(d+1)^2 satisfies
f_d >= (epsilon^2/4)*(1-epsilon)^d. Indeed, for d>=1,
(d+1)^2*(1-epsilon)^d <= 4*d^2*exp(-epsilon*d) <= 4/epsilon^2;
d=0 is immediate. Thus even arbitrarily good exponential rates can coexist
with summability when their prefactors are too small. This elementary
sequence is an explanatory example, not a signed Collatz trajectory.

## Formalization

[FibreMinorants.lean](../../formal/Problems/Collatz/FibreMinorants.lean)
proves `coarse_geometric_lower` and `coarse_not_summable_of_weights` for both
signs. The first uses the complete operator and actual positive children.
The second retains the family, convergence and fixed-root lower bound as
explicit hypotheses. Neither theorem treats a finite table as an asymptotic
family. The exact Python certificate rows have not been imported into Lean.

The executable [axiom audit](../../formal/AxiomCheckCollatzMinorants.lean)
and its [expected output](../../formal/AxiomCheckCollatzMinorants.expected)
cover both public theorems. Independent review and advisory statement
coverage remain pending; no external statement request is made in this phase.

The active build passes all 9,026 jobs. Both audits report only propext,
Classical.choice and Quot.sound, and the style gate has zero new violations.
All ten certificate controls and fourteen selected existing fibre controls
pass. This is validation of the stated implications and finite records,
not evidence discharging the family hypothesis.

## Results

Both signs give the following certified rates and normalized global minima.
The last two columns separately evaluate the normalized weights at fixed roots.
Displayed decimals are rounded; the saved file contains exact rational data.

| Level | Certified q | Global minimum h | Plus h(7) | Minus h(47) |
|---|---:|---:|---:|---:|
| 1 | 0.285714285 | 0.500000000 | 0.500000000 | 0.500000000 |
| 2 | 0.575889816 | 0.125000000 | 0.125000000 | 0.125000000 |
| 3 | 0.713279690 | 0.057352407 | 0.070241187 | 0.070241187 |
| 4 | 0.771500620 | 0.030343229 | 0.070209099 | 0.036408891 |

The global-minimum ratio h_min/(1-q) decreases from about 0.700 to 0.133.
At level four the root-specific ratios are about 0.307 for plus 7 and 0.159
for minus 47. These finitely many positive ratios prove no asymptotic bound.
The equality of the signs' rates does not establish transfer of fixed-integer
claims between signs; residue reflection moves the evaluated root.

Here is the limiting argument. If sum_d C_d(a) were finite, for every depth D
its tail would satisfy, by (1) and (2),

\[
 \sum_{d\ge D} C_d(a)
 \ge c(1-q_i)\sum_{d\ge D}q_i^d
 =c q_i^D.
\]

For fixed D, let i tend to infinity. Every tail would be at least c>0,
contradicting convergence. No exchange of an infinite sum with a limit is
needed. The unresolved work is constructing the arithmetic family, not this
analytic implication.

## Open questions

Can the actual signed inverse recurrence produce q_i tending to one and
normalized periodic subsolutions h_i with h_i(a)/(1-q_i) bounded below at
one fixed nonperiodic positive odd unit root a?

## Decision

**PARK** the finite-certificate route at its stated four-level budget.
Retain the exact certificates and conditional Lean criterion. The next best
question is the fixed-root family estimate in the preceding paragraph;
larger finite tables alone do not answer it. No coefficient divergence,
Juggler pressure bound, termination or infinite escape has been established.

The subsequent [block-weight audit](collatz_fibre_block_weights.md) proves
that the natural geometric sum of generations, with its rate certified by
the block minimum, loses the required normalized root prefactor. It also
proves an all-depth linear upper bound at each nonperiodic positive odd root.
The general family question above remains open.

## Publication assessment

Status: `STRUCTURAL`. Standard comparison and limiting arguments, with a
bounded exact computation and an explicit unresolved arithmetic premise.
No manuscript or publication claim is changed.
