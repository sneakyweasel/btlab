# Polynomial affine loss for actual negative Collatz ancestors

23 September 2026. A kernel-checked extension of the
[positive generation-series criterion](collatz_generation_mass_lean_note.md).
Independent review and advisory statement coverage remain pending. No
literature priority is claimed.

**Strengthening, later on 23 September:** the
[uniform continuation](collatz_uniform_generation_mass_lean_note.md) replaces
the sixth-root allowance by one absolute constant, using signed finite-path
packing. The earlier theorem below remains valid. Unweighted coefficient
divergence suffices on the minus side too, and remains open.

## Exact statements

Let S(n)=(3n-1)/2^v2(3n-1) on positive odd integers. Let
K_d^-=L_-^d 1_units be the existing complete coefficient operator from
[FibreMass.lean](../../formal/Problems/Collatz/FibreMass.lean). For a positive
odd target a with S^j(a)!=a for every j>=1, and every d>=0,

\[
 \sum_{\substack{n\ge1,\ n\text{ odd},\ 3\nmid n\\S^d(n)=a}}\frac1n
 \ \ge\ \frac{K_d^-(a)}{a(d+1)^{1/6}}.
\]

Consequently,

\[
 \sum_{d\ge0}\frac{K_d^-(a)}{(d+1)^{1/6}}=\infty
 \quad\Longrightarrow\quad
 \sum_{\substack{n\ge1,\ n\text{ odd},\ 3\nmid n\\
                   \exists d\ge0:\ S^d(n)=a}}\frac1n=\infty.
\]

The series-divergence premise remains **OPEN**. The exponent 1/6 is a
proved allowance, with constant one, not a claim of optimality. A target
may be preperiodic; only periodic targets are excluded.

## Why the loss is polynomial

For an actual path x_0=n,...,x_d=a, write k_j=v2(3*x_j-1) and
P=product_(0<=j<d)(3/2^k_j). The exact identity is

\[
 a=nP\prod_{j=0}^{d-1}\left(1-\frac1{3x_j}\right).
\]

No two states before the target can coincide: a repetition would make
the target periodic. None can be 1 or 3, since either reaches the fixed
point 1 within one step. Thus the d source states are distinct odd
integers at least five.

Put b_j=floor(x_j/2). These are distinct integers at least two.
Bernoulli's inequality gives

\[
 \left(1-\frac1{3x_j}\right)^6
 \ge 1-\frac2{x_j}
 \ge \frac{b_j-1}{b_j}.
\]

In increasing order, the i-th b is at least i+1, for i=1,...,d.
The function (b-1)/b is increasing, so

\[
 \left[\prod_j\left(1-\frac1{3x_j}\right)\right]^6
 \ge \prod_{i=1}^d\frac{i}{i+1}=\frac1{d+1}.
\]

Substitution in the exact height identity proves
1/n>=P/(a*(d+1)^(1/6)). This accounts for every affine correction;
there is no distribution or independence hypothesis on the path.

## Complete operator and counting

[FibreDistortion.lean](../../formal/Problems/Collatz/FibreDistortion.lean)
uses the existing negative odd-return map and actual predecessor
bijection. `kernel_eq_path_sum` identifies the complete residue operator
with the sum of homogeneous coefficients over actual integer paths,
including every admissible halving exponent. Each fixed-depth coefficient
recurrence converges by the existing geometric domination argument.

`pathLoss_pow_lower` and `pathCoefficient_le` prove the path inequality.
`kernel_mass_le` sums it over the full generation, allowing infinite
actual mass from the outset. The generic disjoint-generation theorem in
`BTCalculus.PreimageGenerations` then permits summation over all depths.
`ancestor_reciprocals_not_summable` states the conclusion using an ordinary
real reciprocal series indexed by natural integers.

Nonperiodicity cannot simply be removed. At the periodic root 1, the
repeated inverse path 1 has coefficient (3/2)^d and correction (2/3)^d,
which eventually violates the polynomial bound. Its repetitions also
prevent counting different generations as disjoint sets.

## Research consequence

The elementary minus affine comparison still reverses the plus comparison.
The new result controls its accumulation on nonperiodic paths. The two
explicit sufficient coefficient-series targets are now

| Map | Sufficient divergent series at a nonperiodic target |
|---|---|
| 3n+1 | sum_d K_d^+(a) |
| 3n-1 | sum_d K_d^-(a)/(d+1)^(1/6) |

Neither series is proved divergent here. Harmonic divergence itself
does not supply a quantitative fate-growth theorem or a termination
contradiction. The finite periodic weight obstruction is unchanged: it
concerns uniform fixed-depth reproduction, while this result permits
a polynomial loss and assumes nonperiodicity.

Juggler's actual growing-depth pressure estimate remains open at
r-eta>3/8. The proposed all-odd count was audited against the existing
Paper B transfer: two predecessor weights are covered, but the next nested
phase is not. No new Juggler counting bound is claimed from that audit.

## Validation

The complete public-theorem audit is
[AxiomCheckCollatzDistortion.lean](../../formal/AxiomCheckCollatzDistortion.lean),
with saved [dependency output](../../formal/AxiomCheckCollatzDistortion.expected).
The [exact regression checks](../../tests/research/collatz/test_fibre_distortion.py)
independently traverse finite negative-map ancestor generations at six
certified nonperiodic roots, compare exact rational height ratios and
coefficients, and include periodic-root and wrong-sign controls.
All 24 public theorems use only propext, Classical.choice and Quot.sound.
The active Juggler/Collatz build passes 9,011 jobs. All eight new exact
regressions pass, including the periodic and sign controls. The style
gate reports no new violations. Ledger rendering, branch-index consistency
and Paper E release consistency pass.

The combined targeted run has 47 passes and three failures from two
concurrently deleted older ledger targets: `docs/literature_comparison.md`
and `formal/Representation/Words.lean`. No failure concerns the new path,
generation, declaration-resolution, generated-record or documentation-link
checks. Those unrelated deletions are preserved. The scoped commit is
checked separately against its own source tree and generated records.
All 49 selected mathematical, ledger, declaration and generated-artifact
tests pass on that isolated source tree. Its unchanged ledger rows are
checked against the base revision, and all named source paths resolve.

## Decision

**PROMOTE** the polynomial negative affine bound and complete conditional
generation-series implication. This bounded phase stops here. Arithmetic
divergence of the coefficient series, Juggler pressure, termination and
infinite escape remain open.
