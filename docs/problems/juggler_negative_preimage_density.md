# Signed Collatz preimage density: residue symmetry needs a height argument

Status: **PARK** (22 September 2026). The former assertion that the
Krasikov–Lagarias exponent transfers by residue relabelling alone is
withdrawn as unproved. The eventual 3n-1 bound is not refuted. A follow-up
now bounds height corrections through any finite family of expanding
inverse blocks. A second follow-up proves actual signed tree-count
inequalities on a strict grid for nonperiodic roots at least 4096, with a
decreasing induction measure. Closing the root domain and supplying a
growth certificate remain open.

Branch of the [Collatz bridge](juggler_collatz_bridge.md). The exact
predecessor comparison is now kernel-checked in
[PreimageScale.lean](../../formal/Problems/Collatz/PreimageScale.lean).

## Problem

Does the known positive 3x+1 preimage-count exponent also follow for
the 3n-1 shortcut map from the residue program already implemented here?
The previous answer conflated its residue symmetry with validity of
the associated inequalities for actual height-truncated inverse trees.

## Exact statement

For g(n)=n/2 at even n and (3n-1)/2 at odd n, the proposed conclusion
is that every positive target a not divisible by 3 has at least
x^0.84 positive ancestors below x for all sufficiently large x.
This remains an unproved claim in this branch.

What is proved is the sign-dependent scale comparison. For a=1 mod 3,
the odd predecessor c=(2a+1)/3 satisfies

\[
c>2a/3,\qquad
\frac{x}{c}=\frac{(x/a)(3/2)}{1+1/(2a)}.
\]

For the plus map, a=2 mod 3 gives c=(2a-1)/3<2a/3. Thus the nominal
child cutoff (x/a)(3/2)c is below x for plus, but above x for minus.
The residue classes transpose; this Archimedean inequality reverses.

## Current literature

[Krasikov–Lagarias, 2003](https://arxiv.org/abs/math/0205002) prove the
x^0.84 bound for positive targets under 3x+1. Section 2 defines the
height-truncated count and its residue-class infimum. Proposition 2.1
supplies the difference inequalities; Theorem 2.2 uses their validity,
positivity, and monotonicity. Theorem 6.1 supplies the numerical exponent.
The published theorem does not directly cover positive 3n-1 targets.

Their Sections 3–5 remove advanced terms and transfer feasible solutions
to a derived system. Invoking that machinery for minus still requires
a proof that the actual minus-tree counting functions satisfy suitable
inequalities. Equality of two formal programs is not that proof.

The [published 2003 version](https://www.impan.pl/shop/en/publication/transaction/download/product/81918)
also explicitly restricts Theorem 6.1 to positive targets. The older
[Applegate–Lagarias Part II preprint](https://dept.math.lsa.umich.edu/~lagarias/doc/applegateII.pdf)
states its 0.81 result in an integer-wide introduction, but its displayed
normalization (2.2) uses 2^y a, while (2.1) counts absolute heights.
That broad statement alone does not reconstruct the signed height step
needed here. We do not use it to certify the stronger 0.84 transfer.

**A different proof route.** M. Sharpe's
[KLGrid.lean](https://github.com/msharpe248/collatz/blob/main/lean/Collatz/KLGrid.lean)
uses a 1/50 grid and induction on 10t+floor(log2(a^498)) for positive
roots. The slight loss in the advanced shift makes this measure decrease;
working with individual roots avoids deletion inside residue minima.
We inspected that proof and its hypotheses, including the root's reaching
8. We did not rebuild or independently audit the external repository's
large density certificates. Its MIT cap table and method are attributed in
our [PreimageGrid.lean](../../formal/Problems/Collatz/PreimageGrid.lean).
The signed inequalities below are locally kernel-checked with their
different cutoff comparison and explicit root threshold.

## Branch budget

- **Target:** audit the scale inequalities behind the recorded transposition.
- **Novelty hypothesis:** residue symmetry omitted a signed height correction.
- **Falsifier:** a uniform justification of the same shifts in the source proof.
- **Already killed by?:** not the backward-mass obstruction, which concerns
  harmonic mass rather than this counting theorem.
- **Existing machinery:** the signed predecessor maps and original paper.
- **Maximum Phase-0 scope:** exact scale comparison, Lean proof, and claim correction.
- **Promotion criterion:** justified transfer or a precise verified missing premise.
- **Stop criterion:** no density conclusion from matching residues or solvers.

Follow-up scope: prove the three actual minus-tree recurrences and a
decreasing natural-number induction measure above a fixed root threshold.
The falsifier is a failed cutoff inclusion or measure decrease. This is
not the closed exact-shift transfer: a strict grid margin is retained.
Promotion requires statements about genuine height-truncated integer
trees. Stop before claiming a density exponent without a closed root
domain and a checked growth certificate.

## Balanced-ternary formulation

Residues modulo 3^k describe integrality of backward branches. They do
not determine the height cutoff. No BT representation change is used.

## Why BT may be relevant

Only through ternary residue bookkeeping. No termination input follows.

## Candidate operations / invariants

Negation sends fertile classes 2 mod 3 to 1 mod 3 and permutes the
mod-9 classes 2,5,8 to 7,4,1. It also transposes the quotient indices
and the three lifts. The existing finite exact checks of this algebra
remain valid. The formal programs attach the same homogeneous shifts
to both signs; the missing premise is their application to actual counts.

## Experiments

`python -m research.juggler_sequence.negative_preimage_density` now
labels the minus outputs as **residue-model exponents**, and records
no established minus-map density exponent. The archived high-k model
values remain historical numerical results, not newly certified bounds.

The independent forward enumeration agrees with the backward BFS:

| Child target | Cutoff | Ancestors with whole path below cutoff |
|---|---:|---:|
| 13 | 103 | 12 |
| 13 | 105 | 13 |

The old wrong-sign regression had never tested its alleged identity:
for a=1 mod 3 its guard `(2*a-1) % 3 == 0` is always false. It now
reports that nonintegrality explicitly. The BFS also returns zero when
its root itself is outside the positive cutoff interval.

The grid checks cover all 50 rounding phases, and independently test
integer roots and capped inverse trees. Two boundary diagnostics are
retained: the grid cutoff itself fails at a=19, while a=4096 has the
smaller odd predecessor 2731. Thus a lower root threshold by itself is
not an invariant domain for a growth induction.

## Conjectures

`J-kl-preimage-density-transposes-to-3n-1` is now **CONJECTURE**.
This status concerns the missing proof here; no claim is made that
the asymptotic conclusion is false or unavailable by another method.

## Counterexamples

Take a=19, c=13, x=103. The copied homogeneous shift gives child
cutoff 4017/38, between 105 and 106. It includes the genuine path
104 -> 52 -> 26 -> 13, which is excluded at cutoff 103.
Also x>=4a, so this is inside the original y>=2 regime.
The target is nonperiodic: 19 -> 28 -> 14 -> 7 -> 10 -> 5 -> 7.
Both facts are kernel-checked.

This refutes the proposed pointwise cutoff inclusion. It does not
refute every possible difference inequality for the residue infima:
additional terms or another normalization might compensate, but that
requires a separate proof. In particular, the counterexample does not
refute an eventual x^0.84 lower bound.

## Formalization

`PreimageScale.lean`, imported by `Problems.lean`, proves the exact
odd predecessor equations for both signs, their opposite comparisons
with 2a/3, the correction factor, and the reversed nominal-budget
inequalities for every positive real cutoff. `excluded_ancestor`
checks the finite path and its location; `nineteen_not_periodic`
checks all positive return times by a finite forward invariant set.
The density exponent and the all-level residue-program isomorphism
are not claimed to be formalized.

The follow-up adds `inverseWord` for the real inverse letters
E(x)=2x and O(x)=(2x+1)/3. `inverseWord_affine` proves
f_w(x)=R_w x+B_w with R_w>0 and B_w>=0. These are formal real
itineraries; actual integer paths still need their branch guards.
`shifted_block_iff`, `shifted_blocks`, and `finite_expanding_shift`
prove the uniform correction below. `internal_prefix_height` also
controls intermediate states. `two_step_preimage` verifies that the
OE example is an actual predecessor at fertile integer targets.
`no_elementary_shift` proves why the same method cannot apply to both
single letters with their original multipliers.

`PreimageGrid.lean` defines the actual positive-integer capped inverse
tree and proves monotonicity, extension along bounded paths, uniqueness
of hitting times at a nonperiodic root, and disjointness of the two
subtrees. `count_four`, `count_odd`, and `count_doubled_odd` prove the
three pointwise recurrences below. `measure_children` proves all three
strict decreases, and `fertile_children` checks the residue selection.
These are bounds on actual counts, not a floating-point residue model.

Validation: full `lake build` passes (9028 jobs). The
[22-declaration audit](../../formal/AxiomCheckCollatzPreimageScale.expected)
uses only `propext`, `Classical.choice`, and `Quot.sound`. The focused
probe tests plus integration and ledger gates give 153 passes and
14 skips. The regenerated probe preserves 366 exact finite tree splits,
and reports 366 nonintegral wrong-sign expressions explicitly.

Grid follow-up validation: full `lake build` passes (9029 jobs), and
the [29-declaration grid audit](../../formal/AxiomCheckCollatzPreimageGrid.expected)
has only standard Lean dependencies. Exact independent checks cover all
rounding phases, actual signed roots, and capped integer subtrees. Focused,
integration, ledger, and registry tests give 162 passes and 14 skips.

## Results

The valid residue algebra is preserved. Its former promotion to a
counting theorem is withdrawn. The exact missing shift in the minus
odd branch is

\[
y+\log_2 3-1-\log_2(1+1/(2a)),
\]

with the same positive correction for the doubled odd branch, whose
nominal shift is y+log_2 3-2. Dropping this correction is unfavorable
to a lower bound. It tends to zero as a grows, but that observation
alone does not control repeated production steps or the infimum over
all targets in a residue class.

### Uniform correction for expanding blocks

For a finite family F of inverse words with every R_w>1, take

\[
K=1+\sum_{w\in F}\frac{B_w}{R_w-1}.
\]

Then B_w<=(R_w-1)K, hence f_w(x)+K<=R_w(x+K). Induction proves
for **every** finite concatenation W of these blocks, with any real x,

\[
f_W(x)+K\le R_W(x+K).
\]

Thus there is no factor growing with the number of blocks. This is
the standard affine-shift argument, now instantiated and kernel-checked
for the signed inverse words; it is not a new density theorem. For x>0
the endpoint is at most R_W x times 1+K/x, regardless of depth.
If an internal prefix u has length at most L and x>=0, the formal proof
also gives

\[
f_{Wu}(x)+1\le 2^L R_W(x+K).
\]

This matters for the whole-path cutoff, not just endpoint height.
For the blocks EE and OE, the maps are 4x and (4x+2)/3, and K=2
already works. The OE bound is equality. For every a=1 mod 3,
2(2a+1)/3 is an integer two-step ancestor of a.

The expansion hypothesis cannot be discarded. A common translation
for E and O individually would require K>=0 and K<=-1 simultaneously.
In particular, the contracting O production in the original residue
system is not covered by this block lemma.

### Actual counting inequalities with a strict grid margin

Let N(a,X) count positive n that reach a with every intervening state at
most X. Put C(t)=2^floor(t/50) r(t mod 50), using the explicit integer
table r in `PreimageGrid.lean`; its first value is 10000. For a>=4096
with a=1 mod 3 and b=(2a+1)/3, the exact comparisons are

\[
12288b\le8193a,\quad
8193C(t+29)\le12288C(t),\quad
16386C(t)\le12288C(t+21).
\]

Consequently, for every nonperiodic such root and all t>=0,

\[
\begin{aligned}
N(a,C(t+100)a)&\ge N(4a,C(t)4a),\\
N(a,C(t+100)a)&\ge N(4a,C(t)4a)+N(b,C(t+129)b),\\
N(a,C(t+100)a)&\ge N(4a,C(t)4a)+N(2b,C(t+79)2b).
\end{aligned}
\]

The first inequality does not need nonperiodicity or the lower root
threshold. To stay in fertile classes, use the second inequality when
a=1 mod 9, the third when a=7 mod 9, and just the first when a=4 mod 9.
The two odd-branch alternatives are not added together.

For M(t,a)=10t+floor(log2(a^498)), the kernel checks

\[
\begin{aligned}
M(t,4a)+4&\le M(t+100,a),\\
M(t+79,2b)+3&\le M(t+100,a),\\
M(t+129,b)+1&\le M(t+100,a).
\end{aligned}
\]

The decisive integer inequality is
2^291 * 8193^498 < 12288^498. It keeps a strict decrease after the
signed offset is included. This gives a viable way to handle the
advanced term without the older elimination/deletion proof.
The number 4096 is an auxiliary root threshold, not a new computational
termination floor for either map.

The known-cycle census means the three known cycles and their fifteen
members; it supplies no exhaustiveness theorem. Existing finite tree
split checks remain computational and must retain their noncycle scope.

## Open questions

The strict-grid route now supplies actual pointwise counting inequalities
and a well-founded measure above 4096. The next question is to construct
a root domain closed under the selected inverse productions, with every
root above that threshold, or supply a justified boundary argument.
Nonperiodicity is inherited by predecessors, but the numerical threshold
is not. A growth certificate must then be checked for these grid shifts
and combined with the induction; the old homogeneous model's output is
not that certificate. The original deletion argument remains unsupported
for the signed functions and is not used by this route.

Even a repaired x^0.84 lower bound would not supply Juggler's required
divergent harmonic-mass estimate or its growing-depth pressure bound.

## Decision

**PARK** the density exponent pending the closed-domain growth induction
and its numerical certificate. The expanding-block lemma and strict-grid
counting recurrences are recorded as proved components. The residue
symmetry is retained; automatic analytic transfer remains closed. No new
cycle exclusion, termination theorem, or computation floor follows, and
neither Paper C nor Paper D requires modification.

## Publication assessment

Working correction and partial repair. Do not present the 3n-1 exponent
as a corollary until the growth induction and certificate are supplied.
