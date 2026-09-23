# Uniform affine loss for negative Collatz generations

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Exact statement

Let S(n)=(3n-1)/2^v2(3n-1) on positive odd integers, and let
K_d^-=L_-^d 1_units be the complete coefficient from
[FibreDistortion.lean](../../formal/Problems/Collatz/FibreDistortion.lean).
There is one absolute real C>0 such that, for every positive odd a satisfying
S^j(a)!=a for every j>=1, and every d>=0,

\[
 \sum_{\substack{n\ge1,\ n\text{ odd},\ 3\nmid n\\S^d(n)=a}}\frac1n
 \ \ge\ \frac{K_d^-(a)}{Ca}.
\]

Consequently, divergence of the **unweighted** series sum_d K_d^-(a)
implies divergence of the ordinary reciprocal series over all actual
positive odd unit ancestors of a. The divergence premise remains **OPEN**.
The same C works for every source, target and depth. Preperiodic targets
are included; periodic targets are excluded.

This strengthens the [sixth-root allowance](collatz_negative_generation_mass_lean_note.md).
Both signs now have the same sufficient arithmetic premise, divergence of
their respective complete coefficient series at a nonperiodic target.
There is no transfer of divergence between signs, and no termination theorem.

## Finite-path packing

For either shortcut map T_s(n)=n/2 on even inputs and (3n+s)/2 on odd
inputs, let o_k(n) count odd source states in the first k shortcut steps.
The exact binary-residue moment is sum_(0<=n<2^k) 2^o_k(n)=3^k.
The branches at sources 2n and 2n+1 have successors n and 3n+b_s,
where b_+=2 and b_-=1. Multiplication by three permutes binary residues,
so the moment multiplies by three at each depth. This uses no assumption
of independence on a selected orbit.

The envelope T_s^k(n)<2*3^o_k(n) for n<2^k and a split at o_(5m)=3m
give 8^m|A|<=2*216^m+243^m for a finite set A in [0,32^m) on which
T_s^(5m) is injective. For a finite nonrepeating path of length N,
this injectivity holds on its first max(N-5m,0) states. Removing the
last 5m states proves the uniform finite-path estimate

\[
 8^m|A|\le2\cdot216^m+243^m+8^m(5m).
\]

The final-window term is essential. The negative shortcut prefix 3,4,2
has distinct states and a nonperiodic endpoint, but its three third
iterates all equal the later fixed point 1. Injectivity on the entire
future of a preperiodic path would be false.

## Uniform reciprocal and affine bounds

In the shell [32^m,32^(m+1)), reciprocal mass is bounded by

\[
 b_m=54(27/32)^m+(243/8)(243/256)^m+5(m+1)(1/32)^m.
\]

All three series converge. Put B=sum_(m>=0) b_m and C=exp(B).
Every positive nonrepeating finite shortcut path has reciprocal mass
at most B. The constants are deliberately coarse.

The actual acceleration correspondence is proved: the odd part of
T_-^k(n) equals S^o_k(n) applied to the odd part of n. A positive
shortcut return from an odd target therefore gives an accelerated return.
Accelerated nonperiodicity ensures nonrepetition of every finite shortcut
path ending there, and the accelerated sources lie on that shortcut path.

For x>=1, exp(-1/x)<=1-1/(3x). Thus an actual negative path to a
nonperiodic target has affine product at least exp(-B)=1/C. The existing
exact height and complete coefficient/path-sum identities give the
generation inequality. Disjoint generations allow summation over depth.
No target mixing or finiteness of the ancestor mass is assumed.

## Proof map and attribution

- [SignedOrbitPacking.lean](../../formal/Problems/Collatz/SignedOrbitPacking.lean):
  `parity_moment`, `packing_bound`, `finite_path_packing`,
  `shellBudget_summable`, `finite_path_reciprocal`.
- [UniformFibreDistortion.lean](../../formal/Problems/Collatz/UniformFibreDistortion.lean):
  actual acceleration, `path_reciprocal_bound`, `pathLoss_lower`,
  `pathCoefficient_le`, `kernel_mass_le`, `ancestorMass_eq_top`,
  `ancestor_reciprocals_not_summable`.
- [Public audit](../../formal/AxiomCheckCollatzUniformDistortion.lean)
  and [saved dependencies](../../formal/AxiomCheckCollatzUniformDistortion.expected).

Packing is a known method. The five-step split and constants follow
M. Sharpe's MIT-licensed
[OrbitPacking.lean](https://github.com/msharpe248/collatz/blob/main/lean/Collatz/OrbitPacking.lean),
read on 23 September 2026. The signed moment, finite-path correction and
application to the complete negative ancestor operator are proved here.
The [license record](../../literature/licenses/msharpe248-collatz-MIT.txt)
retains attribution for adapted portions. No literature priority is claimed.

The [Juggler transfer audit](../problems/juggler_collatz_bridge.md) is unchanged:
Juggler lacks this binary-residue count on its integer sources. Its signed
orbit code does not transfer packing, the constant affine allowance or
coefficient divergence. Actual growing-depth pressure remains open at r-eta>3/8.

## Validation

The active Juggler/Collatz build passes all 9,018 jobs. The public audit
covers all 21 new theorems and reports only propext, Classical.choice and
Quot.sound. The style gate reports no new violations. All 58 selected
mathematical, ledger, declaration, documentation-link and generated-record
checks pass. Exact controls cover both signs, preperiodic future mergers,
the acceleration clock and the failure of time-indexed reciprocal bounds
at a periodic root. Advisory statement coverage remains pending; no external
request was sent.

The isolated tracked-source snapshot passes the other 57 selected checks.
Its global link gate finds four older journal links to ignored scratch files
under tmp; these targets exist in the shared worktree but are absent from Git.
All links introduced in this phase resolve. The older journal entries and
their unrelated staged edits are preserved in the scoped commit.

## Decision

**PROMOTE** the depth-independent negative comparison and complete unweighted
generation-series criterion. The remaining arithmetic target has the same
form for both signs: a divergent coefficient series at one fixed nonperiodic
unit in each full fate class. A positive constant lower bound on coefficient
sums over infinitely many disjoint dyadic depth blocks would suffice for
either sign. That estimate and series divergence remain open.
This bounded phase stops without opening another counting campaign.
