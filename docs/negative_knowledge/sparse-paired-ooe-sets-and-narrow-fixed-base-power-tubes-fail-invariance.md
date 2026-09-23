# Sparse paired OOE sets and narrow fixed-base power tubes fail invariance

[OOE escape families, Sections 5--7](../problems/juggler_ooe_escape_families.md)
records the attempted sparse invariant construction from a fixed seed.
No such collection was found. A subset of {4t^2±1: t odd} that contains
both signs at a parameter s>=5 cannot be A-invariant: the two return
values differ by more than two but less than the spacing between distinct
template parameters. This applies to arbitrarily sparse paired selections,
and does not exclude a one-sided selection. Both tested seeds 1599840003
and 1599840005 return outside the template and then have even O images;
each completes one OOE block only. Their later actual fates were not tested.

For any fixed real base c>1 and logarithmic tube width 0<=epsilon<1/17,
no infinite prescribed OOE tail can stay within epsilon of integer
log_c exponents. Above the explicit positive-exponent threshold, the
endpoint error forces 8e=9d and v2(e)+3=v2(d). Thus a finite k-step
segment in those tubes satisfies 3k<=v2(d_start). Arbitrarily sparse
exponents and nonpolynomial updates do not avoid the restriction.
Fixed additive errors from fixed-base powers, or relative errors tending
to zero, are included. Wider tubes or varying bases are not excluded.

Exact inverse cells and arbitrarily deep moving-seed constructions do
not supply a common ordinary integer. A uniform finite initial seed set
surviving every depth would suffice, but has not been proved. The nested
odd congruence classes x=(4^n-1)/3 mod 4^n illustrate that compatible
finite witnesses can have no common nonnegative integer. This is a
compactness countermodel, not an actual OOE counterexample. The general
sparse invariant-set construction remains PARK, with no escape proof.
Members: ooe_escape_families, J-ooe-escape-sparse-pair-obstruction,
J-ooe-escape-power-tube-obstruction.

