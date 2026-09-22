# Finite differencing with exact overlap correlations

22 September 2026. Classical analytic input, now kernel-checked in
[WeylDifferencing.lean](../../formal/BTCalculus/WeylDifferencing.lean).
This is a formalization milestone, not a new cancellation theorem for
the Juggler map. The corresponding classical inequality appears in
[Jammes, Section 2.2](https://math.univ-cotedazur.fr/~pjammes/publications/diviseurs95.pdf).
The ledger's advisory statement-coverage label remains pending.

## Exact statement

Let z be any complex sequence with |z(n)|<=1 for 0<=n<N. For natural
integers 1<=H<=N define

\[
 S=\sum_{n=0}^{N-1}z(n),\qquad
 T_d=\sum_{n=0}^{N-d-1}z(n+d)\overline{z(n)}.
\]

The theorem `van_der_corput` proves

\[
 |S|^2\le\frac{2N^2}{H}
          +\frac{4N}{H}\sum_{1\le d<H}|T_d|.
 \tag{1}
\]

The sum defining T_d is over exactly N-d terms. There is no periodic
completion and no assumption on cancellation in T_d. The H=1 case
has an empty correlation sum and is included.

## Proof checked by Lean

For 0<=h<H, pad z by zero outside the shifted interval h<=n<h+N:
u_h(n)=z(n-h) on that interval. Sum all rows over 0<=n<N+H.
`sum_pad` proves each row has total S. `pad_overlap` proves that the
inner product of rows h and k, for h<=k, is exactly T_(k-h).
The proof uses a bijection between the intersection interval and
the range of length N-(k-h), including empty intersections.

Cauchy--Schwarz over the N+H columns gives

\[
 H^2|S|^2\le(N+H)\sum_{n=0}^{N+H-1}
                    \left|\sum_{h=0}^{H-1}u_h(n)\right|^2.
\]

Expand each squared norm into real parts of the row inner products.
The diagonal is bounded by N for every row. For each fixed row, the
positive distances to rows on its left and right each inject into
{1,...,H-1}. Nonnegativity of |T_d| therefore bounds the off-diagonal
contribution by twice their complete sum. `column_energy_bound` and
`differencing_energy` give, for all natural N and H,

\[
 H^2|S|^2\le(N+H)H\left(N+2\sum_{1\le d<H}|T_d|\right).
 \tag{2}
\]

When 1<=H<=N, use N+H<=2N and divide by H^2 to obtain (1).
All support, reindexing, conjugation, and positivity steps are proved
in the module; (2) has no derivative or exponential-sum hypothesis.

## Actual exponential phases

Define phase(t)=exp(2*pi*i*t). `phase_norm` and `phase_mul_conj` prove
unit modulus and phase(a)*conj(phase(b))=phase(a-b).
For any real-valued f on natural integers and any natural start a,
`odd_lattice_van_der_corput` specializes (1) to z(n)=phase(f(a+2n)).
Its d-th correlation is exactly

\[
 \sum_{n=0}^{N-d-1}
    e\bigl(f(a+2(n+d))-f(a+2n)\bigr).
\]

If a is odd these are the actual odd source positions. The inequality
also holds when a is even; no parity assumption is needed for the
finite analytic tool itself.

## Boundary of the OOEE application

The [OOEE proof](juggler_ooee_poor_fibre_tail_note.md), equation (16),
uses precisely this inequality. Its source length is O(P^(7/16)),
its differencing range is floor(P^(1/16)), and its written correlation
bound is O(P^(3/8)). Substitution yields the square-sum exponent 13/16,
hence the sum exponent 13/32. These correlation bounds are not supplied
by (1). For fewer than H terms, the trivial bound handles the interval.

The next analytic prerequisites are the first- and second-derivative
tests, carry Fourier approximation, and finite discrepancy bounds.
Their application to the actual phases must then be checked. The
OOEE poor-fibre theorem and the unconditional 5/8 contagion result
remain written proofs awaiting analytic Lean formalization and
independent mathematical review. Termination and escape are unchanged.
