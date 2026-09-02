# Run-type survivors as a continued-fraction lattice

Status: laboratory extract. Date: 31 August 2026.

This records the Diophantine organization of
\(\mathcal E_{\mathrm{run}}(10^6)\), the \(99\) lengths that
survive both the length-only parity \(6/5\) table and the
run-type packing at \(N_0=10^6\), \(L\le 10^5\). It is not a
halt theorem, not a leftover-itinerary census, and not a new finance
identity. Paper A prints the packing as Theorems 4.7--4.8 and
the lattice as Proposition 4.9. The finance writeup is
[juggler_cycle_finance_note.md](juggler_cycle_finance_note.md).
The packing that cuts \(141\) to \(99\) is
[juggler_cycle_budget_opt.md](../problems/juggler_cycle_budget_opt.md).
Loader: `survivor_lengths` in
`src/research/juggler_sequence/cycle_run_extremum.py`.
SHA-256 of the length list:
`9e2098923ccb39933630b116133a3fc2ddaf98ace4eb76dbab9b5ab9f6e604e6`.

## What the \(99\) are

They are the surplus near-convergents of \(\ln 2/\ln 3\) that
still beat packed run-type finance at \(n=10^6+1\). Each has
\(o=o_{\min}(L)\), so \(2^L<3^o\), and both cheap and expensive
valleys: \(o-e>0\) and \(2e-o>0\). First survivor \(L=25781\).
Tightest leftover \(L=55293\) (\(P/\theta\approx 1.012\)).
They are not all equally close to the finance wall:
\(L=50508\) has \(P/\theta\approx 158.7\).

The \(42\) lengths \(56347+1054k\) (\(k=0,\ldots,41\)) are not
a fourth family. They are the continuation of the first family
past the packing cut.

## The lattice — **COMPUTATIONALLY VERIFIED**

Write \(v_*=(25781,16266)\) and \(v_{1054}=(1054,665)\). Then

\[
25781\cdot 665-1054\cdot 16266=1,
\]

so these two vectors are a unimodular basis. Every survivor,
and every one of the \(42\) packing deaths, is

\[
(L,o_{\min})=a\,v_*+b\,v_{1054}.
\]

The only family step is

\[
(L,o_{\min})\mapsto(L+1054,\,o_{\min}+665).
\]

The three affine slices, with table cap \(L\le 10^5\), are

| Family | Coordinates | Count | Lengths |
|---|---|---|---|
| \(F_1\) | \(a=1\), \(b=0,\ldots,28\) | \(29\) | \(25781+1054k\) through \(55293\) |
| \(F_2\) | \(a=2\), \(b=-1,\ldots,45\) | \(47\) | \(50508+1054k\) through \(98992\) |
| \(F_3\) | \(a=3\), \(b=-1,\ldots,21\) | \(23\) | \(76289+1054k\) through \(99477\) |
| packing deaths | \(a=1\), \(b=29,\ldots,70\) | \(42\) | \(56347+1054k\) through \(99561\) |

Seeds:

\[
50508=2\cdot 25781-1054,\qquad
76289=3\cdot 25781-1054=50508+25781.
\]

So \(F_2\) begins at the next principal convergent and \(F_3\)
at the Farey sum of the two previous seeds. The slogan
\(a,b>0\Rightarrow\) contradiction misses the live seeds with
\(b=-1\).

## Exact surplus recurrence — **COMPUTATIONALLY VERIFIED**

Write \(r(L)=3^{o_{\min}(L)}/2^L\) and
\(\rho=3^{665}/2^{1054}\). Then \(\rho>1\) and, within each
family,

\[
r(L+1054)=\rho\,r(L)
\]

as an integer identity (checked in floats to relative error
\(<10^{-13}\)). In the code convention
\(\theta=1-2^L/3^o\),

\[
\theta(L+1054)=\Bigl(1-\frac1\rho\Bigr)+\frac{\theta(L)}{\rho}.
\]

Each step adds about \(4.365\cdot 10^{-5}\) of surplus. That
is why a family walks toward the packed wall as \(b\) grows,
and why \(F_1\) hits it first: at \(L=55293\),
\(P/\theta\approx 1.012\); the next point \(L=56347\) has
\(P/\theta\approx 0.9967\). \(F_2\) and \(F_3\) are
cap-truncated, not packing-truncated.

## Continued-fraction identification — **KNOWN** / **REPARAMETERIZATION**

This is the intermediate-fraction lattice of \(\log 2/\log 3\),
not a new cycle invariant. Principal convergents nearby are

\[
\frac{665}{1054},\quad
\frac{15601}{24727},\quad
\frac{31867}{50508},\quad
\frac{79335}{125743}.
\]

The convergent \(15601/24727\) sits on the deficit side
\(3^{15601}<2^{24727}\), so it never enters
\(\mathcal E_{\mathrm{par}}\). The first surplus intermediate
is

\[
\frac{15601+665}{24727+1054}=\frac{16266}{25781}.
\]

The next principal convergent is the \(F_2\) seed
\(31867/50508\). The finance dossier already named the coarse
form: leftovers are multiples of \(25781\) plus combinations
with earlier convergents. The three APs are that statement,
restricted to surplus intermediates at floor \(10^6\) and
\(L\le 10^5\), then truncated by packing.

\(L=50508\) is loose because it is a better approximant
(\(\theta\approx 7.26\cdot 10^{-6}\)), not because finance
treats it specially. A theorem that only uses \(\theta\to 0\)
is aimed at that seed, not at the finance frontier \(55293\).

## The \(1054\)-block is an itinerary, not an obstruction

The ceiling Christoffel word changes along a family step by
insertion of the length-\(1054\) Christoffel word of slope
\(665/1054\). The first \(F_1\) step is concatenation

\[
C(26835)=C(1054)\,C(25781).
\]

The extremal path \(o_k=r(k)\) appends the same block:

\[
E(L+1054)=E(L)\,E(1054).
\]

Both words are prefix-expanding and start `OOE`. Prefix
feasibility already certified them at every leftover
(`juggler_cycle_prefix_feasibility_leftover_killer`). A real
cycle itinerary need not be that necklace
(`juggler_christoffel_one_parameter`).

## What is closed

Because the basis is unimodular, \((a,b)\leftrightarrow(L,o)\)
is a change of coordinates. A predicate of one pair
\((a,b)\) is a predicate of that leftover’s \((L,o)\). Finance
already sees the point.

Same-start transfer is composition plus the existing finance
exclusion of period \(1054\):
\(n_{\max}^{\mathrm{par}}(1054)=788014\). If \(T_w(n)=n\), then
\(T_{w\star C_{1054}}(n)=T_{C_{1054}}(n)\ne n\) at CycleMin
scale. Concatenating the generator at a hypothetical \(L\)-cycle
does not produce an \((L+1054)\)-cycle at the same \(n\).

```text
single-point lattice information     CLOSED
generator-as-word rigidity           CLOSED
same-start block transfer            CLOSED
cross-period transfer                UNTESTED, and currently has no Φ
```

The only remaining lattice-shaped question would be a relation
between two hypothetical cycles at possibly different starts,

\[
\operatorname{Cycle}(L,o)\;\Rightarrow\;\Phi(L+1054,o+665),
\]

with \(\Phi\) dynamical and not a function of one pair. No such
\(\Phi\) is named. That does not justify a research phase.

## Endpoint

Continued-fraction structure explains the survivors. It does
not constrain actual cycles. Treat the three families as
different CF objects when reading the list. Do not attack the
\(99\) individually, and do not reopen pair-level, modular,
finance-conditioned, or Christoffel leftover-killers under a
change of basis.

Ledger: `J-run-survivor-lattice` (arithmetic) and the existing
run-type instance row. Lean: `RunSurvivorLattice.lean`, imported
by `Problems.JugglerPaper`. Paper A: Theorems 4.7--4.8 and
Proposition 4.9.
