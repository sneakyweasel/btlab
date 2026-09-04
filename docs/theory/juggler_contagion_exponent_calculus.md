# The contagion exponent as a transfer matrix

Status: **laboratory extract** (4 September 2026). Not a new production
and not an unconditional improvement of \(\lambda^{***}\). It
reorganizes the §4 recursion of
[juggler_fate_contagion_note.md](juggler_fate_contagion_note.md) as a
transfer matrix on the backward tree, recovers \(\lambda^*\),
\(\lambda^{**}\) and the \(0.4927\) ceiling from one equation, shows the
method's ceiling is **exactly** \(\lambda=1\), identifies the single
criterion that decides which productions get the ideal share, and
prices the remaining ground — including where it stops. Verification:
[`tests/research/juggler_sequence/test_contagion_exponent_calculus.py`](../../tests/research/juggler_sequence/test_contagion_exponent_calculus.py).

## 1. Two elementary backward steps

Let \(A\) be nonempty and backward-closed. From \(m\in A\), backward
closure gives two preimage productions, in *(log-mass, log-scale)*
coordinates:

| step | log-mass factor | log-scale factor | source |
|---|---|---|---|
| \(E\)-preimage \(E(m)\) | \(1\) | \(\times 2\) | Lemma 2.1 (exact) |
| \(O\)-preimage \(\{n\ \text{odd}:\lfloor n^{3/2}\rfloor=m\}\) | \(\eta/3\) | \(\times\tfrac23\) | Lemma 2.2 + fiber share |

The \(E\)-block is mass-preserving (\(\sum_{n\in E(m)}1/n=(1+O(1/m))/m\)).
The \(O\)-preimage is at most one integer, present for a
\(\tfrac13m^{-1/3}\) proportion of \(m\) and carrying log-mass
\(m^{-2/3}\), so its *ideal* expected mass factor is \(\tfrac13\); here
\(\eta\in[0,1]\) is the **realized fiber-parity share divided by the
ideal \(\tfrac12\)**.

A production word \(w\) (the forward parity word, \(a\) letters \(E\)
and \(b\) letters \(O\)) carries its source at log-scale
\(\rho_w t\) with

\[
\rho_w=2^{-a}\bigl(\tfrac32\bigr)^{b},
\qquad
c_w^{\rm ideal}=\frac{2^{-|w|}}{\rho_w} .
\]

That single formula returns every coefficient in the note:
\(c_E=1\), \(c_{OE}=\tfrac13\), \(c_{OEE}=\tfrac13\),
\(c_{OOEEE}=\tfrac19\).

## 2. Which \(\eta\) applies is a function of the path

The note's own lemmas give three regimes, distinguished by how many
consecutive backward \(E\)-steps precede the \(O\)-step:

- \(\ge 2\) preceding \(E\)'s — the source is a block of blocks, so the
  long interval \(I(m')\) is available and Proposition 3.4's
  exponential-sum block average attains the ideal: \(\eta_2=1\).
- exactly \(1\) preceding \(E\) — the source is one even block \(E(m)\)
  and only Lemma 3.2 applies, \(G_m\ge\tfrac13H_m\) against the ideal
  \(\tfrac12H_m\): \(\eta_1=2/3\).
- an \(O\) precedes — not covered by any lemma of §§1–4: \(\eta_0=0\).

## 3. The transfer matrix

Take the state to be \(\min(2,\#\text{consecutive preceding }E)\). With
\(x=2^{-\lambda}\) and \(y_j=(\eta_j/3)(3/2)^{\lambda}\), the exponent
is the root of \(\rho(M(\lambda))=1\), i.e.

\[
1-y_0\ =\ \frac{x^2y_2}{1-x}\ +\ x\,y_1 .
\tag{3.1}
\]

**Proposition 3.1 (EXACT — HUMAN PROOF).** At
\((\eta_0,\eta_1,\eta_2)=(0,\tfrac23,1)\), (3.1) is algebraically
identical to the note's \(\lambda^{**}\) equation.

*Proof.* With \(y_0=0\), multiply by \(1-x\) and use
\(x^2(3/2)^\lambda=(3/8)^\lambda\), \(x(3/2)^\lambda=(3/4)^\lambda\),
\(x(3/4)^{\lambda}=(3/8)^{\lambda}\):
\(\tfrac13(3/8)^\lambda-\tfrac29(3/8)^\lambda+\tfrac29(3/4)^\lambda=1-x\),
i.e. \(\tfrac19(3/8)^{\lambda}+\tfrac29(3/4)^{\lambda}=1-2^{-\lambda}\).
\(\square\)

**Validation (COMPUTATIONALLY VERIFIED).** One equation, four published
constants:

| \((\eta_0,\eta_1,\eta_2)\) | (3.1) | note |
|---|---|---|
| \((0,0,1)\) — items 1+2 only | \(0.3774\) | \(\lambda^*\) |
| \((0,\tfrac23,1)\) — all three items | \(0.4480\) | \(\lambda^{**}\) |
| \((0,1,1)\) — perfect fiber shares | \(0.4927\) | ideal depth-2 ceiling |
| \((1,1,1)\) | \(1\) | — |

## 4. The ceiling is exactly \(1\)

With \(\eta_0=\eta_1=\eta_2=\eta\), multiplying (3.1) by \(1-x\) gives
\(x^2y+xy(1-x)+(y-1)(1-x)=x+y-1\) identically, so (3.1) collapses to

\[
2^{-\lambda}+\tfrac{\eta}{3}\bigl(\tfrac32\bigr)^{\lambda}=1 .
\tag{4.1}
\]

At \(\eta=1\), \(\lambda=1\) **exactly**: \(\tfrac12+\tfrac13\cdot\tfrac32=1\).
Implicit differentiation gives
\(-\partial_\lambda=\tfrac12\ln\tfrac43\), \(\partial_\eta=\tfrac12\), so

\[
\frac{d\lambda}{d\eta}\Big|_{\eta=1}=\frac1{\ln(4/3)}=3.4761\ldots,
\qquad 1-\lambda\ \approx\ \frac{1-\eta}{\ln(4/3)} .
\]

Summing the backward tree by path type (\(\theta=\) odd share,
\(\binom{k}{\theta k}\) arrangements, mass \((\eta/3)^{\theta k}\),
scale constraint \(k(1-\theta\log_23)\le u\)) gives the variational form

\[
\lambda(\eta)=\max_{0\le\theta<1/\log_23}
\frac{H(\theta)-\theta\log_2(3/\eta)}{1-\theta\log_2 3},
\]

maximized at \(\theta=\tfrac12\) when \(\eta=1\), where numerator and
denominator coincide at \(1-\tfrac12\log_23\). **The extremal backward
path is the fair-coin one** — which is why the ceiling lands exactly on
the value the Tao route needs, and not short of it.

## 5. The binding constraint is \(\eta_0\)

**With \(\eta_0=0\), \(\lambda\le 0.4927\) even with perfect fiber
shares.** The reason is entropic: \(\lambda=1\) needs backward paths at
odd share \(\theta=\tfrac12\) carrying full entropy \(H(\tfrac12)=1\),
and forbidding two consecutive \(O\)-steps leaves, at
\(\theta=\tfrac12\), only the alternating word — entropy \(0\). Every
arrangement that makes the entropy is one that puts two \(O\)'s in a
row.

## 6. The fiber-length criterion (EXACT — HUMAN PROOF)

**Proposition 6.1.** For a production word \(w\) with source scale
\(\rho_w t\), the source \(m'\) has \(n\asymp m'^{1/\rho_w}\), so at
scale \(P=n\) the fiber is
\(I(m')=[m'^{1/\rho_w},(m'+1)^{1/\rho_w})\) with

\[
|I(m')|=\tfrac1{\rho_w}\,m'^{1/\rho_w-1}
       =\tfrac1{\rho_w}\,P^{\,1-\rho_w}.
\]

Proposition 7.1 requires \(Y\ge P^{1/2}\). Hence **the localized
Paper B estimate — and with it the ideal share \(\eta=1\) — is
available exactly when \(\rho_w\le\tfrac12\).**

This reproduces all three fiber lengths printed in the note and
classifies every production it uses:

| word | \(\rho_w\) | \(|I|\) | \(\rho_w\le\tfrac12\) | production |
|---|---|---|---|---|
| \(E\) | \(1/2\) | \(P^{1/2}\) | yes | Lemma 2.1, exact |
| \(OEE\) | \(3/8\) | \(P^{5/8}\) | yes | Prop 3.4, ideal |
| \(OOEEE\) | \(9/32\) | \(P^{23/32}\) | yes | Prop 7.1, ideal |
| \(OE\) | \(3/4\) | \(P^{1/4}\) | **no** | elementary sweep, \(\eta=2/3\) |
| \(OOEE\) | \(9/16\) | \(P^{7/16}\) | **no** | unavailable |

**The \(\tfrac13\)-versus-\(\tfrac12\) "depth-two gap" and the
short-fiber regime \(\rho_w>\tfrac12\) are the same set.** They are not
two problems. This also explains why §7 had to reach \(OOEEE\) rather
than \(OOEE\): \(OOEE\) has \(\rho=9/16>\tfrac12\), so its fiber
\(P^{7/16}\) is below Proposition 7.1's threshold; the extra \(E\)
lengthens the fiber past it.

## 7. The word list, and where it stops

Production words must be prefix-free (else the same \(n\) is produced
from two sources). The natural set is the *first passage below
\(\tfrac12\)*: \(\rho_w\le\tfrac12\) with every proper prefix above.
An \(O\)-run of length \(r\) forces \(r\) nested \(3/2\)-powers plus the
closing square root, i.e. **Paper B at depth \(r+1\)**. Paper B is
complete to depth \(4\), and to depth \(5\) except \(OOOO*\) — the
\(K_3\) wall. So \(r\le 3\).

| word | \(\rho_w\) | longest \(O\)-run | Paper B depth | status |
|---|---|---|---|---|
| \(E\) | \(1/2\) | 0 | — | exact |
| \(OEE\) | \(3/8\) | 1 | 2 | **proved** (Prop 3.4) |
| \(OOEEE\) | \(9/32\) | 2 | 3 | **proved** (§7) |
| \(OEOEE\) | \(9/32\) | 1 | 2 | needs localized depth 2 |
| \(OOEOEE\), \(OOEEOE\), \(OEOOEE\) | \(27/64\) | 2 | 3 | needs localized depth 3 |
| \(OOOEEE\) | \(27/64\) | 3 | 4 | needs localized depth 4 |
| \(OOOOEEEE\) | \(81/256\) | 4 | 5 | **\(K_3\) wall** |

§7's Proposition 7.2 attains the *ideal* share \(\tfrac1{16}\) for
\(OOEEE\); its estimate is not lossy. The remaining ground is therefore
**more words, not a better estimate for the word already used**, and
each new word costs one localization of a Paper B theorem to sub-dyadic
intervals — the same modification list §7 ran for Theorems 4.4/4.7.

## 8. Price list

\(r\) = longest controllable \(O\)-run; Tao \(C\) = least constant with
\(e(C)>1-\lambda\).

| \(r\) | Paper B depth | \(\lambda\) (\(\eta_1=\tfrac23\), current sweep) | \(C\) | \(\lambda\) (\(\eta_1=1\)) | \(C\) |
|---|---|---|---|---|---|
| 1 | 2 | 0.4480 | 20 | 0.4927 | 19 |
| 2 | 3 | 0.6247 | 16 | 0.7180 | 14 |
| 3 | 4 | 0.7095 | 14 | 0.8414 | 11 |
| 4 | 5 | 0.7516 | 13 | 0.9121 | 9 |

Row \(r=4\) is behind \(K_3\). **The reachable target is \(r=3\):
\(\lambda\le0.7095\) (\(C=14\)) with the present sweep, and
\(\lambda\le0.8414\) (\(C=11\)) if the short-fiber regime is also
brought to the ideal share.** Current print is \(\lambda^{***}=0.5392\)
(\(C=18\)).

Two independent levers, both needed for \(\lambda\to1\): the
short-fiber share \(\eta_1\) alone caps at \(0.4927\); the \(O\)-run
lever alone saturates at \(0.7909\).

## 9. What this does not do

\(\lambda=1\) requires \(r\to\infty\), hence \(O\)-runs of every length,
hence Paper B past \(OOOO*\): **the contagion lever is guarded by
\(K_3\) too, at \(r=4\).** It is not a route around the wall — it
approaches the same wall from the other side, and buys real ground
before reaching it (\(C=18\to14\), or \(\to11\)). Since
\(1-\lambda\approx(1-\eta)/\ln(4/3)\) and \(\eta\) is a fiber-parity
share, the ceiling is approached only through statements of the same
species as \(\mathrm H(C,A)\). Improving \(\lambda\) lowers the Tao
constant; it does not remove the \(\log\log y\) depth requirement, and
\(\lambda=1\) would still leave the Tao route needing *some* positive
rate.
