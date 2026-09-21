# Can the finite growing power family continue indefinitely?

Status: **CLOSE** the direct continuation of the positive-density power
construction. Square re-entry has parameter density zero unconditionally
and occurs only finitely often for each fixed block assuming abc.
Arbitrary sparse Juggler escape remains unresolved.

## Problem

Authorized continuation, 22 September 2026: determine whether the genuine
finite growing blocks in
[denominator coupling](juggler_cycle_denominator_coupling.md) can feed
their endpoints back into the perfect-power starting family indefinitely.

## Exact statement

Fix integers \(a,b\ge1\) with \(3^a>2^{a+b}\), and put
\[
d=2^{a-1},\quad P=3^a,\quad h=2^{b+1},\quad \beta=P/h>d.
\]
Necessarily \(a\ge2\), \(d\ge a\), and \(\beta>2\).
The construction starts at \(n=s^d\), for odd \(s\ge3\).
If its actual branch word is \(O^aE^b\), its endpoint is
\[
F_{a,b}(s)=J^{a+b}(s^d)=\lfloor s^\beta\rfloor.
\]
All starting families of this type consist of odd squares. Therefore
continuation into any of them requires \(F_{a,b}(s)\) to be a square;
return to the same family requires the stronger \(d\)-th-power condition.

**Retained result, EXACT — HUMAN PROOF, AI-assisted written argument.**

1. For each fixed \(a,b\), the parameters with square endpoint have
   density zero among odd \(s\), and along every fixed arithmetic
   progression of odd parameters. This holds even before imposing guards.
2. **Assuming the standard abc conjecture**, only finitely many odd \(s\)
   have both the actual word \(O^aE^b\) and a square endpoint.
3. Consequently, **assuming abc**, no infinite trajectory can be assembled
   from a fixed finite collection of these expanding block types while
   imposing \(n=s^{2^{a-1}}\) at the start of each chosen block. Different
   integer bases and arbitrarily sparse selections are allowed.

The first statement does not assert finiteness. The latter two are
conditional implications, not unconditional no-escape theorems.

## Current literature

- boshernitzan-1994-hardy-fields: **KNOWN** equidistribution of nonintegral
  powers along arithmetic progressions. The criterion was checked in
  [Reilly, Theorem 1.1](https://arxiv.org/html/2606.08040v1).
- conrad-2013-abc-conjecture: the **standard conjectural** bound for coprime
  positive \(A+B=C\), \(C\ll_\epsilon\operatorname{rad}(ABC)^{1+\epsilon}\).
  Read in [Brian Conrad's slides, page 26](https://www.math.stonybrook.edu/Videos/Colloquium/PDFs/20130912-Conrad.pdf).
  Only the stated conditional bound is used; no claimed proof is imported.
- [OOE escape families](juggler_ooe_escape_families.md), Sections 5--7:
  paired sparse templates, narrow fixed-base tubes, and the invalid
  compactness inference are already addressed. Here the base varies
  arbitrarily and a return to any square is the necessary condition.
- The perfect-power-gap reduction is an elementary application of
  classical arithmetic machinery. External novelty is not claimed.
  The laboratory consequence concerns this finite-block construction.

## Branch budget

~~~text
Mathematical target     Closure of the O^a E^b perfect-power family.
Novelty hypothesis      Its exact endpoint admits a repeatable integer parameter.
Falsifier               Re-entry requires an extra arithmetic condition that
                        the finite-block construction does not preserve.
Already killed by?      Fixed-base tubes and full polynomial families are closed;
                        varying-base perfect-power re-entry is not covered.
Existing machinery      Exact block formula and the phase-family theorem.
Maximum Phase-0 scope   Derive the re-entry condition; check three fixed word
                        types over at most 25,000 odd parameters each.
Promotion criterion     A repeatable rule with a fixed seed, or a precise new
                        obstruction to this construction.
Stop criterion          No closure rule; only an unresolved approximation problem.
~~~

The exact shrinking target justified one theorem phase: prove density
zero and check the conditional abc obstruction. No larger census or
alternate invariant family was opened.

## Balanced-ternary formulation

None used. The arithmetic concerns perfect-power gaps and radicals.

## Why BT may be relevant

No advantage from representation is asserted.

## Candidate operations / invariants

- Reuse a positive-density phase family as an invariant domain:
  **REFUTED** by the zero-density square re-entry condition.
- Finitely many guarded square re-entries for a fixed block:
  **EXACT — HUMAN PROOF of an implication from abc**, not an
  unconditional assertion.
- An ordinary integer seed that can continue forever: **OPEN**.

## Experiments

The bounded exact check used the odd parameters \(3\le s\le50001\):
25,000 for each of the following three words. Tests replay actual
integer-square-root steps and stop accepting a word at its first
incorrect source parity.

| Word | Actual blocks with odd exit | Actual blocks with square exit |
|---|---:|---:|
| OOE | 6186 | 0 |
| OOOE | 6364 | 0 |
| OOOOEE | 3095 | 0 |

These are finite observations, not evidence sufficient for finiteness
at all heights. The range is in the base parameter, not a Juggler
verification floor; no eventual fate was computed.

[Exact regression checks](../../tests/research/juggler_sequence/test_power_family_reentry.py)
also retain the false unguarded return, a contracting square-return
control, the gcd normalization, and the exponent margin in the abc proof.
No production probe or new runtime component is needed.

## Conjectures

No new conjecture adopted. The abc conjecture is an explicit external
hypothesis in the conditional statements.

## Counterexamples

Ignoring the guards gives a spurious exact return at \(a=2,b=1,s=6561=3^8\):
\[
3^{16}\ \xrightarrow{O}\ 3^{24}\ \xrightarrow{O}\ 3^{36}
\ \xrightarrow{\text{prescribed }E}\ 3^{18}.
\]
The last source is odd. The actual third step is O and gives \(3^{54}\).
Thus perfect-power closure of the unguarded formula does not
supply a repeatable Juggler block.

The contracting control \(21\to96\to9\), word OE, is a genuine
square return. The assumption \(\beta>2\) cannot be dropped from the
exponent argument below. For this control \(P=3,h=4,\beta=3/4\).

## Formalization

No new Lean module. The arguments below are written and AI-assisted;
independent human review and Lean verification remain outstanding.
Tests verify exact finite arithmetic, not abc or an infinite statement.

## Results

### 1. Exact endpoint and strict growth

The first \(a-1\) odd steps are exact:
\[
n_i=s^{3^i2^{a-1-i}}\qquad(0\le i<a).
\]
The last odd image is \(\lfloor s^{P/2}\rfloor\). The subsequent
even steps collapse exactly to \(\lfloor s^{P/h}\rfloor\), using
\(\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt{x}\rfloor\).
The endpoint formula describes the actual orbit only when all
source parity guards hold.

Every such guarded block strictly grows for every odd \(s\ge3\).
Since \(P-dh\) is a positive integer,
\[
s^\beta-s^d
>s^d(\beta-d)\log s
\ge \frac{s^d\log s}{h}
>\frac{d\,3^d\log3}{3^a}
\ge d\log3>1.
\]
Here \(h<P/d\), \(s\ge3\), and \(d\ge a\) justify the last bounds.
Thus \(F_{a,b}(s)>s^d\). The odd portion increases and the even portion
decreases to that endpoint, so every state stays above the start.

### 2. Square re-entry is a shrinking target

Write the endpoint as \(t^2\). Then
\[
t^2\le s^\beta<t^2+1,\qquad
0\le s^{\beta/2}-t
<\frac{1}{s^{\beta/2}+t}
\le s^{-\beta/2}. \tag{1}
\]
Thus \(t=\lfloor s^{\beta/2}\rfloor\) and the fractional part
of \(s^{\beta/2}\) lies in a target shrinking to zero.

The exponent \(\beta/2=3^a/2^{b+2}\) is nonintegral. Hence
\((r+mj)^{\beta/2}\) is uniformly distributed modulo 1 for every fixed
positive arithmetic progression. For any \(\eta>0\), all sufficiently
large square-return parameters satisfy
\(\{(r+mj)^{\beta/2}\}\in[0,\eta)\). Their upper density is at most
\(\eta\), and letting \(\eta\downarrow0\) proves density zero.

The original phase family has positive parameter density
\(1/(2^{b+1}M)\) in \(s=1+2Mj\). Therefore even within that family
the proportion returning to a square tends to zero. No subset of
positive parameter density can be closed under these returns.
An arbitrary zero-density invariant subset is not excluded.

Although the target sizes \(s^{-\beta/2}\) are summable, this is not a
deterministic finiteness proof. Ordinary equidistribution does not control
visits to shrinking targets. Indeed \(s^{\beta/2}\) is exactly integral at
every \(s=u^{2h}\); these infinitely many formal hits fail the E guard
below. No random parameter was supplied for a metric Borel--Cantelli argument.

### 3. The perfect-power gap and the zero-gap guard

Raising the endpoint cell to the integer power \(h\) gives
\[
0\le R:=s^P-t^{2h}<(t^2+1)^h-t^{2h}. \tag{2}
\]
If \(R=0\), coprimality of \(P\) and \(2h\) implies
\[
s=u^{2h},\qquad t=u^P.
\]
The base \(u\) is odd, so the first proposed E source is
\(\lfloor s^{P/2}\rfloor=u^{hP}\), which is odd. Therefore every
**guarded** square return has \(R>0\).

For \(t\ge1\), the mean value theorem and \(t^2+1\le2t^2\) give
\[
0<R<h\,2^{h-1}t^{2h-2}
\le C_h s^{P-\beta},\qquad C_h=h2^{h-1}. \tag{3}
\]
This small-gap requirement is not supplied by the finite phase construction.

### 4. Conditional finiteness from abc, including common factors

Assume that for every \(\epsilon>0\) there is \(K_\epsilon\) such that
every coprime positive triple \(A+B=C\) satisfies
\[
C\le K_\epsilon\operatorname{rad}(ABC)^{1+\epsilon}.
\]
For a guarded square return let \(g=\gcd(s^P,t^{2h})\). The triple
\[
A=t^{2h}/g,\quad B=R/g,\quad C=s^P/g
\]
is positive and coprime. No coprimality of \(s,t\) is assumed.
Every prime in \(A C\) divides \(s t\), so
\[
\operatorname{rad}(ABC)
\le st(R/g)
\le C_h s^{E}/g,\qquad E=P+1-\beta/2. \tag{4}
\]
Because \(\beta>2\), \(0<E<P\). Applying abc and multiplying by \(g\)
yields
\[
s^P\le K_\epsilon C_h^{1+\epsilon}
s^{E(1+\epsilon)}g^{-\epsilon}
\le K_\epsilon C_h^{1+\epsilon}s^{E(1+\epsilon)}.
\]
Choose \(\epsilon=(P-E)/(2E)>0\). The exponent on the right is
\((P+E)/2<P\); hence \(s\) is bounded. This proves conditional finiteness.
The abc constant is not an explicit computable search bound here.

For OOE, \(P=9,\beta=9/4,E=71/8\): the positive exponent margin is
\(P-E=1/8\). Infinitely many guarded square re-entries would produce
normalized abc triples with asymptotic quality at least \(72/71>1\).
More generally, (3) gives \(g\le R\) and
\(C\ge s^\beta/C_h\to\infty\). Equation (4) and \(P>E\) imply
\[
\operatorname{rad}(ABC)^P
\le C_h^P s^{EP}/g^P
\le C_h^P C^E.
\]
Consequently their quality has lower limit at least \(P/E>1\).
This is an unconditional implication about a hypothetical infinite
family, not a construction of abc counterexamples.

### 5. Scope of the obstruction

An infinite concatenation strictly increases at every block boundary.
If its types belong to a fixed finite collection, one type occurs with
unbounded starting base \(s\). Its endpoints must be odd squares to
start the next constructed block. This contradicts the conditional
finiteness result, assuming abc.

Unconditionally, a very sparse invariant set remains possible.
Conditionally, the result leaves unbounded variation in the block types,
departure from the perfect-power family, and general nonsquare trajectories
unresolved. It neither proves Juggler termination nor constructs escape.

## Open questions

No unconditional finiteness theorem for these square returns was obtained.
No fixed ordinary integer with infinite continuation was found.
The previous finite-prefix theorem retains its original quantifiers.

## Decision

**CLOSE** the direct continuation of the positive-density perfect-power
family as an escape construction. Retain the unconditional sparsity result
and the conditional abc obstruction. They explain the arithmetic price of
continuation without supplying an invariant seed.

Best next question: can one construct an explicit nonsquare invariant
domain with a fixed integer seed, rather than requiring square re-entry?
That question is not opened here; the general escape construction remains
unresolved.

## Publication assessment

Status: **STRUCTURAL**, an elementary application of classical
equidistribution and a standard conjectural gap principle. External
novelty is not asserted. Papers A--D, release files, the certified floor,
and the cycle-period bound are unchanged.
