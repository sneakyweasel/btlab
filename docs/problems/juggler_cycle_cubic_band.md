# Cycle order below the cubic height

Status: **PARK**. Research attempt dated 9 September 2026.

**The no-cycle conjecture is not proved.** The result obtained is a
conditional restriction on the complete itinerary of a primitive cycle.
If its maximum is below the cube of its minimum, its ordered states
must rotate by a fixed rank increment. Consequently its length and odd
count are coprime and its word is exactly a ceiling mechanical word.
The parity obstruction needed to exclude even this class is unproved.
Cycles reaching or exceeding the cubic height are also unexcluded.

## Problem

Let
\[
J(x)=\begin{cases}
\lfloor\sqrt{x^3}\rfloor,&x\text{ odd},\\
\lfloor\sqrt{x}\rfloor,&x\text{ even}.
\end{cases}
\]
Can global order on a finite invariant set provide a cycle obstruction
that does not depend on making the logarithmic surplus small?
The concrete test is the class of primitive cycles with minimum
\(m>1\), maximum \(M\), and \(M<m^3\).

Paper A's certified period lower bound remains \(780239\). This work
does not raise the descent floor or exclude any further period.

## Exact statement

**Proposition 1 — cubic-band order rigidity
(`J-cycle-cubic-band-order`, EXACT — HUMAN PROOF).**
Suppose \(C\) is a primitive nontrivial Juggler cycle of length \(L\),
minimum \(m>1\), maximum \(M<m^3\), and odd-state count \(o\).
Put \(e=L-o\) and list its states as
\(c_0=m<c_1<\cdots<c_{L-1}=M\). Then
\[
\begin{split}
&c_i\text{ is odd}\quad\Longleftrightarrow\quad i<o
\quad\Longleftrightarrow\quad c_i<m^2,\\
&J(c_i)=c_{(i+e)\bmod L},\qquad \gcd(L,o)=1.
\end{split}\tag{1}
\]
If \(a_k\) is the number of odd steps in the first \(k\) steps from
the minimum, then, for \(0\le k\le L\),
\[
a_k=\left\lceil\frac{ko}{L}\right\rceil.\tag{2}
\]
Thus the letter at position \(k\), starting with position zero, is
\(O\) precisely when
\(\lceil(k+1)o/L\rceil-\lceil ko/L\rceil=1\).
This specifies the word, rather than only its letter counts.

In particular, a primitive nontrivial cycle whose minimum-based word
is not (2), or whose counts satisfy \(\gcd(L,o)>1\), must satisfy
\(M\ge m^3\). Since \(m\) is odd and \(M\) even, the integer
consequence is \(M\ge m^3+1\). This is a conditional height bound,
not a global cycle exclusion.

**Proposition 2 — arbitrarily high closed orbits after removing the
parity rule (`J-cycle-threshold-relaxation`, EXACT — HUMAN PROOF).**
For every integer \(b\ge3\), define a different map on
\(I_b=\{b,b+1,\ldots,b^3-1\}\):
\[
S_b(x)=\begin{cases}
\lfloor\sqrt{x^3}\rfloor,&x<b^2,\\
\lfloor\sqrt{x}\rfloor,&x\ge b^2.
\end{cases}\tag{3}
\]
It maps \(I_b\) into itself, has no fixed point, and therefore has
a cycle of length at least two. All its primitive cycles have the
rank-rotation and mechanical-word properties in (1)--(2), counting
branch labels instead of actual odd integers. Their minima are at
least \(b\), so this construction is unbounded in scale.

**Map distinction:** (3) chooses its branch by size. It is not the
Juggler map. A cycle of (3) is a Juggler cycle if and only if every
state satisfies
\[
x\text{ odd}\quad\Longleftrightarrow\quad x<b^2.\tag{4}
\]
The construction does not assert that (4) ever holds on a full cycle.

## Current literature

**Extended within the repository; external priority not claimed.**
[Paper A](../theory/juggler_finite_dynamics_note.md) supplies the
existing cycle bounds. [Method ceilings](juggler_cycle_method_ceilings.md)
identifies the missing global information.
[The earlier Christoffel branch](juggler_cycle_christoffel.md) refutes
an unconditional reduction based on finance or admissible open words;
it explicitly leaves actual-cycle rigidity open. Proposition 1 uses
the additional height hypothesis and injectivity on a closed orbit.
It does not contradict that earlier refutation or identify the
Christoffel word with the greedy charge maximizer.

[The corrected run-alphabet dossier](juggler_cycle_run_alphabet.md)
withdraws an argument from \(R<27/8\). That assertion stays withdrawn.
The order proof here uses the different, explicit hypothesis
\(M<m^3\), exact floor inequalities, and no zero-drift assumption.
[Mechanical-window experiments](juggler_cycle_mechanical_window.md)
already showed finite prescribed-word fixed points with failed parity
checks. Proposition 2 gives a finite invariant-set construction at
every scale, without enumerating a prescribed word's fixed-point band.

The map and the general convergence conjecture are documented in
[OEIS A094683](https://oeis.org/A094683) and
[Weisstein's Juggler Sequence entry](https://mathworld.wolfram.com/JugglerSequence.html)
(accessed 9 September 2026). No external analytic theorem is used in
the proofs below, and the finite searches do not establish novelty.

## Branch budget

- **Target:** exclude primitive cycles with \(M<m^3\).
- **Novelty hypothesis:** sorted-state order plus bijectivity forces
  a complete word, rather than another bound on the surplus.
- **Falsifier:** the forced word and exact integer closure still do
  not yield a contradiction to the actual parity requirement.
- **Already killed by?:** unconditional Christoffel and local-cell
  shortcuts are closed. The additional global height hypothesis and
  permutation argument are not supplied by those shortcuts; this is
  a restriction on complete words uniform over this height class.
- **Existing machinery:** minimum/maximum parity, exact square/cube
  cells, monotonicity of the two prescribed branches, primitive-cycle
  injectivity, and the recorded method ceilings.
- **Maximum Phase-0 scope:** written order proof; exact complete
  threshold graphs for \(3\le b\le30\); one start per threshold for
  \(3\le b\le10000\); four capped large-scale controls; explicit
  counterexamples to stronger interpretations. No floor campaign.
- **Promotion criterion:** a proved uniform parity obstruction.
- **Stop criterion:** retain the structural result, identify the
  unproved arithmetic statement, and PARK without a no-cycle claim.

## Balanced-ternary formulation

All states are ordinary positive integers. Canonical balanced ternary
can represent them but does not enter the proof.

## Why BT may be relevant

No representation advantage is used. This remains a Juggler research
module and introduces no dependency in the core `bt` package.

## Candidate operations / invariants

The invariant is the cyclic order of the complete finite orbit. The
even images occupy the lowest ranks and the odd images the highest.
The rank increment is the number of even states. Individual inverse
cells alone do not establish this permutation structure.

The attempted final step was a uniform obstruction to (4). Integer
closure, mechanical balance, coprime counts, extrema parity, and the
sign of the surplus do not supply it; the witnesses below demonstrate
the distinction. No statistical parity assumption is made.

## Experiments

Probe: `research.juggler_sequence.cycle_cubic_band`.
Data: [summary.json](../../data/research/juggler/cycle_cubic_band/summary.json).
Tests: [test_cycle_cubic_band.py](../../tests/research/juggler_sequence/test_cycle_cubic_band.py).
Regenerate with `python -m research.juggler_sequence.cycle_cubic_band`.

The probe uses arbitrary-precision integers and `math.isqrt`.
The explicit control cycles additionally receive an independent
certificate \(y^2\le x^h<(y+1)^2\), with \(h=3\) or \(1\).

| Scope | Exact finite outcome |
|---|---|
| Every state of \(I_b\), \(3\le b\le30\) | 38 primitive cycles across 28 threshold maps; all pass the order checks and fail actual parity compatibility |
| Orbit starting at \(b\), \(3\le b\le10000\) | 9,998 eventual cycles; all pass rank rotation, coprimality, mechanical-word, exact-edge and expansion checks; none is a Juggler cycle |
| Same 9,998 starts | 1,355 are periodic from the initial state; the others have a transient |
| Longest observed cycle | \(b=9385\), minimum 9392, maximum 826579131129, length 16631, odd-branch count 10493, parity mismatches 8310 |
| \(b=350000001,1000000007,1000000000039,1000000000000000003\) | No repeat within the specified 200,000-step cap for each; all four are unresolved computations |

One sampled orbit is not a complete graph survey. The 9,998 rows are
not claimed to represent distinct cycles across different thresholds.
The complete small-graph count is likewise a count across maps.
The large capped runs are not evidence of escape: Proposition 2
proves that they eventually repeat. No cap or parity-frequency
observation is promoted into an infinite statement.

## Conjectures

No new conjecture file is opened. The desired global no-cycle theorem
remains unproved. The precise missing step within this height class
is stated under Open questions.

## Counterexamples

**Correct closure and word, incorrect parity.** At \(b=9\), (3) has
the exact primitive closed orbit
\[
9,27,140,11,36,216,14,52,374,19,82,9.
\]
Its word is \(OOEOOEOOEOE\), its counts are \((L,o)=(11,7)\),
its minimum is odd, its maximum is even, and \(374<9^3\).
It has no \(EE\) or \(OOO\), and \(3^7>2^{11}\).
Nevertheless the prescribed odd branch is used at the even states
36, 14 and 52. In the actual map, for example, \(J(36)=6\),
whereas \(S_9(36)=216\). This is not a Juggler cycle.
It also refutes a blanket claim that at least one third of each
threshold cycle must have the wrong parity: here the fraction is
\(3/11\). No weaker positive fraction has been proved.

**The height hypothesis matters to the order argument.** The
prescribed word \(OOOEOE\) closes exactly on
\[
3,5,11,36,6,14,3.
\]
All six states before return are distinct, while
\(\gcd(6,4)=2\) and \(36>3^3\). This word is not the ceiling word
for \((6,4)\). Only the step at 6 uses the wrong parity:
\(\lfloor\sqrt{6^3}\rfloor=14\), whereas \(J(6)=2\).
This refutes the parity-relaxed extension without the height bound;
it is not a counterexample to any theorem about actual Juggler cycles.

## Formalization

The two propositions have written proofs below. The repository tag
is **EXACT — HUMAN PROOF**, meaning an analytic proof rather than a
Lean-checked theorem. These proofs were prepared with AI assistance;
no independent human review or new Lean verification is claimed.
Finite integer tests validate examples and implementation boundaries,
not the universally quantified assertions. No Paper A Lean module or
publication source has been modified for this research attempt.

## Results

### Proof of Proposition 1

A cycle with minimum greater than 1 has odd minimum \(m\ge3\):
an even minimum would map below itself. Its maximum is even, since
\(\lfloor\sqrt{x^3}\rfloor>x\) for every integer \(x\ge3\).
Thus \(o,e>0\).

If an even state \(x\in C\) satisfied \(x<m^2\), then
\(J(x)<m\), impossible. If an odd state \(x\in C\) satisfied
\(x\ge m^2\), then
\(J(x)\ge\lfloor\sqrt{(m^2)^3}\rfloor=m^3>M\), also impossible.
Therefore the first \(o\) sorted states are exactly the odd states.

For any even \(x\in C\) and odd \(y\in C\), monotonicity gives
\[
J(x)\le\lfloor\sqrt M\rfloor
\le\lfloor\sqrt{m^3}\rfloor\le J(y).
\]
The possible equality from taking floors must be handled: \(J\)
permutes the states of a primitive cycle, so it is injective on
\(C\). Equality of these images would force \(x=y\), impossible
for opposite parities. Hence every even image is strictly below
every odd image. Each branch is nondecreasing, and injectivity on
\(C\) makes its restriction strictly increasing.

The \(e\) even images are consequently \(c_0,\ldots,c_{e-1}\),
in that order, and the \(o\) odd images are
\(c_e,\ldots,c_{L-1}\), in that order. This proves
\(J(c_i)=c_{(i+e)\bmod L}\).
Adding \(e\) modulo \(L\) has an orbit of size
\(L/\gcd(e,L)\). Primitivity requires that size to be \(L\),
so \(\gcd(e,L)=\gcd(o,L)=1\).

From rank zero the rank at time \(k\) is \(ke\bmod L\).
An even step occurs exactly when adding \(e\) wraps past \(L\):
the starting rank is then at least \(L-e=o\). The number of wraps
in the first \(k\) additions is \(\lfloor ke/L\rfloor\).
The odd count is therefore
\(k-\lfloor ke/L\rfloor=\lceil ko/L\rceil\), proving (2).
No exact logarithmic closure is used.

### Proof of Proposition 2

For \(b\le x<b^2\),
\(b\le x<\lfloor\sqrt{x^3}\rfloor<b^3\).
For \(b^2\le x<b^3\),
\(b\le\lfloor\sqrt x\rfloor<b^2\le x\).
Both conclusions follow directly from the square/cube inequalities;
the strict growth uses \(x\ge3\). Thus (3) preserves the nonempty
finite set \(I_b\), and neither branch has a fixed point there.
Every orbit eventually repeats, yielding a primitive cycle of
length at least two.

On any such cycle the states using the odd branch are its lower
part \(x<b^2\). The even-branch images are at most
\(\lfloor\sqrt{b^3-1}\rfloor\), and the odd-branch images are
at least \(\lfloor\sqrt{b^3}\rfloor\).
Once again these weak inequalities become strict between cycle
images by injectivity. The same sorting and modular-rank argument
proves (1)--(2) with branch counts. Since the least state is at
least \(b\), these closed orbits exist beyond any fixed lower bound.

Their formal exponent is also strictly expanding. Composing
\(S_b(x)\le x^{3/2}\) or \(S_b(x)\le x^{1/2}\) around a cycle
with minimum \(r>1\) gives
\(r\le r^{3^o/2^L}\), hence \(3^o\ge2^L\).
Equality is impossible for positive \(o,L\), since a positive
power of 3 is odd and a positive power of 2 is even.
Consequently \(3^o>2^L\). This sign, exact floors, distinctness,
closed-orbit order and unbounded minimum coexist in the relaxed map.
They do not force the missing parity rule (4).

### A limited run consequence

For an actual cycle under Proposition 1, \(EE\) is impossible:
all even states are at least \(m^2\), whereas their images are
less than \(m^2\). Also \(OOO\) is impossible. If its starting
state is \(q\ge5\), the existing exact lemma
`ooo_residual_ge_cube` in `Preimages.lean` places its third image
at least \((q+1)^3>m^3\). The remaining odd case \(q=3\) has
the exact third image 36, larger than \(3^3\).
Thus the word consists cyclically of blocks \(OE\) and \(OOE\).
This is a corollary under \(M<m^3\), not the withdrawn claim
under \(R<27/8\); no first-fall location is inferred.

## Open questions

For \(b\ge3\), define the wrong-parity set
\[
B_b=\{x\in I_b:x<b^2\text{ and }x\text{ even}\}
\ \cup\ \{x\in I_b:x\ge b^2\text{ and }x\text{ odd}\}.
\]
The exact missing arithmetic statement is that every cycle of
\(S_b\) intersects \(B_b\), for every \(b\ge3\).
Equivalently, every orbit of \(S_b\) eventually visits \(B_b\).
This would exclude all actual Juggler cycles with \(M<m^3\):
use \(b=m\). Conversely, a cycle of \(S_b\) avoiding \(B_b\)
would be an actual Juggler cycle whose minimum \(r\ge b\) and
maximum \(<b^3\le r^3\) satisfy that height condition.

The order lemma proves no such intersection. The measurements do
not prove parity independence or any uniform discrepancy estimate
on this sparse cycle-selected set. An estimate over consecutive
integer starts would not automatically apply to it. Even a proof
of this missing statement would still leave the separate regime
\(M\ge m^3\) unresolved.

## Decision

**PARK.** The structural propositions survive exact checking, but
the proposed cycle exclusion does not. Retain the written proofs
and explicit counterexamples; do not enlarge the capped runs or
translate a positive observed mismatch fraction into a theorem.
Exactly one next mathematical question for this branch is whether
every threshold cycle must meet \(B_b\), uniformly in \(b\).
No new attack is opened automatically from this record.

## Publication assessment

Status: **STRUCTURAL**. This is a separate research record with
AI-assisted written proofs, not a publication-ready no-cycle proof.
Paper A's released title, sources, PDF and certified period bounds
remain unchanged by this attempt.
