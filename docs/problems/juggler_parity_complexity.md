# Juggler: factor complexity of the depth-one parity sequence

## Problem

The letter after an odd step. For the odd start \(2k+1\) the next letter of the
itinerary is the parity of \(\lfloor (2k+1)^{3/2}\rfloor\). Is the sequence
\(a(k)=\lfloor (2k+1)^{3/2}\rfloor \bmod 2\) automatic, so that finite-state tooling
(Walnut, Ostrowski automata) could decide frontier-parity questions for the Juggler
map?

## Exact statement

Let \(f(x)=(2x+1)^{3/2}\), \(a(k)=\lfloor f(k)\rfloor \bmod 2\), and let \(p(L)\) be
the number of distinct words \((a(k),\dots,a(k+L-1))\), \(k\ge 0\).

Question: is \(p(L)=O(L)\)?

Answer: no. Let \(R(L)\) be the number of interior equal-interval rotation words of
length \(L\), the words \(j\mapsto[\{y+j\beta\}\ge\tfrac12]\) realised on an open set
of \((y,\beta)\). Then
\[
p(L)\;\ge\;R(L)\;\ge\sum_{\substack{r\ \text{odd}\\ 2r+2\le L}}(2r+1)\;=\;\frac{L^2}{8}-O(L).
\]
Consequently \(a\) is not \(q\)-automatic for any \(q\), not Sturmian, and not the
coding of any single rotation by two intervals.

## Current literature

| Source | Statement | Relation |
|---|---|---|
| `allouche-shallit-2003-automatic-sequences`, Chapter 10 | a \(q\)-automatic sequence has \(p(L)=O(L)\) (Cobham); Sturmian words have \(p(L)=L+1\) | `known`, the consequence step |
| `boshernitzan-1994-hardy-fields` | \(\{g(n)\}\) is uniformly distributed for \(g\) in a Hardy field of polynomial growth staying logarithmically away from \(\mathbb Q[t]\) | `known`, the occurrence step; here \(g=a f+b f'\), which is Hardy in \(k\) (no nested floor) |
| [juggler_information_complexity](juggler_information_complexity.md) | information needed to predict a finite future from a sample | a different object; that branch is CLOSE and is not reopened |
| [juggler_rate_free_floor_hardy](juggler_rate_free_floor_hardy.md), [juggler_v94_rate_free](juggler_v94_rate_free.md) | Boshernitzan applies to \(\{n^{27/8}\}\) and not to \(\lfloor n^{3/2}\rfloor^{9/4}\) | same tool, same limitation: the reduction below is depth one only |

Relationship: `independent` for the specific sequence and its profile; the argument is
a standard Taylor-plus-equidistribution reduction and claims no new method.

## Branch budget

- **Target:** is the depth-one frontier parity over odd starts an automatic sequence?
- **Novelty hypothesis:** its complexity profile and the automaticity verdict were not in
  the record; the laboratory has Walnut and Ostrowski-automatic tooling that this decides
  the fate of.
- **Falsifier:** \(p(L)\le CL\) on a growing range, or a rotation word that never occurs.
- **Already killed by?:** none. Not a cycle claim, not a termination construction of
  \(e(uw^{3/2})\), not a local attack; it is negative knowledge about a tool class.
- **Existing machinery:** `floorPower`, kernel `decide` on `Nat.sqrt`, Boshernitzan already
  cited in the record.
- **Maximum Phase-0 scope:** factor census to \(L=22\) on \(3\cdot10^6\) terms, exact
  enumeration of rotation words, Lean exhaustion indices.
- **Promotion criterion:** none; the branch is negative knowledge by design.
- **Stop criterion:** the verdict is proved. Stop.

## Balanced-ternary formulation

None. Parity is a base-two reading and balanced ternary plays no role.

## Why BT may be relevant

It is not; recorded for the template.

## Candidate operations / invariants

- factor complexity \(p(L)\): **COMPUTATIONALLY VERIFIED** table to \(L=22\);
- exhaustion index, the least \(n\) with every word of length \(L\) among the first
  \(n\) letters: **EXACT — LEAN VERIFIED** for \(L\le 6\);
- rotation-word count \(R(L)\) and the periodic family: **EXACT — HUMAN PROOF** lower
  bound with **KNOWN** inputs;
- entropy proxy \(\log p(L)/L\) and growth exponent: **OBSERVATION**.

## Experiments

`python -m research.juggler_sequence.parity_complexity` writes
`data/research/juggler/parity_complexity/summary.json` (\(N=10^6\), \(L\le 22\)): the
table with \(p\), \(R\), family and control counts, missing counts, exhaustion indices,
prefix sensitivity, and the joint-phase histogram. The census below is the
\(N=3\cdot10^6\) run; the artifact at \(N=10^6\) agrees to \(L=13\), is lower by at
most 59 words beyond, and has every rotation word present to \(L=20\) rather than 22.

| \(L\) | \(p(L)\) | \(2^L\) | \(R(L)\) | family | control \(2L\) |
|---|---|---|---|---|---|
| 1–6 | \(2^L\) | \(2^L\) | 2, 4, 8, 16, 28, 48 | 0, 0, 0, 3, 3, 3 | \(2L\) |
| 7 | 126 | 128 | 72 | 3 | 14 |
| 8 | 229 | 256 | 108 | 10 | 16 |
| 9 | 390 | 512 | 152 | 10 | 18 |
| 10 | 618 | 1024 | 208 | 10 | 20 |
| 11 | 932 | 2048 | 272 | 10 | 22 |
| 12 | 1354 | 4096 | 356 | 21 | 24 |
| 14 | 2586 | 16384 | 564 | 21 | 28 |
| 16 | 4551 | 65536 | 836 | 36 | 32 |
| 18 | 7525 | 262144 | 1188 | 36 | 36 |
| 20 | 11719 | 1048576 | 1632 | 55 | 40 |
| 22 | 17453 | 4194304 | 2168 | 55 | 44 |

Every rotation word and every family word of length \(\le 22\) occurs in the first
\(3\cdot10^6\) terms (zero missing at every \(L\)). The control
\(\lfloor k\sqrt2\rfloor\bmod 2\), the equal-interval coding of one rotation, has
\(p(L)=2L\) exactly.

Exhaustion indices: 18, 48, 169, 574 for \(L=3,4,5,6\); at \(L=7\) two words never
occur in \(3\cdot10^6\) terms.

Prefix sensitivity at \(L=12\): 1354 words from the start, 970 from position 1000,
544 from position \(10^5\) (532 in the \(N=10^6\) artifact), against \(R(12)=356\). The
joint phase \((f(k),f'(k))\bmod 2\) fills a \(10\times10\) grid to within \(\pm15\%\) of
uniform at \(N=3\cdot10^6\), and within \(-19\%/+33\%\) at the artifact's \(3\cdot10^5\).

## Conjectures

None registered. The growth is polynomial-looking over the measured window,
\(\log p/\log L=3.16\) at \(L=22\) with local slope \(4.2\) on \([11,22]\) (the rotation
count alone has local slope \(2.99\)), and \(\log p/L\) falls from \(0.693\) to \(0.444\).
That is consistent with zero entropy and is an observation, not a conjecture.

## Counterexamples

The two words of length 7 absent from \(3\cdot10^6\) terms are \(0010000\) and
\(0100010\). Both have runs whose lengths differ by more than one, so neither is a
rotation word; whether either ever occurs through a curvature effect at small \(k\) is
open and immaterial to the verdict.

## Formalization

`formal/Problems/Juggler/ParityComplexity.lean` (registered in `Problems.Juggler` and in
`lean_paths.LAYERS`): `oddCubeParity`, `oddCubeParity_eq_floorPower` (the sequence is
`floorPower (2k+1) % 2`), `parityPrefix`, `windows`, `factorCount`, and the kernel-checked
`parityPrefix_eight`, `factorCount_three_saturates` (18), `factorCount_four_saturates`
(48), `factorCount_five_saturates` (169), `factorCount_six_saturates` (574),
`factorCount_six_not_before` (63 words at 573). Standard foundations only. The asymptotic
lower bound is not formalized: Boshernitzan's theorem is not in Mathlib.

## Results

**1 (EXACT — LEAN VERIFIED).** Every binary word of length \(\le 6\) occurs, and the
words of length \(3,4,5,6\) are exhausted at exactly \(18,48,169,574\) terms.

**2 (EXACT — HUMAN PROOF, KNOWN inputs).** \(p(L)\ge R(L)\ge L^2/8-O(L)\).

*Taylor.* For \(j<L\), \(f(k+j)=f(k)+jf'(k)+\rho_j\) with
\(0\le\rho_j\le \tfrac{j^2}{2}f''(k)\le 1.5L^2/\sqrt{2k+1}\), since
\(f''(x)=3(2x+1)^{-1/2}\) is positive and decreasing.

*Cell.* Fix an interior rotation word \(w\) of length \(L\), realised on an open cell
\(U\subset(\mathbb R/2\mathbb Z)^2\) of \((y,\beta)\), and shrink it to \(U_\varepsilon\)
where every phase \(y+j\beta\) is at distance \(\ge\varepsilon\) from the integers.
\(U_\varepsilon\) is a nonempty open polygon. If \((f(k),f'(k))\bmod 2\in U_\varepsilon\)
and \(1.5L^2/\sqrt{2k+1}<\varepsilon\), the window at \(k\) is exactly \(w\), because
adding \(\rho_j\in[0,\varepsilon)\) moves no phase across an integer.

*Occurrence.* \((f(k)/2,f'(k)/2)\bmod 1\) is jointly uniformly distributed: by Weyl's
criterion it suffices that \(\tfrac a2 f+\tfrac{3b}2(2x+1)^{1/2}\) is uniformly
distributed mod 1 for integers \((a,b)\ne(0,0)\), and that is Boshernitzan 1994, the
function being in a Hardy field, of polynomial growth, and at distance \(\gg x^{1/2}\)
from every rational polynomial. Hence the set of \(k\) landing in \(U_\varepsilon\) has
positive density, and all but finitely many of them satisfy the curvature condition. So
every interior rotation word occurs, with positive lower density.

*Counting.* For odd \(r\) with \(2r+2\le L\), the \(2r+1\) shifts of
\((0^r1^{r+1})^\infty\) are interior rotation words (slope \(1/(2r+1)\), generic phase),
pairwise distinct since the period is primitive, and distinct across \(r\) since a window
of length \(\ge 2r+2\) contains a complete run, of length \(r\) or \(r+1\), which recovers
\(r\). So \(R(L)\ge\sum_{r\ \mathrm{odd},\,2r+2\le L}(2r+1)=L^2/8-O(L)\).

*Consequences.* A \(q\)-automatic sequence has \(p(L)=O(L)\) (Cobham); a Sturmian word
has \(p(L)=L+1\); the coding of one rotation by two intervals has linear complexity. None
applies. In particular the depth-one frontier parity is not automatic in any numeration
system, so Walnut-style or Ostrowski-automatic decision procedures cannot settle
frontier-parity questions for the Juggler map, at depth one already.

**3 (COMPUTATIONALLY VERIFIED).** The table above; \(R(L)\) and the family are contained
in the factor set for all \(L\le 22\) at \(N=3\cdot10^6\); the control has \(p(L)=2L\).

**4 (OBSERVATION).** Growth and entropy as in Conjectures. The factor set is dominated by
early positions, where curvature is large: from position \(10^5\) on, \(p(12)\) is 544
against the rotation floor 356, so the tail approaches the rotation language slowly.

## Open questions

- The order of growth of \(p(L)\). The rotation count alone is roughly cubic; the
  curvature words add more and the local exponent has not settled by \(L=22\). An upper
  bound of polynomial type would need a cell count for the quadratic-phase family along the
  curve \((f,f',f''/2)(k)\), which is not attempted.
- Whether the two missing length-7 words ever occur.
- Depth two and beyond. The letter after \(OO\) is the parity of
  \(\lfloor\lfloor m^{3/2}\rfloor^{3/2}\rfloor\), which is not a Hardy function of \(m\);
  the reduction here stops at depth one. The lab's nested-floor wall stands exactly where
  the rate-free Hardy dossiers found it.

## Decision

**CLOSE.** The target is answered in the negative direction the laboratory needed: the
frontier parity is not automatic, so a tool class the laboratory invested in elsewhere
(Walnut, Ostrowski-automatic adders) cannot be turned on the Juggler map. Nothing here
bears on termination or cycles, and the branch has no promotion criterion. Recorded as
negative knowledge.

Best next question: none from this branch. The residue worth keeping is descriptive: at
depth one the parity word is, locally, an equal-interval rotation word with slope
\(3\sqrt{2k+1}\bmod 2\) plus a curvature correction, the same second derivative the
depth-one main term integrates.

## Publication assessment

Status: `ARCHIVED`. A remark, not a paper: the reduction is standard and the sequence is
special to this laboratory. It could serve as a one-paragraph justification, in any
write-up of the tooling, for not attempting automatic-sequence methods on Juggler parity.
