# Juggler leftover first-lift eighth cell

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a W_5
reopen, not a first-return \(Q\)-map, not Paper A, and not a claim
that every positive integer reaches 1.

The mixed OE cell names \(T^{2}(x)<n^{2}\) iff \(x^{3}<n^{8}\)
when \(x\) is odd and \(T(x)\) is even. This phase asks whether
that safe side is forced on the first cube-odd leftover lift.

## Problem

Does every relevant first cube-odd landing of an `AboveAnchor`
leftover satisfy \(x^{3}<n^{8}\) whenever the next image is even?

## Exact statement

Let \(n\) be odd and let \(x=T_{u}(n)\) be the first odd state
with \(n^{2}\le x<n^{3}\) on an `AboveAnchor` prefix \(u\). Assume
\(T(x)\) is even. The preferred theorem was

\[
\texttt{AboveAnchor}(n,u)
\land
\texttt{LeftoverFirstLift}(n,u)
\Longrightarrow
x^{3}<n^{8}.
\]

That implication is false. The smallest leftover-generated
counterexample is

\[
n=4309,\qquad
u=\mathtt{OOEOOEOO},\qquad
x=22357213525,
\]

with \(T(x)\) even and \(x^{3}\ge n^{8}\). The long leftover
\(n=5791\) (first drop at step \(42\)) realizes the same word
and the same unsafe side.

The four named leftovers remain safe at their first lift, but
only because those itineraries keep the inherited envelope

\[
3^{o+1}<8\cdot 2^{|w|}.
\]

The first PE prefix that loses the gap is exactly
\(\mathtt{OOEOOEOO}\).

## Current literature

- mixed OE cell \(T^{2}(x)<n^{2}\Leftrightarrow x^{3}<n^{8}\) —
  **EXACT — LEAN VERIFIED** (`J-mixed-oe-eighth`)
- leftover first lifts of \(365,501,1517,6187\) sit below \(n^{8}\) —
  **COMPUTATIONALLY VERIFIED**
- later \(501\) landing \(x=48693935\) sits above \(n^{8}\) —
  **COMPUTATIONALLY VERIFIED** (`J-cube-odd-even-below-square`)
- first leftover cube-odd even lift always sits below \(n^{8}\) —
  **REFUTED** (`J-leftover-first-eighth`)
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated mixed-cell
question after the leftover / \(501\) split.

## Branch budget

```text
Mathematical target     first leftover cube-odd even lift
                        forced into x^3 < n^8?
Novelty hypothesis      leftover PE prefixes inherit B/A <= 8/3
Falsifier               leftover-generated first cube-odd x
                        with T(x) even and x^3 >= n^8
Existing machinery      odd_even_eighth_lt_sq; EnvelopeState;
                        first_odd_cube_on_anchor; 365/501/1517/6187
Maximum Phase-0 scope   leftover first hits; OOEOOEOO census;
                        envelope gap; no Q-return; no letter chain
Promotion criterion     shared AboveAnchor + first-lift lemma
Stop criterion          first lifts already fail; only x < n^3;
                        word enumeration; later landings dominate
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `AboveAnchor` alone forces the eighth cell —
  false (\(n=4309\))
- first cube-odd after an even reset forces the eighth cell —
  false (the same witness; predecessor is odd)
- leftover \(O^{a}E\) / PE structure forces the eighth cell —
  false (\(\mathtt{OOEOOEOO}\) is that architecture)
- inherited `EnvelopeState` with \(3B<8A\) forces \(x^{3}<n^{8}\) —
  **EXACT — HUMAN PROOF** (word algebra). Named leftover
  first-lift words satisfy the gap; \(\mathtt{OOEOOEOO}\) does
  not (\(2187>2048\))
- exact boundary \(x^{3}=n^{8}\) with \(x\) odd and \(T(x)\) even —
  impossible: the positive integer solutions are \(n=m^{3}\),
  \(x=m^{8}\), and then \(T(x)=m^{12}\) is odd
- first lift equals an arbitrary later odd landing —
  false (\(501\) later \(48693935\))
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.first_lift_eighth`
- Records: [juggler_first_lift_eighth.md](../research/juggler_first_lift_eighth.md),
  [juggler_first_lift_eighth.json](../research/juggler_first_lift_eighth.json)
- Tests: `tests/research/juggler_sequence/test_first_lift_eighth.py`
- Lean: none new. The mixed cell and `EnvelopeState` are reused.
  Paper A unchanged. No `sorry`.

## Conjectures

None opened.

## Counterexamples

“Every `AboveAnchor` first cube-odd even lift satisfies
\(x^{3}<n^{8}\)” is false. For \(n=4309\) the first cube-odd
state is \(x=22357213525\), the prefix is \(\mathtt{OOEOOEOO}\),
\(T(x)\) is even, and \(T^{2}(x)=57818025\ge 4309^{2}\). No
smaller odd anchor has an unsafe first even-lift.

The same word appears on the long leftover \(n=5791\),
\(x=51875574891\), first drop at step \(42\).

The complementary late landing on \(501\) remains a later
state, not a first lift.

## Formalization

No new Lean file and no first-lift primitive. The mixed cell
`odd_even_eighth_lt_sq` is unchanged. Paper A is unchanged.
No `sorry`. No halt theorem.

## Results

Classification **FIRST_LIFT_EIGHTH_REFUTED**.

Exact first-lift table (integer comparisons only):

| \(n\) | word | \(x\) | \(x^{3}-n^{8}\) | \(T(x)\) even | \(T^{2}(x)-n^{2}\) | env \(3^{o+1}-8\cdot 2^{\|w\|}\) |
| ---: | --- | ---: | ---: | --- | ---: | ---: |
| 365 | `OOEOOEOOEO` | 296551 | \(<0\) | yes | \(<0\) | \(-1631\) |
| 501 | `OOEOO` | 6812597 | \(<0\) | yes | \(<0\) | \(-13\) |
| 1517 | `OOEOOEOOEOEOO` | 43916043 | \(<0\) | yes | \(<0\) | \(-6487\) |
| 6187 | `OOEOO` | 3955183437 | \(<0\) | yes | \(<0\) | \(-13\) |
| 4309 | `OOEOOEOO` | 22357213525 | \(>0\) | yes | \(>0\) | \(+139\) |
| 5791 | `OOEOOEOO` | 51875574891 | \(>0\) | yes | \(>0\) | \(+139\) |

The mixed cell then splits the next image as already known:
safe side gives \(T^{2}(x)<n^{2}\); unsafe side does not fire
the square trap. On \(365,501,6187\) that return is odd. On
\(1517\) it is even and \(T^{3}(x)=734<1517\).

This is not a halt theorem and not a first-return section.

## Open questions

The \(\mathtt{OOEOOEOO}\) lower-cell question is answered in
[juggler_ooeooeoo_eighth.md](juggler_ooeooeoo_eighth.md): no
laboratory-scale lower cell. Do not resume a first-return
\(Q\)-map. Do not reopen W_5.

## Decision

**PARK**. The preferred shared first-lift theorem is false on
genuine leftover-generated states. The named leftovers stay
safe only by word-level envelope, and the loss is exactly the
third `OOE` block. The unsafe side is the already-named high
scale where the square trap is silent. That is not a new
shared `MinimumRelative` lemma.

Best next question: is every first cube-odd even lift of
\(\mathtt{OOEOOEOO}\) forced above \(n^{8}\), or only the
observed family?

## Publication assessment

Status: `EXPLORATORY`.

A first-lift refutation that locates the envelope gap. Not a
paper candidate and not a Juggler totality result.
