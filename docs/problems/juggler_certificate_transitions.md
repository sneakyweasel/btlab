# Juggler certificate-transition closure

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It
iterates the parked harvest certificates \(\{E,OE,OOEE,R\}\) from
each first-descent landing. It is **not** a Word Atlas recensus,
not a new atlas language tag, not a certificate automaton, not a
Research Engine control-layer experiment, not Paper A or Paper B,
and not a claim that every positive integer reaches 1.

## Problem

Can every infinite `AboveAnchor` trajectory be represented as an
infinite sequence of existing certificate states whose transitions
force `FiniteProgress` or an already-controlled recurrence — or is
that layer only a 4-letter label on first descent?

## Exact statement

At a state \(x\ge 2\), the **certificate** is the first realized
word \(w\) with \(T_{|w|}(x)<x\), labelled

- \(E\) if \(w=E\) — `even_finiteProgress`
- \(OE\) if \(w=OE\) — `odd_even_finiteProgress`
- \(OOEE\) if \(w=OOEE\) — `finiteProgress_of_imageLt`
- \(R\) otherwise — `finiteProgress_of_imageLt`

The iterator continues from the landing \(T_{|w|}(x)<x\). Absence
of a transition under a bound is `NOT OBSERVED WITHIN SEARCH BOUND`.
This is not a halt theorem.

Residual does **not** remain `AboveAnchor` after the leftover word
fires. The leftover word is already a descent. Taken literally,
“until `FiniteProgress`” has depth 1 for every start. The Phase-0
object is therefore the **labelled descent chain**, not a new
unresolved residual state.

## Current literature

- Uniform short certificates \(E\) / \(OE\) —
  **EXACT — LEAN VERIFIED**
- Any realized drop is `FiniteProgress` —
  **EXACT — LEAN VERIFIED** (`finiteProgress_of_imageLt`)
- Leftover-class harvest —
  **PARK**
  ([juggler_certificate_harvest.md](juggler_certificate_harvest.md))
- \(Q\)-blocks / excursion transfer —
  **CLOSE**
- Every start reaches 1 — not claimed

Project relationship: **extended**. Composition of existing
certificates. Do not reopen source descent or the word language.

## Branch budget

```text
Mathematical target     After a residual first certificate, does the
                        next semantic event close under {E, OE, OOEE, R}
                        with a finite residual depth, or is the layer
                        only a 4-letter label on first descent / Q-blocks?
Novelty hypothesis      Residual→next has missing edges or a bounded
                        τ_R, giving a certificate calculus beyond T<n.
Falsifier               Every first descent is already FiniteProgress;
                        the first residual word is the Q-itinerary;
                        R→R is a decreasing landing quotient.
Existing machinery      first_certificate; trajectory_until_drop; q_blocks;
                        even_finiteProgress; odd_even_finiteProgress;
                        finiteProgress_of_imageLt
Maximum Phase-0 scope   CPU iterator on n≤2e4 plus labs; support
                        matrix; τ_R; SCCs; lab sequences; Q-block
                        identity. No Lean, no GPU, no 10^9 recensus.
Promotion criterion     A theorem-backed missing edge, bounded τ_R
                        with a proof idea, or an absorbing residual law
Stop criterion          Relabel of Q / T<n; CertificateAutomaton;
                        source-descent restated
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- first-descent certificate label —
  **COMPUTATIONALLY VERIFIED** as a bounded observation
- transition support \(M_{ij}\) —
  **OBSERVATION**
- residual depth \(\tau_R\) —
  **OBSERVATION**
- Q-itinerary identity of the first word —
  **COMPUTATIONALLY VERIFIED** on \(n\le 2\cdot 10^4\)
- certificate automaton — not added
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.certificate_transitions`
- Records: [juggler_certificate_transitions.md](../research/juggler_certificate_transitions.md),
  [juggler_certificate_transitions.json](../research/juggler_certificate_transitions.json)
- Dataset: `data/research/juggler/certificate_transitions/`
- Tests: `tests/research/juggler_sequence/test_certificate_transitions.py`

Science window: \(n\le 2\cdot 10^4\) plus laboratories
\(37,69,89,365,501,1517,6187\). Tests use \(n\le 400\). No Lean.
No GPU. No \(10^9\) recensus.

## Conjectures

None opened.

## Counterexamples

- “a residual first certificate remains `AboveAnchor` and is not
  yet `FiniteProgress`” — every realized leftover word is already
  a first descent, hence `finiteProgress_of_imageLt`.
- “the first residual certificate is a new object, not a \(Q\)-block
  itinerary” — on every start \(2\le n\le 2\cdot 10^4\), the first
  certificate word equals `word_of_path(trajectory_until_drop(n))`.
- “some certificate transition is impossible” — all 16 edges
  \(C_i\to C_j\) occur in the window
  (`NOT OBSERVED WITHIN SEARCH BOUND` for a missing edge).
- “\(R\to R\) is a numerical cycle” — landings are strictly
  decreasing. The residual-depth record \(1891\) is
  \(1891\to 895\to 309\to 37\to 8\to 2\to 1\).
- “a pair of certificates forces a unique third” — no pair
  \(C_iC_j\) has a unique next class on \(n\le 4000\).

## Formalization

None added. Existing `even_finiteProgress`,
`odd_even_finiteProgress`, `finiteProgress_of_imageLt`, and
`ReturnBelow` already contain the identities. No
`CertificateTransition.lean`. No `CertificateAutomaton.lean`.
No `sorry`. Paper A is unchanged.

## Results

Classification **CERTIFICATE_TRANSITIONS_CLOSED**.

Science window: \(2\le n\le 2\cdot 10^4\) (\(19\,999\) starts)
plus the named laboratories
(`COMPUTATIONALLY VERIFIED` as a bounded observation).

### 1. Certificate definitions

| \(C\) | Lean output | meaning |
|---|---|---|
| \(E\) | `even_finiteProgress` | even \(n\ge 2\); landing \(\lfloor\sqrt n\rfloor<n\) |
| \(OE\) | `odd_even_finiteProgress` | odd-to-even; landing \(T^2(n)<n\) |
| \(OOEE\) | `finiteProgress_of_imageLt` | first descent is exactly `OOEE` |
| \(R\) | `finiteProgress_of_imageLt` | leftover first descent |

First-certificate counts:
\(E=10000\), \(OE=4989\), \(OOEE=1225\), \(R=3785\).
Q-itinerary identity on first words: true for all \(19\,999\)
starts.

### 2. Transition support

\[
M_{ij}=1\quad\text{for every pair }C_i,C_j\in\{E,OE,OOEE,R\}.
\]

No transition is impossible in-window. An absent edge would have
been recorded as `NOT OBSERVED WITHIN SEARCH BOUND`, not as a
prohibition theorem.

### 3. Residual-to-residual transitions

\(R\to R\) occurs \(1113\) times. From a residual start:
Type A (next is non-\(R\)) \(3073\); Type B (next is \(R\))
\(712\). Residual outgoing counts:
\(R\to E=11677\), \(R\to OE=2733\), \(R\to OOEE=418\),
\(R\to R=1113\).

### 4. Maximum residual depth

\(\max\tau_R=4\) at \(n=1891\)
(\(R,R,R,R,E,E\); landings \(895,309,37,8,2,1\)).
The same maximum is the longest interior \(R\)-run.
Growth: \(\max\tau_R=2\) on \(n\le 200\), then \(4\) on
\(n\le 2000\) and still \(4\) on \(n\le 2\cdot 10^4\).
Nine starts have \(\tau_R=4\). Maximum certificate depth
\(d_C=9\). This is not a bounded-\(\tau_R\) theorem.

### 5. SCC structure

One SCC: \(\{E,OE,OOEE,R\}\). There is no residual-only
nonterminal SCC. Numerical landings strictly decrease, so the
semantic SCC is a Section-12A quotient artifact, not a numerical
cycle (Falsifier A in the form “unbounded numerical growth inside
an SCC” does not arise).

### 6. Laboratory certificate sequences

| \(n\) | certificates | \(\tau_R\) | first word |
|---|---|---|---|
| \(37\) | \(R\,E\,E\) | 1 | `OOOOEOOOEEOOEEE` |
| \(69\) | \(R\,E\,R\,E\) | 1 | `OOEOOEE` |
| \(89\) | \(R\,E\,E\,E\) | 1 | `OOEOOEOE` |
| \(365\) | \(R\,E\,OOEE\,E\) | 1 | `OOEOOEOOEOOEOEE` |
| \(501\) | \(R\,E\,OOEE\,E\) | 1 | `OOEOOOEOOEEOOEOOEOOEOEE` |
| \(1517\) | \(R\,E\,OE\,OE\,E\,E\) | 1 | `OOEOOEOOEOEOOOEE` |
| \(6187\) | \(R\,OE\,OE\,E\,OE\,E\,E\) | 1 | `OOEOOOEOOEEOE` |

Every laboratory has \(\tau_R=1\). After the first residual,
\(365\) and \(501\) share the suffix \(E\,OOEE\,E\) and merge at
landing \(34\). The residual-depth record \(1891\) lands on
laboratory \(37\).

### 7. Absorbing states

None in the transition graph: every class, including \(E\) and
\(OE\), has outgoing edges to all four classes. Semantically,
every certificate including \(R\) is already `FiniteProgress` at
the current state. There is no residual absorbing-exit law
beyond “the leftover word drops.”

### 8. Strongest candidate composition rules

None. On \(n\le 4000\), no pair \(C_iC_j\) forces a unique next
certificate. Typical next class after any pair is \(E\) (share
roughly \(0.5\)–\(0.88\)), which is only the evenness of a
smaller landing.

### 9. Strongest falsifiers

- **C (layer is \(Q\)-blocks):** first certificate word equals
  the first-descent \(Q\)-itinerary on the whole window.
- **every descent is `FiniteProgress`:** `finiteProgress_of_imageLt`
  already applies to \(R\).
- **D (free concatenation at this alphabet):** all 16 edges
  occur; residual sequences are not restricted by the 4-letter
  labels.
- **A** fails in the stated form: landings decrease, so the SCC
  cannot carry unbounded numerical growth.
- **B** does not fire as rapid unbounded growth in-window
  (\(\tau_R\) plateaus at \(4\) from \(2\cdot 10^3\) to
  \(2\cdot 10^4\)), and is not needed: C already closes the
  branch.
- **E** would fire if \(T<n\) were relabelled as a new theorem.
  It is recorded as `REPARAMETERIZATION`, not promoted.

### 10. Classification

**CLOSE** as `REPARAMETERIZATION`. The certificate iterator is a
4-letter label on successive first descents. It does not generate
a closed semantic transition system beyond \(T<n\) and the
existing uniform certificates.

## Open questions

None from certificate-transition composition. Do not write
`CertificateAutomaton.lean`, do not recensus at \(10^9\), and
do not refine the SCC with a numerical coordinate. The leftover
hole is still a cube cell without a square cell.

## Decision

**CLOSE**. Every first descent, including residual, is already
`FiniteProgress`. The first certificate word is the \(Q\)-itinerary.
\(R\to R\) is a strictly decreasing landing quotient. All 16
transitions occur. No pair composes to a forced third certificate.
A branch whose statements are all `KNOWN` or `REPARAMETERIZATION`
is a close.

Best next question: none from certificate-transition closure.

## Publication assessment

Status: `EXPLORATORY`. A certificate-composition census, not a
paper candidate and not a Juggler totality result.
