# Juggler drift-first-passage tree

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Along actual prefix-noncontracting Juggler words, do the nested
realizing sets \(A_w^{NC}\) acquire a named arithmetic constraint
that forbids indefinite continuation?

## Exact statement

For a finite actual parity itinerary \(w\) write

\[
A_w=\{n:\operatorname{follows}(n,w)\},\qquad
G(w)=2^{|w|}-3^{\#O(w)},
\]

and

\[
A_w^{NC}
=
\{n\in A_w:
G(v)\le 0\text{ for every prefix }v\preceq w\}.
\]

If \(w\) is already prefix-NC then \(A_w^{NC}=A_w\). Phase 0 asks
whether the node \((w,A_w,G(w))\) thins or prunes under
NC-preserving extension in a way that is not the itinerary itself, not
\(T\ge n\), and not the \(G\)-recurrence.

Do not claim \(\tau_+(n)<\infty\). A window-empty child is not
\(A_w=\varnothing\). A cardinality drop
\(A_{wE}\cap[2,N]\subset A_w\cap[2,N]\) is tautological. A finite
max \(\tau_+\) on a window is not a uniform bound. A larger record
is not an unbounded family.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Terras stopping-time residue trees (`terras-1976-stopping-time`)
  are **methodological guidance only**. No Collatz density theorem
  is imported.
- \(G_k>0\Longrightarrow T^k(n)<n\) — **EXACT — LEAN VERIFIED**
  (`power_bound_contracts`).
- First positive \(G\) is an even letter —
  **EXACT — HUMAN PROOF** as a \(G\)-recurrence;
  **COMPUTATIONALLY VERIFIED** on \(n\le 10^5\) except one bit-cap
  leftover.
- Prefix-NC arithmetic admissibility — closed as
  `PREFIX_NC_ARITHMETIC_COMPLEX`. Dangerous finite itineraries are
  realizable.
- Drift-crossing endpoint filtration — closed as
  `DRIFT_ENDPOINT_COMPLEX`. Endpoints of long NC prefixes do not
  collapse.
- Escape-state, corridor, odd-odd residuals, CycleDiophantine —
  closed. Odd-fourth-power and excursions — parked.

Project relationship: **extended**. The leftover after the closed
word-realizability and endpoint labs is the nested start-set of
the same prefixes. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Along actual prefix-NC chains, does A_w^{NC}
                        acquire a named arithmetic constraint that
                        forbids indefinite NC continuation?
Novelty hypothesis      Dangerous finite itineraries exist, but the nested
                        start-set (w, A_w, G) thins or prunes in a
                        way the itinerary-only and endpoint labs missed
Falsifier               The only shrinkage is tautological
                        |A_w ∩ window| decrease, or every signature
                        is the itinerary / T≥n / G-recurrence
Existing machinery      walk_until_crossing, exponent_gap,
                        prefix_noncontracting, follows_itinerary, Ival
                        pullback, even_preimage / odd_preimage_unique,
                        n=193 record, power_bound_contracts
Maximum Phase-0 scope   One probe: nested-set signatures on actual
                        prefixes; short-word structure; modest τ_+
                        hunt; persist; classify; no Lean
Promotion criterion     A named pruning rule, a compressed class
                        structure, or a structured unbounded-τ_+
                        family — not a larger record alone
Stop criterion          DRIFT_FIRST_PASSAGE_COMPLEX; machinery
                        gravity; ResidualStep / prefix-NC /
                        corridor / endpoint reopen; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Node \((w,A_w,G)\) with \(A_w\) part of the object —
  **OBSERVATION** of the representation; not a theorem
- Window-exact \(A_w\cap[2,2000]\) — **COMPUTATIONALLY VERIFIED**
  relative to the window; not the exact unbounded set
- AP modulus and residue signatures of \(A_w\cap[2,N]\) —
  **OBSERVATION**; they do not compress below the itineraries
- Named thinning versus tautological subset —
  **OBSERVATION**; named-thinner hits are residue/modulus
  artefacts of longer prefixes, not a pruning rule
- First-passage start sets \(C_{k,o}\) —
  **OBSERVATION**; large classes are just evens
  (\(C_{1,0}\)) and odds that cross on `OE` (\(C_{2,1}\))
- Short-word Ival pullback as a signature, never as emptiness —
  **OBSERVATION**; empty-over-image is already **REFUTED** as
  unrealizable
- \(n=193\), \(\tau_+=70\) — **COMPUTATIONALLY VERIFIED**
  regression; last NC state \(6498\)
- \(n=78901\), \(\tau_+=253\) — **COMPUTATIONALLY VERIFIED**
  hunt record; not an unbounded family
- Uniform \(\tau_+\) bound from a finite hunt — not claimed
- Infinite prefix-NC arithmetic branch — not claimed
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.drift_first_passage`
- Records: [juggler_drift_first_passage.md](../research/juggler_drift_first_passage.md),
  [juggler_drift_first_passage.json](../research/juggler_drift_first_passage.json)
- Dataset: `data/research/juggler/drift_first_passage/`
- Tests: `tests/research/juggler_sequence/test_drift_first_passage.py`
- Nested-set window \(n=2..2000\); \(\tau_+\) hunt \(n=2..10^5\);
  short-word pullback \(k\le 8\)
- The Research Engine control layer is not modified
- `ResidualStep` is not extended. Prefix-NC admissibility, the
  corridor, escape-state, endpoint filtration, and odd-fourth-power
  are not reopened
- No Lean file

## Conjectures

None opened.

## Counterexamples

- “Nested \(A_w^{NC}\) signatures compress while words proliferate”:
  after length 4, compression stays near \(1\). At length \(3\)–\(4\)
  the drop to \(0.5\) / \(0.33\) is the tiny combinatorial prefix-NC
  language, not a start-set law.
- “A cardinality drop is a pruning rule”: \(1072\) window-empty
  children and \(10\) tautological subsets; \(259\) named-thinner
  hits keep modulus \(2\) and only lose residues.
- “\(\tau_+\le 70\)”: **REFUTED** as a window bound.
  \(n=78901\) has \(\tau_+=253\). That is not
  \(\tau_+(n_j)\to\infty\) as a family.
- “Late first-passage starts occupy a thin residue class”:
  \(C_{k,o}\) start signatures remain all odds (modulus \(2\))
  whenever the class is large.
- Hunt leftover \(n=48443\) hit the \(2\cdot 10^6\)-bit cap still
  prefix-NC. That cutoff is not a bound \(L\) and not a
  non-terminator.

## Formalization

None added. Envelope and `power_bound_contracts` already live in
`formal/Problems/Engine/FloorPower.lean`. No
`DriftFirstPassage.lean`. `ResidualChain.lean` is not rewritten.
No `sorry`. No ledger row.

## Results

Classification **DRIFT_FIRST_PASSAGE_COMPLEX**.

On \(2\le n\le 2000\), all \(1999\) starts cross. Unique
prefix-NC words: \(1318\) (\(1307\) mixed). Extension tags:
empty \(1072\), same \(1048\), strict subset \(10\), named
thinner \(259\). Depth compression is \(1\) after the first
four lengths. Least-constrained mixed prefixes are the short
words `OOE` (\(|A|=254\)), `OOEO` (\(130\)), `OOOE` (\(117\)).
First-passage classes \(C_{k,o}\) are the even starts
(\(\tau_+=1\)) and the odd `OE` / short mixed crossings; they
are not a new arithmetic filtration of \(n\).

Hunt \(2\le n\le 10^5\): \(99998\) crossed, one bit-cap leftover
(\(n=48443\)). New records include \(n=78901\), \(\tau_+=253\),
peak bits \(1234916\); \(n=34175\), \(\tau_+=183\);
\(n=28719\), \(\tau_+=156\). The old regression
\(n=193\), \(\tau_+=70\), last NC \(6498\) still holds. A
larger record is not an unbounded family and not
\(\tau_+<\infty\).

No Lean file. No halt theorem.

## Open questions

The missing theorem is unchanged: does every \(n\ge 2\) realize a
finite prefix with \(3^o<2^k\)? Nested start-set signatures do
not supply the obstruction. Do not reopen endpoint filtration,
prefix-NC word admissibility, the corridor, ResidualStep, or
odd-fourth-power. Do not build a giant formal tree.

## Decision

**CLOSE** the drift-first-passage branch as
`DRIFT_FIRST_PASSAGE_COMPLEX`. The node \((w,A_w,G)\) is the
right object, but on actual prefixes the nested window sets do
not prune or compress in a named way. Isolated larger
\(\tau_+\) records change the known delay, not the induction.
Do not add Lean. Do not claim \(\tau_+<\infty\). Do not claim
termination.

Best next question: a genuine existence argument that every
\(n\ge 2\) eventually takes an even step in the window
\(2^{k-1}\le 3^{o_{k-1}}<2^k\), not another start-set census
and not a formal tree of the \(1318\) window words.

## Publication assessment

Status: `EXPLORATORY`. A negative nested-set result plus a larger
computational delay record, not a paper candidate and not a
Juggler totality result.
