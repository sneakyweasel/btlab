# Juggler nested anchor cylinders

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
the closed formal-versus-realized itinerary census, not a parity-balance
reopen, not a new atlas language tag, not an automaton, not Paper A,
and not a claim that every positive integer reaches 1.

Finite history realizability is closed: every
`prefixNoncontracting` itinerary of length \(\le 20\) is atlas
`REALIZABLE`, and apparent `AboveAnchor` holes below \(10^6\)
are hold-out unstable. This phase measures a different object:
the nested integer support of a fixed history.

## Problem

Can one fixed integer anchor realize an arbitrarily deep nested
sequence of `AboveAnchor` prefixes, or does the arithmetic
support of a prefix migrate upward or shrink as the prefix grows?

## Exact statement

For a window \(X\) and an itinerary \(w\) write

\[
R_w(X)=\{n\le X:\operatorname{follows}(n,w)\},
\]

\[
A_w(X)=\{n\le X:\operatorname{AboveAnchor}(n,w)\}.
\]

These are distinct. \(A_{wv}(X)\subseteq A_w(X)\). Phase 0
follows the exact prefix chains of the named hard starts and
asks whether, in a scale-stable way,

\[
N_{\min}(w_k)\to\infty
\qquad\text{or}\qquad
|A_{w_k}(X)|/X\to 0
\]

along those branches, or whether support stays a positive
fraction of \(X\) / merely scale-shifts.

Absence of \(n\le X\) is `NOT OBSERVED WITHIN SEARCH BOUND`,
never \(A_w=\varnothing\).

This is not a halt theorem.

## Current literature

- Shared formal language is `prefixNoncontracting` —
  **CLOSE** as `PARITY_BALANCE_CLOSED`
- Formal versus AAn itinerary gap —
  **CLOSE** as `FORMAL_REALIZED_GAP_CLOSED`
  ([juggler_formal_realized_gap.md](juggler_formal_realized_gap.md))
- Existential PE grammar —
  **CLOSE** as `JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`
- Word atlas \(k\le 20\), \(n\le 10^8\) — **PARK** as machinery
- Landing-image prefix trie — **PARK**; \(Y_w\) is the image
  set, not the start set \(A_w\)
- Residual state needs the landing integer —
  **CLOSE** as `RESIDUAL_STATE_NEEDS_X`
- Cube cell without a square cell — a **separate** leftover
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated diagnostic
after the itinerary-language close.

## Branch budget

```text
Mathematical target     Along hard AboveAnchor prefix chains,
                        does |A_w(X)| decay and/or N_min(w)
                        grow in a scale-stable way, or is
                        support full-dimensional / scale-shifting?
Novelty hypothesis      Every finite history occurs somewhere,
                        but nested A_{w_k} shrinks or migrates
                        so no fixed anchor supports an infinite
                        branch.
Falsifier               Deep hard prefixes retain a positive
                        fraction of X at two scales; N_min is
                        the trivial envelope/scale bound;
                        hard branches are no more isolated
                        than generic max-|A_w| prefixes.
Existing machinery      walk_aa; above_anchor; prefixNoncontracting;
                        leftover laboratories; formal_realized_gap
                        scan; landing_image.components
Maximum Phase-0 scope   One-pass R_w / A_w counts at X=1e5 and
                        1e6, k<=20; hard-chain C-ratios, N_min,
                        M_k vs M_k^hard; first bottleneck;
                        interval counts only on hard prefixes
                        at X=1e5. No Lean, no automaton, no
                        atlas language tag, no X=1e8 recensus.
Promotion criterion     Scale-stable N_min growth along every
                        candidate infinite branch, or scale-stable
                        finite/exponential decay of |A_w| with
                        a simple arithmetic explanation.
Stop criterion          Positive-density support at larger X;
                        N_min only the envelope scale; chaotic
                        geometry; hard starts not isolated;
                        finite-window extinction is hold-out
                        scale-shift; the only fact is
                        prefixNoncontracting.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(R_w(X)\) versus \(A_w(X)\) —
  **COMPUTATIONALLY VERIFIED** as a bounded observation
- Nested \(A_{wv}\subseteq A_w\) —
  **KNOWN** from `aboveAnchor_of_prefix`
- \(N_{\min}(w)\) and \(C(w\to wv;X)\) along hard chains —
  **COMPUTATIONALLY VERIFIED** in-window
- Scale-stable isolation or decay of hard cylinders —
  **REFUTED** at the Phase-0 window: \(M_k\sim X/2^k\),
  \(M_k^{\mathrm{hard}}\) tracks \(M_k\), and short leftovers
  keep a scale-stable positive fraction
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.anchor_cylinders`
- Records: [juggler_anchor_cylinders.md](../research/juggler_anchor_cylinders.md),
  [juggler_anchor_cylinders.json](../research/juggler_anchor_cylinders.json)
- Dataset: `data/research/juggler/anchor_cylinders/`
- Tests: `tests/research/juggler_sequence/test_anchor_cylinders.py`

Science window: \(k\le 20\), \(X\in\{10^5,10^6\}\), hard
laboratories \(37,69,89,365,501,1517,6187,329,33391\). Tests
use \(k\le 8\), \(X\le 400\). No CLI. No Lean.

## Conjectures

None opened.

## Counterexamples

- “Hard `AboveAnchor` prefixes occupy a visibly thinner
  subset of \(A_w(X)\) than generic length-\(k\) words.”
  False: \(M_k^{\mathrm{hard}}\) tracks \(M_k\)
  (`hard_thinner_max` is false). At \(X=10^6\) the tails are
  \(4\) versus \(7\).
- “Deep uniqueness of \(501\) or \(33391\) is a hard-branch
  law.” False: \(M_{20}(10^6)=7\), so uniqueness at
  \(k\sim\log_2 X\) is the generic occupancy of one length-\(k\)
  itinerary (`NOT OBSERVED WITHIN SEARCH BOUND`).
- “Every hard laboratory has vanishing density as \(X\)
  grows.” False: \(69\) and \(89\) keep scale-stable fractions
  \(\approx 0.016\) and \(\approx 0.008\) from \(X=10^5\) to
  \(X=10^6\).
- “\(N_{\min}(w_k)\) along a hard chain is a new obstruction
  independent of the laboratory start.” False: for every named
  lab except \(6187\), the last \(N_{\min}\) equals the lab
  itself; \(6187\) shares its prefix with \(501\).
- “Some extra `AboveAnchor` word sits outside
  `prefixNoncontracting`.” False: extra-AA-not-formal count is
  \(0\).

## Formalization

None added. Existing `AboveAnchor`, `aboveAnchor_of_prefix`,
and `prefixNoncontracting` already contain the identities.
No `AnchorCylinder.lean`. No `sorry`. Paper A is unchanged.

## Results

Classification **ANCHOR_CYLINDER_CLOSED**.

Science window \(k\le 20\), \(X\in\{10^5,10^6\}\), hard
laboratories \(37,69,89,365,501,1517,6187,329,33391\)
(`COMPUTATIONALLY VERIFIED` as a bounded observation):

- \(R_w\) and \(A_w\) stay distinct: `OE` has \(A=0\) and
  \(R=250073\) at \(X=10^6\); `OOE` has
  \(A=R=124954\) and \(N_{\min}=5\). Extra `AboveAnchor` words
  outside `prefixNoncontracting` are \(0\).
- Generic max occupancy is \(M_k(10^6)=
  [499999,249926,\ldots,9,7]\), the \(\sim X/2^k\) count of
  one length-\(k\) word. Hard-chain max occupancy tracks it:
  \(M_k^{\mathrm{hard}}\) ends at \(4\), not a thinner family.
- Short leftovers keep a scale-stable positive fraction:
  \(69\) has \(|A|=15768\) (\(S=6\), frac \(\approx 0.016\))
  at both windows; \(89\) has \(|A|=7881\) (\(S=7\), frac
  \(\approx 0.008\)).
- Longer laboratories shrink to the window scale, not a new
  law: \(37\) and \(365\) have \(|A|\approx 50\) at length
  \(14\); \(501\) and \(33391\) are unique at \(k=20\);
  \(329\) has four anchors. The only recorded bottleneck is
  \(501\) at \(k=18\) with \(C\approx 0.22\).
- \(N_{\min}\) along a chain equals the laboratory start
  (or \(501\) for the \(6187\) prefix). A start \(n_*\)
  remains in its own nested \(A_{w_k}\) until it drops; that
  is tautological, not a halt mechanism.

This is the positive-density falsifier on short leftovers
and the “hard branches are no more isolated than generic
\(M_k\)” falsifier. Late \(O(1)\) support is
\(k\sim\log_2 X\), not a uniqueness theorem.

## Open questions

None from nested start-set occupancy at this window. Do not
recensus at \(X=10^8\), do not build an interval automaton,
and do not treat \(A_w(X)=\varnothing\) as \(A_w=\varnothing\).
The leftover residual is still the cube cell without a
square cell, not a cylinder-support law.

## Decision

**CLOSE**. Nested \(|A_w(X)|\) is the generic
\(\sim X/2^k\) occupancy of a length-\(k\) word. Hard
laboratories are not thinner than \(M_k\). Short leftovers
keep a scale-stable positive fraction. Late uniqueness
coincides with the window scale \(k\sim\log_2 X\).
\(N_{\min}\) is the laboratory start, not an independent
growth law. Finite histories still occur somewhere; one
scanned anchor realizing its own prefix until drop is
already `aboveAnchor_of_prefix`. A branch of that kind is a
close.

Best next question: none from nested start-set occupancy.
The leftover hole is still a cube cell without a square cell.

## Publication assessment

Status: `EXPLORATORY`. A bounded start-set census, not a paper
candidate and not a Juggler totality result.
