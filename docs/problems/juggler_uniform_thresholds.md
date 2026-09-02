# Juggler uniform superquadratic thresholds

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can the eventual non-contraction theorem be made uniform over all
suffixes whose formal exponent is bounded away from \(2\)?

## Exact statement

Write \(\alpha_v=3^{\#O(v)}/2^{|v|}\). Prove or refute:

\[
\forall\varepsilon>0\ \exists Q(\varepsilon)\ \forall v
\bigl(\alpha_v\ge 2+\varepsilon\land q\ge Q(\varepsilon)\land\mathrm{follows}(q,v)
\Longrightarrow T_v(q)\ge(q+1)^2\bigr).
\]

If this fails, identify the smallest extra parameter that restores a
true family statement, or exhibit an unbounded changing-suffix family.

The fixed-itinerary theorem `eventually_no_first_even_contraction` remains.
This is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Fixed-word eventual non-contraction for each \(v\) with
  \(\alpha_v>2\) — **EXACT — LEAN VERIFIED**.
- Exact short thresholds \(Q_{OO}=\{1,3\}\), \(Q_{OOO}=\{1\}\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The fixed-itinerary theorem is kept; the
\(\varepsilon\)-only upgrade is refuted.

## Branch budget

```text
Mathematical target     Does Q(ε) exist for all α_v ≥ 2+ε?
Novelty hypothesis      A uniform margin above 2 might bound Q_v
Falsifier               Superquadratic v_q with unbounded contracting q
Existing machinery      LowerPowerBound, first_even_freeze,
                        eventually_no_first_even_contraction
Maximum Phase-0 scope   q_max vs ε; D_v audit; even-tower family;
                        Lean family theorem if the collapse holds
Promotion criterion     A true family theorem, or a minimal
                        changing-suffix counterexample
Stop criterion          Generic lower-envelope theory; PowerHeight;
                        halt claim; competing with exact OO/OOO
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Short-word \(q_{\max}(v)\) grouped by \(\varepsilon_v=\alpha_v-2\) —
  **COMPUTATIONALLY VERIFIED**
- `lowerDenom` depends on letter order, not only \((r,o)\) —
  **EXACT — LEAN VERIFIED** (definitional) / **OBSERVATION**
- Discrete gap \(3^o-2^{r+1}\ge 1\) when \(\alpha_v>2\) —
  **EXACT — LEAN VERIFIED**
- Collapse family \(v_k=E^kO^{3k}\), \(q_k=2^{2^{k-1}}\), \(T=1\) —
  **EXACT — LEAN VERIFIED**
- Uniform \(Q(\varepsilon)\) — **REFUTED**
- \(Q(\varepsilon,|v|)\) exists by finiteness of itineraries of length \(r\),
  but must be at least \(2^{2^{r-1}}\) on this family — not useful
- Generic lower-envelope structure — not added
- `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.uniform_superquadratic`
- Records: [juggler_uniform_thresholds.md](../research/juggler_uniform_thresholds.md),
  [juggler_uniform_thresholds.json](../research/juggler_uniform_thresholds.json)
- Tests: `tests/research/juggler_sequence/test_uniform_superquadratic.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. The \(\varepsilon\)-only uniform statement is closed as
false.

## Counterexamples

The family

\[
v_k=E^kO^{3k},\qquad q_k=2^{2^{k-1}}
\]

is formally expanding for every \(k\ge 2\):

\[
2^{4k+1}<3^{3k}.
\]

The even tower maps \(q_k\) onto \(1\), and the odd tail stays at \(1\).
Hence \(T_{v_k}(q_k)+1<(q_k+1)^2\) with \(q_k\to\infty\). Smallest
computational witnesses: \(k=2\), \(v=\mathtt{EEOOOOOO}\), \(q=4\);
\(k=3\), \(q=16\); \(k=4\), \(q=256\).

The same collapse works for any odd tail, so the margin may even tend
to infinity: \(\alpha(v_k)=(27/16)^k\).

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `alphaMargin` / `minimal_superquadratic_margin`
- `even_tower_to_one` / `even_tower_odd_tail_contracts`
- `three_k_superquadratic`
- `changing_suffix_unbounded_contraction`

Unchanged: `LowerPowerBound`, `eventually_no_first_even_contraction`,
`oo_suffix_threshold`, `ooo_suffix_threshold`, `first_even_freeze`,
`power_bound_compensated_contracts`. No `sorry`. No ledger row. No
`uniform_first_even_threshold`. No `PowerHeight`.

## Results

Classification **CHANGING_SUFFIX_COUNTEREXAMPLE**.

The \(\varepsilon\)-only statement is false. Word-dependent
`lowerDenom` is order-sensitive (early even letters, late odd letters
produce a larger \(D_v\)), but that is not the obstruction: stronger
universal branch constants cannot restore \(Q(\varepsilon)\), because
the collapsing \(q\) makes the formal exponent irrelevant.

A length-and-margin bound \(Q(\varepsilon,r)\) is true for the trivial
reason that there are finitely many itineraries of length \(r\). On the
collapse family it must grow at least like \(2^{2^{k-1}}\). That is
not useful family-level control of unbounded-length suffixes.

Exact short-word thresholds remain: \(Q_{OO}=\{1,3\}\),
\(Q_{OOO}=\{1\}\).

This is not a termination theorem. It does not claim that every
changing positive-drift family produces large contraction cells — only
that a uniform superquadratic margin is not enough to prevent them.

## Open questions

Answered in [juggler_collapse_normalization.md](juggler_collapse_normalization.md):
excluding an *initial* even tower is not enough. Internal even runs
after an odd letter still collapse large \(q\) onto \(1\).

## Decision

**PROMOTE** the changing-suffix family theorem
`CHANGING_SUFFIX_COUNTEREXAMPLE`. Close the \(\varepsilon\)-only
uniformity hypothesis as **REFUTED**. Keep the fixed-itinerary theorem and
the exact OO/OOO classifications. Do not open a generic lower-envelope
theory. Do not claim termination.

Best next question: if suffixes that collapse a large even tower onto a
small state are excluded, does any residual uniform bound remain?

## Publication assessment

Status: `EXPLORATORY`. A local family counterexample to uniformity, not
a paper candidate and not a Juggler totality result.
