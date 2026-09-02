# Juggler PE preimage cylinders

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Does the predecessor relation \(x\xrightarrow{w}y\) constrain the next
square-root floor of \(y\) in a way that \(y\) alone does not?

## Exact statement

An itinerary cylinder is

\[
\mathcal C_w=\{y:\exists x,\ \text{\texttt{follows}}(x,w)\wedge T_w(x)=y\}.
\]

Restrict to expanding residual overshoots \(x<y\) with \(x,y\) odd.
The next landing is \(z=T(y)=\lfloor y^{3/2}\rfloor\), equivalently
\(z^2\le y^3<(z+1)^2\). Persistence of the next residual is
\(z\) odd.

\(T(y)\) is a function of \(y\). The only possible new mechanism is
that \(\mathcal C_w\) is a thin subset of odd integers whose cubes
avoid one parity of square cells, or that \((x,w)\) forbids a next
residual word class.

Do not assume such a restriction exists. This says nothing about
totality.

## Current literature

- Inverse-floor cells —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- `follows` / `image` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary`.
- Landing \(\theta\) unrestricted —
  **CLOSE** as `LANDING_THETA_UNRESTRICTED`.
- \(v_2(\rho)\) is \(y\bmod 8\) —
  **CLOSE** as `LANDING_VALUATION_IS_Y_MOD_8`.
- Residual-state finite quotients need the integer itself —
  **CLOSE** as `RESIDUAL_STATE_NEEDS_X`.
- Expanding grammar is persistence —
  **CLOSE** as `EXPANDING_GRAMMAR_IS_PERSISTENCE`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Does (x,w) constrain T(y) mod 2 or the next
                        residual grammar in a way y alone does not?
Novelty hypothesis      The predecessor cylinder C_w is a proper
                        subset whose next square cells, or next
                        words, are restricted
Falsifier               Every well-sampled PE word realises both
                        next parities; same residue/θ still splits
Existing machinery      inverse-floor cells, follows/image, PE
                        walker, landing θ, two-block OOE chain
Maximum Phase-0 scope   Census C_w by word; opposite-parity pairs;
                        package the inverse word relation; one
                        Lean split witness. No halt
Promotion criterion     An itinerary forces next parity or forbids a
                        next residual class, not from y alone
Stop criterion          Falsifiers A–E; cylinder is y; machinery
                        gravity
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `itineraryCylinder` / `itinerary_cylinder_exact` / letter cons —
  **REPARAMETERIZATION** of `follows` and `image`
- `squareCylinder` / `square_gap_exact` —
  **REPARAMETERIZATION** of the inverse-floor cells and
  `localDefect`
- A PE word \(w\) forces \(T(y)\) odd or even —
  **REFUTED**
- Same \(y\bmod 8\) and similar \(\theta\) lock the next parity —
  **REFUTED**
- Predecessor history forbids a next residual class —
  **REFUTED** on the scanned window
- Infinite PE orbit — not claimed

## Experiments

Cheap cylinder census, not a new raw search.

- Expanding overshoots \(n\le 4000\): 706 blocks, 17 word types.
  Every word with at least 8 samples realises both next parities.
  `OOE` is \(161\) odd / \(152\) even, entropy \(\approx 1\).
  \(\theta\) on both classes occupies essentially \((0,1)\). All
  odd residues modulo \(8\) appear on both sides.
- Same-word opposite-parity pairs with matching residue and
  \(\theta\): \(3461\xrightarrow{\mathrm{OOE}}9585\) (\(T\) even,
  \(\theta\approx 0.382\), \(y\equiv 1\pmod 8\)) versus
  \(3803\xrightarrow{\mathrm{OOE}}10657\) (\(T\) odd,
  \(\theta\approx 0.382\), \(y\equiv 1\pmod 8\)). Next words
  `OEE` versus `OOE`.
- The certified chain
  \(365\xrightarrow{\mathrm{OOE}}763\xrightarrow{\mathrm{OOE}}1749
  \xrightarrow{\mathrm{OOE}}4447\) exits by
  \(4447\xrightarrow{\mathrm{OOE}}12707\) with \(T(12707)\) even.
  Both \(763\) and \(12707\) are \(3\pmod 8\).
- Length-7 runs at \(11681\), \(14237\), \(15343\), \(27623\)
  likewise exit by leaving odd-odd, not by a cylinder law.

Tests: `tests/research/juggler_sequence/test_preimage_cylinders.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “The `OOE` cylinder forces the next landing parity.” False:
  \(3461\to 9585\) even and \(3803\to 10657\) odd,
  **EXACT — LEAN VERIFIED**.
- “Matching residue plus \(\theta\) recovers the missing history.”
  False: both endpoints above are \(1\pmod 8\) with
  \(\theta\approx 0.382\).
- “A well-sampled PE word forbids a next residual class.” False:
  `OOE` continues as persistent `OOE` and as non-persistent `OEE`.
- “Long PE runs occupy a restricted next cylinder.” False: they
  exit by an ordinary odd-to-even landing.

## Formalization

`formal/Problems/Juggler/PreimageCylinders.lean`, after
`LandingValuation`. No `sorry`. No halt theorem. No predecessor
state machine.

## Results

- The inverse word relation is `follows` plus `image`.
- Each letter is the existing inverse-floor cell.
- \(T(y)\) is a function of \(y\). History can only thin the set
  of attainable \(y\).
- That set still realises both next parities for every
  well-sampled PE itinerary, including at fixed residue and \(\theta\).

## Open questions

The leftover is still whether an odd-to-odd residual chain can
continue indefinitely. Predecessor cylinders do not decide the
next landing. Iterated odd-landing sets are forward orbits of
\(T\); see
[juggler_odd_landing_sets.md](juggler_odd_landing_sets.md).
Do not reopen residues, \(\theta\), valuation, or
expanding-word grammar.

## Decision

**CLOSE** the predecessor-cylinder attack as
`PREIMAGE_CYLINDER_IS_Y`. The exact inverse of a finite itinerary is
the existing itinerary relation. The cylinder of a PE word does
not restrict the next square cell or the next residual grammar
beyond the integer \(y\). Do not claim termination.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. A negative cylinder-history result and a
thin inverse-word packaging, not a paper candidate and not a
Juggler totality result.
