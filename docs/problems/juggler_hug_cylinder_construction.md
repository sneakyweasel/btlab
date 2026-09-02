# Juggler hug-cylinder construction (backward freedom flow)

Status: **EXPLORATORY**

Follow-up to the hug-cylinder realization branch's recorded question.
It is **not** a \(K_3\) attack, not a reopen of the closed
mechanical-lift branch (that was exact single-cell inverse lifts for
cycles; `empty_ooe` was death of cell-following, not of counting),
not a halt theorem, and not a claim that hug cylinders are proved
nonempty at every depth.

## Problem

Is hug-cylinder nonemptiness provable at **every** depth by an
explicit preimage-cylinder construction (existence, not density) —
turning the fixed-depth close of the realization branch from a scan
into a theorem?

## Exact statement

The hug itinerary factors into `OE`/`OOE` blocks: O-runs are \(\le 2\)
because \(2\log_2(3/2)>1\), E-runs are exactly \(1\). The
E-preimage of a single valid state \(y\) is the full interval
\([y^2,(y+1)^2)\), so backward freedom regenerates every block.
Counting harvestable suffix-realizers \(V\) at level scale
\(X=2^\lambda\):

- an E-regeneration multiplies \(V\) by \(\sim X^{1/2}\)
  (\(+\lambda/2\) bits);
- an O-pullback multiplies \(V\) by \(\sim\frac13 X^{-1/3}\)
  (\(-\lambda/3-\log_2 3\) bits).

Per block the flow is **strictly positive**: `OE` nets
\(+5\lambda/12\) bits, `OOE` nets \(+7\lambda/24\) bits. The
induction's remaining analytic step is a short-interval
depth-\(\le 2\) hit on odd-\(x\) windows of length
\(\sim\frac23 X^{1/3}\) — above the van der Corput threshold
\(X^{1/4}\), not the \(K_3\) wall (depth \(5\), deterministic
shift). Depth \(1\) is now a theorem: there is \(X_0\) such that
every interval of \(\bigl\lfloor\tfrac23 X^{1/3}\bigr\rfloor\)
consecutive odd integers in \([X,2X]\) meets both parities of
\(\lfloor x^{3/2}\rfloor\) (`J-hug-flow-window-depth-one`).
Depth \(2\) is still open. The existence claim
\(C_L\ne\emptyset\) for every \(L\) is not a theorem.

## Current literature

- Hug itinerary block grammar `OE`/`OOE` — **EXACT — LEAN VERIFIED**
  (`WalkChargeItineraries.lean` hug rule; the grammar is the
  \(2\log_2(3/2)>1\) window arithmetic).
- Hug cylinder filled to depth \(28\) at the \(2^{-L}\) rate on
  \([3,2\cdot 10^8]\) — **COMPUTATIONALLY VERIFIED**
  (realization branch, CLOSE).
- Long-interval parity equidistribution of nested floor powers to
  depth \(\le 4\) with power savings — **EXACT — HUMAN PROOF**
  (Paper B). Depth \(1\) on the working window \(H\asymp X^{1/3}\)
  is the short-interval localization of Paper B Theorem 4.1,
  recorded as `J-hug-flow-window-depth-one`. The interval-iteration reading of depth \(2\) is CLOSE
  (`J-hug-flow-image-gap`). A sparse-set depth-\(2\) analogue
  of Paper B is not opened.
- Exact single-cell inverse hug lifts die at empty `OOE` cells —
  mechanical-lift branch, CLOSE (`empty_ooe`); consistent with the
  \(w^{-1/9}\) per-anchor hazard measured here, and superseded by
  counting over regenerated intervals.

Project relationship: **PROJECT-SPECIFIC** exponent ledger on top of
KNOWN van der Corput / Erdős–Turán machinery. Depth \(1\) is
**EXACT — HUMAN PROOF** (KNOWN method, PROJECT-SPECIFIC window).
Interval-ET depth \(2\) is CLOSE. A sparse-set depth-\(2\)
statement is not opened.

## Branch budget

```text
Mathematical target     is C_L != empty provable for every L by
                        backward induction - concretely: is the
                        freedom flow positive per block, and do the
                        parity hits the induction needs live inside
                        provable windows?
Novelty hypothesis      the block grammar bounds the induction's
                        analytic needs at depth <= 2 on windows
                        X^{1/3} - above the vdC threshold, below the
                        K3 wall; nobody priced the backward flow
Falsifier               generator-chain / pullback death at generic
                        positions, or parity runs exceeding the
                        X^{1/3} working window
Existing machinery      hug letters (Lean rule), gmpy2 exact roots,
                        Paper B depth<=4 (long-interval), the
                        realization scan to depth 28
Maximum Phase-0 scope   one probe: parity-run census 2^20..2^40,
                        OE-pullback survivor census, OOE two-stage
                        hazard census (generic + resonant offsets);
                        no Lean, no Paper edits, no deep search
Promotion criterion     flow confirmed at all scales and a provable
                        route for the window lemma
Stop criterion          flow anomaly at generic positions, or the
                        route reducing to K3-strength statements
```

## Balanced-ternary formulation

Not BT-specific; the flow exponents are the shared \(2\)–\(3\)
multiplicative data (the block mix that makes the scale exponent
neutral is the hug rotation itself).

## Why BT may be relevant

Only through the shared \(2\)–\(3\) structure; no representation
claim.

## Candidate operations / invariants

- **Freedom-flow ledger** (per backward block, at level scale
  \(2^\lambda\)): E-regeneration \(+\lambda/2\) bits, O-pullback
  \(-\lambda/3-\log_2 3\) bits; `OE` \(+5\lambda/12\), `OOE`
  \(+7\lambda/24\) (**OBSERVATION**, exponent arithmetic confirmed
  by census).
- **Working window**: parity hits needed on odd-\(x\) windows of
  length \(\frac23 X^{1/3}\); measured constant-parity runs must
  stay below it (**OBSERVATION**).
- **Resonance hazard**: where \(\sqrt x\) is near-integral, the
  increment \(\lfloor 3\sqrt x\rfloor\) parity locks and runs grow;
  `OOE` pullbacks can die locally (**OBSERVATION**).

## Experiments

Runner: `python -m research.juggler_sequence.hug_cylinder_construction`
(probe `src/research/juggler_sequence/hug_cylinder_construction.py`).
Artifact:
`data/research/juggler/hug_cylinder_construction/summary.json`.
Fast suite:
`tests/research/juggler_sequence/test_hug_cylinder_construction.py`.

Three censuses, all exact integer arithmetic: constant-parity runs
of \(\lfloor x^{3/2}\rfloor\) over odd \(x\) at scales
\(2^{20}\)–\(2^{40}\); `OE`-block pullback survivors on full
regenerated windows at \(2^{16}\)–\(2^{40}\); `OOE`-block two-stage
pullback hazard over \(3000\)-anchor runs at generic and
sqrt-resonant offsets.

## Conjectures

- `juggler_hug_flow_window` (ACTIVE): depth \(1\) is discharged by
  `J-hug-flow-window-depth-one`; the interval-iteration reading
  of depth \(2\) is CLOSE (`J-hug-flow-image-gap`). A sparse-set
  depth-\(2\) statement is not opened from this dossier.

## Counterexamples

None for the depth-\(1\) window. The falsifier did not fire at
generic positions. The resonant `OOE` death at \(2^{36}\) (below)
is the hazard the depth-\(2\) half must carry, not a flow
refutation and not a depth-\(1\) emptying. Anchor \(z=1000\) has
a monochromatic geometric `OE` cell (all even); that is the
\(X^{1/4}\) remainder, not a counterexample to
`J-hug-flow-window-depth-one`.

## Formalization

None new. The block grammar is already Lean
(`WalkChargeItineraries.lean`). The depth-\(1\) window lemma is
**EXACT — HUMAN PROOF** (`J-hug-flow-window-depth-one`), not Lean.
No `HugFlowWindow.lean`.

## Results

- **Flow confirmed (COMPUTATIONALLY VERIFIED, classification
  `HUG_FLOW_CONFIRMED`):**
  - parity runs: max constant-parity runs of
    \(\lfloor x^{3/2}\rfloor\) over odd \(x\) are \(58\) at
    \(2^{20}\) up to \(836\) at \(2^{40}\) — always below the
    \(\frac23 X^{1/3}\) working window, with the ratio falling
    \(0.86\to 0.12\); but **above** the naive quadratic-crossing
    budget \(\frac23 X^{1/4}\) at \(2^{36}\) and \(2^{40}\)
    (\(754>341\), \(836>683\)) — the induction genuinely needs the
    \(X^{1/3}\) window, i.e. the vdC-nontrivial regime;
  - `OE` pullbacks: survival rate \(0.4996\)–\(0.50\) on full
    windows, **zero** empty anchors across \(7\) scales;
  - `OOE` pullbacks: generic-offset hits track the
    \(\frac{8/27}{2}w^{-1/9}\) law at \(0.71\)–\(0.82\) of
    prediction at every scale \(2^{16}\)–\(2^{40}\).
- **Resonance hazard isolated:** at the \(2^{36}\) resonant offset
  the swept \(x\approx 2^{32}\) is a perfect square;
  \(\lfloor x^{3/2}\rfloor\) parity locks and `OOE` pullbacks die
  completely (\(0/3000\) against \(\approx 28\) predicted). Any
  all-depth statement must excise or route around sqrt-resonances;
  anchor freedom at generic positions is ample.
- **Negative knowledge — construction cost:** a backward
  *constructor* pays \(\sim X^{1/9}\) anchor pulls per `OOE` block,
  cascading multiplicatively across blocks; no backward search is
  cheaper than the \(2^L\) forward scan. The deepest certified
  witness stays the realization branch's depth \(28\). (The naive
  generator-chain implementation was discarded for this reason.)
- **Route classified:** all-depth nonemptiness still reduces to
  some depth-\(2\) hit, but **not** to interval Erdős–Turán on
  the image span. The sentence “an \(X^{1/3}\) window maps to
  length \(\asymp X^{5/6}\) at scale \(X^{3/2}\), then Paper B
  on that interval” is the named trap: the span is long, the
  occupants are \(3\sqrt X\)-separated
  (`J-hug-flow-image-gap`, satellite CLOSE). Depth \(2\) as
  sparse-set mixing is not opened here.

- **Depth-\(1\) window lemma (`J-hug-flow-window-depth-one`,
  EXACT — HUMAN PROOF).** There is an ineffective \(X_0\) such
  that for every \(X\ge X_0\) and every interval \(I\) of
  consecutive odd integers contained in \([X,2X]\) with
  \(\lvert I\rvert=\bigl\lfloor\tfrac23 X^{1/3}\bigr\rfloor\), the
  values \(\lfloor x^{3/2}\rfloor\) for \(x\in I\) are not all of
  one parity. The argument is Paper B Lemmas 3.2–3.4 localized to
  the working window; no exponent-pair upgrade and no Paper B
  edit. The method is KNOWN; the window \(H\asymp X^{1/3}\) is
  the PROJECT-SPECIFIC content (it is already above the van der
  Corput threshold \(X^{1/4}\)).

  *Proof.* Write \(x=2r+1\) and
  \(g(r)=\tfrac12(2r+1)^{3/2}\). Paper B Lemma 3.2 says
  \(\lfloor x^{3/2}\rfloor\) is odd if and only if
  \(\{g(r)\}\ge\tfrac12\), so it is enough to show that the
  \(H=\lvert I\rvert\) points \(\{g(r)\}\) meet both
  \(\bigl[0,\tfrac12\bigr)\) and \(\bigl[\tfrac12,1\bigr)\).
  The \(r\)-images of \(I\) are \(H\) consecutive integers with
  \(r\asymp X\). Differentiating gives
  \(g''(r)=\tfrac32(2r+1)^{-1/2}\), positive and decreasing. On
  \(x\in[X,2X]\)
  \[
  \tfrac32(4X+1)^{-1/2}\le g''(r)\le\tfrac32 X^{-1/2},
  \]
  hence \(\lambda\le\lvert g''\rvert\le\alpha\lambda\) with
  \(\lambda\asymp X^{-1/2}\) and \(\alpha\le 2\) for \(X\ge 1\).
  The curvature window is **uniform** on the whole dyadic block,
  including near perfect squares: first-derivative locking
  \(3\sqrt{x}\approx 2\mathbb Z\) lengthens sojourns of \(\{g\}\)
  but does not shrink \(g''\). No resonance exclusion is used.

  For the \(h\)-th mode \(f=hg\), Paper B Lemma 3.3 in the
  \(r\)-variable (or Lemma 3.10(b) read in \(n\)) gives
  \[
  \Bigl\lvert\sum e\bigl(hg(r)\bigr)\Bigr\rvert
  \ll H\bigl(h X^{-1/2}\bigr)^{1/2}
  +\bigl(h X^{-1/2}\bigr)^{-1/2}
  = H h^{1/2}X^{-1/4}+h^{-1/2}X^{1/4}.
  \]
  Let \(D\) be the absolute discrepancy of the \(H\) points
  \(\{g(r)\}\) against an interval of \(\mathbb R/\mathbb Z\).
  Paper B Lemma 3.4 with cutoff \(K=\lfloor X^{1/6}\rfloor\)
  yields
  \[
  D
  \ll\frac HK
  +\sum_{h=1}^{K}\frac1h
  \bigl(H h^{1/2}X^{-1/4}+h^{-1/2}X^{1/4}\bigr)
  \ll\frac HK+H X^{-1/4}K^{1/2}+X^{1/4},
  \]
  because \(\sum_{h\le K}h^{-1/2}\ll K^{1/2}\) and
  \(\sum_{h\le K}h^{-3/2}\ll 1\). Substituting
  \(H\asymp X^{1/3}\) and \(K=X^{1/6}\) gives
  \(D\ll X^{1/6}+X^{1/4}\). Since \(\tfrac13>\tfrac14\), one has
  \(D=o(H)\) as \(X\to\infty\). Choose \(X_0\) large enough that
  \(D<H/2\). Then both halves of \(\mathbb R/\mathbb Z\) contain
  a point, so both parities of \(\lfloor x^{3/2}\rfloor\) occur
  in \(I\). \(\square\)

  This is the short-interval form of Paper B Theorem 4.1 (that
  theorem takes a full dyadic block of length \(M\) and gets
  \(D\ll M^{5/6}\)). The second-derivative remainder
  \(X^{1/4}\) is why the naive crossing budget
  \(\tfrac23 X^{1/4}\) is not a theorem and why the census
  runs exceed it at \(2^{36}\) and \(2^{40}\); those runs stay
  \(o(X^{1/3})\), which is what the working window needs. The
  resonant `OOE` death at \(2^{36}\) is depth \(2\) and is not
  a counterexample here. The implied constants of Lemmas 3.3
  and 3.4 make \(X_0\) ineffective; an effective threshold plus
  a finite check is needed for a \(C_L\) induction, not for
  this lemma. The statement is not a transfer theorem and does
  not populate a single orbit. A single geometric `OE`
  cell can be monochromatic at modest scale (anchor
  \(z=1000\): six odd \(x\) in \([1000^{4/3},1001^{4/3})\),
  all \(\lfloor x^{3/2}\rfloor\) even) — that cell has
  length \(\asymp X^{1/4}\) at the source, which is the
  remainder, not the working window.

## Open questions

- None that interval ET can answer. The depth-\(2\)
  interval-iteration route is CLOSE
  (`juggler_hug_flow_depth_two`, `J-hug-flow-image-gap`).
  A sparse-set depth-\(2\) statement would be a new Phase-0.

## Decision

**PARK** (branch) / **PROMOTE** (depth-\(1\) lemma). The flow
ledger is positive per block and the census confirms every
exponent at every measured scale. Depth \(1\) of
`juggler_hug_flow_window` is now `J-hug-flow-window-depth-one`
(**EXACT — HUMAN PROOF**), uniformly, with no resonance
exclusion. The branch does not promote: the payoff is still the
existence theorem \(C_L\ne\emptyset\) for every \(L\), and that
needs the depth-\(2\) half. That half is bookkeeping in the
sense of the recorded key, not a theorem written here. The
three earlier CLOSEs (mechanical lift / empty `OOE`;
hug-prefix realization to depth \(28\); formal-versus-realized
prefix-NC) do not say hug prefixes cannot be realized.

Best next question: none from this branch — the depth-\(2\)
interval-ET reopen is CLOSE (`juggler_hug_flow_depth_two`).
The asymptotic-descent program's standing targets remain
`juggler_asymptotic_descent` and `juggler_descent_time_log`.

## Publication assessment

Status: **EXPLORATORY** (existence) / **THEOREM** (depth \(1\)).
The freedom-flow ledger plus the depth-\(1\) window is a
section-length note inside any future obstruction-existence
write-up; it is not a descent-certificate paper and not a
Paper B edit.
