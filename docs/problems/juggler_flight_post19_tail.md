# Juggler post-19 tails (overshoot versus descent)

Status: **PARK** (the named question is answered: a long post-19
miss is walk-height overshoot, not a short descent; overshoot is
not forced)

Child of [juggler_flight_fan_concat.md](juggler_flight_fan_concat.md).
Not a halt theorem, not a divergence exclusion, not a glue reopen,
not a CF census, not a mechanical-lift reopen, and not a Paper A
edit.

## Problem

The fan-concat PARK left two long post-19 tails
(\(n=761\), 41 steps; \(n=1245741\), 118 steps) that miss a second
\(R_{0.05}\) near-return. Are those misses a walk-height reason, or
only the later descent of a terminating orbit?

## Exact statement

**Lemma (post-19 dichotomy; EXACT — HUMAN PROOF, components Lean).**
Let a prefix of length 19 be `AboveAnchor`. Hug domination gives
\(o\ge\mathrm{hugOdds}(19)=12\). The envelope gives
\(\delta\le o\log_2 3-19\). Hence \(o=12\) forces
\(\delta\le\theta_{19}<0.05\): a 19-near-return. Equivalently, a
tail of length \(\ge 19\) misses \(R_{0.05}\) at \(t=19\) if and
only if \(o\ge 13\) and \(\delta>0.05\).

*Proof.* `aboveAnchor_prefix_odds_ge_hug` and
`follows_log_le_walkWeight`. \(\square\)

So a *long* miss cannot be “the orbit later descends.” Descent can
only kill a tail of length \(<19\). A long miss is hug-overshoot
plus a jump past the near-return window.

**Observation (COMPUTATIONALLY VERIFIED).** On the existing
fan-concat windows the 52 length-19 near-returns split as follows.

- Window \(n\le 2000\) (44 events): 27 die immediately, 16 die
  before length 19, one overshoots (\(n=761\): \(o_{19}=14\),
  \(\delta_{19}\approx 3.19\), first hug-split at letter 3).
- Seven high-flyers (8 events): 1 dies immediately, 6 die before
  length 19, one overshoots (\(n=1245741\): \(o_{19}=15\),
  \(\delta_{19}\approx 4.77\), first hug-split at letter 3;
  still overshooting at \(t=38,84,103\)).
- Zero hug-minimal 19-continuations (that would have been glue).
- Letter 3 is not forced: among tails of length \(\ge 3\), five
  window and two flyer prefixes stay on hug until they die
  (`first_hug_split` empty). The two long overshoots take O where
  hug takes its first E.

Both mechanisms occur. Overshoot is not a launch invariant.
Exclusion of divergent flights is not claimed.

## Current literature

- Local \(19\to 19\) glue absent on these windows — **OBSERVATION**
  ([juggler_flight_fan_concat.md](juggler_flight_fan_concat.md),
  PARK).
- Hug domination and the envelope — **EXACT — LEAN VERIFIED**
  (`aboveAnchor_prefix_odds_ge_hug`, `follows_log_le_walkWeight`).
- Record-jump quantization — **EXACT — HUMAN PROOF**
  (`J-flight-return-quantization`).
- Record composition, mechanical lift, expanding-residual concat,
  hug-cylinder \(C_L\), Paper A — not reopened.

Project relationship: **extended** (answers the fan-concat best
next question on the same witnesses).

## Branch budget

```text
Mathematical target     is a long post-19 miss a walk-height
                        overshoot (o>=13 and delta>0.05), or only
                        later descent of a terminating orbit?
Novelty hypothesis      the dichotomy is a one-line corollary;
                        the two long tails decide which side is
                        live, and whether overshoot is forced
Falsifier               a long tail with o=12 (glue, already
                        zero); or every long miss is a short
                        descent mismeasured; or the lemma is
                        only packaging and the tails add nothing
Existing machinery      fan-concat events, hug table, two-sided
                        envelope, R_0.05
Maximum Phase-0 scope   profile existing post-19 tails only; no
                        new n-window, no Lean, no Paper A, no
                        glue reopen
Promotion criterion     overshoot forced by the (19,12) landing,
                        not an archived cell
Stop criterion          lemma is packaging and both sides of the
                        split occur without a force (PARK);
                        or the miss is first-descent (CLOSE)
```

## Balanced-ternary formulation

None required.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Post-19 dichotomy \(o=12\Rightarrow\) near-return —
  **EXACT — HUMAN PROOF** (corollary of existing Lean; not a
  new ledger row).
- Long miss \(=\) overshoot on the two named tails —
  **COMPUTATIONALLY VERIFIED**.
- Letter-3 extra O forced after every (19,12) landing —
  **false** on the window (hug-following short tails exist).
- Overshoot forced — not claimed.

## Experiments

- Probe: `research.juggler_sequence.flight_post19_tail`
- Artifact:
  `data/research/juggler/flight_post19_tail/summary.json`
- Tests:
  `tests/research/juggler_sequence/test_flight_post19_tail.py`

Same starts as fan-concat. No \(n_{\max}\) raise.

## Conjectures

None opened.

## Counterexamples

- “Every post-19 tail of length \(\ge 3\) leaves hug at letter 3.”
  False: five window and two flyer prefixes stay on hug until
  they die before length 19.
- “The \(1245741\) miss is only later descent.” False: 118
  AboveAnchor steps with \(o_{19}=15\) and \(\delta_{19}\approx 4.77\).

## Formalization

None new. The dichotomy uses existing Lean. No `sorry`. No
Paper A edit.

## Results

Classification **POST19_TAIL_SPLIT_CONFIRMED**.

- The standing question is answered: a long post-19 miss is
  walk-height overshoot. Descent explains the short tails
  (43 of 44 window events; 7 of 8 flyer events), not the two
  long ones.
- Overshoot is realized and not forced. Hug-follow after a
  (19,12) landing is realized and dies before length 19.
- No launch invariant, no glue, no ledger row.

## Open questions

- Is there a landing-cell reason that a hug-following post-19
  tail cannot reach length 19? Answered by
  [juggler_flight_fan_landing.md](juggler_flight_fan_landing.md)
  (**CLOSE**): the two-way slogan is **REFUTED**; remaining
  labels are \(T\)-parity.
- Infinite concatenable fan blocks remain unconstructed and
  unobstructed.

## Decision

**PARK.** The named alternative is decided: long miss \(=\)
overshoot, short miss \(=\) descent, both occur, neither is a
force. The dichotomy is a corollary, not a new ledger theorem.
Do not raise \(n_{\max}\). Best next question: the landing-cell slogan is now CLOSE
(`juggler_flight_fan_landing`); none further from this door.

## Publication assessment

Status: `EXPLORATORY`. A one-paragraph clarification of the
fan-concat long tails. Not a paper candidate. No Paper A/B edit.
