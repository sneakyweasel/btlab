# m-cycles of the 3n−1 map: the Simons–de Weger template on the negative side

Status: **PROMOTE** (a theorem with one external input, and a paper candidate)

Standalone phase on the Collatz bridge, following
[juggler_negative_floor_3x1](juggler_negative_floor_3x1.md) and
[juggler_collatz_finance_mirror](juggler_collatz_finance_mirror.md). Not a halt theorem for
either map, not a Juggler cycle exclusion, and not a change to \(N_0\). The manuscript is
[collatz_3n_minus_1_m_cycles_note.md](../theory/collatz_3n_minus_1_m_cycles_note.md).

## Problem

The \(3n-1\) map \(g(y)=y/2\) (\(y\) even), \((3y-1)/2\) (\(y\) odd) on the positive integers
is the shortcut \(3n+1\) map read on the negative integers. Its known cycles are \(1\),
\((5,7,10)\) and the eleven-element cycle at \(17\), and every start below \(2^{44}\) reaches
one of them (the laboratory's certificate). An \(m\)-cycle is a cycle with \(m\) odd runs,
equivalently \(m\) local minima. Simons 2007 proves there is exactly one nontrivial 2-cycle,
floor-free, and says his method stops at \(m\ge3\); Simons–de Weger 2005 and Hercher 2023
exclude \(3n+1\) \(m\)-cycles for \(m\le68\) and \(m\le91\) from verification floors; nobody
has run that template on \(3n-1\), because nobody had a floor there. Run it.

## Exact statement

For which \(m\) does the \(3n-1\) map have no \(m\)-cycle whose least element is at least
\(2^{44}\), hence (by the floor) no \(m\)-cycle other than the two known ones with an even
step? What does each larger floor buy, and which lengths \(K\) does the template leave at
the first open \(m\)?

## Current literature

- `simons-2007-inductive-two-cycles-3x1`, read in full: exactly one nontrivial 2-cycle of
  \(3x-1\), at \(17\), floor-free; the method stops at \(m\ge3\). **known**; the note's
  \(m\le2\) rows reprove a weaker, floor-dependent form of it.
- `simons-2008-m-cycles-generalized-syracuse`, read in full: the five-step template (floor,
  cycle-equation bound on \(\Lambda\), Crandall's lemma, Rhin's bound, lattice reduction),
  applied to \(3x+q\), \(px+q\), Guy's permutation and the Roelants problem; nothing on
  \(3x-1\). **extended**: the template transposed, with the negative-side constants derived
  here.
- `simons-de-weger-2005-collatz-m-cycles`, read in full on 21 September 2026 from the PDF
  Philippe fetched: \(m\le68\) for \(3n+1\) at \(X_0=301\cdot2^{50}>3.3889\cdot10^{17}\)
  (Roosendaal, November 2004), by three stages, tables (Lemma 15: \(57\)), the
  continued-fraction reduction through the champion partial quotients (Lemma 17: \(63\)) and
  de Weger's approximation lattice (Lemma 18: \(68\)); the \(75\) is Simons 2008 at the later
  floor. **extended**: their Section 7 lattice is a two-dimensional approximation lattice
  whose short points are the \((K,L)\) pairs in the Corollary 5 window below the ceiling,
  each then tested against Corollary 5 and Lemma 7; the three-gap walk produces that list and
  the probe applies those two tests, so the fifth step is not open. Run on their side at their
  floor, the machinery reproduces their Lemma 18 to the unit (none for \(64\le m\le68\), their
  five pairs at \(69\le m\le72\) with their killing floors to rounding). On the \(3n-1\) side
  the same floor gives \(63\): the five values are the sign, not a stage. (A first reading on
  21 September had called the transposition "their Lemma 17 exactly" and the lattice "worth
  five values of \(m\)"; corrected the same day.)
- `rhin-1987-pade-irrationality`, read at its Proposition on 21 September 2026:
  \(|u_0+u_1\log2+u_2\log3|\ge H^{-13.3}\) for \(H=\max(|u_1|,|u_2|)\ge2\), no further
  constant. The form \(e^{-13.3(0.46057+\log K)}\) carried since Paper A is [SdW] Lemma 12,
  the same bound at \(H=K+L\) in the odd count; the probe now uses (7) at \(H\) the length.
- `hercher-2023-collatz-m-cycles`, read from the PDF: \(m\le91\) for \(3n+1\) at
  \(695\cdot2^{60}\), with the valley arrangement and Lemma 8. **known**; the plain template
  here gives \(82\) at \(2^{68}\), so his refinement is worth about nine values of \(m\) and is
  the next thing to transpose.
- `sinisalo-2003-collatz-minimal-cycle-lengths`: Table 2 is the \(m\)-free survivor table on
  this side. **known**.
- Prior-art search by name, 21 September 2026: "3x−1 problem" cycles, "3n−1" negative Collatz
  cycles 2025–2026 on arXiv; nothing beyond the records above. The two earlier sweeps for a
  \(3x-1\) floor (19 and 20 September) found none in print.

## Branch budget

- **Target:** the largest \(M\) such that no \(m\)-cycle with \(m\le M\) exists above the
  \(2^{44}\) floor, by the Simons–de Weger template with negative-side constants.
- **Novelty hypothesis:** the first \(m\)-cycle theorem for \(3n-1\) with \(m\ge3\), and the
  first floor to feed one.
- **Falsifier:** a real cycle failing the inequalities — the template must leave the
  \(17\)-cycle's length \(11\) at \(m=2\) when the floor is set at \(17\), and the
  \((5,7,10)\) length \(3\) at \(m=1\) with the floor at \(5\).
- **Already killed by?:** none. The finance-mirror cluster reproduced Eliahou and Hercher on
  the positive side and priced the negative side as a table; the floor branch supplied the
  floor; neither ran the \(m\)-cycle step, and the journal of 20 September named it the best
  next question.
- **Existing machinery:** `neg_cycle_finance`, `neg_prefix_noncontracting`,
  `neg_cycle_expanding` (Lean, `CollatzBridge.lean`); `lambda_juggler`, the continued
  fraction of \(\log2/\log3\) and the three-gap walk (`collatz_finance_mirror`); the floor
  certificate (`negative_floor_3x1`).
- **Maximum Phase-0 scope:** the tables at the five floors and the survivor lengths at the
  first open \(m\).
- **Promotion criterion:** \(M\ge3\) with the known cycles surviving the same test.
- **Stop criterion:** a negative-side constant that does not carry, or an admissible length
  the tower cannot reach at every \(m\ge3\).

## Balanced-ternary formulation

Not used. The objects are the parity word of a cycle and the linear form
\(o\log3-K\log2\).

## Why BT may be relevant

It is not; recorded for the template.

## Candidate operations / invariants

The run identity \(g^k(y)-1=(3/2)^k(y-1)\), the run length \(v_2(y-1)\), the cycle product
\(3^o2^{-K}\prod(1-1/(3y))=1\), the chaining \(u_{i+1}<u_i^{\delta}/2\) with
\(\delta=\log_23\), the three-gap walk for the admissible lengths, Rhin's ceiling. All
**EXACT — HUMAN PROOF** in the note except Rhin (external) and the window enumeration (exact
arithmetic at 80 digits).

## Experiments

`python -m research.juggler_sequence.negative_m_cycles` writes
`data/research/juggler/negative_m_cycles/summary.json` and
[juggler_negative_m_cycles.md](../research/juggler_negative_m_cycles.md): per floor and per
\(m\), the bound on \(\Lambda\), Rhin's ceiling \(K_3(m)\), the admissible lengths below it,
the least one \(K_0(m)\), the closest margin in bits and the survivors; and, on the \(3n+1\)
side at [SdW]'s floor, their Lemma 18 rows for \(64\le m\le72\).

`python tools/check_3n_minus_1_note_numeric.py` recomputes the manuscript's numbers by a
route independent of the probe: an integer sieve over \(K=iQ+j\) for the admissible lengths
at \(2^{40}\), \(2^{44}\) and \(2^{48}\) (checked first against a direct scan at coarse
windows), the ceilings from their defining inequality at \(K_3-1\) and \(K_3\), the margins
at one hundred digits, the known cycles by iteration, the floor's printed counts against the
certificate; it compares them with the note's tables and the summary, writes
`manuscript_check.json` beside the summary, and fails on a copy of the note with two wrong
cells (21 September 2026: two findings, nothing else). `python tools/build_3n_minus_1_note.py`
builds [collatz_3n_minus_1_m_cycles_note.pdf](../../juggler_review/collatz_3n_minus_1_m_cycles_note.pdf)
(seven pages) with the Paper C chain and a strict layout gate; `--check` verifies the PDF
against its manifest in `.build/collatz_3n_minus_1_note/`.

## Conjectures

None. The \(3n-1\) analogue of the Collatz conjecture, that \(1\), \(5\) and \(17\) are the
only cycles and no orbit diverges, is not a laboratory conjecture and is not touched.

## Counterexamples

The known cycles are the witnesses that the inequalities are sound: with the floor at their
least element they pass every test, and with the floor one above it they do not.
`tests/research/juggler_sequence/test_negative_m_cycles.py`.

## Formalization

None new. The negative-side finance and word shape are Lean already
(`neg_cycle_finance`, `neg_prefix_noncontracting`, `neg_cycle_expanding`,
`neg_cycle_word_is_juggler_shape` in `CollatzBridge.lean`). Lemmas 1–3 of the note are
elementary and are the natural next Lean; Rhin's bound would enter as a hypothesis, as
`cycleMin_length_of_rhin` does on the Juggler side.

## Results

- **Theorem (EXACT — HUMAN PROOF, one external input).** Given Rhin's bound, the \(3n-1\) map
  has no \(m\)-cycle with \(1\le m\le49\) whose least element is at least \(2^{44}\); with
  the floor, none with \(m\le49\) other than \((5,7,10)\) and the cycle at \(17\). For
  \(m\le43\) no admissible length lies below Rhin's ceiling at all; for \(44\le m\le49\) the
  admissible lengths are excluded by the chaining, the closest by \(1.4\) bits at \(m=49\),
  \(K=757698850864\).
- **The floors (COMPUTATIONALLY VERIFIED).** \(2^{40}\): \(m\le44\); \(2^{44}\) to
  \(2^{48}\): \(m\le49\); \(2^{49}\): \(54\); \(2^{50}\): \(56\); \(2^{51}\) to \(2^{55}\): \(58\);
  \(2^{56}\): \(63\); \(301\cdot2^{50}\), [SdW]'s floor: \(63\) on this side against their
  \(68\) on theirs, first open length \(766512153894657\) at \(m=64\); \(2^{60}\): \(68\);
  \(2^{68}\): \(82\). The rows at \(2^{49}\), \(2^{50}\) and \(2^{51}\) were also sieved
  independently (104 admissible lengths below \(K_3(59)\); the same three answers).
- **What the template leaves at \(m=50\), floor \(2^{44}\):** the lengths
  \(539722056247\), \(757698850864\), \(975675645481\), \(1193652440098\), with \(22.4\),
  \(15.0\), \(7.8\), \(2.9\) bits of room; at \(2^{48}\) only the last. They are the output of
  the template's last step, not its input; the floors that remove them are \(2^{44.01}\),
  \(2^{44.57}\), \(2^{45.48}\) and \(2^{48.58}\).
- **Sanity.** With the floor at \(17\), \(m=2\) leaves \(K=11\); at \(5\), \(m=1\) leaves
  \(K=3\); the chaining is tight on the \(17\)-cycle (\(16\to40\) against \(40.5\)).
- **Ceilings corrected (21 September 2026, by the manuscript check).** The probe's
  \(K_3(m)\) was one above the least integer of its definition: it evaluated \(L_{\min}\)
  at \(\lfloor K\rfloor\) inside a real bisection and rounded up. It is exact now; Table 1
  of the note moved down by one in every row, and nothing else moved, the admissible counts,
  least lengths, margins and survivors being the same at every floor.
- **The fifth step is not open (21 September 2026, second pass).** [SdW] Section 7, re-read:
  the approximation lattice lists the admissible pairs and each is "checked for fulfilling
  Corollary 5 and Lemma 7", which is what the probe has done since 20 September. Proof by
  reproduction on their side: with the window on the contracting side at \(301\cdot2^{50}\),
  none for \(64\le m\le68\); at \(m=69\) the pair \((5750934602875680,3364081086781987)\)
  falling at \(576.2\cdot2^{50}\) against their \(577\); the same pair at \(584.6\), \(592.9\),
  \(601.3\) for \(m=70,71,72\) against \(585\), \(593\), \(602\); their second pair at
  \(623.6\), \(632.4\) against \(624\), \(633\); their three \(m=72\) pairs at \(308.2\),
  \(666.8\), \(705.3\) against \(309\), \(667\), \(706\). One point more at \(m=72\), the
  double of their second pair (\(0.9\) bits of room, \(316.2\cdot2^{50}\)), which their table
  does not carry. Their Lemma 7 constant \(c_m\) is, algebraically, the
  \(2^{-(B-m)/((\delta-1)B)}\) of the note's Lemma 3.

## Open questions

- The floor. On the 3900X at the measured \(9.9\) core-hours for \([2^{40},2^{44})\):
  \(2^{49}\) (about fourteen hours wall) buys \(m\le54\), \(2^{50}\) (about twenty-nine) buys
  \(56\), \(2^{51}\) (two and a half days) buys \(58\); nothing more until \(2^{56}\) (eleven
  weeks). The verifier and the chunk driver are archived with `negative_floor_3x1`.
- Hercher's valley arrangement transposed, worth about nine values of \(m\) at \(2^{68}\).
- The Eliahou-type period lattice on this side at \(2^{44}\).
- Their Lemma 7 constant \(c_m\to0.30576\) against the \((B-m)/(\delta-1)\) term here, a
  bookkeeping comparison that would move nothing at \(2^{44}\) but is owed to the note.

## Decision

`PROMOTE`. The template carries with the sign flipped, the constants improve rather than
worsen (the odd step subtracts), and the result is a theorem nobody has stated about a map
the literature names but has not verified; on their side at their floor it reproduces their
Lemma 18 to the unit. Best next question: the floor to \(2^{50}\) or \(2^{51}\), then Hercher's
valley arrangement.

## Publication assessment

Status: `PAPER_CANDIDATE`, not yet a review object (assessed 21 September 2026). A short
note, the length of Simons 2007. What has been checked: Lemmas 1–4, Proposition 5 and
Theorem 6 read line by line; every number in the manuscript recomputed by
`tools/check_3n_minus_1_note_numeric.py` by a route independent of the probe; the PDF built
with no layout warning. What a referee would ask for before acceptance, in the order it
matters:

1. **The floor.** There is no lattice step left: [SdW]'s Section 7 is the list the three-gap
   walk produces, tested the same way, and the note now says so and reproduces their Lemma 18
   on their side. What a referee will ask instead is why the floor stops at \(2^{44}\) when
   \(2^{49}\) costs a day of the machine and buys five values of \(m\), and \(2^{51}\) costs
   three days and buys nine; the note should carry the higher floor or say what it costs.
2. **The floor as a citable object.** One implementation, one run, archived in the
   repository. It needs a deposit with a DOI (verifier sources, chunk reports, coverage
   check) and, ideally, an independent re-run; Paper A's Remark 5.20 already rests on it, so
   the deposit serves both.
3. **Internal names.** Branch names, Lean lemma names and `python -m` commands must become a
   repository URL with a commit hash, or the DOI of the deposit.
4. **Front matter.** The draft banner and "not a review object" go; an AI-assistance
   disclosure and the author's responsibility statement as in Papers A–C; a 2020 MSC line,
   which is also what the layout filter uses to close the abstract.
5. **References.** [Si03], [E93], [St77], [L85] and [A] are listed and never cited by key;
   Lemma 4's walk needs the three-distance theorem cited (Sós 1958, Świerczkowski 1959,
   Slater 1967); DOIs throughout.
6. **Wording.** "No published verification floor and no \(m\)-cycle theorem with
   \(m\ge3\) existed" should read "to our knowledge", with the search named; Simons [S07]
   sketches the \(3x-1\) case in his Section 6 rather than proving it in full, and the note
   should say so; Proposition 5's "the doubled constant covers \(m/\Lambda+1\)" should say
   that the factor two is a margin the proof does not need.
7. **Lean.** Lemmas 1–3 are elementary; the laboratory's standard is to have them
   machine-checked before deposit, with Rhin's bound entering as a hypothesis as
   `cycleMin_length_of_rhin` does on the Juggler side.

None of these touches the theorem. Items 1 and 2 decide whether it is a note worth a
referee's time or a table.
