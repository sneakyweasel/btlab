# The 3x-1 verification floor

Status: **PROMOTE** (the floor is supplied and pushed to \(2^{44}\); the
mirror's period bound is a statement)

Standalone computational phase on the Collatz bridge. Not a halt theorem
for either map, not a Juggler cycle exclusion, and not a change to
\(N_0\).

## Problem

`J-negative-cycle-finance-is-the-juggler-mirror` gave a conditional
table. Its missing input was a verification floor for the \(3x-1\) map,
which the laboratory searched for and did not find in the literature, and
which the journal named as the branch's best next question. Supply it,
then push it as far as the laboratory's own machine allows.

## Exact statement

Let \(g(y)=y/2\) for even \(y\) and \((3y-1)/2\) for odd \(y\) on
\(\mathbb Z_{>0}\); its cycles are \(1\), the triple \(5,7,10\), and the
eleven-element cycle at \(17\). Verify that every \(1\le y<2^{44}\)
reaches one of those three. Then read the kernel-checked
`neg_cycle_finance`, \(2(|x|-1)(3^o-2^K)\le (K-o)3^o\) at a negative
cycle's least \(|x|\), at that floor, and report the least period a
fourth cycle could have. The floor was \(2^{38}\) on 19 September 2026,
\(2^{40}\) on the morning of 20 September and \(2^{44}\) that evening.

## Current literature

- `hercher-2023-collatz-m-cycles`, `eliahou-1993-collatz-cycle-lengths` and the
  positive-side period bounds. **known**; the positive side is
  reproduced, not extended, by
  [collatz_finance_mirror](juggler_collatz_finance_mirror.md).
- No published verification floor for \(3x-1\) exists in anything
  reachable, searched twice: from a container on 19 September (OEIS text
  records, Roosendaal's index, Lagarias's bibliography, Chamberland section
  6.1) and from the laboratory machine with web access on 20 September (the
  full local OEIS corpus, both Lagarias bibliographies in full text,
  Wikipedia, Roosendaal, Ghosh, Tremblay, Cox). The only statement found is
  OEIS A037084's unattributed comment "up to at least 100000000, every
  number reaches 1, 5 or 17" (`oeis-A037084`). **independent**: the floor
  here is the laboratory's own computation, and the only one it can cite.
- `sinisalo-2003-collatz-minimal-cycle-lengths`, Table 2 — the conditional
  survivor table of the finance mirror, twenty-three years early, with a
  Crandall-type bound one or two rows weaker than the even-charge finance
  at each floor, and no verified floor. **known**; see
  [collatz_finance_mirror](juggler_collatz_finance_mirror.md).
- `simons-2007-inductive-two-cycles-3x1`, read in full — the \(3x-1\)
  function has exactly one nontrivial 2-cycle, at 17, and the proof uses
  no verification floor: de Weger's bound leaves nine \((K,L)\) pairs with
  \(0<3^K-2^{K+L}<3^{0.89K}\), one is the 17-cycle, the rest have no integer
  solution, and Steiner plus an extremal bound finish it. So no floor is
  published there either, and none was needed. His method stops at
  \(m\ge3\), where the floor-based template of Simons 2008 is the route.
  **known**.
- `simons-2008-m-cycles-generalized-syracuse`, read in full on 20
  September — contains nothing on \(3x-1\): its "inverse Collatz problem"
  is Guy's permutation \(x\mapsto 3x/2,\ (3x\mp1)/4\), and its
  \(3x+q\) section takes \(q=1\) or \(q\ge5\) prime. What it gives is
  the five-step Simons–de Weger template, whose step (3), the generalized
  Crandall lemma, turns a floor \(X_0\) into \(K\ge q_{n+1}\) for
  \(q_n+q_{n+1}\le(\log 2)X_0/m\). Nobody has run it on the \(3x-1\)
  side because nobody had a floor there; this branch now supplies
  \(X_0=2^{44}\). **known**; the transposition is a branch, not a reading.
- `neg_cycle_finance`, `neg_cycle_word_is_juggler_shape` in
  `Problems/Juggler/CollatzBridge.lean`. **EXACT — LEAN VERIFIED**; the
  implication from floor to period is theirs, and only the floor is
  empirical.
- The sieve's class count at \(K=24\) is `A076227(24) = 286581`
  ([the OEIS neighbourhood](juggler_oeis_neighbourhood.md)); the jump
  table is the block map of Terras and Everett used as an accelerator.
  **known**.

Project relationship: **independent**.

## Branch budget

```text
Mathematical target     Supply a verification floor for 3x-1 and convert the
                        conditional mirror table into an unconditional period
                        bound for a fourth negative cycle; then push the floor.
Novelty hypothesis      The floor is reachable by an ordinary descent verifier
                        and no published one exists to import.
Falsifier               A fourth cycle inside the range, or a start that does
                        not descend within the step cap.
Already killed by?      No. The finance mirror is PROMOTE and explicitly asks
                        for this input; nothing in negative_knowledge.md forbids
                        a verification floor, and this is not N_0, not Baker,
                        and not a local attack.
Existing machinery      negative_cycle_survivors, lambda_juggler,
                        three_gap_walk, neg_cycle_finance.
Maximum Phase-0 scope   C verifiers, chunked, archived beside the summary with
                        the raw reports and a run record; a Python reference on
                        a small window; the bound read off the laboratory's own
                        finance walk.
Promotion criterion     A clean certificate covering an interval to a stated
                        floor, agreeing with an independent reference rule.
Stop criterion          Any failure or any new cycle in range.
```

## Balanced-ternary formulation

None required. Integer arithmetic on \(\mathbb Z_{>0}\).

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- ascending-induction descent verification of \(g\) —
  **COMPUTATIONALLY VERIFIED** to \(2^{44}\)
- the descent rule agrees with full iteration to a cycle element —
  **COMPUTATIONALLY VERIFIED** on \(y<300000\)
- the mod-\(2^{24}\) prefix sieve is unconditional on this side
  (`neg_prefix_noncontracting`) and keeps exactly \(286581\) classes —
  **COMPUTATIONALLY VERIFIED**
- floor \(\Rightarrow\) period bound through `neg_cycle_finance` —
  **EXACT — LEAN VERIFIED**

## Experiments

`python -m research.juggler_sequence.negative_floor_3x1` writes
`data/research/juggler/negative_floor_3x1/summary.json`,
`chunks.json`, and
[juggler_negative_floor_3x1.md](../research/juggler_negative_floor_3x1.md).
Three verifier sources are archived beside them: `verify_3x1.c`, the plain
descent walker (chunks 0 to 15, \([3,2^{40})\)); `verify_3x1_sieved.c`,
the mod-\(2^{24}\) sieve on its own, kept for the measurement below; and
`verify_3x1_jump.c`, sieve plus \(2^{16}\) jump table (chunks 16 to 111,
\([2^{40},2^{44})\)). `runs.json` records each run — source digest,
compiler, host, timings, validation — `p44_reports.log` holds the 96 raw
reports, and `drive_p44.sh` is the driver that produced them. The probe
compiles either walker with `gcc`, or inside WSL when the checkout has no
native compiler, and can re-run it on any window.

A fourth verifier, `verify_3x1_gpu.cu`, runs the same descent on the GPU (21 September
2026): the mod-\(2^{24}\) sieve of the jump walker, the run identity \(g^a(y)-1=(3/2)^a(y-1)\)
for a whole odd run in one multiplication and a whole even run in one shift (Barina's domain
switch, sign flipped), 128-bit state in two limbs with an overflow report, the exact
trajectory peak and the plain walker's exact step count. `build_gpu.bat` builds it with the
CUDA toolkit and the MSVC Build Tools that built the atlas;
`python -m research.juggler_sequence.negative_floor_gpu calibrate` reruns the calibration set
and writes `gpu_calibration/summary.json` and
[juggler_negative_floor_gpu.md](../research/juggler_negative_floor_gpu.md); `sweep LO HI`
verifies a new range in chunks into `gpu_chunks/` with a run record in `gpu_runs.json`.
`walk` in that module is the same procedure on Python integers, for the tests and for any
start whose state would overflow.

## Conjectures

None.

## Counterexamples

None. Zero failures, zero new cycles. Greatest step count 544 against a
cap of 4000 with the plain walker below \(2^{40}\), and 704
against a cap of 40000 with the jump walker above it — that walker counts
sixteen steps per table jump and checks the drop only at a landing, so
its counts overshoot by up to fifteen. No orbit in range came within an
order of magnitude of either cap, which is what would flag a cycle whose
least element exceeds the start being tested.

## Formalization

No new Lean module. The implication is already `neg_cycle_finance`; a
verification floor is not a Lean object.

## Results

- **Every \(1\le y<2^{44}=17592186044416\) reaches \(1\), \(5\) or
  \(17\).** 112 chunks: sixteen with the plain walker to \(2^{40}\),
  then 96 chunks of \(5\cdot2^{35}\) numbers each with the sieve-plus-jump
  walker, 8246337208320 odd starts counted exactly (every odd start is
  either walked or sieved, and the two counts sum to the width), 0
  failures, 0 new cycles. The plain walker's printed counts fall one short
  per chunk by their own formula, which is how the hole below was found.
- **A fourth cycle of the \(3x-1\) shortcut map has period at least
  \(16483927\)**, with \(10400200\) odd steps. Equivalently a fourth
  negative cycle of shortcut \(3x+1\), whose word is a Paper A CycleMin
  shape letter for letter. The uniform and the hug-word constants give the
  same length at this floor. The history: \(4404167\) at \(2^{38}\),
  \(9538065\) with \(6017849\) odd steps at \(2^{40}\), \(16483927\) now.
- **The first certificate had seven holes, and the record now says so.**
  The plain walker prints `floor((limit - lo)/2)` with `lo` odd; that
  explains one missing start per chunk, sixteen in all, and the committed
  total to \(2^{40}\) was short by 23. The only launch value that
  reproduces the counts of chunks 1 to 7 is \(k2^{35}+3\), so the seven
  odd starts \(k2^{35}+1\), \(k=1,\dots,7\), lay between the chunks of
  the \(2^{38}\) certificate and were walked by nothing. Each reaches a
  known cycle by full iteration, in 118 to 232 steps to the first drop,
  and so does every odd start within 64 of every legacy boundary. The
  probe now recovers each chunk's launch value, records it, lists every
  gap between chunks, verifies each, and reports the certificate unclean
  otherwise. The floor statements at \(2^{38}\) and \(2^{40}\) were
  true; the word "tiling" was not.
- **Excursions.** The greatest landing value above \(2^{40}\), \(1.21\cdot10^{26}\), exceeds the record from below it, so the certificate's greatest known excursion moves to \(121443575752945981388885320\). The `unsigned __int128` state never
  came near overflow; skipped starts stay below \((3/2)^{24}2^{44}<2^{58}\).
- The two verification rules agree: descent and full iteration give the
  same verdict on every odd \(y<300000\).

## Open questions

Pushing the floor further is scheduling, not mathematics, and since the GPU verifier below
it is cheap scheduling: at the calibrated rate, from \(2^{44}\), \(2^{51}\) is about
1.0 hour, \(2^{56}\) about 32 hours and \(2^{60}\) about
21 days of the RTX 5090, floors rather than estimates since trajectories
lengthen slowly with size. What each floor buys the \(3n-1\) \(m\)-cycle theorem is in
[juggler_negative_m_cycles](juggler_negative_m_cycles.md): \(2^{51}\) gives \(m\le58\),
\(2^{56}\) gives \(63\), \(2^{60}\) gives \(68\). The 128-bit state has headroom to
about \(2^{60}\) on the evidence of the peak below \(2^{44}\), \(2^{86.6}\); an overflow
is reported and re-walked wide on the host, not silently wrapped.

## The GPU verifier, calibrated on the certified range

**21 September 2026, RTX 5090, CUDA 13.3.** `verify_3x1_gpu.cu` against the certificate
(record in `gpu_calibration/summary.json`, tests in
`tests/research/juggler_sequence/test_negative_floor_gpu.py`):

- **Sieve.** 286581 classes at \(K=24\), A076227(24), as the jump walker.
- **Known-bad input.** With the 17-cycle forgotten, `NEW CYCLE at 17` on \([3,2000)\) and exit
  code 1; with it known, a clean run. The Python walker on the same 32 survivors gives the
  same 62 steps and peak 413344.
- **\([3,2^{35})\)** against chunk 0: max steps 508 and peak 174217613946575461336, both exact.
- **\([3,2^{40})\)** against chunks 0 to 15: max steps 544 and peak 261160802435320822179964,
  both exact; the odd-start count is 23 above the CPU's, the CPU's per-chunk formula being
  one short when the chunk starts odd (sixteen) plus the seven gap starts that were verified
  separately and lie inside the GPU's range.
- **\([2^{40},2^{44})\)** against `runs.json`: 8246337208320 odd starts, no failure, no cycle,
  no overflow; peak 121443575752945981388885320, equal to the jump walker's landing peak;
  max steps 703 exact against the jump walker's 704, which is granular to sixteen.
- **Time.** 26.2 s for \([2^{40},2^{44})\) against the CPU's 1628 s wall on 24 threads
  (62 times) and 35666 core-seconds (1359 times one core); 3.14e+11
  odd starts per second, 1.07e+10 walked.

The GPU run is a second implementation of the certificate's statement, with a different
iteration (run identity rather than jump table) and a different language, agreeing with the
CPU on every quantity where the semantics coincide. It does not replace the certificate; it
reproduces it and prices its extension.

## Accelerating the verifier, measured — and a speedup claim withdrawn

Pushing the floor further is a compute problem, and this section records what
the compute actually costs, because an earlier estimate in this laboratory
was wrong by a factor of thirty.

**Measured on four cores at 2.8 GHz.** The plain verifier runs 30.5 M odd
starts per second per process. The range \([2^{40}, 2^{44})\) is
\(8.25\cdot 10^{12}\) odd starts, so brute force is **18.8 hours** on four
processes.

**The sieve is unconditional on this side.** For a start \(y\) whose first
\(k\) steps have word \(w\) with \(a\) odd letters,
\(2^k y_k = 3^a y - C(w)\) with \(C \ge 0\), because the odd step
\((3y-1)/2\) *subtracts*. Hence \(y_k < y \iff y(3^a - 2^k) < C\), and when
the prefix contracts (\(3^a < 2^k\)) the left side is negative while
\(C \ge 0\) — so the drop holds for **every** member of the class, with no
threshold at all. That is `neg_prefix_noncontracting`, and it is why the
sieve is clean here and needs a threshold argument on the Collatz side.
Only prefix-noncontracting classes need walking. At \(k = 24\) the builder
finds **286581** of them, which is exactly **A076227(24)** — an independent
check of the builder against the sequence identified in
[the OEIS neighbourhood](juggler_oeis_neighbourhood.md).

**The speedup is 2.7×, not 58×, and the earlier claim is withdrawn.** The
class density is \(286581/2^{24} = 1.7\%\), and a note elsewhere in this
laboratory inferred a ~58× speedup from that ratio. That inference is
wrong: it equates class density with *work* density. The skipped classes
are precisely the ones that drop within a few iterations, so skipping them
saves almost nothing; essentially all the time sits in the 3.4 % that
survive. Measured, the sieve alone gives **2.7×**.

**The jump table is what pays.** For \(r \bmod 2^J\), \(J\) steps send
\(y = q2^J + r\) to \(q\,3^{a(r)} + t(r)\), one multiply-add for \(J\)
iterations — the jump function of A368877 used as an accelerator. At
\(J = 16\) on top of the \(k = 24\) sieve the total is **7.1×**, putting
\([2^{40}, 2^{44})\) at **4.9 hours** on four cores.

**Validation.** Against the plain verifier on four disjoint already-verified
windows: `fails` and `new_cycles` agree everywhere (0 and 0). Two caveats,
both recorded rather than smoothed over. The reported peak is a maximum over
*walked* starts only, so it is not comparable with the plain verifier's;
the skipped starts are bounded analytically instead, since within 24 steps a
start below \(2^{44}\) cannot exceed \((3/2)^{24}2^{44} < 2^{58}\), far under
the `unsigned __int128` ceiling. And a jump can carry past a \(v = y\)
return, so a missed cycle surfaces as a `STEPCAP` — reported, never a silent
pass — which is why the step cap is raised to 40000 in that variant.

**An attempt that produced nothing.** A chunked run over
\([2^{40}, 2^{44})\) was launched in the session container on 20 September
and its workers died before a single chunk completed. The three archived
artifacts — `verify_3x1_sieved.c`, `verify_3x1_jump.c` and `drive_chunked.sh`
— are what that run used.

**Run on the laboratory machine, 20 September 2026.** The same
`verify_3x1_jump.c`, compiled with gcc 13.3 `-O3 -march=native` under WSL2
Ubuntu 24.04 on the Ryzen 9 3900X — the Windows side has no C compiler and
the source needs `unsigned __int128`. Validated first on this machine: the
sieve builder returns 286581 classes at \(k = 24\); with the 17-cycle
removed from `known()` the walker reports `NEW CYCLE at 17` on
\([3, 2000)\); plain and jump walkers agree (0 and 0) on three
\(2^{27}\)-wide already-verified windows at \(2^{38}\), near \(2^{39}\)
and just below \(2^{40}\). One core walks \(2^{30}\) odd starts above
\(2^{40}\) in 2.73 s, about 393 million per second, 1.8 times the
container's rate. The range ran as 96 chunks, 24 at a time at nice 10, in
**27 minutes** wall (9.9 core-hours; chunks took
243 to 618 s as SMT contention set in). Every chunk exited
0; no `NEW CYCLE`, no `STEPCAP`. Run record in `runs.json`, raw reports in
`p44_reports.log`.

## Decision

**PROMOTE**. The branch does what the journal asked and then the push it
named: the table entry is a statement, and the statement now stands at
\(2^{44}\). The floor is a computation and is labelled as one; the
implication it feeds is kernel-checked; the seven-start hole in the first
certificate is verified shut and written down. Nothing about the Juggler
moves — this is a Collatz-side input that the Juggler's own finance
inequality converts.

Best next question: none from the mathematics. The next floor is a
scheduling decision — \(2^{48}\) overnight here, \(2^{68}\) on a GPU.

*21 September 2026.* The floor now feeds a theorem: the Simons–de Weger
\(m\)-cycle template, transposed in
[juggler_negative_m_cycles](juggler_negative_m_cycles.md), excludes every
\(m\)-cycle with \(m\le49\) above \(2^{44}\), given Rhin. By its tables
\(2^{48}\) buys nothing over \(2^{44}\) there, so the next floor stays a
scheduling decision.

## Publication assessment

Status: `STRUCTURAL`. A computational certificate plus a one-line
implication; it belongs with the finance mirror, not in a manuscript of
its own. Paper A's Remark 5.20 carries the \(2^{44}\) floor, the bound
\(16483927\), the certificate's checksums, Sinisalo and Simons since the
revision of 20 September 2026; the Zenodo new version is pending.
