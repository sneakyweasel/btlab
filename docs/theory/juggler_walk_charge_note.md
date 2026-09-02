# The walk-charge envelope: transport to a census-free window theorem

Status: laboratory extract. Date: 1 September 2026.

> **Consolidated.** As of the 1 September 2026 consolidation this
> content is printed in Paper A Section 5
> ([juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md)):
> transport is Theorem 5.3, the hug adversary Theorem 5.4, the itinerary
> identity Lemma 5.6, DK/Ostrowski Theorem 5.7, the window theorem
> Theorem 5.8, and the kill table Theorem 5.9. The discrete word
> layer and the quotient arithmetic are Lean
> (`WalkChargeItineraries.lean`, `OstrowskiSandwich.lean`;
> `J-cyclemin-walk-word-identity`,
> `J-cyclemin-walk-ostrowski-arithmetic`). This extract stays as the
> program-order reading path over the nine dossiers.

This consolidates the walk-charge program — seven Phase-0
branches run at the certified descent floor \(N_0=26254995\) —
into one reading path. It is **not a halt theorem**, not a
"no cycle of any length" claim, not a floor raise, and not a
uniform \(B/\theta\) claim; the certified period bound is
unchanged at \(176251\). It is a laboratory extract,
not a second manuscript: together with the finance notes it is
a coherent section for a successor of Paper A. The open-orbit
counterpart is the flight extract
[juggler_flight_note.md](juggler_flight_note.md).

Dossiers, in program order:
[walk charge](../problems/juggler_cycle_walk_charge.md),
[walk mechanical](../problems/juggler_cycle_walk_mechanical.md),
[walk greedy](../problems/juggler_cycle_walk_greedy.md),
[walk exchange](../problems/juggler_cycle_walk_exchange.md),
[walk Koksma](../problems/juggler_cycle_walk_koksma.md),
[walk envelope](../problems/juggler_cycle_walk_envelope.md),
[walk Ostrowski](../problems/juggler_cycle_walk_ostrowski.md),
[walk window](../problems/juggler_cycle_walk_window.md),
[walk sharpness](../problems/juggler_cycle_walk_sharpness.md),
[walk arch](../problems/juggler_cycle_walk_arch.md).

## 1. Transport — **EXACT — HUMAN PROOF**

On a CycleMin cycle with minimum \(n\ge 400\), every state obeys
\(x_k\ge (n e^{-D})^{w_k}\) with deficit
\(D=1.05\,e/n+0.7\,o/n^{3/2}\), from the log-deficit recursion
with amplification \(w_k/w_{j+1}\), odd states \(\ge n\), even
states \(\ge n^2\). All charge comparisons happen at the reduced
base \(n'=n e^{-D}\); at the certified floor and window lengths
\(D\le 4.6\cdot 10^{-3}\), so \(\ln n'\ge 17.07\).
(`J-cyclemin-walk-transport`; the certified \(L=50508\) kill by
the walk DP has margin \(1.1204\).)

## 2. The adversary is the hug itinerary — **EXACT — HUMAN PROOF**

Admissible words are exponent walks
\(u_k=(1+\alpha)a_k-k\ge 0\), \(\alpha=\log_2(3/2)\). The hug
itinerary (take \(E\) at the first legal time) is the unique
prefix-minimal admissible walk: at the first disagreement the
other word holds an \(O\) where \(E\) was legal, and the
odd-count gap is a nonnegative \(\{-1,0,+1\}\) path. Since the
charge density is strictly decreasing in \(u\), hug uniquely
maximises the charge. Ceiling-Christoffel prefix-dominance is
**REFUTED** (greedy `OOEO` beats `OOOE` at \((4,3)\)). The
infinite hug walk is rotation by \(\alpha\) on
\(\mathbb R/(1+\alpha)\mathbb Z\), and the charge-per-letter of
the rotation is the Laplace integral
\(C_*(n)=(1/\ln 3)\int_1^3 n^{1-t}t^{-2}\,dt<1/(\ln 3\,\ln n)\).
(`J-cyclemin-walk-hug-exchange`, `J-cyclemin-walk-cstar`.)

## 3. Itinerary identity — **EXACT — HUMAN PROOF**

For every \(L\), the budgeted hug itinerary at \((L,o_{\min})\)
equals the exact IET \(L\)-prefix: the exact rule (E iff
\(u\ge 1\), integer test \(3^a\ge 2^{k+1}\)) keeps
\(u\in[0,1+\alpha)\), forcing exactly
\(o_{\min}=\lceil L\log 2/\log 3\rceil\) odds; a first
budget-forced divergence would make the exact prefix use more
of one letter than its own total. So the leftover charge **is**
a Birkhoff average of the rotation.
(`J-cyclemin-walk-window-envelope`, lemma 1.)

## 4. The DK/Ostrowski envelope — **EXACT — HUMAN PROOF**

\(F(u)=n^{1-2^u}/2^u\) decreases from \(F(0)=1\), so its
circle variation including the wrap jump is \(<2\).
Denjoy–Koksma (KNOWN) bounds every block of length \(q_j\) — a
convergent denominator of \(\theta=\log(3/2)/\log 3\) — within
\(\mathrm{Var}(F)\) of \(q_jC_*\). Any decomposition
\(L=\sum_jb_jq_j\) therefore gives

\[
\bigl|C_L-C_*(n')\bigr|\le \frac{2\,s(L)}{L},\qquad
s(L)=\sum_jb_j .
\]

The \(q_j\) list \(1,2,3,8,19,65,84,485,1054,24727,50508,
125743,176251\) is certified by an interval continued fraction
on the big-integer sandwich \(2^{17087915}>3^{10781274}\),
\(2^{16785921}<3^{10590737}\). Koksma at constant \(1\) stays
**REFUTED** — the correct constant is \(2s(L)\); the six
\(+1/L\) failures are exactly the rows with
excess\(\cdot L>1\). (`J-cyclemin-walk-dk-envelope`.)

## 5. The window theorem — **EXACT — HUMAN PROOF**

Greedy Ostrowski digits obey \(b_j\le a_{j+1}\), so with the
certified quotients \(\theta=[0;2,1,2,2,3,1,5,2,23,2,2,1,\dots]\)
the digit sum on \([50508,301994)\) is at most \(47\), and

\[
\frac{2s(L)}{L}\le\frac{94}{50508}=1.87\cdot 10^{-3}
<0.00514\le\frac1{\ln 3\,\ln n'}-C_*(n')
\]

(the \(J\)-gap from
\(J\le 1-2/\ln n+6/(\ln n)^2\)). Hence, census-free and DP-free,

\[
C_L<\frac1{\ln 3\,\ln n'}
\quad\text{for every } L\in[50508,\,301994).
\]

Exact scan sharpening (**COMPUTATIONALLY VERIFIED**): max
digit sum \(37\) (at \(L=275632\)), uniform envelope margin
\(\ge 5.48\). This discharges the crude-envelope caveat "not a
theorem for every \(L\)" on the window and supersedes both the
walk DP and the 19-row occupancy census \(h\le 4\) for the
envelope side. (`J-cyclemin-walk-window-envelope`.)

## 6. Kills, sharpness, and what stays open

**Kills (COMPUTATIONALLY VERIFIED).** Substituting the DK
bound into the \(6/5\) unroll recovers the same 18 leftover
kills as the certified walk DP (margin \(1.1196\) at
\(L=50508\)); the near-convergent \(L=176251\) survives
(\(0.1588\)). Kill decisions are the per-length finance
comparison \(\theta(L)>(6/5)B\cdot\text{guard}\) — Diophantine,
not envelope-limited. Uniform \(B/\theta<1\) at a fixed floor
stays **REFUTED**.

**Sharpness (OBSERVATION).** A float census of all
\(301993\) lengths at the representative base shows the excess
\(e(L)=L(C_L-C_*)\) is one-sided and window-bounded
(\(e\in(-0.28,4.97]\)); DK is never tight (\(|e|/2s\le 0.476\)).
The accumulation is a quadratic arch along the
partial-quotient-23 tower that closes at a full quotient cycle.
Alternating-sum, additive-digit, and endpoint-coboundary laws
all fail; a human arch bound was the recorded (PARKed)
reopening point. Its period-bound reading is **REFUTED**
([walk arch](../problems/juggler_cycle_walk_arch.md)): the hug
DP already is \(C_L\) and loses at \(L=478245\).

**Open.** Beyond \(q_{13}=301994\) the window theorem needs
deeper certified quotients; killing the remaining
near-convergent survivors is the Diophantine frontier
(Baker/SdW transfer stays **REFUTED**; the DK-arch free-kill
stays **REFUTED**).

## Endpoint

The walk-charge program replaced a certified DP and two finite
censuses with a human chain: transport, hug identification,
itinerary identity, Denjoy–Koksma over certified Ostrowski blocks,
and digit caps. Every claim above carries its ledger row; the
artifacts live under `data/research/juggler/cycle_walk_*`. Since
the consolidation the discrete word layer and the quotient
arithmetic are Lean (`WalkChargeItineraries.lean`,
`OstrowskiSandwich.lean`); the transport recursion, the Laplace
integral, Denjoy–Koksma, and the digit caps stay human.
`RunSurvivorLattice.lean` and the finance Lean layers are
unchanged. Not a halt theorem; the certified period bound stays
\(176251\).
