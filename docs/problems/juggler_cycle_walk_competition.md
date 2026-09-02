# Juggler walk-charge vs finance: the asymptotic competition

Status: **ACTIVE** (Phase 0 decided)

Successor of the DK/Ostrowski envelope
([juggler_cycle_walk_ostrowski.md](juggler_cycle_walk_ostrowski.md)),
answering the synthesis question it left open: finance identifies
the itineraries that are globally almost neutral (the near-resonances
\(\varepsilon_L=1-2^L/3^o\)); the greedy/IET walk determines the
maximum local compensation those itineraries can extract. Which asymptotic
scale wins? Not a halt theorem, not a floor raise, not a uniform
\(B/\theta\) claim (REFUTED at fixed floor), and not a Baker revival
(\(\theta\) is computed exactly, never lower-bounded).

## Problem

For a survivor length \(L\) with minimal odd count \(o\), the DK/IET
envelope prices the optimal walk charge census-free:
\(B_{\rm DK}=\bigl(C_*(n')+2s(L)/L\bigr)\,L/(n'\ln n')\) with
\(n'=ne^{-D}\). A cycle requires
\(\theta(L)\le\tfrac65 B_{\rm DK}\). Both sides are now pure
arithmetic at any hypothetical floor. Along the survivor lattice —
the negative-side convergent denominators of
\(\theta_{\rm rot}=\log(3/2)/\log 3\) and their semiconvergent
fans — does the floor-scaled competition admit permanent
separation \(\tfrac65 B_{\rm DK}/\theta\le 1-\delta\), or does the
ratio approach \(1\) along increasingly good approximants?

## Exact statement

**Deep certification (COMPUTATIONALLY VERIFIED, exact integers).**
\(x=\log 2/\log 3\) lies strictly between the consecutive
convergents \(171928773/272500658\) and \(53715833/85137581\), by
the two pure big-integer comparisons \(2^{272500658}>3^{171928773}\)
and \(2^{85137581}<3^{53715833}\) (interval width
\(4.31\cdot 10^{-17}\)). The interval CF certifies the
\(\theta_{\rm rot}\) partial quotients
\([0;2,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4]\) and denominators through
\(85137581\).

**Dangerous seeds.** The negative-side convergent denominators
(\(Lx\) just below an integer, so \(\theta\) small) are
\(50508,\ 176251,\ 16785921,\ 85137581\); the intermediate hard
lengths are the semiconvergent fans \(176251+k\cdot 301994\)
(\(k=1..54\); \(k=1\) is the known hard leftover \(478245\)) and
\(16785921+k\cdot 17087915\) (\(k=1..3\)). Exact \(\theta\) for
every row by big-int power sandwiches (the fan is evaluated
incrementally; \(o\)-minimality is certified per row by
\(3^{o-1}\le 2^L<3^o\)).

**Break-even floor (COMPUTATIONALLY VERIFIED).** For each row,
\(n^*(L)\) is the smallest floor at which the DK envelope kills
\(L\) (monotone bisection with outward guards, restricted to the
transport-lemma domain \(n\ge 30L\)). Anchors reproduce the
laboratory: \(n^*(50508)=2.37\cdot 10^7<26254995\),
\(n^*(176251)=1.38\cdot 10^8<162849448\), and the DK margin at the
in-flight floor is \(1.1980\), just below the certified DP value
\(1.1983\).

**Scaling law (COMPUTATIONALLY VERIFIED).** On all 74 interior
rows,

\[
\frac{n^*(\ln n^*)^2\,\theta(L)}{L}
\;=\;
\frac{6}{5\ln 3}\,\bigl(J\text{-corrected}\bigr),
\qquad
\text{ratio}\in[0.8956,\,0.9409],
\]

monotone along the seeds and matching \(J(n^*)=1-2/\ln n^*+\cdots\):
the constant \(6/(5\ln 3)\) is asymptotically exact. On the seeds
with a certified next denominator,
\(n^*(\ln n^*)^2/(q_jq_{j+1})\in\{1.077,\ 0.912,\ 1.140\}\): the
break-even floors grow like \(q_jq_{j+1}\).

**Self-consistent schedule (COMPUTATIONALLY VERIFIED, hypothetical
floors).** With anchors \(26254995\) (certified) and \(162849448\)
(in flight) and \(n_{j+1}=n^*(\text{first survivor at } n_j)\), the
walk terminates after 61 levels at floor \(2.64\cdot 10^{13}\) with
every priced row killed and kill-contiguity over the rows at every
level. The required-improvement sequence starts at \(6.30\)
(level 0, survivor \(176251\)) and \(2.31\) (level 1, survivor
\(478245\)), decays to its minimum \(\mathbf{1.0735}\) at mid-fan
(\(L\approx 8.6\cdot 10^6\)), then rises toward the seed jumps
(floor growth up to \(6.2\times\), \(5.1\times\) at the last seed).

No cycle of any length — not claimed. No new period bound — floors
beyond \(162849448\) are arithmetic schedule points only.

## Current literature

- DK/Ostrowski census-free envelope \(|C_L-C_*|\le 2s(L)/L\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_ostrowski.md](juggler_cycle_walk_ostrowski.md))
- Transport lemma and reduced base \(n'=ne^{-D}\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md))
- Uniform \(B/\theta<1\) at a fixed floor — **REFUTED**
  ([juggler_cycle_walk_excursion.md](juggler_cycle_walk_excursion.md));
  this branch prices the floor-scaled competition instead
- Baker lower bounds kill near-convergents — **REFUTED**
  (`juggler_baker_kills_near_convergents`); \(\theta\) here is exact
- New-floor extension (floor \(162849448\)) — in flight
  ([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md));
  used only as an anchor, not edited
- Every start reaches 1 — not claimed

Project relationship: **extended** (the synthesis of Paper A
finance and the Section-5 walk program into one computable
competition).

## Branch budget

```text
Mathematical target     Along the survivor-lattice lengths, does the
                        floor-scaled ratio (6/5)B_DK/theta admit permanent
                        separation at the feasible schedule, or does it
                        approach 1 along good approximants?
Novelty hypothesis      The break-even floor obeys
                        n*(ln n*)^2 theta/L -> 6/(5 ln 3), so the future of
                        the DP/DK machinery is the computable Diophantine
                        law n*(q_j) ~ q_j q_{j+1}, testable with exact
                        big-int arithmetic and no floor verification
Falsifier               ratio -> 1 along a subsequence at schedule floors,
                        or the break-even floors fail the Diophantine law
Existing machinery      o_min/theta exact (cycle_finance), x-sandwich +
                        interval CF + greedy digits (cycle_walk_ostrowski),
                        c_star_integral + gap_lower (exchange/envelope),
                        deficit_D (cycle_walk_charge)
Maximum Phase-0 scope   One probe + dossier + conjecture + tests + journal.
                        Arithmetic only: no floor raise, no new certified
                        period bound, no Lean, no Paper A edit, no CLI,
                        no touching the running 162849448 extension
Promotion criterion     A clean verified scaling law for n*(L) on all
                        certified convergent seeds, plus a decisive
                        dichotomy verdict
Stop criterion          Break-even floors fail any Diophantine law, or the
                        question degenerates to a reparameterization of the
                        REFUTED uniform-B/theta or Baker claims
```

## Balanced-ternary formulation

None required. The competition lives on the exponent lattice
\(\mu a-b\) and the convergents of \(\log 2/\log 3\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Deep sandwich for \(x\) and certified \(\theta_{\rm rot}\)
  denominators through \(85137581\) — **COMPUTATIONALLY VERIFIED**
  (two big-int comparisons)
- Exact \(\theta(L)\) with per-row \(o\)-minimality certificates,
  incremental along fans — **COMPUTATIONALLY VERIFIED**
- Break-even floor \(n^*(L)\) with outward guards —
  **COMPUTATIONALLY VERIFIED**
- Scaling law \(n^*(\ln n^*)^2\theta/L\to 6/(5\ln 3)\) with the
  \(J\)-correction \(1-2/\ln n^*\) — **OBSERVATION**
  (exact on 74 rows; the limit statement is prose)
- Diophantine growth \(n^*(q_j)\asymp q_jq_{j+1}\) — **OBSERVATION**
  (three certified seed instances)
- Uniform separation \(\delta>0\) across schedule levels — fails:
  required improvement dips to \(1.0735\); no uniform-ratio theorem
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_competition`
- Artifacts: `data/research/juggler/cycle_walk_competition/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_competition.py`

No CLI. No Lean. Paper A unchanged. The certified walk DP and the
running new-floor extension are not edited.

## Conjectures

`juggler_walk_finance_competition` — **CONJECTURE** (the asymptotic
dichotomy): along the dangerous convergent seeds \(q_j\) of
\(\theta_{\rm rot}\), the DK break-even floors satisfy
\(n^*(q_j)(\ln n^*)^2=\Theta(q_jq_{j+1})\) and the per-level
required improvement is bounded below by \(1\) but not by any
\(1+\delta\): the competition is asymptotically sharp, and no fixed
floor kills the whole lattice. Supported by the certified range
(seeds through \(85137581\), 61 schedule levels, minimum
requirement \(1.0735\)).

## Counterexamples

None against the scaling law. The would-be uniform statements are
already REFUTED elsewhere and are not reasserted: uniform
\(B/\theta<1\) at a fixed floor
(`juggler_walk_excursion_optimum` survey), Baker kills
(`juggler_baker_kills_near_convergents`).

## Formalization

None. No new Lean, no `sorry`. The only exact-claim layers are the
two big-int comparisons, the per-row power sandwiches, and the
guarded float comparisons shared with Theorem 4.6.

## Results

Classification **WALK_COMPETITION_GREEN**.

- Deep sandwich certified (width \(4.31\cdot 10^{-17}\));
  \(\theta_{\rm rot}\) denominators certified through \(85137581\);
  the greedy digit sums of all 19 laboratory leftovers are
  unchanged by the deeper list
- Cross-checks: exact \(\theta\) reproduces every stored value
  (relative error \(0\)), DK margins reproduce the certified
  19-row survey (max relative error \(2.3\cdot 10^{-16}\)), and the
  in-flight floor anchor gives DK margin \(1.1980<1.1983\) (DP) at
  \(176251\) — still a kill
- 78 rows priced: 4 dangerous seeds, 57 fan members, 16 offsets,
  1 positive-side convergent (\(301994\), \(\theta\approx 2/3\),
  harmless as predicted)
- \(n^*\): \(2.37\cdot 10^7\) (50508), \(1.38\cdot 10^8\) (176251),
  \(3.48\cdot 10^8\) (478245), \(4.54\cdot 10^{11}\) (16785921),
  \(2.64\cdot 10^{13}\) (85137581)
- Scaling law ratio \([0.8956, 0.9409]\), monotone along seeds,
  matching \(J(n^*)\): the constant \(6/(5\ln 3)\) is asymptotically
  exact — the DK machinery has no hidden constant-factor slack left
- Diophantine growth: \(n^*(\ln n^*)^2/(q_jq_{j+1})\in
  \{1.077, 0.912, 1.140\}\)
- Schedule: 61 levels, all priced rows killed by \(2.64\cdot 10^{13}\),
  kill-contiguity at every level; required improvement
  \(6.30\to 2.31\to\cdots\to\mathbf{1.0735}\) (mid-fan) \(\to\)
  seed jumps; separation at the anchored laboratory floors is
  \(\delta=0.107\) and \(0.165\) (max \(\rho\) over killed rows
  \(0.893\), \(0.835\))

The dichotomy verdict in the certified range: **every fixed length
dies at a finite computable floor, but the floors diverge like
\(q_jq_{j+1}\) and the per-level slack dips to \(7\%\)**. Finance
(endpoint resonance) and the walk charge (path cost) never cross
permanently: the machinery is asymptotically sharp in its constant
and can only chase the lattice, floor by floor. Killing the whole
infinite lattice needs an ingredient that grows with the
approximation quality — not a better constant.

## Open questions

Is the mid-fan minimum of the required improvement bounded away
from \(1\) uniformly over fans (it is \(1.0735\) on the \(55\)-fan;
the next fans have partial quotients \(4, 3, 1, 1, 15,\dots\)), or
does a subsequence of fans drive it to \(1\)? Equivalently: does
\(\liminf_j \theta(L_{j+1})L_j/(\theta(L_j)L_{j+1})>1\) hold along
the schedule survivors? Do not raise \(N_0\); do not reopen the
uniform-ratio claim.

## Decision

**PROMOTE.** The Phase-0 promotion criterion is met: the scaling
law \(n^*(\ln n^*)^2\theta/L\to 6/(5\ln 3)\) is verified on every
interior row with the \(J\)-correction resolved, the Diophantine
growth \(n^*\asymp q_jq_{j+1}\) holds on all certified seeds, and
the dichotomy is answered in the certified range: no permanent
crossing, asymptotically sharp constant, per-level slack down to
\(1.0735\). This fixes the strategic picture — further floor
campaigns buy single fan members at \(q_jq_{j+1}\) cost, and the
open frontier is the fan-minimum question above.

## Publication assessment

A quantitative synthesis section for Paper A's successor: the
finance gap and the walk charge are complementary measurements of
one near-resonance, and their competition reduces to a computable
Diophantine scaling law with an asymptotically exact constant.
Claim tags: the certifications and cross-checks are
COMPUTATIONALLY VERIFIED; the limit statements are OBSERVATION /
CONJECTURE. Not a halt theorem.
