# Juggler hug-itinerary exchange and explicit \(C_*(n)\)

Status: **ACTIVE** (Phase 0 decided)

Refinement of
([juggler_cycle_walk_greedy.md](juggler_cycle_walk_greedy.md)).
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not a reopen of the REFUTED Christoffel prefix-dominance
or leftover-cell slogans.

## Problem

Greedy PROMOTE identified the certified walk-charge maximizer with
the hug itinerary, computationally. Is that an exchange lemma for every
feasible \((L,o)\), and is leftover charge-per-letter the explicit
ergodic integral of that walk?

## Exact statement

**No-strand (EXACT — HUMAN PROOF).** On a feasible pair
(\(\mathrm{STEP}\cdot o\ge L\)) the hug rule — take \(E\) iff
\(u\ge 1\) and an even remains, else \(O\) — never strands. The
only candidate strand is \(o_{\mathrm{left}}=0\),
\(e_{\mathrm{left}}\ge 1\), \(u<1\). Then \(a=o\),
\(k=L-e_{\mathrm{left}}\), so
\(u=(\mathrm{STEP}\cdot o-L)+e_{\mathrm{left}}\ge e_{\mathrm{left}}\ge 1\).

**Exchange lemma (EXACT — HUMAN PROOF).** Among admissible
\(u\ge 0\) walks with a prescribed \((L,o)\), hug is the unique
prefix-min path. Write \(\delta_k=a_k(w)-a_k(\mathrm{hug})\). Until
the first disagreement the prefixes agree, so the state
\((a,k,u)\) and the remaining counts agree. Hug takes \(O\) only
when \(E\) is illegal (\(u<1\) or no even left); then \(w\) cannot
take \(E\) either. The first disagreement is therefore hug-\(E\)
versus \(w\)-\(O\), after which \(\delta=1\). Thereafter \(\delta\)
changes by \(+1,0,-1\). To reach \(\delta=-1\) the paths must pass
through \(\delta=0\) and then hug-\(O\) versus \(w\)-\(E\); but
\(\delta=0\) restores the same state, and that split is illegal.
Hence \(\delta\ge 0\) at every \(k\), so
\(a_k(\mathrm{hug})\le a_k(w)\). Equality at all \(k\) iff
\(w\) is hug.

**Unique maximizer (EXACT — HUMAN PROOF).**
\(g(u)=1/(n^{2^u}\,2^u\ln n)\) is strictly decreasing for
\(n>1\), \(u\ge 0\). Prefix-min \(u\) therefore uniquely maximises
walk charge. The certified survey \(B\) is that unique maximum.

**Rotation (EXACT — HUMAN PROOF).** The infinite hug walk (no
letter budget) is \(T(u)=u+\alpha\) on \([0,1)\) and \(T(u)=u-1\)
on \([1,1+\alpha]\), i.e. rotation by \(\alpha=\log_2(3/2)\) on
the circle \(\mathbb R/(1+\alpha)\mathbb Z\). The rotation number
\(\alpha/(1+\alpha)=1-\log_3 2\) is irrational, so the unique
invariant probability is Lebesgue/\((1+\alpha)\). Mean height is
\((1+\alpha)/2\).

**Explicit \(C_*(n)\) (EXACT — HUMAN PROOF).** Charge-per-letter
along the infinite hug itinerary is

\[
C_*(n)
=\frac1{\ln 3}\int_1^3 n^{1-t}\,t^{-2}\,dt
=\frac1{\ln 3\,\ln n}
\int_0^{2\ln n}\frac{e^{-s}}{(1+s/\ln n)^2}\,ds.
\]

The integrand of the second form is at most \(e^{-s}\), so

\[
C_*(n)\;<\;\frac1{\ln 3\,\ln n}.
\]

Substitution: \(t=2^u\) sends \([0,1+\alpha]\) to \([1,3]\) and
\(1/(1+\alpha)={\ln 2}/{\ln 3}\).

**Finite leftovers do not sit under \(C_*\)
(COMPUTATIONALLY VERIFIED).** On the 19-row survey,
\(C_{\mathrm{hug}}-C_*\in[-1.7\cdot 10^{-8},\,1.57\cdot 10^{-5}]\).
The inequality \(C_{\mathrm{hug}}\le C_*\) is false. The excess is
the \(1/L\) size predicted by Koksma / Denjoy–Koksma for a
bounded-variation integrand (\(\mathrm{Var}(f)<1\)).

**Simple bound on the 19 leftovers
(COMPUTATIONALLY VERIFIED, not a theorem).** Every leftover hug
\(C\) is below \(1/(\ln 3\,\ln n')\). Replacing the DP by that
closed envelope would still kill the same 18 lengths (margin
\(1.008\) at \(L=50508\)) and still miss \(L=176251\) (margin
\(0.143\)). Uniform \(B/\theta<1\) at this floor stays false. This
is not a certified period bound: \(C_{\mathrm{hug}}\le 1/(\ln 3\,\ln n')\)
is not proved.

No cycle of any length — not claimed.

## Current literature

- Greedy hug-itinerary maximizer —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_greedy.md](juggler_cycle_walk_greedy.md))
- Mechanical extremizer —
  **CLOSE** / **REFUTED** Christoffel prefix-dominance
  ([juggler_cycle_walk_mechanical.md](juggler_cycle_walk_mechanical.md))
- Walk-excursion maximizer identification —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_excursion.md](juggler_cycle_walk_excursion.md))
- Coupled walk charge / certified survey —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md))
- Irrational rotation unique ergodicity —
  **KNOWN**
- Christoffel leftover-cell reduction —
  **REFUTED** (`juggler_christoffel_one_parameter`)
- Baker/Rhin transfer —
  **REFUTED** (`juggler_baker_kills_near_convergents`)
- Every start reaches 1 — not claimed

Project relationship: **extended** (human identification of the
already certified walk DP; not a new finance identity).

## Branch budget

```text
Mathematical target     Write and verify an exchange lemma that
                        hug is the unique prefix-min admissible
                        walk; identify C_*(n) with the IET integral
                        (1/ln 3) ∫_1^3 n^{1-t} t^{-2} dt
Novelty hypothesis      The prefix-min fact is a δ-invariant
                        (not a Christoffel theorem); C_* is not a
                        mysterious 0.048 but an explicit Laplace
                        integral, so B has a closed envelope
Falsifier               A feasible pair where hug is not unique
                        prefix-min; or the integral disagrees with
                        mechanical C_* beyond discrepancy
Existing machinery      hug_word, prefix_min_odds, mechanical_average,
                        charge_density, certified_log_n, survey B
Maximum Phase-0 scope   Human write-up of exchange + no-strand;
                        brute-force δ-check on L≤12; quadrature of
                        C_* vs mechanical / IET prefix; simple bound
                        vs the 19 leftovers. No Lean, no Paper A,
                        no N0, no new DP, no certified new kills
Promotion criterion     Exchange lemma written as EXACT — HUMAN
                        PROOF; integral matches mechanical C_* to
                        the already-seen 10^{-4} spread
Stop criterion          A hole in the exchange (completability);
                        integral mismatch; or the bound is too
                        weak and the integral is only a
                        REPARAMETERIZATION of the mechanical average
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Hug is the unique prefix-min admissible walk —
  **EXACT — HUMAN PROOF** (`juggler_walk_hug_exchange`)
- Infinite hug is rotation by \(\alpha\) on
  \(\mathbb R/(1+\alpha)\mathbb Z\) —
  **EXACT — HUMAN PROOF**
- \(C_*(n)=(1/\ln 3)\int_1^3 n^{1-t}t^{-2}\,dt
  <1/(\ln 3\,\ln n)\) —
  **EXACT — HUMAN PROOF**
- \(C_{\mathrm{hug}}\le C_*\) —
  **REFUTED** (excess up to \(1.57\cdot 10^{-5}\))
- Leftover \(C<1/(\ln 3\,\ln n')\) —
  **COMPUTATIONALLY VERIFIED** on the 19-row survey
- Uniform \(B/\theta<1\) at fixed \(N_0\) —
  **REFUTED** (already; confirmed on every envelope)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_exchange`
- Artifacts: `data/research/juggler/cycle_walk_exchange/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_exchange.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_hug_exchange` — **EXACT — HUMAN PROOF**. Hug is
the unique prefix-min admissible walk of a given \((L,o)\) and
therefore the unique walk-charge maximizer.

## Counterexamples

- \(C_{\mathrm{hug}}\le C_*\) fails on survey offsets (worst
  excess \(1.57\cdot 10^{-5}\) at \(L=180467\)).
- The Christoffel counterexamples of the parent branches stand:
  \((4,3)\) is hug `OOEO`, not `OOOE`.

## Formalization

None. No `WalkExchange.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem.

## Results

Classification **WALK_EXCHANGE_GREEN**.

- Brute-force exchange: \(35/35\) feasible pairs with
  \(L\le 12\), \(507\) admissible words, zero undercuts
- Witness \((4,3)\): hug `OOEO`, the other admissible word is
  `OOOE`, first split is \(E\) versus \(O\)
- \(C_*=0.047941\) at the \(50508\) reduced base; mechanical and
  IET prefixes of \(10^5\) give \(0.047947\) (relative
  \(1.16\cdot 10^{-4}\)); Lebesgue mean height \(0.792481\)
- Simple bound \(1/(\ln 3\,\ln n')=0.053285\)
- Survey: all 19 leftover \(C\) below the simple bound; the same
  18 lengths die under \(C_*\), the simple bound (margin
  \(1.008\) at \(50508\)), and the Koksma add-on \(C_*+1/L\);
  \(L=176251\) survives (margin \(0.159\) hug, \(0.143\) bound)

## Open questions

A Koksma / Denjoy–Koksma envelope
\(C_L\le C_*(n)+1/L\), or the cruder
\(C_L\le 1/(\ln 3\,\ln n)\), for leftover hug itineraries. Either would
make the 18 kills DP-free. Do not raise \(N_0\) and do not claim
a uniform \(B/\theta\) gap.

## Decision

**PROMOTE.** The exchange lemma is a finite \(\delta\)-invariant,
not a restatement of the greedy census: first disagreement is
forced, and the odd-count gap cannot go negative. The mysterious
survey plateau \(C\approx 0.048\) is the Laplace integral of
Lebesgue measure on the circle of length \(1+\alpha\), with the
elementary bound \(C_*<1/(\ln 3\,\ln n)\). That is not a
reparameterization of Beatty language and not a leftover-cell
reopen. The finite inequality \(C_{\mathrm{hug}}\le C_*\) is
false; the simple bound is only computationally a 19-row
envelope, so it is not promoted as a certified kill table.

Best next question: does Koksma give
\(C_L\le C_*(n')+1/L\) (or \(C_L\le 1/(\ln 3\,\ln n')\)) for
every leftover hug itinerary, making the 18 kills DP-free?

## Publication assessment

Status: `THEOREM`.

A human identification of the walk-charge maximizer and a closed
form for the infinite density. Not a paper candidate until a
finite-\(L\) envelope is proved. Not a halt theorem.
