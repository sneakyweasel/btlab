# Descent-free flights: envelope, dichotomy, and the shared lattice

Status: laboratory extract. Date: 1 September 2026.

This consolidates the flight program — the open-orbit counterpart of
Paper A §5 — into one reading path. It is **not a halt theorem**,
not a "no cycle of any length" claim, not a divergent-orbit
existence claim, not a floor raise, **not a second manuscript**, and
not a Paper A or Paper B edit. Paper A remains a cycle paper; this
extract is the laboratory companion for descent-free prefixes.

Dossiers, in program order:
[flight envelope](../problems/juggler_flight_envelope.md),
[walk-divergence](../problems/juggler_flight_walk_divergence.md),
[anchor-period](../problems/juggler_flight_anchor_period.md),
[divergent structure](../problems/juggler_flight_divergent_structure.md),
[return quantization](../problems/juggler_flight_return_quantization.md).
Closed or parked companions (do not reopen from here):
[record composition](../problems/juggler_flight_record_composition.md)
(`REPARAMETERIZATION`),
[odd-tower fragment](../problems/juggler_odd_tower_fragment.md)
(`CLOSE`),
[DK pricing](../problems/juggler_flight_dk_pricing.md) (`CLOSE`),
[valley composition](../problems/juggler_flight_valley_composition.md)
(`CLOSE` on the exclusion reading).
The terminating-side height-law PARK stays with the
[flight envelope](../problems/juggler_flight_envelope.md) branch.
The walk-charge extract
([juggler_walk_charge_note.md](juggler_walk_charge_note.md)) is the
cycle-side parent.

## The bar

The composition branch asked whether this arc should be a note, and
which results meet it. The extract prints only statements that are
new off-cycle and not a restatement of Paper A §5:

| Prints | Ledger | Why it meets the bar |
|---|---|---|
| Two-sided envelope | `J-flight-envelope-transport` | Lean transport on `AboveAnchor`, not only `CycleMin` |
| Walk-height law | `J-flight-height-law` | Doubly exponential lower bound in the walk height |
| Walk-divergence and dichotomy | `J-flight-walk-divergence` | Hug-hugging adversary is cycle-exclusive |
| Anchor-period instance | `J-flight-anchor-period` | Conditional period \(780239\) with no new floor |
| Divergent structure | `J-flight-divergent-structure` | Pointwise laws, not just \(\sup\) |
| Return quantization | `J-flight-return-quantization` | Shared \(\log_2 3\)-lattice with cycle survivors |

Composition widths, uniqueness packaging, the odd-tower placement,
the DK split, and valley-composition exclusion do not meet the bar:
they are recorded in §7 so they are not re-derived.

A *descent-free flight* is an infinite orbit \(x_0=n\ge 2\),
\(x_{k+1}=T(x_k)\), with \(x_k\ge n\) for all \(k\). Write
\(a_k\) for the odd count of the length-\(k\) prefix,
\(w_k=3^{a_k}/2^k\) for the walk weight, and
\(u_k=a_k\log_2 3-k\) for the exponent walk. Hug domination
\(a_k\ge\mathrm{hugOdds}(k)\) and the floor \(u_k\ge 0\) are Lean
on every `AboveAnchor` prefix
(`aboveAnchor_prefix_odds_ge_hug`, `aboveAnchor_prefix_pow_le`).

## 1. Flight envelope — **EXACT — LEAN VERIFIED**

On `AboveAnchor(n,w)` with \(n\ge 400\), every prefix of length
\(k\) obeys the two-sided transport
(`aboveAnchor_transport`, `follows_log_le_walkWeight`,
`WalkTransport.lean`)

\[
w_k\,(\log n-\Delta)
\;\le\;
\log x_k
\;\le\;
w_k\log n,
\qquad
\Delta=\frac{1.05\,e}{n}+\frac{0.7\,o}{n\sqrt n}.
\]

The upper side needs no anchor (floors only lose) and holds on
every realized itinerary. At an ascent peak this is
\(\Phi(n)=\log H(n)/\log n=w_P\) up to the transport error: the
parity itinerary determines the peak. The seven high-flyers attain the
upper side to sub-bit precision (peaks \(0.7\)–\(6.5\) million
bits). (`J-flight-envelope-transport`.)

## 2. Walk-height law — **EXACT — LEAN VERIFIED**

If the walk has height at least \(B\) doublings at step \(k\)
(\(2^{k+B}\le 3^{a_k}\)), then
\(\log x_k\ge 2^B(\log n-\Delta)\): heights along a descent-free
prefix are doubly exponential in the walk height
(`aboveAnchor_height_of_walk`). Composed with §3, every
descent-free flight realizes this rate along an unbounded walk.
(`J-flight-height-law`.)

## 3. Walk-divergence and the dichotomy — **EXACT — HUMAN PROOF**

Every descent-free flight has unbounded exponent walk:
\(\sup_k u_k=\infty\). In particular no flight stays within
bounded excess of the hug itinerary (Lean hug band
\(0\le u^{\mathrm{hug}}_k<\log_2 3\)).

*Proof.* A walk bounded by \(B\) forces \(x_k\le n^{2^B}\) (Lean
`power_bound_word`). Determinism: a first repetition closes a
cycle, and until then the prefix is injective, so pigeonhole
gives eventual periodicity. The period word is a realized return
and is strictly expanding, \(2^p<3^o\) (Lean
`cycle_strict_envelope`). Each traversal adds
\(\delta=\log_2(3^o/2^p)>0\) to the walk — contradiction.
\(\square\)

The laboratory dichotomy, at the certified floor
\(N_0=162\,849\,448\): a descent-free flight starts above \(N_0\)
and is exactly one of

1. **closure** — finite injective preperiod, then a nontrivial
   cycle with minimum \(>N_0\) and period \(\ge 478\,245\); the
   walk then diverges linearly at the cycle's expansion rate; or
2. **infinite injective trajectory** — all states distinct,
   \(x_k\to\infty\) (this is §5, not merely \(\limsup\)).

The hug-hugging adversary of Paper A §5 is cycle-exclusive: an
open flight cannot realize it. Paper B's depth-\(\le 4\) layer
does not kill it (ambient density; ambient-to-orbit transfer
`TRANSFER_COMPLEX` stays `REFUTED`). (`J-flight-walk-divergence`.)

## 4. Anchor-period law — **COMPUTATIONALLY VERIFIED**

**Anchor-transfer lemma (EXACT — HUMAN PROOF).** A bounded-walk
descent-free flight from anchor \(n\) enters a cycle with
minimum \(\ge n\). Both kill right-hand sides (parity finance,
DK envelope) are strictly decreasing in the floor, so the kill
tables at floor \(n\) apply with no descent campaign. The
anchor floors *both* the injective preperiod and the eventual
cycle.

**Instance.** Any descent-free flight from
\(n\ge 3.5\cdot 10^8\) with bounded walk enters a cycle of
period \(\ge 780\,239=176251+2\cdot 301994\). Combined with §3:
every such flight either has unbounded states or an eventual
cycle of period \(\ge 780\,239\). Certification: lengths
\(<478245\) already die at \(N_0\) and persist upward; all
\(301995\) lengths in \([478245,780239]\) scanned at the
anchor (conservative float prefilter, \(112\) exact \(\theta\),
\(11\) parity survivors); the ten below \(780239\) die under
the census-free DK envelope (blocker margin \(1.0053\)); first
survivor exactly \(780239\). Not an unconditional period bound
and not a floor raise. (`J-flight-anchor-period`.)

The remaining schedule (conditional ladder toward period
\(\sim 10^8\) at anchor \(2.64\cdot 10^{13}\)) is deferred:
no new mechanism, machinery gravity.

## 5. Divergent structure — **EXACT — HUMAN PROOF**

A non-eventually-periodic descent-free flight satisfies, pointwise:

1. all states distinct, \(x_0=n\) the global minimum,
   \(x_k\to\infty\);
2. linear peak growth \(\max_{j\le k}x_j\ge n+k\);
3. \(u_k\ge\log_2(\log x_k/\log n)\to\infty\), hence
   \(\sup_{j\le k}u_j\ge\log_2(\log(n+k)/\log n)\);
4. hug excess \(a_k-\mathrm{hugOdds}(k)\to\infty\);
5. *recurrent hug domination*: infinitely many cofinal record
   indices (tail minima) from which the tail is itself a
   descent-free flight, so hug domination restarts from every
   record.

The log-log rate is sharp at realized peaks (probe slack \(0.0\)
on the seven high-flyers). No faster pointwise rate follows from
these layers. Exclusion of divergent flights is not claimed:
that is the all-depth equidistribution frontier, and even that
program is silent on a single orbit (§7).
(`J-flight-divergent-structure`.)

## 6. Return quantization — **EXACT — HUMAN PROOF**

At a record with anchor \(m\ge 400\), any later state \(M\) at
distance \(p\) with odd count \(o\) and doubly-log jump
\(\delta=\log_2(\log M/\log m)\) obeys

\[
\delta
\;\le\;
o\log_2 3-p
\;\le\;
\delta+\Delta',
\qquad
\Delta'=-\log_2\!\Bigl(1-\frac{\Delta}{\ln m}\Bigr),\quad
\Delta\le\frac{1.05\,p}{m}.
\]

(Left: `follows_log_le_walkWeight`. Right:
`aboveAnchor_transport`. Record validity: §5 point 5.)

Admissible jumps occupy a measure fraction
\(O(p/(m\ln m))\) of the lattice gap \(\log_2 3\) (at the
frontier anchor \(3.5\cdot 10^8\): \(4\cdot 10^{-9}\) at
\(p=19\); vacuous only past \(p^*\approx 0.63\,m\ln m\approx
7\cdot 10^9\) steps). Near-returns \(\delta\le\varepsilon\)
force \(\theta_p=o_{\min}(p)\log_2 3-p\le\varepsilon+\Delta'\),
and \(\theta_p\) *is the hug walk height*. The return-time set
\(R_\varepsilon=\{p:\theta_p\le\varepsilon\}\) has three-gap
structure; the shortest time is \(19\)
(\(\theta_{19}=12\log_2 3-19=0.01955\)); as
\(\varepsilon\downarrow 0\) the spectrum passes through the
cycle survivors \(84\) and \(1054\). Cycles and flights share
one Diophantine skeleton.

Cycle pricing is the \(\delta=0\) slice of the same jump budget.
DK/parity pricing of *lengths* needs near-closure; recurrent hug
domination alone prices nothing. Census mirror: all realized
near-returns on orbits \(n\le 2000\) land on \(\{19,38\}\).
(`J-flight-return-quantization`.)

## 7. What does not meet the bar

- **Record composition** (`J-flight-record-composition`,
  `REPARAMETERIZATION`). The lattice is an additive monoid, so
  summing record segments is the per-pair law at a wide pair.
  Re-anchored widths beat the direct width and give unbounded
  range on deficit-summable flights, but that is finitely many
  applications of §6.
- **Uniqueness trichotomy.** Determinism plus §§3–5; not a new
  obstruction. State-packing as an exclusion attack is CLOSE
  ([juggler_flight_valley_composition.md](../problems/juggler_flight_valley_composition.md)):
  hug cylinders fill; records strictly increase; later peaks
  live at larger scales; comparable-scale occupancy is the
  existing pigeonhole or hug-hugging.
- **Odd towers.** \(\mathcal T_\infty=\{x:F^j(x)\text{ odd for all
  }j\}\), \(F(x)=\lfloor x^{3/2}\rfloor\), is incomparable to
  all-depth equidistribution (density cannot empty a
  density-zero set). Every lab route is recorded negative
  knowledge (`ODD_LANDING_SETS_ARE_FORWARD_ORBITS`,
  `TRANSFER_COMPLEX`). Towers sit above \(N_0\) and are pinned
  by §1 at walk weight \((3/2)^k\).
- **DK split.** Ostrowski/DK *prices* open hug prefixes (Paper A
  Theorems 5.7–5.8, Lean `hug_charge_maximal`); the *kill*
  needs \(\theta=1-2^L/3^o\) from \(x_L=n\). Infinite hugging is
  already dead by §3, not by DK.
- **Valley composition.** The *exclusion* reading is CLOSE
  (`juggler_flight_valley_composition`): occupancy of comparable-scale
  envelope windows is the walk-divergence pigeonhole or
  hug-hugging; composition across records enlarges the admissible
  set; terminating-side re-anchor cannot exclude a descent-free
  flight. The *height-law* reading (re-anchor after first descent
  for the \(19.6\%\) peak-after-descent class) stays PARK with the
  flight-envelope branch and is not an exclusion mechanism.
- **Hug cylinders.** Three CLOSEs do not say prefixes cannot be
  realized: mechanical lift dies at exact single-cell `empty_ooe`;
  prefix realization fills to depth \(28\) and shows fixed-depth
  equidistribution cannot kill a flight; formal-versus-realized
  finds no extra predicate on generic prefix-NC. Construction
  stays PARK (`juggler_hug_flow_window`): backward `OE`/`OOE`
  freedom is positive, depth \(1\) on windows
  \(H\asymp X^{1/3}\) is `J-hug-flow-window-depth-one`.
  Interval-ET depth \(2\) is CLOSE (`J-hug-flow-image-gap`):
  the image of a depth-\(1\) window is \(3\sqrt X\)-separated,
  not an interval. \(C_L\ne\emptyset\) is not a theorem and is
  not opened from this extract.

## Endpoint

The flight program replaced an open-orbit question (can the hug
adversary live off-cycle?) with a closed descriptive arc:
Lean envelope and height law, walk-divergence, a conditional
period ladder whose first rung is certified, pointwise structure
for the divergent case, and a quantization law that identifies
the cycle survivor fan with the near-zeros of the hug walk.
Every printed claim carries its ledger row. The discrete
transport and hug lemmas are Lean (`WalkTransport.lean`,
`AboveAnchorWalk.lean`, `Envelope.lean`); the infinite-orbit
glue (pigeonhole, records, injectivity) stays human.

The program is terminal on the descriptive side. The last named
flight-side reopen (valley-composition exclusion) is CLOSE:
occupancy is the existing pigeonhole. Further flight-side progress
requires either the cycle Diophantine blocker \(L=478245\) or a
new pointwise handle on the parity of iterated \(\mathrm{isqrt}\)
(odd towers). Neither is opened from this extract. Not a halt
theorem; the unconditional period bound stays \(478245\).
