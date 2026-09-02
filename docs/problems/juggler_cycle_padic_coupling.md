# Juggler archimedean / p-adic coupling

Status: **ARCHIVED**

Literature-suggested attack B after the walk-finance terminal
reduction
([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md)):
couple archimedean closeness of \(2^L\) and \(3^o\) with a large
2-adic or 3-adic valuation on the *same* cycle quantity. Not a
residue-modular census
([juggler_cycle_mod_closure.md](juggler_cycle_mod_closure.md)),
not a Baker/Rhin reopen
([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)),
not the parked \(x^3-y^2\) campaign, not a floor raise, and not
a halt theorem.

## Problem

Chim's explicit two-\(p\)-adic-logarithm bounds constrain
\(\lvert\alpha_1^{b_1}-\alpha_2^{b_2}\rvert_p\) when the two
powers are \(p\)-adically comparable. Juggler floor cells produce
exact integer relations and strong divisibility. Does a
hypothetical CycleMin cycle force one quantity to be
simultaneously archimedean-close (from \(2^L\approx 3^o\)) and of
large 2-adic or 3-adic valuation, in a way that
lifting-the-exponent or Chim makes incompatible?

## Exact statement

**The finance gap is a 2-unit and a 3-unit
(EXACT — HUMAN PROOF).**
For \(L\ge 1\) and \(o\ge 1\),
\(3^o-2^L\) is odd, and
\(3^o-2^L\equiv-(-1)^L\pmod 3\not\equiv 0\). Hence
\(v_2(3^o-2^L)=v_3(3^o-2^L)=0\). Checked exactly on the leftover
lengths \(19,84,569,1054\); the lemma covers
\(25781,50508,176251\).

**The ratio is not a 2-adic or 3-adic unit
(EXACT — HUMAN PROOF).**
\(v_2(2^L/3^o)=L\) and \(v_3(2^L/3^o)=-o\). In \(\mathbb Q_2\)
the \(2^L\) term vanishes, so \(2^L/3^o-1\to-1\) and
\(v_2=0\). In \(\mathbb Q_3\) the \(3^{-o}\) term dominates and
\(v_3(2^L/3^o-1)=-o\). Chim's form
\(\lvert\alpha_1^{b_1}-\alpha_2^{b_2}\rvert_p\) therefore does
not apply at \(p=2,3\): the two powers have unequal valuation and
\(\lvert 2^L-3^o\rvert_p=1\).

**The closeness-to-1 forms are independent of \(\theta\)
(EXACT — HUMAN PROOF / KNOWN).**
LTE gives \(v_2(3^o-1)=O(v_2(o))\) and
\(v_3(2^L-1)=O(v_3(L))\). Those are the quantities Chim *would*
bound (how close \(3^o\) is to \(1\) in \(\mathbb Z_2^\times\),
or \(2^L\) to \(1\) in \(\mathbb Z_3^\times\)). They do not see
how close \(2^L\) is to \(3^o\). On the leftovers:
\(v_2(3^{12}-1)=4\), \(v_2(3^{53}-1)=1\).

**The return identity has bounded 2-valuation
(EXACT — HUMAN PROOF).**
On a cycle, \(\Delta=n^{3^o}-n^{2^L}=n^{2^L}(n^{3^o-2^L}-1)\).
CycleMin \(n\) is odd and the gap \(3^o-2^L\) is odd, so
\(v_2(\Delta)=v_2(n-1)\). The valuation does not grow with \(L\)
and does not grow as \(\theta\to 0\).

**Last-even defect chunks are odd on odd landings
(COMPUTATIONALLY VERIFIED).**
If the landing \(y\) is odd and the last state is even, then
\(\rho\) is odd and
\(\operatorname{powGap}(y^2,\rho,2^{L-1})\) is odd. Realized
\(\mathtt{OOE}/\mathtt{OOOEE}\) at \(25,365,1517,1000057\) all
have \(v_2(\mathrm{last\ chunk})=0\). There is no forced high
2-valuation in the defect assembly to couple with.

**Local cell remainders stay inside the width bound
(COMPUTATIONALLY VERIFIED).**
On \(53\) \(\mathtt{OOE}\) starts in \([13,400)\),
\(\max v_2(\rho)=4\), \(\max v_3(\rho)=5\), and no remainder
has \(v_2\ge 8\). The cell width \(2y+1\) already caps the
local valuation.

No cycle of any length — not claimed.

## Current literature

- Chim two \(p\)-adic logarithms —
  **known** (`chim-2025-p-adic-two-logarithms`). The bound is
  on \(v_p(\alpha_1^{b_1}-\alpha_2^{b_2})\) when the powers are
  comparable. It does not apply to \(2^L\) versus \(3^o\) at
  \(p=2,3\).
- Wu–Wang linear-independence measure of \(1,\log 2,\log 3\) —
  **known** (`wu-wang-2014-irrationality-measure-log3`). An
  archimedean two-logarithm refinement; not a \(p\)-adic
  coupling. Attack C packages it as fan-width growth.
- Rhin / Laurent–Mignotte–Nesterenko / Simons–de Weger —
  **known**; the archimedean transfer is already
  **CLOSE** / **REFUTED**
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)).
- Cycle-scale modular closure —
  **CLOSE** / **REFUTED** leftover-killer
  ([juggler_cycle_mod_closure.md](juggler_cycle_mod_closure.md)).
  Defects are free residues once \(2Y+1>m\). This branch asks
  for a growing *valuation*, not a forbidden residue.
- Global defect and the return leftover —
  **EXACT — LEAN VERIFIED**
  (`global_defect_identity`, `image_eq_start_defectRatio`)
- Cycle finance —
  **EXACT — LEAN VERIFIED** (`cycleMin_finance`)
- 2-adic itinerary cylinders —
  **CLOSE**
  ([juggler_2adic_integer_bridge.md](juggler_2adic_integer_bridge.md))
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a coupling leftover-killer;
the valuation lemmas themselves are **known**.

## Branch budget

```text
Mathematical target     Does any exact Juggler cycle identity
                        produce a single quantity that is
                        simultaneously archimedean-close from
                        2^L ≈ 3^o and of large 2-adic or 3-adic
                        valuation from the floor cells or the
                        return?
Novelty hypothesis      Floor divisibility plus archimedean
                        closeness of the same Q yields a
                        Chim / LTE contradiction that residue
                        censuses and Baker cannot see
Falsifier               3^o−2^L is a 2-unit and a 3-unit;
                        2^L/3^o is not a p-adic unit at p=2,3;
                        LTE on n^{gap}−1 is v_2(n−1); local
                        remainders and last-even chunks have
                        no growing valuation
Existing machinery      global_defect_identity;
                        image_eq_start_defectRatio;
                        cycleMin_finance; cycle_mod_closure;
                        cycle_gap_baker; accumulatedDefect
Maximum Phase-0 scope   Exact v_2/v_3 of leftover gaps; unit
                        obstruction; LTE grid; realized-word
                        defect valuations; OOE local window.
                        No Chim constant import, no Lean, no
                        residue census, no floor raise
Promotion criterion     A quantity Q with |Q|_∞ / main → 0
                        along near-convergents and v_2(Q) or
                        v_3(Q) growing with L or with 1/θ
Stop criterion          No such Q; Chim does not apply at
                        p=2,3; the identities are known LTE
                        or global_defect reparameterizations
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. Powers of \(2\) and \(3\) enter as the even
and odd floor exponents, not as a trit encoding.

## Candidate operations / invariants

- \(v_2(3^o-2^L)=v_3(3^o-2^L)=0\) —
  **EXACT — HUMAN PROOF**
- \(2^L/3^o\) not a 2-adic or 3-adic unit —
  **EXACT — HUMAN PROOF**
- LTE \(v_2(n^{k}-1)\) for odd \(n\), odd \(k\) equals
  \(v_2(n-1)\) —
  **KNOWN** / **COMPUTATIONALLY VERIFIED** on the grid
- Cycle \(\Delta\) has \(v_2=v_2(n-1)\) —
  **EXACT — HUMAN PROOF**
- Last-even \(\operatorname{powGap}\) odd on odd landings —
  **COMPUTATIONALLY VERIFIED**
- Local \(\rho\) valuation growing with \(L\) or \(\theta\) —
  **REFUTED**
- Archimedean / \(p\)-adic coupling leftover-killer —
  **REFUTED** (`juggler_cycle_padic_coupling`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_padic_coupling`
- Artifact: `data/research/juggler/cycle_padic_coupling/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_padic_coupling.py`
- Window: exact leftover gaps \(L\le 1054\); modular lemma
  through \(176251\); LTE on odd \(n\le 99\), \(k\le 24\);
  realized \(\mathtt{OE}/\mathtt{OOE}/\mathtt{OOOEE}/\mathtt{OOEOOE}\)
  at \(13,25,365,1517,1000057\); \(\mathtt{OOE}\) local defects
  on \([13,400)\). Fast suite only. No CLI. No new Lean.

## Conjectures

`juggler_cycle_padic_coupling` — **REFUTED**.

## Counterexamples

- Leftover gaps at \(L=19,84,569,1054\): exact
  \(v_2=v_3=0\). Falsifier of a high-valuation finance gap.
- \(2^{19}/3^{12}\) has 2-valuation \(19\) and 3-valuation
  \(-12\). Falsifier of Chim at \(p=2,3\).
- Hypothetical return at \(n=13\), \(L=19\):
  \(v_2(\Delta)=v_2(12)=2\), independent of the tiny \(\theta\).
- \(365\) \(\mathtt{OOE}\): last chunk has \(v_2=0\);
  \(\max v_2(\rho)=2\). Falsifier of forced defect-assembly
  valuation.
- \(\mathtt{OOE}\) window: no local \(v_2\ge 8\).

## Formalization

None added. The identities are already
`global_defect_identity` and `image_eq_start_defectRatio`.
The floors are already `cycleMin_finance`. No
`PadicCoupling.lean`, no Chim import, no `sorry`. Paper A is
unchanged.

## Results

Classification **PADIC_COUPLING_CLOSED**.

- **Gap units** — **EXACT — HUMAN PROOF**, exact check on
  four leftovers (`cycle_padic_coupling/summary.json`).
- **Unit obstruction** — **EXACT — HUMAN PROOF**.
- **LTE grid** — **COMPUTATIONALLY VERIFIED**, \(1176\) pairs,
  zero mismatches.
- **Return valuation** — **EXACT — HUMAN PROOF**:
  \(v_2(\Delta)=v_2(n-1)\).
- **No coupled realized itinerary** — **COMPUTATIONALLY VERIFIED**.
- **No new cyclic obstruction.**

## Open questions

None from 2-adic / 3-adic coupling of a single
\((L,o)\) quantity. Do not reopen modular closure, Baker, or
defect congruence. The other two literature attacks are
separate branches: multi-point constraints
([juggler_cycle_fan_multipoint.md](juggler_cycle_fan_multipoint.md))
and fan-growth
([juggler_cycle_walk_fan_growth.md](juggler_cycle_walk_fan_growth.md)).

## Decision

**CLOSE**. The coupling target is empty at \(p=2,3\). The
finance gap is never divisible by \(2\) or \(3\); the ratio
\(2^L/3^o\) is close to \(1\) archimedeanly *because* it is far
from \(1\) in \(\mathbb Q_2\) and \(\mathbb Q_3\); Chim's
comparable-powers form does not apply; LTE on the return
identity produces only \(v_2(n-1)\); last-even defect chunks
on odd landings are odd. This is not a residue census and not
a reason to import a better Baker constant. No Paper A edit,
no ledger row, no new Lean, no \(N_0\) raise.

Best next question: none from archimedean / 2-adic / 3-adic
coupling of one \((L,o)\) pair.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
literature-suggested attack; not a second manuscript and not
a Paper A edit.
