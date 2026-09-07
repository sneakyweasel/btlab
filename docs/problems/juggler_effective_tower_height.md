# Juggler effective tower height: pricing the good-base reset of \(s_\theta\)

Status: **CLOSE** (the consistent reset-split tolerance is the critical
share itself; the fair-coin room of any reset rule is an accounting
inconsistency)

Not a Paper B estimate, not a pressure census, not a third formulation
of the frontier. The objects are the existing hypotheses
`J-tao-pressure-form` and the reset split of
[juggler_pressure_direct.md](juggler_pressure_direct.md).

## Problem

What is the right notion of "reset" for the tilted odd share
\(s_\theta(t)\), how much tilted live mass does it leave uncontrolled,
and what bias on the uncontrolled towers can the split tolerate when
the same bias is charged to the measure and to the bound?

## Exact statement

**Absorption (EXACT — HUMAN PROOF, elementary).** For real \(x\ge0\),
\(\lfloor\sqrt{\lfloor x\rfloor}\rfloor=\lfloor\sqrt x\rfloor\). Hence
an even step never deepens the nested floor tower: after a word with
odd letters at positions \(i_1<i_2<\dots\) and \(j_r\) even letters
after the \(r\)-th odd one, the orbit value is
\(\lfloor\lfloor\lfloor n^{a_1}\rfloor^{a_2}\rfloor\cdots\rfloor\)
with \(a_r=3/2^{j_r+1}\). The tower *height* is the number of odd
letters, not the depth; every letter of the orbit is the parity of
such a tower.

**Good base (EXACT — HUMAN PROOF).** An even step taken at exponent-walk
height \(u\) (before the step) maps the current population onto every
integer \(m\) of a range, with multiplicity \(\#([w]\cap I_m)\) for an
interval \(I_m\) of starts of length \(y^{1-2^{u-1}}\) (up to the
\(O(1)\) endpoint effect of each inner floor, negligible when the
image of \(I_m\) at every level has length \(\gg1\)). So the base is
dense with smooth multiplicity iff \(u<1\), and its fibres are long
enough for Paper B's localized theorems (\(\ge y^{1/2}\), fate note
§7) iff \(u\le0\). From such a base every word class of depth
\(\le4\) splits fairly (Paper B Corollary 4.9 with smooth weights by
partial summation). The *effective height* is the number of odd
letters since the last good base, the *effective depth* the number of
letters since it, and the next letter is Paper-B-controlled iff
effective height \(\le3\) and effective depth \(\le4\).

**Reset split (EXACT — HUMAN PROOF).** Let \(\mu_t\) be the tilted
live mass fraction whose next letter is uncontrolled. If uncontrolled
letters split with odd share \(\le\beta\), then
\(s_\theta(t)\le\tfrac12(1-\mu_t)+\beta\mu_t+o(1)\). The *tower
tolerance* \(\beta_*(L,C)\) is the largest \(\beta\) for which this
bound, averaged over the second half of the depths \(t<d=\lceil
CL\rceil\), stays below \(p_C\) — with \(\mu_t=\mu_t(\beta)\) computed
on the tilted walk-live measure in which uncontrolled letters split
at \(\beta\) too. \(\mathrm M_{\theta,q}(C)\) would follow, by Paper B
alone, from "every uncontrolled tower level splits with odd share
\(\le\beta_*\)".

## Current literature

- Tao note §10 / Paper C §9, `J-tao-pressure-form` — `known`: the
  weakest form and its reset split.
- [juggler_pressure_direct.md](juggler_pressure_direct.md) — `known`:
  reset at any \(E\), fair-coin \(\mu_4\in[0.13,0.17]\), sparse
  high-walk images. This branch refines the reset and reprices it.
- Paper B Corollary 4.9 (depth-\(\le4\) word classes), fate note §7
  localization to intervals \(\ge P^{1/2}\) — `known`.
- Literature check (7 Sep 2026, web): no 2025–2026 result on
  equidistribution of Hardy-of-floor compositions or on the Juggler
  map's termination; the audit of
  [juggler_rate_free_floor_hardy.md](juggler_rate_free_floor_hardy.md)
  stands.

## Branch budget

```text
Mathematical target     Does resetting s_θ only at good bases (E at
                        u ≤ 0) leave room in M_{θ,q}, and what tower
                        bias does the split tolerate consistently?
Novelty hypothesis      The lab's reset at any E has room but
                        uncontrollable complements; a reset only at
                        good bases has Paper-B-controllable
                        complements and might still have room.
Falsifier               The live band u > -L forbids good bases at
                        accessible L; or the consistent tolerance
                        collapses to p_C, making the split H_q on the
                        towers.
Existing machinery      fair_tilted_live_suffix_odd_mass, the exponent
                        walk of tao_reduction, Paper B Cor. 4.9.
Maximum Phase-0 scope   One fair-coin DP over (odd count, effective
                        height, effective depth) with four reset
                        rules and a bisection on β. No orbit census,
                        no Lean, no manuscript edit.
Promotion criterion     A reset rule with Paper-B-controllable
                        complement and consistent tolerance β_* < 1
                        strictly above p_C.
Stop criterion          β_* = p_C + o(1) for every controllable rule.
```

## Balanced-ternary formulation

None. The objects are the exponent walk and floor towers on ordinary
positive integers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Absorption identity and tower-height bookkeeping — **EXACT — HUMAN
  PROOF**.
- Good-base criterion \(u<1\) (dense) / \(u\le0\) (Paper-B-localizable)
  with fibre length \(y^{1-2^{u-1}}\) — **EXACT — HUMAN PROOF** for
  the pure power map, **OBSERVATION**-level for the \(O(1)\) inner-floor
  endpoint effects (verified at the OE and OOEE fibres by hand:
  \((4/3)m^{1/3}\) and \((16/9)m^{7/9}\)).
- Fair-coin uncontrolled shares and the consistent tolerance —
  **COMPUTATIONALLY VERIFIED** (DP, cross-checked against
  `fair_tilted_live_suffix_odd_mass` to \(6\cdot10^{-17}\)).
- The climbing threshold: a pool splitting at odd share \(\beta\) has
  tilted odd probability \(e^\theta\beta/(e^\theta\beta+1-\beta)\),
  above \(\log2/\log3\) iff \(\beta>0.533\) at \(\theta_{20}\) —
  **EXACT — HUMAN PROOF**.

## Experiments

- Probe: `research.juggler_sequence.effective_tower_height`
  (`python -m research.juggler_sequence.effective_tower_height`).
- Artifact: `data/research/juggler/effective_tower_height/summary.json`.
- Tests: `tests/research/juggler_sequence/test_effective_tower_height.py`.
- No orbit sample. Scales \(10^{12},10^{50},10^{100}\) at
  \(N_0=3.5\cdot10^8\), \(C\in\{20,43,230\}\), and the asymptotic
  band \(L\in\{8,20,40,80\}\) at \(C\in\{20,43\}\).

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays ACTIVE;
\(\mathrm P_\theta\) / \(\mathrm M_{\theta,q}\) remain its weakest form.

## Counterexamples

None. The route died by the tolerance collapsing to \(p_C\), not by a
counterexample to \(\mathrm M_{\theta,q}\).

## Formalization

`formal/Problems/Juggler/TowerAbsorption.lean` (kernel-checked; axioms
`propext`, `Classical.choice`, `Quot.sound` only):
`sqrt_iter_eq_iff` — `j` iterated `Nat.sqrt` of `x` equals `s` iff
`s^(2^j) ≤ x < (s+1)^(2^j)`; `floorPower_iter_of_even` — on an even run
the Juggler map is iterated `Nat.sqrt`; `floorPower_odd_even_run` and
`floorPower_odd_even_run_eq_iff` — an odd step followed by `j` even
steps is `Nat.sqrt^[j+1] (n^3)`, the cell `s^(2^(j+1)) ≤ n^3 <
(s+1)^(2^(j+1))`, i.e. the value `⌊n^{3/2^(j+1)}⌋` with one floor and
no nesting; `floorPower_oe_eq_iff` recovers the `OE` fiber of
`FateContagion` as `j = 1`. This is the absorption clause; the DP is
bookkeeping and is not formalized.

## Results

Classification **GOOD_BASE_RESET_ROOM_IS_ASYMPTOTIC_ONLY** for the
fair-coin shares, and **tolerance \(\beta_*=p_C+O(1/d)\)** for every
rule with a Paper-B-controllable complement.

Fair-coin uncontrolled share (second-half mean) against the budget
\(2p_C-1\):

```text
  scale    L      C    budget   u<=0    u<1    any E   never
  1e12    0.526   20   0.199    1.000   0.798  0.188   1.000
  1e50    2.558   20   0.199    0.854   0.738  0.139   1.000
  1e50    2.558   43   0.233    0.931   0.868  0.149   1.000
  1e100   3.553   20   0.199    0.795   0.694  0.137   1.000
  1e100   3.553   230  0.256    0.982   0.970  0.156   1.000
  L=20     —      20   0.199    0.356   0.330  0.131   1.000
  L=40     —      20   0.199    0.216   0.207  0.130   1.000
  L=80     —      20   0.199    0.147   0.146  0.130   1.000
  L=80     —      43   0.233    0.236   0.231  0.144   1.000
```

- At \(10^{12}\) the honest rule leaves *everything* uncontrolled:
  \(L=0.526\), so an even step at \(u\le0\) lands below \(-L\) and no
  live start ever has a good base after depth \(0\). The live band
  is the collapsed regime's enemy: the population the tilt selects
  lives at \(u>0\), where every \(E\)-image is sparse.
- The honest share falls with \(L\) (the tilted walk at \(C=20\)
  drifts at \(-0.05\) per step and reaches \(u\le0\) once the band is
  wide) and crosses the budget near \(L\approx45\), i.e.
  \(y\approx10^{10^{14}}\); at \(C=43\) it has not crossed by
  \(L=80\); at \(C=230\) the walk is nearly driftless and the share
  stays above \(0.6\). Larger \(C\) is worse for this split.
- **The consistent tolerance.** Charging the bias \(\beta\) to the
  measure as well as to the bound:

```text
  scale   C    p_C      beta*(u<=0)  beta*(u<1)  beta*(never)  beta*(any E)
  1e50   20   0.5994    0.6016       0.6045      0.5986        0.7793
  1e50   43   0.6163    0.6162       0.6162      0.6162        0.7861
  1e100  20   0.5994    0.602        —           —             0.78
  1e100  230  0.6282    0.628        —           —             —
  L=20   20   0.5994    0.599        —           —             0.7822
  L=80   20   0.5994    0.599        —           —             0.7822
```

  For every rule whose complement is Paper-B-controllable the
  tolerance is \(p_C\) up to \(O(1/d)\), at every scale including
  \(L=80\): the split reduces \(\mathrm M_{\theta,q}\) to "uncontrolled
  tower levels split \(\le p_C\)", which is \(\mathrm H_q\) on the
  towers at \(q=p_C\). The mechanism is exact: a pool splitting at
  \(\beta\) has tilted odd probability
  \(e^\theta\beta/(e^\theta\beta+1-\beta)\), which exceeds
  \(\log2/\log3\) once \(\beta>0.533\); such a pool climbs, takes no
  even step at \(u\le0\), is never reset, and its tilted mass grows
  faster than the fair population's whenever \(\beta>\tfrac12\), so
  \(\mu_t\to1\) and the bound tends to \(\beta\) itself.
- The only rule with a tolerance above \(p_C\) — reset at any
  \(E\), \(\beta_*\approx0.78\), independent of \(L\) — is the one
  whose complement the laboratory already showed is not
  Paper B (sparse high-walk images). One can have room or control,
  not both; the fair-coin "room" of either rule is the inconsistency
  of taking \(\beta=\tfrac12\) in the measure and \(\beta=1\) in the
  bound.

Not claimed: \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\), any
tower split, termination.

## Open questions

None in this laboratory. The export is unchanged:
\(\mathrm M_{\theta,q}(C)\) as recorded in the Tao dossier. What this
branch adds is the exact price of the reset split: it buys nothing
beyond \(\mathrm H_{p_C}\) on the uncontrolled towers, at any scale.

## Decision

**CLOSE.** The stop criterion fired: for every reset rule with a
Paper-B-controllable complement the consistent tolerance is
\(\beta_*=p_C+O(1/d)\), so the split is \(\mathrm H_q\) on the towers
at the critical share; the rule with room (\(\beta_*\approx0.78\)) is
the one whose complement is uncontrollable. The fair-coin room of
`juggler_pressure_direct` (\(\mu_4\in[0.13,0.17]\)) and the asymptotic
room of the honest rule (\(L\gtrsim45\) at \(C=20\)) are both the
\(\beta=\tfrac12\)-versus-\(\beta=1\) inconsistency and should not be
read as room. Do not reopen as a short-interval localization of
Paper B (it would move the good-base threshold from \(u\le0\) to
\(u<1\), whose tolerance is the same \(p_C\)), as a depth-5 repair of
the controlled set, or as a census of effective heights. Best next
question: none on this line.

## Publication assessment

Status: `ARCHIVED`. A pricing of one estimate the paper deferred, with
one structural fact (the absorption identity and the tower-height
bookkeeping) worth a sentence in the fate note. Not a paper claim.
