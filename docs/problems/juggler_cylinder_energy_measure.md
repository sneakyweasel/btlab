# Cylinder energy, measured: the bad cylinders collapse

Status: **CLOSE** (the energy route of Section 10(d) has no numerical
support at any computable scale: the bad-restricted bias energy sits at
its worst-case value from depth about 18 on, because bad cylinders
collapse onto single values). The collapsed-fiber survival question it
raises is a new branch, not this one.

## Problem

Exact bias energy of the cylinders of the Juggler map at the depths
Paper C's hypotheses use, measured by enumeration, no sampling.

## Exact statement

For the odd starts of \((y,2y]\) and a word \(w\) of length \(t\), let
\(\#[w]\) be the cylinder count, \(D(w)=\#[wO]-\tfrac12\#[w]\) the bias,
and for a set \(S\) of words \(E_t(S)=\sum_{w\in S}D(w)^2\) the bias
energy. `Energy.energy_implies_conjecture` (Lean,
`FateEnergyAtoms.lean`) says: if for all large \(y\) and every depth
\(1\le t<\lceil CL(y)\rceil\) the energy over the \(L(y)\)-bad words is at
most \((q-\tfrac12)^2y^2(\log y)^{-2B}/2^t\), with \(\tfrac12<q<p_C\),
\(B>C\log_2x+1+e\) and \(\tfrac7{10}<e<CD(p_C\|q)/\ln2\), every
positive integer reaches \(1\). The question here: what is \(E_t\),
exactly, over all words, over the \(L(y)\)-bad words and over the live
starts (every iterate above the Lean floor \(260\)), for
\(y\in\{10^4,10^5,10^6,10^7\}\) and \(t\le30\)?

## Current literature

`reproduced` and `extended`: the absorbed-cylinder obstruction
([juggler_absorbed_cylinder.md](juggler_absorbed_cylinder.md),
`J-absorbed-cylinder`) proves that starts which have reached \(1\)
overpopulate all-word cylinders, which is why Paper C restricts
\(\mathrm H(C,A)\) to bad words. The measurement reproduces that
(the unrestricted energy is at the worst case by depth about \(20\))
and finds a second mechanism inside the bad words. Paper C Section 11
measured the *sampled* tilted share along depth at \(10^{20}\)--\(10^{50}\)
(forty thousand starts, depths to \(40\)); nothing there is a
per-cylinder statistic. No external result is claimed.

## Branch budget

- **Target:** at computable scales, is the bad-restricted bias energy
  close to the fair-coin value \(N_{\rm bad}/4\), and how does the mass
  of atoms violating \(\#[wO]\le q\#[w]\) behave?
- **Novelty hypothesis:** an exact, unsampled second-moment statistic
  of cylinder splitting at depths approaching \(d(y)\).
- **Falsifier:** the energy ratio to the fair-coin value growing
  systematically with \(t\) or \(y\), or reaching the worst case
  \(C_t/4\) in the dense window.
- **Already killed by?:** none as a measurement; the *unrestricted*
  statistic was already known dead by `J-absorbed-cylinder`, and this
  probe measures the restricted one.
- **Existing machinery:** `floor_power`; the itinerary words;
  `CylinderEnergy.sum_bias_sq` (the identity \(4E_t=2\mathcal C_{t+1}-\mathcal C_t\),
  asserted on every row); the \(L(y)\)-bad criterion of Lemma 8.1 and the
  live criterion of `LiveCountWeight`.
- **Maximum Phase-0 scope:** one exact enumeration of every odd start
  of \((y,2y]\) to depth \(30\) at four scales; the three restrictions;
  two shares. No sampling, no larger scale, no Lean.
- **Promotion criterion:** the bad-restricted ratio \(4E_t/N_{\rm bad}\)
  within a constant factor of \(1\) across \(t\le30\) and the four
  scales, with violator masses decreasing in \(y\).
- **Stop criterion:** the falsifier.

## Balanced-ternary formulation

Not used. The statistic is a parity count on the integer orbit.

## Why BT may be relevant

Not relevant here; no claim.

## Candidate operations / invariants

The three restrictions of \(E_t\) (all, \(L(y)\)-bad, live), the ratios
\(4E_t/N\) (fair coin gives \(1\)) and \(4E_t/\mathcal C_t\) (every atom
fully biased gives \(1\)), the violator masses on both sides, and the
number and largest size of the cylinders. All **COMPUTATIONALLY
VERIFIED** on the recorded ranges.

## Experiments

`python -m research.juggler_sequence.cylinder_energy_measure` writes
`data/research/juggler/cylinder_energy_measure/summary.json`: per scale,
per depth \(0\le t\le30\), per restriction: mass fraction, cylinders,
largest cylinder, \(\mathcal C_t\), \(\mathcal C_{t+1}\), \(E_t\), the
two ratios, and for \(q\in\{0.55,0.60\}\) the odd- and even-side
violator masses and counts; plus the calibration of the formal
constants. Runtime \(253\) s at \(10^7\) (five million starts).

## Conjectures

None. Computational observations are not conjectures.

## Counterexamples

None sought; the branch is a measurement.

## Formalization

`formal/Problems/Juggler/FateEnergyAtoms.lean` carries the reduction
the measurement tests (`Energy.mass_violators_le`,
`Energy.oneSidedShareExc_of_energy`, `Energy.energy_implies_conjecture`),
restricted to the \(L(y)\)-bad words after this measurement showed the
unrestricted form empty. Nothing here is proved about the map beyond
the identity checked on every row.

## Results

**COMPUTATIONALLY VERIFIED** (14 September 2026, exact enumeration).

*The unrestricted energy is dead-orbit dominated.* At every scale the
ratio \(4E_t/\mathcal C_t\) over all words reaches \(1.000\) by depth
\(16\)--\(22\) and the ratio to the fair-coin value settles at about
\(N/55\): \(90\), \(797\), \(6134\), \(44939\) at the four scales. An
orbit that has reached \(1\) has an all-\(O\) tail, so its cylinder is
fully biased at every later depth; this is `J-absorbed-cylinder`, seen
in numbers.

*The bad-restricted energy also reaches the worst case, and its ratio
grows with the scale.* The \(L(y)\)-bad mass decays with depth as
Lemma 8.2 predicts (\(0.11\), \(0.15\), \(0.16\), \(0.20\) of the starts
left at depth \(20\)). Over the bad words, \(4E_t/N_{\rm bad}\) in the
dense window (\(t\) from \(8\) to \(18\)) is about \(2\) at \(10^4\),
\(4\)--\(7\) at \(10^5\), \(16\)--\(29\) at \(10^6\) and \(400\)--\(1500\)
at \(10^7\); and \(4E_t/\mathcal C_t\) over the bad words reaches
\(0.96\) at depth \(20\) for \(10^4\), \(10^5\), \(10^6\) and \(10^7\)
alike, \(1.000\) by depth \(22\)--\(28\), while the largest bad cylinder
at depth \(20\) has \(10\), \(34\), \(243\) and \(11939\) members. This is
not the singleton effect: the bad cylinders are large and fully biased.

*The mechanism is collapse.* At \(10^6\), depth \(12\), the largest bad
cylinder (word `OOOEEEOOOOOO`, \(755\) members spread over
\((1.12\cdot10^6,1.97\cdot10^6)\)) has only five distinct values of
\(J^{12}\) and odd share \(1\): the three even letters contract the whole
scale onto a few hundred values \(n^{27/64}\), and the future is then
the deterministic orbit of that value. At depth \(20\) the largest bad
cylinders are single-valued: \(243\) consecutive odd starts of
\((1361647,1367615)\) with \(J^{20}=2119345842\), \(231\) with
\(J^{20}=1445\), \(222\) with \(J^{20}=1486\). A bad word whose walk
has dipped near \(-L(y)\) has collapsed onto a bounded value above the
floor; from then on its cylinder's letters are constant, and about half
of such cylinders are odd-constant, violating every share bound
\(q<1\) with their full mass.

*The violator masses fall with the scale in the dense window and are
constant in the collapse regime.* Over the bad words at depth \(10\),
\(q=0.55\), the odd-side violator mass is \(0.47\), \(0.26\), \(0.12\),
\(0.05\) of the bad mass at the four scales: larger cylinders average
their parities. At depth \(20\) it is \(0.45\), \(0.49\), \(0.42\), \(0.43\)
at all four scales, with the even side alike: the collapsed cylinders.
The collapse regime begins at depth \(16\)--\(20\) at every scale computed,
while the energy ratio in the dense window is already dominated by the
few collapsed atoms: the second moment is the wrong statistic, the
violator mass the right one, and the two disagree by orders of
magnitude at \(10^7\) (\(4E_t/N_{\rm bad}\approx1500\) against a violating
mass of \(5\%\)).

*The formal bound is not measurable at any computable scale.* With
\(C=28\), \(q=0.51\) (exponent \(CD(p_C\|q)/\ln2=0.79\); the least \(C\)
with exponent above \(0.7\) at that share is \(26\)) the condition
\(B>C\log_2x+1+e\) gives \(B\approx18\) and \(2B+C\approx64\); even fair
splitting, \(E=N/4\), meets the bound only for \(y\) beyond about
\(10^{143}\) (floor \(260\)) or \(10^{124}\) (floor \(3.5\cdot10^8\)). The
measurement can only test the shape a proof would need, and the shape
is the worst one.

## Open questions

Whether the collapsed-but-bad cylinders survive to depth \(d(y)\) with
mass above the per-cylinder allowances of \(\mathrm H(C,A)\) and
\(\mathrm H_q(C,A)\) at scales where the bad words outnumber the
collapse values (\(\Lambda^C\gg N_0^2\), i.e. \(y\gg10^{42}\) at the
certified floor). If they do, both per-cylinder hypotheses are false
as stated, by a construction in the pattern of `J-absorbed-cylinder`
with a dip to a bounded value above the floor in place of absorption;
if the long orbits of the collapse values are too rare, they survive.
The global forms (\(\mathrm P_\theta(C)\), \(\mathrm M_{\theta,q}(C)\))
are untouched by either outcome.

## Decision

**CLOSE.** The falsifier was observed at every computable scale: the
bad-restricted energy reaches its worst-case value from depth \(16\)--\(20\)
on, on large cylinders, and its ratio to the fair-coin value grows with
\(y\) even in the dense window, because a few collapsed atoms dominate
the second moment while carrying little mass. The energy route of
`FateEnergyAtoms.lean` stands as an exact reduction and has no
numerical support as a hypothesis; the right statistic is the violating
mass itself, which falls with the scale in the dense window and is a
constant fraction of the bad mass in the collapse regime, and Paper C's
depth \(d(y)\) lies in the collapse regime as soon as
\(\Lambda^{C+1}\gg N_0\). Do not reopen as a
larger enumeration, a sampled run at \(10^{20}\), or a different
second-moment normalisation. Best next question: a human-proof attempt
at the collapsed-fiber construction, that is, a bad word of depth
\(d(y_k)\) at infinitely many scales whose cylinder is a single fiber
of a bounded value with a long orbit above the floor and mass
\(\gg y_k(\log y_k)^{-A}\); or its refutation by counting the long
orbits of the collapse values.

## Publication assessment

Status: `STRUCTURAL`. Belongs, as an observation, next to Paper C's
Section 11 experiments and Section 10(d): the per-cylinder statistics
of the map at computable scales are collapse-dominated. Not a theorem,
not a halt theorem, and not evidence about the hypotheses at their own
scales.
