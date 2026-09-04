# Near-convergent survivors of the Juggler map after the walk-charge blocker

Status: **external mathematics**. Not a laboratory branch, not a
Juggler construction, and not a Phase-0 kill. Paper A Corollary 5.11
already gives period at least \(780239\) at the certified floor
\(N_0=350000000\). What remains after Baker is REFUTED and further
\(N_0\) campaigns are PARK is a trichotomy: one frozen instance, one
classical continued-fraction question, and one recorded per-orbit
leftover. This page is the export. It constrains cycle *states*. It
does not bound Paper C's free term \(\psi_F\).

The laboratory record is
[juggler_cycle_diophantine_survivors.md](../problems/juggler_cycle_diophantine_survivors.md).
Do not wrap this page as a successor research phase.

## Import

Paper A
([juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md))
is a black box. At the certified descent floor \(N_0=350000000\)
the walk charge excludes every length below the \(k=2\)
semiconvergent fan member

\[
780239=176251+2\cdot 301994.
\]

That is Corollary 5.11 and the ledger row
`J-cycle-period-seven-hundred-eighty-thousand`. The stored non-kill
([L780239.json](../../data/research/juggler/cycle_walk_charge/N350000000_kills/L780239.json))
has \(\theta=3.471\cdot 10^{-6}\), walk margin \(0.6049\), required
improvement \(14.46\), and `certified_excludes: false`. The
survivors are finance-survivors, not candidate cycles.

A finance/walk kill at a fixed floor is determined by three
quantities: the exact relative gap
\(\theta(L)=(3^{o_{\min}}-2^L)/3^{o_{\min}}\), the walk envelope
\(B\), and the floor \(N_0\). Paper A computes the first exactly,
runs the second at the hug DP, and certifies the third. Killing
\(L=780239\) at this floor, or killing the infinite family of later
fan members uniformly, is the leftover this page names.

## Closed routes

The three kill doors at a fixed floor are shut. The rest of the
Diophantine wall is shut with them. Search
[negative_knowledge.md](../negative_knowledge.md) before reopening
any of these.

**Gap lower bounds cannot help.** Dominance
([juggler_cycle_gap_baker.md](../problems/juggler_cycle_gap_baker.md)):
any correct \(\delta\le 3^o-2^L\) produces a finance \(n_{\max}\) at
least as large as the exact-gap \(n_{\max}\). The exact gap at
\(L=780239\) is already known and does not kill. Rhin / Simons–de
Weger Lemma 12 is weaker than the exact gap on every tested length.
The slogan that a Baker-type transfer kills the near-convergents at
a realistic floor is **REFUTED**
(`juggler_baker_kills_near_convergents`). Collatz obtains an
exponentially small *upper* bound on \(\Lambda\) from \(m\)-cycle
geometry; Juggler finance only gives
\(\Lambda\le O(L/(n\log n))\).

**The envelope cannot be tightened enough.** The hug DP *is*
\(C_L\). The DK-arch free-kill of the previous blocker \(478245\)
is **REFUTED**
([juggler_cycle_walk_arch.md](../problems/juggler_cycle_walk_arch.md);
`juggler_walk_arch_kills_blocker`). A valid tightening of
\(2s(L)\) sits above the already-computed hug charge.

**Raising \(N_0\) is PARK.** The DK break-even of \(780239\) is
\(n^*=5.54\cdot 10^8\) and buys exactly one fan member. The next
*seed* \(16785921\) waits at \(4.54\cdot 10^{11}\)
([juggler_descent_floor.md](../problems/juggler_descent_floor.md)).
Do not open \(N_0=5.54\cdot 10^8\).

The other wall members stay closed:
Paper A \(\times\) Paper B merge
(`juggler_cycle_paper_merge`);
affine \(n\)-gap
([juggler_cycle_affine_n_gap.md](../problems/juggler_cycle_affine_n_gap.md));
inhomogeneous Wu–Wang
([juggler_cycle_inhomogeneous_log.md](../problems/juggler_cycle_inhomogeneous_log.md));
p-adic coupling
([juggler_cycle_padic_coupling.md](../problems/juggler_cycle_padic_coupling.md));
fan multipoint
([juggler_cycle_fan_multipoint.md](../problems/juggler_cycle_fan_multipoint.md));
fan-successor rigidity
([juggler_cycle_walk_fan_successor.md](../problems/juggler_cycle_walk_fan_successor.md));
Christoffel
([juggler_cycle_christoffel.md](../problems/juggler_cycle_christoffel.md));
near-tight monochrome
([juggler_cycle_near_tight.md](../problems/juggler_cycle_near_tight.md)).
Wu–Wang width
([juggler_cycle_walk_fan_growth.md](../problems/juggler_cycle_walk_fan_growth.md))
is a cap only: it cannot give \(a=O(1)\) or kill a leftover.
Deeper certified quotients past \(q_{13}=301994\) extend the
window theorem; they do not kill \(780239\).

The peak-pair dossier
([juggler_cycle_diophantine.md](../problems/juggler_cycle_diophantine.md))
is a different object (`DIOPHANTINE_REPACKAGING`).

## Trichotomy

The leftover splits into three inequivalent questions.

**Instance.** Exclude \(L=780239\) at the frozen floor
\(N_0=3.5\cdot 10^8\). Because \(\theta\) is exact, \(B\) is the
hug DP, and the floor is PARK, this needs a constraint that is
none of those three. No unused mechanism is recorded.

**Family.** Drive the walk-finance required-improvement infimum
over all dangerous fans \(L_k=q+kQ\) away from \(1\). Already
reduced
([juggler_cycle_walk_fan_minimum.md](../problems/juggler_cycle_walk_fan_minimum.md)):

\[
\ln R_{\min}\approx\frac{4}{A+B},\qquad
e^{4/(a+2)}\le R_{\min}\lesssim e^{4/a}.
\]

Fan sharpness along a subsequence if and only if the
dangerous-position partial quotients of \(\log 2/\log 3\) are
unbounded. That equivalence is the conjecture
`juggler_walk_fan_minimum_law` (instances
**COMPUTATIONALLY VERIFIED** on both certified fans). Boundedness
of those quotients is a classical **OPEN** problem: Gauss–Kuzmin
genericity expects unbounded, and \(23\) and \(55\) already occur,
but no proof is known either way. The walk-competition program
terminated at this reduction.

**Long cycles.** The floor-free gap transfer
\(n\log n\cdot\min(\Lambda,1)\le 2L\) (Paper A Theorem 4.10, Lean
`cycleMin_gap_transfer`) with Rhin's measure excludes every cycle
with \(L^{14.3}\le n\log n/915\) (Corollary 4.11,
`J-cyclemin-short-cycle-rhin`). That is the *short* regime. The
finance survivors live at \(L\approx n^{0.64}\). Paper A §6
records the remaining problem as a per-orbit parity statement at
depth \(L\), and records it as open **and not as a program**. The
mechanical fixed-point band of a survivor word has the
finance-predicted count and a fair-coin realized parity
([juggler_cycle_mechanical_window.md](../problems/juggler_cycle_mechanical_window.md),
CLOSE).

The boxed external question is the family half:

\[
\text{Are the dangerous-position partial quotients of }\log 2/\log 3\text{ unbounded?}
\]

That is a question in classical Diophantine approximation. It is
not a dynamical construction, and it should not be rewritten as
one. The instance half is not a laboratory kill. The long-cycle
half stays the recorded leftover of Paper A §6.

## Firewall

This page constrains the fate Lachesis from the inside: finance
and the walk charge bound the *states* of a hypothetical cycle
(minimum above \(3.5\cdot 10^8\), period at least \(780239\)).
Paper C Theorem 1 constrains the *basin*: if the cycle exists,
its basin is a two-way closed class with log-count
\(\gg(\log x)^{0.448}\). The two do not meet
([juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md),
§6.3). Neither touches the free term \(\psi_F\) of the exact
first-letter decomposition: the ascending branch \(OO\) sends
mass to \(x^{3/2}\), and its return is the nested-floor parity at
all depths.

Not claimed: a halt theorem; no cycle of any length; a bound on
\(\psi_F\); a new period; a proof that the partial quotients of
\(\log 2/\log 3\) are bounded or unbounded.

Literature: `rhin-1987-pade-irrationality`,
`simons-de-weger-2005-collatz-m-cycles`,
`wu-wang-2014-irrationality-measure-log3`,
`kuipers-niederreiter-1974-uniform-distribution`.
