# Diophantine walls

Killed claim: Baker / Rhin / Simons–de Weger on \(\lvert 3^o-2^L\rvert\)
kills near-convergents at a realistic floor; Paper B analytics merge
into Paper A finance; an \(n\)-dependent lower bound along \(F_1,F_2,F_3\)
escapes Baker dominance; inhomogeneous Wu–Wang supplies a third
coefficient; archimedean closeness couples to a large \(2\)-adic or
\(3\)-adic valuation; a cycle forces two incompatible fan approximations;
\(478245\to 780239\) is a CF-forced class; leftover words are a
one-parameter Christoffel necklace; near-tightness forces a monochrome
tower.
Kill: Rhin/SdW Lemma 12 is weaker than the exact finance gap on every
tested length; merge needs improvement \(32.5\) at \(L=25781\) and
\(223\) at \(L=50508\) against an uncertified constant \(9/8\); \(G\)
is a function of \((L,o_{\min})\) alone; \(\lvert p+\Lambda\rvert\ge 1-\lvert\Lambda\rvert\);
\(3^o-2^L\) is a \(2\)-unit and a \(3\)-unit so Chim 2025 does not
apply at \(p=2,3\); one global \((L,o)\); leftover \(\varepsilon\)
misses classical CF bounds by \(36\times\) at \(478245\); Hamming to
monochrome grows; \(1+q=n^{3^o-2^L}\).
Kind: `REFUTED` / `METHOD_OBSTRUCTION`.
Do not reopen: Baker transfer; Paper A × Paper B merge; affine
\(n\)-gap; inhomogeneous WW; p-adic coupling; fan multipoint;
a laboratory kill of the near-convergents past \(780239\).

Members: `juggler_baker_kills_near_convergents`,
`juggler_cycle_paper_merge`, `juggler_affine_n_gap_escapes_dominance`,
`J-affine-n-gap-escapes-dominance`,
`juggler_inhomogeneous_ww_beats_finance`,
`juggler_cycle_padic_coupling`, `juggler_fan_multipoint_constraints`,
`juggler_fan_successor_rigidity`, `juggler_christoffel_one_parameter`,
`J-christoffel-one-parameter`, `juggler_cycle_near_tight_monochrome`,
`J-cycle-near-tight-monochrome`.

**Complement, not a kill (CLOSE).** The floor-free gap transfer
\(n\log n\cdot\min(\Lambda,1)\le 2L\) (Paper A Thm 4.10, Lean
`cycleMin_gap_transfer`) with Rhin's measure excludes every cycle
with \(L^{14.3}\le n\log n/915\) — the *short* regime, where the
REFUTED floor-level transfer never competed. Corollary 4.11's own
substitution \((a,b,c)=(0,-L,o)\) has \(a=0\) and \(H=L\), so Wu-Wang
applies to it and sharpens the exponent to \(5.1163051\)
([juggler_cycle_wuwang_reduction](../problems/juggler_cycle_wuwang_reduction.md),
`J-cyclemin-gap-power-transfer`); that is still the complement and still
kills nothing, since even a perfect measure forces only \(58676\) at
\(N_0=3.5\cdot10^8\) against the table's \(780239\). It reparameterizes the
no-cycle problem as "no long cycle" and excludes nothing the table
did not; the mechanical fixed-point band of a survivor word has the
finance-predicted count and a fair-coin realized parity depth
(\(L=19,84,1054\)). Do not reopen as a short-interval Paper B, a
two-copy Sturmian rigidity, or a longer band scan
([juggler_cycle_mechanical_window](../problems/juggler_cycle_mechanical_window.md)).

**Laboratory kill past \(780239\) (CLOSE).** After Baker and
\(N_0\) are forbidden, excluding the fan member \(780239\) at the
frozen floor is not a Juggler construction: gap lower bounds lose
to dominance, the hug DP is \(C_L\), and the next floor
\(5.54\cdot 10^8\) is PARK. The leftover splits into the
already-named CF-quotient question (`juggler_walk_fan_minimum_law`)
and the recorded long-cycle leftover of Paper A §6. The near-convergents leftover
working draft (family leftover, not a review object):
[juggler_near_convergent_diophantine_note.md](../theory/juggler_near_convergent_diophantine_note.md).
Do not reopen as a kill campaign.

**Winkler does not reach the CF-quotient question (checked 22 September 2026).**
Mike Winkler's 2026 preprints work the same irrational. A206788, the
semiconvergent denominators of \(\log_2 3\), is his central object, and
*Admissible qx+1*, *Marked Rotations* and the two first-passage papers all turn
on the record minima and maxima of \(\{r\log_2 3\}\). The vocabulary is identical
to the dangerous-fan leftover, so it reads like a route and is not one. Every
Winkler PDF held here was scanned, seven files and roughly 245000 characters of
extracted text: *partial quotient*, *irrationality measure*, *linear form*,
*Baker*, *Roth* and *Liouville* occur zero times, and the only *unbounded* is
about Collatz trajectories. His theorems classify structure **given** the
continued fraction and bound none of it, which is why they cannot touch D8 of the
near-convergents note. `J-cyclemin-closure-threshold`, the period bounds and every
floor are unchanged. The nearest thing to a transfer is that his one-sided split
labels each semiconvergent order by the sign of the linear form, which this
laboratory already gets by computing \(\varepsilon_k\) directly. Do not re-run
this sweep; the register carries the reading at
[winkler-2026-admissible-qx1-sequences.json](../../literature/winkler-2026-admissible-qx1-sequences.json).
Termination is equally untouched: the remaining problem there is the external
two-monomial exponent pair, and nothing of his concerns exponential sums.

**Cycle height-to-alphabet inference withdrawn (CLOSE; corrected 9 September 2026).**
The Lean odd-run inequality is upper growth \(y^{2^r}\le v^{3^r}\),
not the lower growth needed for \((3/2)^r\le R\). Exact \(9\to27\to140\)
also disproves the factor-free two-step inference: \(140^4<9^9\).
Retain \(m^9<2(M+1)^4\), the even-run bound \(2^g\le R\), and the
conditional word identities only. Actual nontrivial cycles have positive
floor drift, not exact logarithmic closure, so neither a two-block alphabet
from \(R<27/8\), exact block proportions, nor height equal to discrepancy
is established. The prescribed-prefix Lean results do not fix the first
fall after exactly three climbs. The necklace census is an abstract model,
not realized cycle geometry. Do not reopen as a cycle kill, a
certificate-density argument, or a longer necklace census
([juggler_cycle_run_alphabet](../problems/juggler_cycle_run_alphabet.md),
`J-cycle-run-alphabet`, `J-cycle-band-discrepancy`).

Dossiers: [juggler_cycle_gap_baker](../problems/juggler_cycle_gap_baker.md),
[juggler_cycle_affine_n_gap](../problems/juggler_cycle_affine_n_gap.md),
[juggler_cycle_inhomogeneous_log](../problems/juggler_cycle_inhomogeneous_log.md),
[juggler_cycle_padic_coupling](../problems/juggler_cycle_padic_coupling.md),
[juggler_cycle_fan_multipoint](../problems/juggler_cycle_fan_multipoint.md),
[juggler_cycle_walk_fan_successor](../problems/juggler_cycle_walk_fan_successor.md),
[juggler_cycle_christoffel](../problems/juggler_cycle_christoffel.md),
[juggler_cycle_near_tight](../problems/juggler_cycle_near_tight.md),
[juggler_cycle_diophantine_survivors](../problems/juggler_cycle_diophantine_survivors.md).

---
