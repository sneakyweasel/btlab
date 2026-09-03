# Juggler kernel localization to \(OOOEE\) / \(OOEOE\) even-block fibers

Status: **CLOSE** (the printed leftovers already exceed the \(T_2\) target
on the intervals the productions use; the forty estimates are not needed)

Not a retag of `J-kernel-cancellation`, not a Paper B edit, not a
Hypothesis L reopen, and not a halt theorem. Child of
[juggler_fate_contagion.md](juggler_fate_contagion.md). The objects
are the printed costs of Paper B Theorem 5.3 / Lemma 3.9.

## Problem

Fate note §7.4 parked localizing the kernel theorem to even-block
\(OOOEE\) / \(OOEOE\) productions, with falsifier "an absolute cost in
Steps 3–5 exceeding \(P^{0.677}\)". Does that falsifier fire, and is
\(P^{0.677}\) the right target?

## Exact statement

Let \(I(m')=[m'^{32/27},(m'+1)^{32/27})\) be the even-block fiber of
\(OOOEE\) or \(OOEOE\) (both have \(J^5(n)\asymp n^{27/32}\)). At
scale \(P=m'^{32/27}\) one has \(\lvert I(m')\rvert\asymp P^{5/32}\).
Weyl assembly of Theorem 5.3 on an interval of length \(Y\) needs
\(\lvert T_2(I)\rvert\ll YP^{-1/24}\) to keep
\(\lvert K_c(I)\rvert\ll YP^{-1/96+\varepsilon}\).

**Fiber length (EXACT).** \(Y\asymp P^{5/32}\), so the target is
\(YP^{-1/24}=P^{11/96}\). Fate note §7.4 used the \(OOEEE\) length
\(Y=P^{23/32}\) and the target \(P^{65/96}\approx P^{0.677}\).

**Lemma 3.9 leftover (EXACT — HUMAN PROOF, already printed).** On any
\(I\subseteq(P,2P]\),
\(\lvert\Omega_V\rvert\le C(E)\,P^{89/96}\) at the printed \(V\).
Hence \(\lvert\Omega_V\cap I\rvert\le\min(Y,P^{89/96})\). At both
\(Y=P^{5/32}\) and \(Y=P^{23/32}\) this is \(Y\), which exceeds
\(YP^{-1/24}\) by \(P^{1/24}\). The transition set receives the trivial
bound, so \(\lvert T_2(I)\rvert\) has no saving.

**Passenger leftovers (EXACT, printed).** The absolute terms
\(P^{7/16}\) and \(P^{3/8}\) exceed \(P^{11/96}\). They sit under the
§7.4 target \(P^{65/96}\), which is why the reading assessment missed
them: that target is the wrong interval.

**\(V\)-retune (EXACT, exponent arithmetic).** On \(Y=P^{23/32}\),
shortening \(\Omega_V\) to the target forces \(\sigma=V/S\le P^{-31/48}\);
the piece-boundary sum \(N_I V^{-1/2}\) then needs
\(\sigma\ge P^{-5/24}\). The two constraints are disjoint (gap
\(P^{21/48}\)). The printed \(\Omega_V\) bound meets the target only
for \(Y\ge P^{31/32}\), a near-dyadic interval, not an even-block fiber.

The dyadic kernel theorem is untouched.

## Current literature

- Fate note §7.4 — `refuted` as an assessment: localization was
  called plausible at \(Y=P^{23/32}\) with leftovers \(\le P^{7/16}\).
  The true fiber is \(P^{5/32}\); Lemma 3.9 is \(P^{89/96}\).
- Paper B Theorem 5.3 / Lemma 3.9 (`J-kernel-cancellation`) —
  `known`; full dyadic blocks only. Not retagged.
- Paper B Theorems 4.11–4.12 / `J-fate-ooeee-production` —
  `known`; those localize at \(Y\ge P^{1/2}\), which the \(OOOEE\)
  fibers do not meet.
- Hypothesis L / Appendix C — `known`; consecutive odd starts, not
  the kernel.
- `hypothetical_kernel_localized` in `fate_contagion.py` — orientation
  root \(\lambda=0.5561\) only; not a theorem.

## Branch budget

```text
Mathematical target     Does any printed leftover of Paper B
                        Theorem 5.3 exceed Y P^{-1/24} on the
                        even-block intervals OOOEE / OOEOE use?
Novelty hypothesis      Section 7.4 used Y = P^{23/32} and leftovers
                        at most P^{7/16}; the true fiber is
                        Y = P^{5/32}, and Lemma 3.9 is P^{89/96}
                        and does not shrink below Y.
Falsifier               An absolute or measure leftover above the
                        true target, or |Ω_V ∩ I| not improvable
                        below Y.
Existing machinery      Paper B 5.3 / 3.9; fate note §7.4;
                        hypothetical_kernel_localized.
Maximum Phase-0 scope   Scale arithmetic and the printed leftovers.
                        No forty-estimate re-derivation, no Paper B
                        edit, no Lean, no orbit census.
Promotion criterion     Every leftover ≤ the true target and
                        Lemma 3.9 localizes.
Stop criterion          Any leftover above the true target, or
                        Lemma 3.9's trivial bound ≥ Y.
```

## Balanced-ternary formulation

None. The objects are interval lengths and printed \(P\)-powers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Fiber length of \(OOOEE\) / \(OOEOE\) — **EXACT**
  (\(J^5\asymp n^{27/32}\), MVT).
- Lemma 3.9 measure bound — **EXACT — HUMAN PROOF** (already in
  Paper B); effective leftover \(\min(Y,P^{89/96})\).
- Passenger / end-cell leftovers — **EXACT**, printed.
- \(V\)-retune incompatibility — **EXACT**, exponent arithmetic.

## Experiments

- Probe: `research.juggler_sequence.kernel_localize`
  (`python -m research.juggler_sequence.kernel_localize`).
- Artifact: `data/research/juggler/kernel_localize/summary.json`.
- Tests: `tests/research/juggler_sequence/test_kernel_localize.py`.
- No orbit sample. No exponential-sum evaluation.

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays **ACTIVE**.
The orientation root \(0.5561\) is not promoted.

## Counterexamples

None as a numerical witness. The kill is the printed Lemma 3.9 length
against the fiber geometry, not a counterexample to Theorem 5.3.

## Formalization

None. The comparison is rational arithmetic on printed exponents.
Lean-ifying it would be machinery gravity.

## Results

Classification **KERNEL_LOCALIZE_FALSIFIER_FIRES**
(`J-kernel-localize`).

- True even-block fiber: \(Y\asymp P^{5/32}\), target \(P^{11/96}\).
- Lemma 3.9 leftover is the whole interval at both candidate lengths.
- \(P^{7/16}\) and \(P^{3/8}\) exceed the fiber target; they do not
  exceed the (wrong) §7.4 target.
- \(V\)-retune is empty at \(Y=P^{23/32}\).
- Free term \(\psi_F\) untouched either way.
- Not claimed: any change to the dyadic kernel theorem, to
  \(\lambda^{***}\), or to termination.

## Open questions

None on this line. The contagion exponent stays at \(\lambda^{***}\)
conditional on Hypothesis L / the localized triple, and at
\(\lambda^{**}\) unconditionally. The OE-fiber constant \(1/7\to 1/3\) is done
([juggler_oe_fiber_constant.md](juggler_oe_fiber_constant.md)).

## Decision

**CLOSE.** The stop criterion fired on the printed leftovers: the
even-block fibers of \(OOOEE\) / \(OOEOE\) have length \(P^{5/32}\),
below the triple-parity threshold \(P^{1/2}\) and below a single
gap cell; Lemma 3.9's trivial bound is the whole interval, so
\(T_2\) has no saving and the Weyl assembly of Theorem 5.3 gives
no kernel cancellation on those fibers. The §7.4 reading
assessment used the \(OOEEE\) length and missed the \(P^{89/96}\)
Step 5b leftover, which already exceeds \(P^{0.677}\) as an
effective cost \(\min(Y,P^{89/96})=Y\). Do not reopen as a
forty-estimate re-derivation, a short-interval kernel, a \(V\)-retune,
or a bulk count over a long union of \(m'\) (sparse \(A\) still
needs per-seed mass). Best next question: none on this line; the
fiber-constant pairing is recorded on
[juggler_oe_fiber_constant.md](juggler_oe_fiber_constant.md).

## Publication assessment

Status: `ARCHIVED`. A classification of a parked constants exercise.
Not a paper claim; Paper B Theorem 5.3 is unchanged. Fate note §7.4
is corrected from PARK to CLOSE.
