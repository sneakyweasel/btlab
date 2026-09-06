# Juggler \(OEOEE\) production: elementary fourth contagion family

Status: **PROMOTE** (Section 11 audited; \(\lambda^{**}=0.4801\))

Child of [juggler_fate_contagion.md](juggler_fate_contagion.md).
Theory: [juggler_oeoee_production.md](../theory/juggler_oeoee_production.md).
Not a new object, not rest-average, not a Paper B localization, not a
halt theorem, and it does not touch \(\psi_F\).

## Problem

Write out the constants in the \(OEOEE\) count so the unconditional
contagion exponent can move from the pairing root \(0.4480\) to
\(0.4801\), which lowers the rate pressure must beat from \(0.552\) to
\(0.5199\).

## Exact statement

**Lemma 1 (EXACT — HUMAN PROOF).** For odd \(n\) with
\(\mathrm{word}_5(n)=OEOEE\) and \(w=\lfloor n^{3/4}\rfloor\),
\(J^2(n)=w\), \(J^3(n)=\lfloor w^{3/2}\rfloor\),
\(J^4(n)=\lfloor w^{3/4}\rfloor\), \(J^5(n)=\lfloor w^{3/8}\rfloor\),
and the fiber \(J^5(n)=m'\) is the exact interval
\(n\in[m'^{32/9},(m'+1)^{32/9})\). No exceptional set.

**Lemma 2 (EXACT — HUMAN PROOF).** The four later parities are
functions of \(w\) alone, constant on each level set
\(I_w=[w^{4/3},(w+1)^{4/3})\). Only \(\psi(n^{3/2})\) varies inside a
block.

**Proposition 3 (EXACT — HUMAN PROOF).** \(|\mathcal O(m')|=\tfrac1{16}\#\{n\text{ odd}\in J(m')\}
+O(|J(m')|\,P^{-1/8+\varepsilon})\). Section 11 recomputes from T1–T5;
binding saving \(P^{-1/8}=m'^{-4/9}\) stands.

**Proposition 4 (EXACT — HUMAN PROOF).** Adding the family changes
the pairing recursion by exactly \(+\tfrac1{27}g_A(9t/32)\). The new
root is \(0.4801\).

**Theorem 5 (EXACT — HUMAN PROOF).** The family
\(V_k=(OE)^{k-1}OEE\) telescopes onto the ideal depth-two equation
(root \(0.4927\)). This branch audits \(V_2=OEOEE\) only.

## Current literature

- Pairing recursion \(0.4480\) (`extended`): the production sits
  inside family 3 and is removed before being re-added at the ideal
  share. Official \(\lambda^{**}\) is now the four-term root \(0.4801\).
- Paper B Lemma 3.5 Vaaler, Kusmin–Landau, second-derivative test
  (`known`): classical inputs, no nested floors.
- Appendix C \(OOEEE\) (`independent`): same fiber length
  \(\rho=9/32\), but \(OOEEE\) is nested and needs Hypothesis L.
- Rest-average \(1/3\to 1/2\) (`refuted` as a pairing-style lemma;
  PARK as a dynamical averaging problem).
- Kernel words \(OOOEE\)/\(OOEOE\) (`refuted` as a method).

## Branch budget

```text
Mathematical target     Do the Section 11 constants of
                        docs/theory/juggler_oeoee_production.md recompute
                        from T1–T5, giving a uniform power saving so that
                        +1/27 at scale 9/32 is a theorem?
Novelty hypothesis      Isolated-O words need no Paper B: J^2(n)=floor(n^{3/4})
                        is exact, the fiber has no exceptional set, and the
                        fifteen sign sums are classical one-variable estimates.
Falsifier               A recomputed T3 / 11.2 / Half A–B / 11.5 constant
                        exceeds the printed bound with no repair that still
                        saves a positive power of P; or the envelope
                        |16|O(m')|-Y| <= 100 Y m'^{-4/9}(1+log m')^2 fails.
Existing machinery      Note Lemmas 1–2 and Prop 4 (EXACT); tests/research/
                        juggler_sequence/test_oeoee_production.py; FateContagion.lean
                        sqrt_sqrt_eq_iff; paper_b_audit as the audit pattern.
Maximum Phase-0 scope   Independent re-derivation of every Section 11
                        displayed constant. No Paper A/C rewrite, no V_3+
                        constants, no r=2 words, no rest-average, no K_3.
Promotion criterion     Every printed constant recomputes at or below the
                        note (or is tightened and still a power saving).
                        Then λ** := 0.4801 is EXACT — HUMAN PROOF.
Stop criterion          A false step with no elementary repair; or the
                        audit becomes a constant hunt (PARK).
```

## Balanced-ternary formulation

None. The objects are parity words of the Juggler map and classical
exponential sums in one integer variable \(w=\lfloor n^{3/4}\rfloor\).

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Exact chain \(J^2=\lfloor n^{3/4}\rfloor\) — **EXACT — HUMAN PROOF**.
- Exact fiber, no exceptional set — **EXACT — HUMAN PROOF**.
- Bookkeeping \(+\tfrac1{27}\) at \(\rho=9/32\) — **EXACT — HUMAN PROOF**.
- Family telescope to the ideal depth-two root — **EXACT — HUMAN PROOF**.
- Section 11 constants — **EXACT — HUMAN PROOF** (audited; T2 display
  and T4 hypothesis tightened, envelope \(100\) still covers).
- Binding length \(1/4\) for \(OEOEOE\) has no per-source saving —
  **COMPUTATIONALLY VERIFIED**.

## Experiments

- Probe: `research.juggler_sequence.oeoee_audit`.
- Artifact: `data/research/juggler/oeoee_audit/summary.json`.
- Tests: `tests/research/juggler_sequence/test_oeoee_audit.py`.
- Identities and envelope already in
  `tests/research/juggler_sequence/test_oeoee_production.py`.
- Companion ledger: [oeoee_audit_ledger.md](../theory/oeoee_audit_ledger.md).

## Conjectures

None opened. The cylinder bound \(\mathrm H(C,A)\) is untouched.

## Counterexamples

None for \(OEOEE\). \(OEOEOE\) is not a counterexample to this word;
it is the \(j=0\) exclusion of the layer criterion.

## Formalization

None in this phase. `FateContagion.lean` already has
`sqrt_sqrt_eq_iff`. Proposition 3 is exponential sums and stays
human. No `sorry`.

## Results

**PROMOTE.** Classification `OEOEE_AUDIT_CONSISTENT`, 29 checks, 0
failures (`research.juggler_sequence.oeoee_audit`). Every displayed
Section 11 constant recomputes from T1–T5, or is tightened and still
saves a positive power of \(P\). Binding saving \(P^{-1/8}\) stands.
Official unconditional \(\lambda^{**}=0.4801\), Tao rate \(0.5199\),
least Chernoff \(C=19\). Pairing \(0.4480\) / \(0.5520\) / \(C=20\)
remains a named intermediate. \(\lambda^{***}=0.5392\) unchanged.
Ledger: `J-fate-oeoee-production`.

## Open questions

Later truncations of \(V_k\) (\(V_3=OEOEOEE\) and after) are not
opened here. Rest-average stays PARK. Kernel localization stays CLOSE.
This branch does not remove \(\log\log y\) depth.

## Decision

**PROMOTE.** Section 11 recomputes from T1–T5. T2's printed max-gap
was a sampling artifact (the cotangent inequality holds). T4's
abstract short-step form is false, but Half B's steps are
\(\asymp\delta\) and the pad covers a \(4\to 5\) retune. The envelope
constant \(100\) still has room. Official \(\lambda^{**}\) moves to
\(0.4801\). Best next question: the \(V_3\) truncation constants, not
in this branch.

## Publication assessment

Status: `THEOREM`. Belongs in Paper C Theorem 1. Not a halt theorem.
