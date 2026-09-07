# Juggler \(V_6=OEOEOEOEOEOEE\) production: next elementary truncation

Status: **PROMOTE** (Section 15 audited; \(\lambda^{**}=0.4926\))

Child of [juggler_v5_production.md](juggler_v5_production.md).
Theory: [juggler_oeoee_production.md](../theory/juggler_oeoee_production.md)
§§10 and 15. Not a new object, not rest-average, not a Paper B
localization, not \(V_7\), not a halt theorem, and it does not touch
\(\psi_F\).

## Problem

Write out the constants in the \(V_6\) count so the unconditional
contagion exponent can move from the \(V_5\) root \(0.4924\) to
\(0.4926\), which lowers the rate pressure must beat from \(0.5076\)
to \(0.5074\). Least Chernoff \(C\) stays \(19\). Azuma \(C(0.55)\)
stays \(41\).

## Exact statement

**Lemma 12 (EXACT — HUMAN PROOF).** For odd \(n\) with
\(\mathrm{word}_{13}(n)=OEOEOEOEOEOEE\) and \(w_1=\lfloor n^{3/4}\rfloor\),
\(w_2=\lfloor w_1^{3/4}\rfloor\), \(w_3=\lfloor w_2^{3/4}\rfloor\),
\(w_4=\lfloor w_3^{3/4}\rfloor\), \(w_5=\lfloor w_4^{3/4}\rfloor\), the
chain \(J^2=w_1\), \(J^4=w_2\), \(J^6=w_3\), \(J^8=w_4\),
\(J^{10}=w_5\),
\(J^{13}=\lfloor w_5^{3/8}\rfloor\) is exact, and the fiber
\(J^{13}(n)=m'\) is \(n\in[m'^{8192/729},(m'+1)^{8192/729})\). No exceptional
set.

**Lemma 13 (EXACT — HUMAN PROOF).** The twelve later letters split across
six layers; each is \(\psi\) of a smooth monomial of its own layer.

**Proposition 15 (EXACT — HUMAN PROOF).**
\(|\mathcal O(m')|=\tfrac1{4096}\#\{n\text{ odd}\in J(m')\}
+O(|J(m')|\,P^{-81/2048+\varepsilon})\). Section 15 recomputes from
T1–T5; binding saving \(P^{-81/2048}=m'^{-4/9}\) stands.

**Proposition 16 (EXACT — HUMAN PROOF).** Adding the family changes
the pairing-plus-\(OEOEE\)-plus-\(V_3\)-plus-\(V_4\)-plus-\(V_5\) recursion by exactly
\(+\tfrac1{2187}g_A(729t/8192)\). The new root is \(0.4926\).

## Current literature

- \(V_5\) truncation \(\lambda^{**}=0.4924\) (`extended`): \(V_6\)
  sits in the \(OE\)-fiber of a \(V_5\)-produced element.
- T1–T5 of Section 11 (`reproduced`): same toolkit, new scales.
- Family telescope (`known`): Theorem 5 already names the \(0.4926\)
  truncation.
- Rest-average (`PARK`). Kernel words (`CLOSE`). \(V_7\) not opened.

## Branch budget

```text
Mathematical target     Do the Section 15 constants of
                        docs/theory/juggler_oeoee_production.md recompute
                        from T1-T5, giving a uniform power saving so that
                        +1/2187 at scale 729/8192 is a theorem?
Novelty hypothesis      The w5-fiber is the OEOEE w-fiber, so Half A
                        transfers; the w1-interval is V_5's n-interval,
                        so V_5 Case 1/2/3/4 transfer; the new top case is
                        Half B at w1; binding is the Section 11 law
                        at k=6.
Falsifier               A recomputed Case 1 / Case 2 / Case 3 / Case 4
                        / Case 5 / Case 7 / 15.9 constant exceeds the
                        printed bound with no repair that still saves a
                        positive power of P; or the envelope at
                        m'=2 fails.
Existing machinery      Note Prop 10 and Theorem 5 (EXACT);
                        test_oeoee_production.py family(5);
                        v5_audit.py as the pattern.
Maximum Phase-0 scope   Independent re-derivation of every Section 15
                        displayed constant. No V_7 constants, no
                        rest-average, no r=2, no K_3.
Promotion criterion     Every printed constant recomputes at or below
                        the note (or is tightened and still a power
                        saving). Then lambda** := 0.4926 is EXACT — HUMAN PROOF.
Stop criterion          A false step with no elementary repair; or the
                        audit becomes a constant hunt (PARK).
```

## Balanced-ternary formulation

None. The objects are parity words and classical one-variable
exponential sums.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Exact chain and exact fiber — **EXACT — HUMAN PROOF**.
- Six-layer decomposition — **EXACT — HUMAN PROOF**.
- Bookkeeping \(+\tfrac1{2187}\) at \(\rho=729/8192\) — **EXACT — HUMAN PROOF**.
- Section 15 constants — **EXACT — HUMAN PROOF** (audited).

## Experiments

- Probe: `research.juggler_sequence.v6_audit`.
- Artifact: `data/research/juggler/v6_audit/summary.json`.
- Tests: `tests/research/juggler_sequence/test_v6_audit.py`.
- Identities already in
  `tests/research/juggler_sequence/test_oeoee_production.py`.
- Companion ledger: [v6_audit_ledger.md](../theory/v6_audit_ledger.md).

## Conjectures

None opened. The cylinder bound \(\mathrm H(C,A)\) is untouched.

## Counterexamples

None for \(V_6\). \(OEOEOE\) remains the \(j=0\) exclusion.

## Formalization

None in this phase. Proposition 15 is exponential sums and stays
human. No `sorry`.

## Results

**PROMOTE.** Classification `V6_AUDIT_CONSISTENT`. Binding saving
\(P^{-81/2048}\) stands. Official unconditional \(\lambda^{**}=0.4926\),
Tao rate \(0.5074\), least Chernoff \(C=19\) unchanged. Azuma
\(C(0.55)\) stays \(41\). \(V_5\) \(0.4924\) / \(0.5076\) remains a
named intermediate. \(\lambda^{***}=0.5392\) unchanged.

## Open questions

Later truncations of \(V_k\) (\(V_7\) and after) are not
opened here. Rest-average stays PARK. This branch does not remove
\(\log\log y\) depth.

## Decision

**PROMOTE.** Section 15 recomputes from T1–T5. Case 1 saves
\(P^{-1/8}\); Case 2 saves \(P^{-3/32}\); Case 3 saves \(P^{-9/128}\);
Case 4 and Case 5 save \(P^{-27/512}\); Case 7 is Half A transferred
four times and binds at \(P^{-81/2048}\). The envelope constant
\(8000\) has room at \(m'\ge 22\). Official \(\lambda^{**}\) moves to
\(0.4926\). Best next question: the \(V_7\) truncation constants, not
in this branch.

## Publication assessment

Status: `THEOREM`. Belongs in Paper C Theorem 1. Not a halt theorem.
