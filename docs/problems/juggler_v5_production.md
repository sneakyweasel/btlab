# Juggler \(V_5=OEOEOEOEOEE\) production: next elementary truncation

Status: **PROMOTE** (Section 14 audited; \(\lambda^{**}=0.4924\))

Child of [juggler_v4_production.md](juggler_v4_production.md).
Theory: [juggler_oeoee_production.md](../theory/juggler_oeoee_production.md)
§§10 and 14. Not a new object, not rest-average, not a Paper B
localization, not \(V_6\), not a halt theorem, and it does not touch
\(\psi_F\).

## Problem

Write out the constants in the \(V_5\) count so the unconditional
contagion exponent can move from the \(V_4\) root \(0.4916\) to
\(0.4924\), which lowers the rate pressure must beat from \(0.5084\)
to \(0.5076\). Least Chernoff \(C\) stays \(19\). Azuma \(C(0.55)\)
drops from \(42\) to \(41\).

## Exact statement

**Lemma 10 (EXACT — HUMAN PROOF).** For odd \(n\) with
\(\mathrm{word}_{11}(n)=OEOEOEOEOEE\) and \(w_1=\lfloor n^{3/4}\rfloor\),
\(w_2=\lfloor w_1^{3/4}\rfloor\), \(w_3=\lfloor w_2^{3/4}\rfloor\),
\(w_4=\lfloor w_3^{3/4}\rfloor\), the
chain \(J^2=w_1\), \(J^4=w_2\), \(J^6=w_3\), \(J^8=w_4\),
\(J^{11}=\lfloor w_4^{3/8}\rfloor\) is exact, and the fiber
\(J^{11}(n)=m'\) is \(n\in[m'^{2048/243},(m'+1)^{2048/243})\). No exceptional
set.

**Lemma 11 (EXACT — HUMAN PROOF).** The ten later letters split across
five layers; each is \(\psi\) of a smooth monomial of its own layer.

**Proposition 13 (EXACT — HUMAN PROOF).**
\(|\mathcal O(m')|=\tfrac1{1024}\#\{n\text{ odd}\in J(m')\}
+O(|J(m')|\,P^{-27/512+\varepsilon})\). Section 14 recomputes from
T1–T5; binding saving \(P^{-27/512}=m'^{-4/9}\) stands.

**Proposition 14 (EXACT — HUMAN PROOF).** Adding the family changes
the pairing-plus-\(OEOEE\)-plus-\(V_3\)-plus-\(V_4\) recursion by exactly
\(+\tfrac1{729}g_A(243t/2048)\). The new root is \(0.4924\).

## Current literature

- \(V_4\) truncation \(\lambda^{**}=0.4916\) (`extended`): \(V_5\)
  sits in the \(OE\)-fiber of a \(V_4\)-produced element.
- T1–T5 of Section 11 (`reproduced`): same toolkit, new scales.
- Family telescope (`known`): Theorem 5 already names the \(0.4924\)
  truncation.
- Rest-average (`PARK`). Kernel words (`CLOSE`). \(V_6\) not opened.

## Branch budget

```text
Mathematical target     Do the Section 14 constants of
                        docs/theory/juggler_oeoee_production.md recompute
                        from T1–T5, giving a uniform power saving so that
                        +1/729 at scale 243/2048 is a theorem?
Novelty hypothesis      The w4-fiber is the OEOEE w-fiber, so Half A
                        transfers; the w1-interval is V_4's n-interval,
                        so V_4 Case 1/2/3 transfer; the new top case is
                        Half B at w1; binding is the Section 11 law
                        at k=5.
Falsifier               A recomputed Case 1 / Case 2 / Case 3 / Case 4
                        / Case 6 / 14.8 constant exceeds the printed
                        bound with no repair that still saves a
                        positive power of P; or the envelope at
                        m'=2,3,4 fails.
Existing machinery      Note Prop 10 and Theorem 5 (EXACT);
                        test_oeoee_production.py family(4);
                        v4_audit.py as the pattern.
Maximum Phase-0 scope   Independent re-derivation of every Section 14
                        displayed constant. No V_6 constants, no
                        rest-average, no r=2, no K_3.
Promotion criterion     Every printed constant recomputes at or below
                        the note (or is tightened and still a power
                        saving). Then λ** := 0.4924 is EXACT — HUMAN PROOF.
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
- Five-layer decomposition — **EXACT — HUMAN PROOF**.
- Bookkeeping \(+\tfrac1{729}\) at \(\rho=243/2048\) — **EXACT — HUMAN PROOF**.
- Section 14 constants — **EXACT — HUMAN PROOF** (audited).

## Experiments

- Probe: `research.juggler_sequence.v5_audit`.
- Artifact: `data/research/juggler/v5_audit/summary.json`.
- Tests: `tests/research/juggler_sequence/test_v5_audit.py`.
- Identities already in
  `tests/research/juggler_sequence/test_oeoee_production.py`.
- Companion ledger: [v5_audit_ledger.md](../theory/v5_audit_ledger.md).

## Conjectures

None opened. The cylinder bound \(\mathrm H(C,A)\) is untouched.

## Counterexamples

None for \(V_5\). \(OEOEOE\) remains the \(j=0\) exclusion.

## Formalization

None in this phase. Proposition 13 is exponential sums and stays
human. No `sorry`.

## Results

**PROMOTE.** Classification `V5_AUDIT_CONSISTENT`, 24 checks, 0
failures. Binding saving \(P^{-27/512}\) stands. Official
unconditional \(\lambda^{**}=0.4924\), Tao rate \(0.5076\), least
Chernoff \(C=19\) unchanged. Azuma \(C(0.55)\) moves \(42\to 41\).
\(V_4\) \(0.4916\) / \(0.5084\) remains a named intermediate.
\(\lambda^{***}=0.5392\) unchanged.

## Open questions

Later truncations of \(V_k\) (\(V_6\) and after) are not
opened here. Rest-average stays PARK. This branch does not remove
\(\log\log y\) depth.

## Decision

**PROMOTE.** Section 14 recomputes from T1–T5. Case 1 saves
\(P^{-1/8}\); Case 2 saves \(P^{-3/32}\); Case 3 and Case 4 save
\(P^{-9/128}\); Case 6 is Half A transferred three times and binds
at \(P^{-27/512}\). The envelope constant \(4000\) has room
(measured ratio \(\le 2.02\)). Official \(\lambda^{**}\) moves to
\(0.4924\). Best next question: the \(V_6\) truncation constants, not
in this branch.

## Publication assessment

Status: `THEOREM`. Belongs in Paper C Theorem 1. Not a halt theorem.
