# Juggler \(V_3=OEOEOEE\) production: next elementary truncation

Status: **PROMOTE** (Section 12 audited; \(\lambda^{**}=0.4891\))

Child of [juggler_oeoee_production.md](juggler_oeoee_production.md).
Theory: [juggler_oeoee_production.md](../theory/juggler_oeoee_production.md)
§§9 and 12. Not a new object, not rest-average, not a Paper B
localization, not \(V_4\), not a halt theorem, and it does not touch
\(\psi_F\).

## Problem

Write out the constants in the \(V_3\) count so the unconditional
contagion exponent can move from the \(OEOEE\) root \(0.4801\) to
\(0.4891\), which lowers the rate pressure must beat from \(0.5199\)
to \(0.5109\). Least Chernoff \(C\) stays \(19\).

## Exact statement

**Lemma 6 (EXACT — HUMAN PROOF).** For odd \(n\) with
\(\mathrm{word}_7(n)=OEOEOEE\) and \(w_1=\lfloor n^{3/4}\rfloor\),
\(w_2=\lfloor w_1^{3/4}\rfloor\), the chain
\(J^2=w_1\), \(J^4=w_2\), \(J^7=\lfloor w_2^{3/8}\rfloor\) is exact,
and the fiber \(J^7(n)=m'\) is
\(n\in[m'^{128/27},(m'+1)^{128/27})\). No exceptional set.

**Lemma 7 (EXACT — HUMAN PROOF).** The six later letters split across
three layers; each is \(\psi\) of a smooth monomial of its own layer.

**Proposition 8 (EXACT — HUMAN PROOF).**
\(|\mathcal O(m')|=\tfrac1{64}\#\{n\text{ odd}\in J(m')\}
+O(|J(m')|\,P^{-3/32+\varepsilon})\). Section 12 recomputes from
T1–T5; binding saving \(P^{-3/32}=m'^{-4/9}\) stands.

**Proposition 9 (EXACT — HUMAN PROOF).** Adding the family changes
the pairing-plus-\(OEOEE\) recursion by exactly
\(+\tfrac1{81}g_A(27t/128)\). The new root is \(0.4891\).

## Current literature

- \(OEOEE\) truncation \(\lambda^{**}=0.4801\) (`extended`): \(V_3\)
  sits in the \(OE\)-fiber of a \(V_2\)-produced element.
- T1–T5 of Section 11 (`reproduced`): same toolkit, new scales.
- Family telescope (`known`): Theorem 5 already names the \(0.4891\)
  truncation.
- Rest-average (`PARK`). Kernel words (`CLOSE`). \(V_4\) not opened.

## Branch budget

```text
Mathematical target     Do the Section 12 constants of
                        docs/theory/juggler_oeoee_production.md recompute
                        from T1–T5, giving a uniform power saving so that
                        +1/81 at scale 27/128 is a theorem?
Novelty hypothesis      The w2-fiber is the OEOEE w-fiber, so Half A
                        transfers; the new middle case saves P^{-1/8}
                        by the same balanced |S_q| route; binding is
                        the Section 11 law at k=3.
Falsifier               A recomputed Case 1 / Case 2 / Case 4 / 12.6
                        constant exceeds the printed bound with no
                        repair that still saves a positive power of P;
                        or the envelope at m'=12,16,20 fails.
Existing machinery      Note Lemmas 6–7 and Prop 9 (EXACT);
                        test_oeoee_production.py V_3 identities;
                        oeoee_audit.py as the pattern.
Maximum Phase-0 scope   Independent re-derivation of every Section 12
                        displayed constant. No V_4 constants, no
                        rest-average, no r=2, no K_3.
Promotion criterion     Every printed constant recomputes at or below
                        the note (or is tightened and still a power
                        saving). Then λ** := 0.4891 is EXACT — HUMAN PROOF.
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
- Three-layer decomposition — **EXACT — HUMAN PROOF**.
- Bookkeeping \(+\tfrac1{81}\) at \(\rho=27/128\) — **EXACT — HUMAN PROOF**.
- Section 12 constants — **EXACT — HUMAN PROOF** (audited).

## Experiments

- Probe: `research.juggler_sequence.v3_audit`.
- Artifact: `data/research/juggler/v3_audit/summary.json`.
- Tests: `tests/research/juggler_sequence/test_v3_audit.py`.
- Identities already in
  `tests/research/juggler_sequence/test_oeoee_production.py`.
- Companion ledger: [v3_audit_ledger.md](../theory/v3_audit_ledger.md).

## Conjectures

None opened. The cylinder bound \(\mathrm H(C,A)\) is untouched.

## Counterexamples

None for \(V_3\). \(OEOEOE\) remains the \(j=0\) exclusion.

## Formalization

None in this phase. Proposition 8 is exponential sums and stays
human. No `sorry`.

## Results

**PROMOTE.** Classification `V3_AUDIT_CONSISTENT`, 23 checks, 0
failures. Binding saving \(P^{-3/32}\) stands. Official
unconditional \(\lambda^{**}=0.4891\), Tao rate \(0.5109\), least
Chernoff \(C=19\) unchanged. \(OEOEE\) \(0.4801\) / \(0.5199\) remains
a named intermediate. \(\lambda^{***}=0.5392\) unchanged.

## Open questions

Later truncations of \(V_k\) (\(V_4=OEOEOEOEE\) and after) are not
opened here. Rest-average stays PARK. This branch does not remove
\(\log\log y\) depth.

## Decision

**PROMOTE.** Section 12 recomputes from T1–T5. Case 1 and Case 2 save
\(P^{-1/8}\); Case 4 is Half A transferred and binds at \(P^{-3/32}\).
The envelope constant \(400\) has room (measured ratio \(\le 0.35\)).
Official \(\lambda^{**}\) moves to \(0.4891\). Best next question: the
\(V_4\) truncation constants, not in this branch.

## Publication assessment

Status: `THEOREM`. Belongs in Paper C Theorem 1. Not a halt theorem.
