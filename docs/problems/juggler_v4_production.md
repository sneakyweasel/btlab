# Juggler \(V_4=OEOEOEOEE\) production: next elementary truncation

Status: **PROMOTE** (Section 13 audited; \(\lambda^{**}=0.4916\))

Child of [juggler_v3_production.md](juggler_v3_production.md).
Theory: [juggler_oeoee_production.md](../theory/juggler_oeoee_production.md)
§§10 and 13. Not a new object, not rest-average, not a Paper B
localization, not \(V_5\), not a halt theorem, and it does not touch
\(\psi_F\).

## Problem

Write out the constants in the \(V_4\) count so the unconditional
contagion exponent can move from the \(V_3\) root \(0.4891\) to
\(0.4916\), which lowers the rate pressure must beat from \(0.5109\)
to \(0.5084\). Least Chernoff \(C\) stays \(19\).

## Exact statement

**Lemma 8 (EXACT — HUMAN PROOF).** For odd \(n\) with
\(\mathrm{word}_9(n)=OEOEOEOEE\) and \(w_1=\lfloor n^{3/4}\rfloor\),
\(w_2=\lfloor w_1^{3/4}\rfloor\), \(w_3=\lfloor w_2^{3/4}\rfloor\), the
chain \(J^2=w_1\), \(J^4=w_2\), \(J^6=w_3\),
\(J^9=\lfloor w_3^{3/8}\rfloor\) is exact, and the fiber
\(J^9(n)=m'\) is \(n\in[m'^{512/81},(m'+1)^{512/81})\). No exceptional
set.

**Lemma 9 (EXACT — HUMAN PROOF).** The eight later letters split across
four layers; each is \(\psi\) of a smooth monomial of its own layer.

**Proposition 11 (EXACT — HUMAN PROOF).**
\(|\mathcal O(m')|=\tfrac1{256}\#\{n\text{ odd}\in J(m')\}
+O(|J(m')|\,P^{-9/128+\varepsilon})\). Section 13 recomputes from
T1–T5; binding saving \(P^{-9/128}=m'^{-4/9}\) stands.

**Proposition 12 (EXACT — HUMAN PROOF).** Adding the family changes
the pairing-plus-\(OEOEE\)-plus-\(V_3\) recursion by exactly
\(+\tfrac1{243}g_A(81t/512)\). The new root is \(0.4916\).

## Current literature

- \(V_3\) truncation \(\lambda^{**}=0.4891\) (`extended`): \(V_4\)
  sits in the \(OE\)-fiber of a \(V_3\)-produced element.
- T1–T5 of Section 11 (`reproduced`): same toolkit, new scales.
- Family telescope (`known`): Theorem 5 already names the \(0.4916\)
  truncation.
- Rest-average (`PARK`). Kernel words (`CLOSE`). \(V_5\) not opened.

## Branch budget

```text
Mathematical target     Do the Section 13 constants of
                        docs/theory/juggler_oeoee_production.md recompute
                        from T1–T5, giving a uniform power saving so that
                        +1/243 at scale 81/512 is a theorem?
Novelty hypothesis      The w3-fiber is the OEOEE w-fiber, so Half A
                        transfers; the w2-interval is V_3's w1-interval,
                        so V_3 Case 1/2 transfer; the new top case is
                        Half B at w1; binding is the Section 11 law
                        at k=4.
Falsifier               A recomputed Case 1 / Case 2 / Case 3 / Case 5
                        / 13.7 constant exceeds the printed bound with
                        no repair that still saves a positive power of
                        P; or the envelope at m'=4,6,8 fails.
Existing machinery      Note Prop 10 and Theorem 5 (EXACT);
                        test_oeoee_production.py V_4 identities;
                        v3_audit.py as the pattern.
Maximum Phase-0 scope   Independent re-derivation of every Section 13
                        displayed constant. No V_5 constants, no
                        rest-average, no r=2, no K_3.
Promotion criterion     Every printed constant recomputes at or below
                        the note (or is tightened and still a power
                        saving). Then λ** := 0.4916 is EXACT — HUMAN PROOF.
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
- Four-layer decomposition — **EXACT — HUMAN PROOF**.
- Bookkeeping \(+\tfrac1{243}\) at \(\rho=81/512\) — **EXACT — HUMAN PROOF**.
- Section 13 constants — **EXACT — HUMAN PROOF** (audited).

## Experiments

- Probe: `research.juggler_sequence.v4_audit`.
- Artifact: `data/research/juggler/v4_audit/summary.json`.
- Tests: `tests/research/juggler_sequence/test_v4_audit.py`.
- Identities already in
  `tests/research/juggler_sequence/test_oeoee_production.py`.
- Companion ledger: [v4_audit_ledger.md](../theory/v4_audit_ledger.md).

## Conjectures

None opened. The cylinder bound \(\mathrm H(C,A)\) is untouched.

## Counterexamples

None for \(V_4\). \(OEOEOE\) remains the \(j=0\) exclusion.

## Formalization

None in this phase. Proposition 11 is exponential sums and stays
human. No `sorry`.

## Results

**PROMOTE.** Classification `V4_AUDIT_CONSISTENT`, 22 checks, 0
failures. Binding saving \(P^{-9/128}\) stands. Official
unconditional \(\lambda^{**}=0.4916\), Tao rate \(0.5084\), least
Chernoff \(C=19\) unchanged. \(V_3\) \(0.4891\) / \(0.5109\) remains
a named intermediate. \(\lambda^{***}=0.5392\) unchanged.

## Open questions

The \(V_5=OEOEOEOEOEE\) truncation is now done
([juggler_v5_production.md](juggler_v5_production.md)), and so is
\(V_6\) ([juggler_v6_production.md](juggler_v6_production.md)). Later
truncations (\(V_7\) and after) are not opened here. Rest-average
stays PARK. This branch does not remove \(\log\log y\) depth.

## Decision

**PROMOTE.** Section 13 recomputes from T1–T5. Case 1 saves
\(P^{-1/8}\); Case 2 and Case 3 save \(P^{-3/32}\); Case 5 is Half A
transferred twice and binds at \(P^{-9/128}\). The envelope constant
\(1600\) has room (measured ratio \(\le 1.64\)). Official
\(\lambda^{**}\) moves to \(0.4916\). Best next question: the
\(V_5\) truncation constants, not in this branch.

## Publication assessment

Status: `THEOREM`. Belongs in Paper C Theorem 1. Not a halt theorem.
