# \(V_5=OEOEOEOEOEE\) audit ledger

Companion to [juggler_oeoee_production.md](juggler_oeoee_production.md)
Sections 10 and 14. Probe: `research.juggler_sequence.v5_audit`. A
script check confirms consistency of what is printed; it is not a
proof.

T1 is Paper B Lemma 3.5 (Vaaler) and is cited, not re-derived. Lemmas
10–11 and Proposition 14 are already **EXACT — HUMAN PROOF**. Every
displayed constant in Section 14 is recomputed from T1–T5 at the
\(V_5\) scales.

| Item | Check | Outcome |
|---|---|---|
| 14.2 \(Y\ge\tfrac{1024}{243}m'^{1805/243}-1\) | hand (MVT); script three \(m'\) | consistent |
| 14.2 \(L_1\) envelope \(\tfrac{512}{81}m'^{431/81}\) | hand (MVT); script \(m'\le79\) | consistent |
| 14.2 \(L_2\) is the \(V_4\) \(w_1\)-interval | hand | consistent |
| 14.2 \(L_3\) is the \(V_3\) \(w_1\)-interval | hand | consistent |
| 14.2 \(L_4\) is the \(OEOEE\) \(w\)-interval | hand | consistent; Case 6 is Half A transferred three times |
| T4 Case 1 step ratio \((1+1/m')^{512/81}\) | hand \(m'=16,60\) | same tightening as \(OEOEE\): steps \(\asymp\delta\); pad \(88\) vs \(67.42\) covers a \(4\to5\) retune |
| Case 1 leading \(\tfrac{4096}{243}\) | hand: \(4\cdot\tfrac{512}{81}\cdot\tfrac23\) | consistent |
| Case 1 log \(4096/(81\pi)=16.096\) | hand | consistent; printed \(16.10\) |
| Case 1 Vaaler \(R\) coefficient \(88\) | hand: \(4\cdot\tfrac{4096}{243}=67.42\) | consistent; printed is a pad |
| Case 1 \(R=0.219\,m'^{256/243}\) | hand: \(\sqrt{(1024/243)/88}=0.2188\) | consistent |
| Case 1 assembled \(38.6\), over \(Y\) \(9.2\) | hand | consistent; saves \(P^{-1/8}\) |
| Case 2 over \(Y\) \(9.0\) | hand: \(28.4\cdot\tfrac43/(1024/243)=8.99\) | consistent; \(V_4\) Case 1 transferred; saves \(P^{-3/32}\) |
| Case 3 over \(Y\) \(9.1\) | hand: \(V_4\) Case 2 transferred | consistent; saves \(P^{-9/128}\) |
| Case 4 over \(Y\) \(6.3\) | hand: \(V_4\) Case 3 transferred | consistent; saves \(P^{-9/128}\) |
| Case 6 over \(Y\) \(6.3\) | hand: \(V_4\) Case 5 times one more \(OE\) weight | consistent; binding \(P^{-27/512}=m'^{-4/9}\) |
| Binding \(P^{-27/512}=m'^{-4/9}\) | hand: \(\tfrac{2048}{243}\cdot\tfrac{27}{512}=\tfrac49\); \(\tfrac16(\tfrac34)^4=\tfrac{27}{512}\) | consistent; a positive power |
| Prop 14 net \(\tfrac1{729}\) | hand: \((\tfrac13-\tfrac29)\tfrac1{81}\) | consistent |
| 14.8 assembly \(4000\) for \(m'\ge 16\) | hand: \(2844\) at the extra-power factors | consistent |
| Envelope \(\lvert 1024\lvert\mathcal O\rvert-Y\rvert\le 4000\,Y\,m'^{-4/9}(1+\log m')^2\) | script \(m'=2,3,4\) | consistent; measured ratios \(1.38,0.70,2.02\) |
| Seven-term root \(0.4924\) | script | consistent; rate \(0.5076\); least \(C\) still \(19\) |

The elementary route has a uniform power saving \(P^{-27/512}\).
Proposition 13 meets the ledger bar **EXACT — HUMAN PROOF**. Net
bookkeeping is \(+1/729\) at scale \(243/2048\). The promotion of
\(\lambda^{**}\) from \(0.4916\) to \(0.4924\) is then bookkeeping.
Later \(V_k\) are not opened here.
