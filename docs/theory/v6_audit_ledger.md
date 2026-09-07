# \(V_6=OEOEOEOEOEOEE\) audit ledger

Companion to [juggler_oeoee_production.md](juggler_oeoee_production.md)
Sections 10 and 15. Probe: `research.juggler_sequence.v6_audit`. A
script check confirms consistency of what is printed; it is not a
proof.

T1 is Paper B Lemma 3.5 (Vaaler) and is cited, not re-derived. Lemmas
12–13 and Proposition 16 are already **EXACT — HUMAN PROOF**. Every
displayed constant in Section 15 is recomputed from T1–T5 at the
\(V_6\) scales.

| Item | Check | Outcome |
|---|---|---|
| 15.2 \(Y\ge\tfrac{4096}{729}m'^{7463/729}-1\) | hand (MVT); script three \(m'\) | consistent |
| 15.2 \(L_1\) envelope \(\tfrac{2048}{243}m'^{1805/243}\) | hand (MVT); script \(m'\le79\) | consistent |
| 15.2 \(L_2\) is the \(V_5\) \(w_1\)-interval | hand | consistent |
| 15.2 \(L_3\) is the \(V_4\) \(w_1\)-interval | hand | consistent |
| 15.2 \(L_4\) is the \(V_3\) \(w_1\)-interval | hand | consistent |
| 15.2 \(L_5\) is the \(OEOEE\) \(w\)-interval | hand | consistent; Case 7 is Half A transferred four times |
| T4 Case 1 step ratio \((1+1/m')^{2048/243}\) | hand \(m'=22,60\) | same tightening as \(OEOEE\): steps \(\asymp\delta\); at \(m'=16\) implied \(5.33>5\), so assembly starts at \(m'=22\); pad \(120\) vs \(89.90\) covers a \(4\to5\) retune |
| Case 1 leading \(\tfrac{16384}{729}\) | hand: \(4\cdot\tfrac{2048}{243}\cdot\tfrac23\) | consistent |
| Case 1 log \(16384/(243\pi)=21.462\) | hand | consistent; printed \(21.47\) |
| Case 1 Vaaler \(R\) coefficient \(120\) | hand: \(4\cdot\tfrac{16384}{729}=89.90\) | consistent; printed is a pad |
| Case 1 \(R=0.216\,m'^{1024/729}\) | hand: \(\sqrt{(4096/729)/120}=0.2164\) | consistent |
| Case 1 assembled \(52.0\), over \(Y\) \(9.3\) | hand | consistent; saves \(P^{-1/8}\) |
| Case 2 over \(Y\) \(9.2\) | hand: \(38.6\cdot\tfrac43/(4096/729)=9.16\) | consistent; \(V_5\) Case 1 transferred; saves \(P^{-3/32}\) |
| Case 3 over \(Y\) \(9.0\) | hand: \(V_5\) Case 2 transferred | consistent; saves \(P^{-9/128}\) |
| Case 4 over \(Y\) \(9.1\) | hand: \(V_5\) Case 3 transferred | consistent; saves \(P^{-27/512}\) |
| Case 5 over \(Y\) \(6.3\) | hand: \(V_5\) Case 4 transferred | consistent; saves \(P^{-27/512}\) |
| Case 7 over \(Y\) \(6.3\) | hand: \(V_5\) Case 6 times one more \(OE\) weight | consistent; binding \(P^{-81/2048}=m'^{-4/9}\) |
| Binding \(P^{-81/2048}=m'^{-4/9}\) | hand: \(\tfrac{8192}{729}\cdot\tfrac{81}{2048}=\tfrac49\); \(\tfrac16(\tfrac34)^5=\tfrac{81}{2048}\) | consistent; a positive power |
| Prop 16 net \(\tfrac1{2187}\) | hand: \((\tfrac13-\tfrac29)\tfrac1{243}\) | consistent |
| 15.9 assembly \(8000\) for \(m'\ge 22\) | hand: \(6030\) at the extra-power factors | consistent |
| Envelope \(\lvert 4096\lvert\mathcal O\rvert-Y\rvert\le 8000\,Y\,m'^{-4/9}(1+\log m')^2\) | script \(m'=2\) only | consistent; measured ratio \(0.94\); \(m'\ge3\) not scanned |
| Eight-term root \(0.4926\) | script | consistent; rate \(0.5074\); least \(C\) still \(19\) |

The elementary route has a uniform power saving \(P^{-81/2048}\).
Proposition 15 meets the ledger bar **EXACT — HUMAN PROOF**. Net
bookkeeping is \(+1/2187\) at scale \(729/8192\). The promotion of
\(\lambda^{**}\) from \(0.4924\) to \(0.4926\) is then bookkeeping.
Later \(V_k\) are not opened here.
