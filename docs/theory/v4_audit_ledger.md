# \(V_4=OEOEOEOEE\) audit ledger

Companion to [juggler_oeoee_production.md](juggler_oeoee_production.md)
Sections 10 and 13. Probe: `research.juggler_sequence.v4_audit`. A
script check confirms consistency of what is printed; it is not a
proof.

**Review-scope notice (9 September 2026).** The rows below audit the
smooth reference window \(J_4^{\rm sm}\) used in the printed constant
calculation, not the exact nested Juggler landing fiber
\(J_4^{\rm ex}\). The exact fiber has iterated ceiling endpoints rather
than the formerly collapsed monomial endpoints. The endpoint correction
is lower order than the binding saving, so the fixed-depth asymptotic
exponent and root bookkeeping transfer, but the audited constant
\(1600\) and finite census ratio do not automatically transfer. No
exact-fiber constant is certified here.

T1 is Paper B Lemma 3.5 (Vaaler) and is cited, not re-derived. Lemmas
8–9 and Proposition 12 are already **EXACT — HUMAN PROOF**. Every
displayed constant in Section 13 is recomputed from T1–T5 at the
\(V_4\) scales.

| Item | Check | Outcome |
|---|---|---|
| 13.2 \(Y\ge\tfrac{256}{81}m'^{431/81}-1\) | hand (MVT); script five \(m'\) | consistent |
| 13.2 \(L_1\) envelope \(\tfrac{128}{27}m'^{101/27}\) | hand (MVT); script \(m'\le79\) | consistent |
| 13.2 \(L_2\) is the \(V_3\) \(w_1\)-interval | hand | consistent |
| 13.2 \(L_3\) is the \(OEOEE\) \(w\)-interval | hand | consistent; Case 5 is Half A transferred twice |
| T4 Case 1 step ratio \((1+1/m')^{128/81}\) | hand \(m'=16,60\) | same tightening as \(OEOEE\): steps \(\asymp\delta\); pad \(64\) vs \(50.57\) covers a \(4\to5\) retune |
| Case 1 leading \(\tfrac{1024}{81}\) | hand: \(4\cdot\tfrac{128}{27}\cdot\tfrac23\) | consistent |
| Case 1 log \(1024/(27\pi)=12.072\) | hand | consistent; printed \(12.08\) |
| Case 1 Vaaler \(R\) coefficient \(64\) | hand: \(4\cdot\tfrac{1024}{81}=50.57\) | consistent; printed is a pad |
| Case 1 \(R=0.222\,m'^{64/81}\) | hand: \(\sqrt{(256/81)/64}=2/9\) | consistent |
| Case 1 assembled \(28.4\), over \(Y\) \(9.0\) | hand | consistent; saves \(P^{-1/8}\) |
| Case 2 over \(Y\) \(9.1\) | hand: \(21.4\cdot\tfrac43/(256/81)=9.03\) | consistent; \(V_3\) Case 1 transferred; saves \(P^{-3/32}\) |
| Case 3 over \(Y\) \(6.3\) | hand: \(14.8\cdot\tfrac43/(256/81)=6.24\) | consistent; \(V_3\) Case 2 transferred; saves \(P^{-3/32}\) |
| Case 5 over \(Y\) \(6.3\) | hand: \(V_3\) Case 4 times one more \(OE\) weight | consistent; binding \(P^{-9/128}=m'^{-4/9}\) |
| Binding \(P^{-9/128}=m'^{-4/9}\) | hand: \(\tfrac{512}{81}\cdot\tfrac9{128}=\tfrac49\); \(\tfrac16(\tfrac34)^3=\tfrac9{128}\) | consistent; a positive power |
| Prop 12 net \(\tfrac1{243}\) | hand: \((\tfrac13-\tfrac29)\tfrac1{27}\) | consistent |
| 13.7 assembly \(1600\) for \(m'\ge 16\) | hand: \(1008\) at the extra-power factors | consistent |
| Envelope \(\lvert 256\lvert\mathcal O\rvert-Y\rvert\le 1600\,Y\,m'^{-4/9}(1+\log m')^2\) | script \(m'=4,6,8\) | consistent; measured ratios \(1.64,0.23,0.60\) |
| Six-term root \(0.4916\) | script | consistent; rate \(0.5084\); least \(C\) still \(19\) |

The elementary route has a uniform power saving \(P^{-9/128}\).
Proposition 11 meets the ledger bar **EXACT — HUMAN PROOF** at the
asymptotic level, with an unspecified enlarged implicit constant on the
exact fiber; the numeral \(1600\) is only the smooth-window audit above.
Net bookkeeping is \(+1/243\) at scale \(81/512\). The promotion of
\(\lambda^{**}\) from \(0.4891\) to \(0.4916\) is then bookkeeping.
Later \(V_k\) are not opened here.
