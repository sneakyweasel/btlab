# \(V_3=OEOEOEE\) audit ledger

Companion to [juggler_oeoee_production.md](juggler_oeoee_production.md)
Sections 9 and 12. Probe: `research.juggler_sequence.v3_audit`. A
script check confirms consistency of what is printed; it is not a
proof.

**Review-scope notice (9 September 2026).** The rows below audit the
smooth reference window \(J_3^{\rm sm}\) used in the printed constant
calculation, not the exact nested Juggler landing fiber
\(J_3^{\rm ex}\). The exact fiber has iterated ceiling endpoints rather
than the formerly collapsed monomial endpoints. The endpoint correction
is lower order than the binding saving, so the fixed-depth asymptotic
exponent and root bookkeeping transfer, but the audited constant \(400\)
and finite census ratio do not automatically transfer. No exact-fiber
constant is certified here.

T1 is Paper B Lemma 3.5 (Vaaler) and is cited, not re-derived. Lemmas
6–7 and Proposition 9 are already **EXACT — HUMAN PROOF**. Every
displayed constant in Section 12 is recomputed from T1–T5 at the
\(V_3\) scales.

| Item | Check | Outcome |
|---|---|---|
| 12.2 \(Y\ge\tfrac{64}{27}m'^{101/27}-1\) | hand (MVT); script five \(m'\) | consistent |
| 12.2 \(L_1\) envelope \(\tfrac{32}9 m'^{23/9}\) | hand (MVT); script \(m'\le79\) | consistent |
| 12.2 \(L_2\) is the \(OEOEE\) \(w\)-interval | hand | consistent; Case 4 is Half A verbatim |
| T4 Case 1 step ratio \((1+1/m')^{32/27}\) | hand \(m'=16,60\) | same tightening as \(OEOEE\): steps \(\asymp\delta\); pad \(48\) vs \(37.93\) covers a \(4\to5\) retune |
| Case 1 leading \(\tfrac{256}{27}\) | hand: \(4\cdot\tfrac{32}9\cdot\tfrac23\) | consistent |
| Case 1 log \(256/(9\pi)=9.054\) | hand | consistent; printed \(9.06\) |
| Case 1 Vaaler \(R\) coefficient \(48\) | hand: \(4\cdot\tfrac{256}{27}=37.93\) | consistent; printed is a pad |
| Case 1 \(R=0.222\,m'^{16/27}\) | hand: \(\sqrt{(64/27)/48}=2/9\) | consistent |
| Case 1 assembled \(21.4\), over \(Y\) \(9.0\) | hand | consistent; saves \(P^{-1/8}\) |
| Case 2 prefactor \(13.1\) | hand: \(2.26\cdot\tfrac12\sqrt{8/3}\cdot\tfrac23\cdot 2\cdot 2\cdot\tfrac83\) | consistent |
| Case 2 \(S=0.320\,m'^{16/27}\) | hand: \(((64/27)/13.1)^{2/3}\) | consistent |
| Case 2 assembled \(14.8\), over \(Y\) \(6.3\) | hand | consistent; saves \(P^{-1/8}\) |
| Case 4 over \(Y\) \(6.3\) | hand: \(11.2\cdot\tfrac43/(64/27)\) | consistent; binding \(P^{-3/32}=m'^{-4/9}\) |
| Binding \(P^{-3/32}=m'^{-4/9}\) | hand: \(\tfrac{128}{27}\cdot\tfrac3{32}=\tfrac49\); \(\tfrac16(\tfrac34)^2=\tfrac3{32}\) | consistent; a positive power |
| Prop 9 net \(\tfrac1{81}\) | hand: \((\tfrac13-\tfrac29)\tfrac19\) | consistent |
| 12.6 assembly \(400\) for \(m'\ge 16\) | hand: \(308\) at the \(m'^{-4/27}\) factor | consistent |
| Envelope \(\lvert 64\lvert\mathcal O\rvert-Y\rvert\le 400\,Y\,m'^{-4/9}(1+\log m')^2\) | script \(m'=12,16,20\) | consistent; measured ratios \(0.13,0.35,0.26\) |
| Five-term root \(0.4891\) | script | consistent; rate \(0.5109\); least \(C\) still \(19\) |

The elementary route has a uniform power saving \(P^{-3/32}\).
Proposition 8 meets the ledger bar **EXACT — HUMAN PROOF** at the
asymptotic level, with an unspecified enlarged implicit constant on the
exact fiber; the numeral \(400\) is only the smooth-window audit above.
Net bookkeeping is \(+1/81\) at scale \(27/128\). The promotion of
\(\lambda^{**}\) from \(0.4801\) to \(0.4891\) is then bookkeeping.
Later \(V_k\) are not opened here.
