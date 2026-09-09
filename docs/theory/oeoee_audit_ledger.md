# \(OEOEE\) audit ledger

Companion to [juggler_oeoee_production.md](juggler_oeoee_production.md)
Section 11. Probe: `research.juggler_sequence.oeoee_audit`. This is a
research-discipline record, not an independent verification and not
part of the journal text. A script check confirms consistency of what
is printed; it is not a proof.

**Review-scope notice (9 September 2026).** The rows below audit the
smooth reference window \(J_2^{\rm sm}\) used in the printed constant
calculation, not the exact nested Juggler landing fiber
\(J_2^{\rm ex}\). The exact fiber has iterated ceiling endpoints rather
than the formerly collapsed monomial endpoints. The endpoint correction
is lower order than the binding saving, so the fixed-depth asymptotic
exponent and root bookkeeping transfer, but the audited constant \(100\)
and finite census ratio do not automatically transfer. No exact-fiber
constant is certified here.

T1 is Paper B Lemma 3.5 (Vaaler) and is cited, not re-derived. Every
other displayed constant in Section 11 is recomputed from the stated
inputs.

| Item | Check | Outcome |
|---|---|---|
| (T2) Kusmin–Landau \(\cot(\pi\delta/2)\le 2/(\pi\delta)\) | hand; script (20000 sample \(\delta\)) | **corrected display**: the inequality holds on \((0,1/2]\). The printed max gap \(-5.2\cdot10^{-4}\) is a sampling artifact; the difference tends to \(0\) from below as \(\delta\to0\) and attains \(1-4/\pi=-0.273\) at \(\delta=1/2\). T2 uses only \(2/(\pi\delta)\), so nothing downstream moves |
| (T3) second-derivative prefactor \(2.26\) | hand: \(4/\sqrt\pi=2.25675\ldots\) | consistent; printed is a valid rounding-up of \(4/\sqrt{\pi\lambda}\) |
| (T4) annulus factor \(4(V+1)\) | hand | **tightened hypothesis**: the abstract statement (only length \(\le\delta\)) is false for arbitrarily short steps. For \(\alpha_q(w)=\tfrac{3q}2w^{2/3}\) the step \(qw^{-1/3}\) varies by \((1+1/m')^{8/9}\) on \(K\), so steps are \(\asymp\delta\) and \(4(V+1)\) holds for large \(m'\). The Half B pad \(35.5\) versus \(28.44\) covers a \(4\to5\) retune at small \(m'\) |
| (T5) pairing \(V\Delta/2+G\) | hand | consistent |
| 11.2 \(L\) envelope \(\tfrac83 m'^{5/3}-1\le L\le\tfrac83(m'+1)^{5/3}+1\) | hand (MVT); script \(m'\le399\) | consistent |
| 11.2 \(\lvert\omega-\tfrac23 w^{1/3}\rvert\le\tfrac32\) | script \(w=2..4999\) | consistent |
| 11.2 \(Y\ge\tfrac{16}9 m'^{23/9}-1\) | hand (MVT); script six \(m'\) | consistent |
| Half B leading \(\tfrac{64}9 q\,m'^{5/3}\) | hand: \(4\cdot\tfrac{8q}3\cdot\tfrac23=\tfrac{64q}9\) | consistent |
| Half B log coefficient \(6.79\) | hand: \(\tfrac{64}{3\pi}=6.790\ldots\) | consistent |
| Half B Vaaler \(R\) coefficient \(35.5\) | hand: both signs give \(\tfrac{256}9=28.44\) | consistent; printed is a pad covering \((m'+1)/m'\) and T4 slack |
| Half B Vaaler log coefficient \(27.2\) | hand: \(4\cdot\tfrac{64}{3\pi}=27.16\) | consistent |
| Half B \(R=0.224\,m'^{4/9}\) | hand: \(\sqrt{(16/9)/35.5}=0.2241\) | consistent |
| Half B assembled \(15.9\,m'^{19/9}\) | hand: \(35.5R+(16/9)/R=15.89\) | consistent |
| Half B over \(Y\) printed \(8.9\) | hand: \(15.9/(16/9)=8.94375\) | **tightened**: write \(8.95\) if the display is reused; the envelope uses \(100\), which still has room |
| Half B \(\Delta_J\) oscillatory modes | hand | printed \(Y/(R+1)\) is the constant term; modes add \(\tfrac{64}9 R\,m'^{19/9}\approx1.59\), absorbed by the \(35.5\) pad and by \(100\) |
| Half A prefactor \(9.85\) | hand: \(\tfrac43\cdot2.26\cdot\sqrt{8/3}\cdot2=9.847\) | consistent |
| Half A \(S=0.318\,m'^{4/9}\) | hand: \(((16/9)/9.85)^{2/3}=0.3196\) | consistent |
| Half A assembled \(11.2\) | hand: \(9.85\sqrt S+(16/9)/S=11.14\) | consistent |
| Half A over \(Y\) printed \(6.3\) | hand: \(11.2/(16/9)=6.30\) | consistent |
| Pairing \(\Lambda_3\), \(\Lambda_1\Lambda_3\), \(\Lambda_1\) | hand | consistent and lower order than Half A/B |
| 11.5 assembly \(8\cdot8.9+4\cdot6.3=96.4\le100\) | hand | consistent; \((1+\log m')^2\) takes the Half B logs |
| Binding saving \(P^{-1/8}=m'^{-4/9}\) | hand: \(\tfrac{32}9\cdot\tfrac18=\tfrac49\) | consistent; a positive power |
| Prop 4 net gain \(\tfrac1{27}\) | hand: \(\tfrac13\cdot\tfrac13-\tfrac29\cdot\tfrac13\) | consistent |
| Envelope \(\lvert16\lvert\mathcal O\rvert-Y\rvert\le100\,Y\,m'^{-4/9}(1+\log m')^2\) | script \(m'=60,90,120\) | consistent; measured ratio \(\le0.25\) against \(100\) |

The elementary route has a uniform power saving. Proposition 3 meets
the ledger bar **EXACT — HUMAN PROOF** at the asymptotic level, with an
unspecified enlarged implicit constant on the exact fiber; the numeral
\(100\) is only the smooth-window audit above. The promotion of
\(\lambda^{**}\) from \(0.4480\) to \(0.4801\) is then bookkeeping.
