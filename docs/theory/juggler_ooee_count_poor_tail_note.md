# Fixed OOEE count deficits and their reciprocal tail

22 September 2026. Kernel-checked continuation of the
[exact fibre-count estimate](juggler_ooee_fibre_parity_note.md).
Advisory statement coverage is pending. This note concerns count
deviations on the actual OOEE fibres, before conversion to conserved
weight or assembly of the physical source cutoff.

## Fixed cutoffs and inclusion

Let F_m be the exact actual OOEE fibre with fourth iterate m, and H_m
its odd candidate count. Put alpha_m=(9/8)m^(2/9) and

\[
 \mathcal P_\eta=\{m:\ |\#F_m/H_m-1/8|\ge\eta\},\qquad
 \mathcal R_{H,C}=\{m:\exists\,1\le q\le H,\ z\in\mathbb Z,
          |q\alpha_m-z|\le C m^{-7/9}\}.
\]

[OOEEFibreResonance.lean](../../formal/Problems/Juggler/OOEEFibreResonance.lean)
proves that for each real eta>0 there exist an integer H>=3, a real C>0
and an integer M>=64 such that every m>=M in P_eta belongs to R_(H,C).
Neither cutoff depends on m. Both frequency signs are reduced to a
positive natural q, including all closed-boundary cases.

To obtain the inclusion, choose H so 15/sqrt(H+1)<eta/4. With
A=A_H^3+6A_H, choose C=max((27/32)H,16A/eta+1), making 4A/C<eta/4.
For m>=1 the two faster negative powers in the fibre estimate are at
most m^(-1/18). Their sum is therefore at most R*m^(-1/18), with
R=2B+18*pi*H+2. The proved limit of that negative power gives a single
threshold after which the remaining contribution is less than eta/4.
The actual count error is then strictly less than eta outside the
resonance family. This proves the inclusion by contraposition.

## Counting the resonance family

[OOEEResonanceTail.lean](../../formal/Problems/Juggler/OOEEResonanceTail.lean)
proves, for natural u>=1, H>=0 and real C>=0,

\[
 \#\bigl(\mathcal R_{H,C}\cap(u,2u]\bigr)
       \le K_{H,C}u^{2/9},\qquad K_{H,C}=H(80C+10H). \tag{1}
\]

For one positive frequency q, the phase increment is at least
(q/4)*(2u)^(-7/9). Every resonance is contained in the shifted arc
for q*alpha_m+C*u^(-7/9); enlarging its width by one phase increment
handles the closed endpoint. The existing monotone arc-counting theorem
gives at most 16C/q+2 points per integer window. At most
5q*u^(2/9) integer windows occur. Their product is
(80C+10q)*u^(2/9), and summing over q<=H gives (1).
No small-width restriction is needed.

Dividing by u bounds reciprocal mass in one block by K_(H,C)*u^(-7/9).
Dyadic summation uses 2^(-7/9)<=2/3, so for all natural U>=1 and N,

\[
 \sum_{\substack{U<m\le N\\m\in\mathcal R_{H,C}}}\frac1m
       \le3K_{H,C}U^{-7/9}. \tag{2}
\]

Combining (2) with the inclusion proves that for each eta>0 there are
D>0 and M>=64 such that, for all U>=M,

\[
 \sum_{\substack{m>U\\m\in\mathcal P_\eta}}\frac1m
       \le D U^{-7/9}. \tag{3}
\]

The final declaration proves summability and the actual infinite-series
bound, by first bounding every finite subset. The cutoff U is excluded
as displayed; no term is silently dropped at an interval boundary.

## Verification and decision

Both modules compile, and the full Lean build passes 9,087 jobs. The
complete [dependency audit](../../formal/AxiomCheckOOEECountPoorTail.lean)
checks all 22 new theorems; their only logical dependencies are propext,
Classical.choice and Quot.sound. Ledger rendering and branch-index
consistency checks pass.

The targeted repository run has 231 passes, 15 skips and 18 failures.
Seventeen failures concern Paper E's release inventory after concurrent
work added BTCalculus.SublinearCountingMass to its transitive imports;
the remaining failure reports stale formalpedia index and DAG artifacts.
These integration gates remained unresolved in that live run. Against
committed publication sources plus this change, the Paper E gate and all
48 targeted release, ledger, layer, declaration and theorem-index tests
pass. This scoped check excludes concurrent Paper E edits; no proof or
publication claim from that separate work is included here.

**PROMOTE** the count-poor reciprocal tail. The subsequent
[weighted-production proof](juggler_ooee_weighted_production_note.md)
now converts counts to coefficient 11/100 and supplies the physical
source cutoff. It discharges OOEEProductionBound and proves unconditional
5/8 contagion. The actual growing-depth pressure estimate and universal
termination remain open.
