# Paper B: the offset composite must subtract the frozen integer floor

The historical Theorem 5.3 Step 5(a) prints 729/512 as the leading
coefficient of the nonzero-offset anchor plus its center mode.
The full phase is c(G-J)-NX, where J=floor(G), with J and N frozen
on each interval. Its leading curvature coefficient is

945/512 - 81/512 - 216/512 = 81/64.

The missing 81/512 is c''J: J=G+O(1), so it cannot be dropped
from the leading curvature. Kind: **REFUTED** displayed identity.
The old positive numerical margins must not be carried over
without this subtraction. This does not refute a power saving.

The [corrected offset proof](../theory/paper_b_offset_anchor_report.md)
centers the coefficient and truncates residual modes below the
curvature-cancellation range, giving O_epsilon(P^(23/24+epsilon))
for its stated family. The subsequent
[dyadic assembly](../theory/paper_b_kernel_assembly_report.md) proves
the weaker undecorated monomial kernel with exponent 127/128.
The subsequent
[OOOEE transfer](../theory/paper_b_oooee_transfer_report.md) proves the
specific four-coordinate modes with exponent 127/128 and the
five-step certificate density 7/8 as AI-assisted written results,
pending independent review. The 95/96 target, arbitrary decorations,
and short-interval localization remain unproved.
Source: [branch dossier](../problems/juggler_paper_b_offset_anchor.md).
Ledger: J-paper-b-offset-composite-729.
Exact regression control: tools/validate_paper_b_offset_anchor.py.

