# Generalized Ostrowski order-(m) adder

Status: **STRUCTURAL**

What residual/carry state is required to recognize addition in
Baranwal’s order-\(m\) \(\Gamma\)-numeration system? The quadratic
Ostrowski adder is already in the literature. This branch does not
rebuild it.

## Problem

Construct, or obstruct, a finite-state recognizer of
\(\operatorname{Add}_\Gamma(x,y,z)\) for a genuine order-\(m>2\)
system in the sense of Baranwal’s thesis §5.3, and identify the
minimal carry residual that makes the recognizer work.

## Exact statement

Let \(\Gamma=(\alpha_1,\ldots,\alpha_m)\) with
\(\alpha_k=[0;d_{k,1},d_{k,2},\ldots]\). Place values (Baranwal 2020,
§5.3):

\[
q_i=
\begin{cases}
0 & i<0,\\
1 & i=0,\\
\sum_{k=1}^{m}d_{k,i}\,q_{i-k} & i>0.
\end{cases}
\qquad
N=[a_{n-1}\cdots a_0]_\Gamma=\sum_{0\le i<n}a_i q_i.
\]

Proposed canonicality, transcribed from the thesis (pp. 49–50), not
invented here:

1. \(a_0<d_{1,1}\);
2. \(0\le a_i\le d_{1,i+1}\) for \(i\ge 1\);
3. for all \(i\ge 1\), if \(a_i=d_{1,i+1}\) then there exists
   \(k\le m\) such that \(a_{i-k}<d_{k,i+1}\).

Missing digits with negative index are read as \(0\). These three
rules are proposed, not proved unique or complete.

Addition:

\[
\operatorname{Add}_\Gamma(x,y,z)
\iff
\operatorname{val}_\Gamma(x)+\operatorname{val}_\Gamma(y)
=\operatorname{val}_\Gamma(z).
\]

The machine reads \((x_i,y_i,z_i)\) in parallel. Thesis Theorem 2.2
is MSD-first with unread-tail residual. LSD-first is tested only
after a finite MSD box exists.

Phase-0 case:

\[
\Gamma=\bigl([0;\overline{2}],[0;\overline{1}],[0;\overline{1}]\bigr),
\qquad
q_i=2q_{i-1}+q_{i-2}+q_{i-3}.
\]

The characteristic polynomial \(x^3-2x^2-x-1\) is irreducible over
\(\mathbb Q\), so this is not a disguised Ostrowski system. The
dominant root is Pisot, so existence of *some* adder is `KNOWN` by
Frougny–Solomyak. That is not the target.

The target: does the unread-tail residual live in a finite
\(m\)-dimensional box, giving an explicit analog of Theorem 2.2?

## Current literature

- `hieronymi-terry-2018-ostrowski-addition`: addition in Ostrowski-\(\alpha\)
  is finite-automaton recognizable when \(\alpha\) is quadratic.
  `KNOWN`.
- `baranwal-2020-ostrowski-thesis`,
  `baranwal-schaeffer-shallit-2021-ostrowski-automatic`: explicit
  4-input DFA with states \((r,s)\in\{-1,0,1\}^2\), seven states after
  pruning; Walnut 3-input compilation for quadratic \(\alpha\).
  Theorem 2.2 / TCS Theorem 4. `KNOWN`. The \(m\)-dimensional state
  is proposed in thesis §5.3, p. 50, not constructed.
- `shallit-1994-numeration-regular`: a finite-alphabet language of
  representations of \(\mathbb N\) is regular only under a linear
  recurrence / periodic continued-fraction hypothesis. A 3-input
  finite-alphabet adder for one fixed non-quadratic \(\alpha\) is
  already impossible. `KNOWN` (negative).
- `frougny-solomyak-1996-linear-numeration`: constant-coefficient
  Pisot linear systems have finite-state normalization, hence
  addition, on any finite integer alphabet. Conversely, for a Perron
  non-Pisot characteristic root there *exist* alphabets on which
  normalization is not finite-state. That converse is not a theorem
  about this \(w\)-alphabet or this live residual. `KNOWN` under the
  Pisot hypothesis; converse not importable.
- `hollander-1998-greedy-regularity`: greedy numeration language
  regularity implies a Parry dominant root. Classifies greedy
  languages, not Baranwal unread-tail residuals. `KNOWN`.
- `hieronymi-et-al-2024-sturmian-decidability`: uniform
  \(\omega\)-automatic / Büchi use of the BSS *order-2* 4-input
  adder. `KNOWN`. Does not treat \(m>2\).
- Tribonacci / Narayana Walnut adders: Pisot / Dumont–Thomas,
  not Baranwal \(\Gamma\)-systems (Narayana has a zero coefficient).
  `KNOWN` / not this definition.
- Multidimensional continued fractions (Jacobi–Perron, Brun): not
  identified with §5.3 in the citing literature. Not used here.

Classification used in this dossier:

```text
order-2 / quadratic adder              KNOWN
m-dimensional carry idea               KNOWN as a suggestion; OPEN as a theorem
general order-m adder existence        OPEN for Baranwal Gamma-systems
Pisot linear adders                    KNOWN (FS1996)
Pisot ⇒ this 55-set                    PROJECT-SPECIFIC (previous phase)
non-Pisot ⇒ no finite adder            NOT a theorem we may import
live residual bounded ⇔ Pisot          OPEN (PARK; reverse contraction does not decide it)
A^{-1} Q-norm contraction              EXACT — HUMAN PROOF
C({0}) finite                          EXACT — HUMAN PROOF (9164 states; basin of origin, not the adder)
adder live set = C({0})                REFUTED
{s3=0} is a finite seed                REFUTED (infinite plane)
K_0 = F = {s3=0}                       EXACT — HUMAN PROOF (this phase; unbounded)
K_n = E_n slab                         EXACT — HUMAN PROOF (infinite for every n)
t_n = (q_{n-1}, -q_{n-2}, 0) in K_n∩F  EXACT — HUMAN PROOF (unbounded K)
t_n in R(0) for n not 0 or 12 mod 24   REFUTED (s1 ≡ 0 mod 3)
s1 ≡ 0 (mod 3) on R(0) for Γ_NP        EXACT — HUMAN PROOF
|L_0|=∞                                OPEN (K unbounded does not imply it)
L finite for Γ_NP                      OPEN
3-input adder, one non-quadratic α     KNOWN negative
uniform encoded adder, arbitrary α     KNOWN (order 2 only)
```

No 2022–2026 paper found that constructs the §5.3 adder, proves a
general existence theorem for it, or gives a state-dimension lower
bound. The TCS 858 open-problems page was not retrieved; the quote
is from the thesis, which supplied Chapters 2 and 5 of that paper.

## Branch budget

```text
Mathematical target     For Baranwal’s genuine order-3 Γ-system, does the unread-tail residual live in a finite m-dimensional box, giving an explicit analog of thesis Theorem 2.2?
Novelty hypothesis      The m-dimensional carry construction was only proposed. An explicit finite box, a sharp unbounded-carry obstruction, or a necessary/sufficient condition would be new. Existence of some adder for Pisot linear systems is not new.
Falsifier               (A) a 2022–2026 paper already gives the construction; (B) the example is disguised order-2; (C) residuals unbounded with no useful condition; (D) the only theorem is Frougny–Solomyak under another name; (E) |Q| is an implementation artifact.
Existing machinery      BT carry-boundary (add_not_DLocal, D_add) for comparison only; distinguish / Myhill–Nerode; research template. No Ostrowski/Fibonacci/numeration-adder code existed.
Maximum Phase-0 scope   Dossier + literature IDs + faithful §5.3 objects + symbolic residual recurrence + order-2 regression + one order-3 Γ + finite-box search + bounded exhaustive verification. No CLI, Walnut, Lean, order 4, or general numeration framework.
Promotion criterion     A genuine order-3 carry invariant with finite closure not already in the literature, or a new finite-state condition, or a precise obstruction that is not a Pisot reparameterization.
Stop criterion          The construction is already published; the example is not genuine order-3; residuals grow with no interesting condition; or every statement is KNOWN/REPARAMETERIZATION.
```

## Balanced-ternary formulation

This is not a balanced-ternary numeration system. Digits are
nonnegative and constrained by \(\Gamma\). The comparison with BT is
only the carry-boundary principle: digit-local arithmetic stops when
addition needs extra residual state.

## Why BT may be relevant

The rewrite-calculus theorem `add_not_DLocal` isolates the LSD carry
as the missing state for \(D(x+y)\). The Ostrowski question is
whether a higher-dimensional unread-tail residual plays the same
role. The systems are not identified.

## Candidate operations / invariants

- Place-value recurrence of §5.3 — **KNOWN** (definition).
- Proposed three-rule canonicality — **REFUTED** as a unique complete
  system: complete on \([0,q_L)\) for the Phase-0 \(\Gamma\) at
  \(L\le 7\), not injective from \(L=3\). The same rules also fail to
  recover Zeckendorf uniqueness.
- Unread-tail residual
  \(E_i=\sum_{j<i}w_j q_j=\sum_{k=1}^{m}s_k q_{i-m+k}\) with
  \(w_j=z_j-(x_j+y_j)\) — **EXACT — HUMAN PROOF** as an identity of the recurrence
  (human + computational check). Analog of thesis (2.1).
- Deterministic transition
  \(t_1=s_m d_{m,i}\),
  \(t_j=s_{j-1}+s_m d_{m-j+1,i}\) for \(2\le j\le m-1\),
  \(t_m=s_{m-1}+s_m d_{1,i}-w\) — **EXACT — HUMAN PROOF** by substitution
  (human + order-2 regression). Analog of (2.3).
- Unrestricted reachable \(s\in\mathbb Z^m\) lie in a finite box —
  **REFUTED** computationally: coordinates grow once liveness is
  ignored.
- Restricted box \(\lvert t_m\rvert\le 1\) is a sufficient adder —
  **REFUTED**.
- Restricted box \(\lvert t_m\rvert\le 2\) is the live last-coordinate
  *projection* — **EXACT — HUMAN PROOF** as a consequence of \(B_{\min}\), not as
  a sufficient invariant by itself.
- Live reachable set
  \(B_{\min}\subset\mathbb Z^3\), \(\lvert B_{\min}\rvert=55\), is
  forward-invariant under every legal live transition —
  **EXACT — HUMAN PROOF** (explicit set + exterior deadness recurrences).
- Phase-0 85-state \(\lvert s_3\rvert\le 2\) graph equals
  \(B_{\min}\) plus 30 never-live vectors — **EXACT — HUMAN PROOF**.
- Order-2 specialisation recovers Theorem 2.2 — **EXACT — HUMAN PROOF** in the
  source; Phase 0 regresses it.
- \(\Gamma_{\mathrm{NP}}=([0;\overline{2}],[0;\overline{1}],[0;\overline{3}])\)
  has irreducible char poly \(x^3-2x^2-x-3\), discriminant \(-439<0\),
  unique real root in \((2,3)\), conjugate modulus squared \(3/\lambda>1\)
  — **EXACT — HUMAN PROOF** (integer certificate). Perron, not Pisot.
- Residual matrix \(A\) with first row \((0,0,d_3)\), second
  \((1,0,d_2)\), third \((0,1,d_1)\), same characteristic polynomial
  as the place-value recurrence — **EXACT — HUMAN PROOF**.
- Hub \((-3,-1,0)\) is live at every remaining length, and the prefix
  \((1,-2)\) reaches it at every even remaining length — **EXACT — HUMAN PROOF**.
- Live residual union of \(\Gamma_{\mathrm{NP}}\) is infinite —
  **OBSERVATION** through length 16 (strictly increasing counts);
  not a theorem. Finite depth is not infinitude.
- Exact reverse map
  \(A^{-1}=\begin{pmatrix}-1/3&1&0\\-2/3&0&1\\1/3&0&0\end{pmatrix}\)
  over \(\mathbb Q\), with integer preimages iff \(t_1\equiv 0\pmod 3\) —
  **EXACT — HUMAN PROOF**.
- Rational SPD \(Q=\begin{pmatrix}10&-3&-7\\-3&11&-3\\-7&-3&12\end{pmatrix}\)
  with Sylvester minors \(10,101,457\), and
  \(Q-(A^{-1})^{\mathsf T}QA^{-1}\) SPD, hence
  \(\lvert A^{-1}x\rvert_Q^2\le(49/50)\lvert x\rvert_Q^2\) —
  **EXACT — HUMAN PROOF**. Spectral radius \(\rho(A^{-1})<1\) was already known from
  the cubic; this is the induced-norm certificate.
- Accepting slice \(F=\{s_3=0\}\) is an infinite plane, so reverse
  contraction does not bound \(C(F)\) — **EXACT — HUMAN PROOF**.
- Basin \(C(\{(0,0,0)\})\) is finite, cardinality \(9164\),
  stabilization depth \(67\), containing the hub \((-3,-1,0)\) and not
  containing the live accepting terminal \((30,25,0)\) —
  **EXACT — HUMAN PROOF** (backward least fixed point; Checks A and B).
- \(C(\{(0,0,0)\})\) equals the unread-tail adder live set from
  \((0,0,0)\) — **REFUTED**: \(\lvert R_{\le 16}\setminus C(\{0\})\rvert=700\).
- Reverse contraction of \(A^{-1}\) bounds the adder live set —
  **REFUTED** as a mechanism. It bounds co-reachability of a finite
  seed, not forward unread-tail images of the origin.
- Terminal acceptance at remaining \(0\) is \(E_0=s_3=0\), i.e.
  \(K_0=F=\{s_3=0\}\), an infinite plane — **EXACT — HUMAN PROOF**. Canonical
  digits do not constrain \((s_1,s_2)\) at remaining \(0\).
- For \(n\ge 1\), \(K_n=\{s:\mathrm{lo}(n)\le E_n(s)\le\mathrm{hi}(n)\}\)
  with \(E_n=s_1 q_{n-2}+s_2 q_{n-1}+s_3 q_n\) and
  \(\mathrm{lo}(n)=-4S_{n-1}+2\), \(\mathrm{hi}(n)=2S_{n-1}-1\) —
  **EXACT — HUMAN PROOF**. Infinite slab. Same predicate as unread-tail liveness.
- Kernel family \(t_n=(q_{n-1},-q_{n-2},0)\in K_n\cap F\) with
  \(E_n(t_n)=0\) and \(\lvert t_n\rvert\to\infty\) —
  **EXACT — HUMAN PROOF**. Also \((k,0,0)\in K_0\) for every \(k\in\mathbb Z\).
- \((30,25,0)\in K_0\) and \((30,25,0)\notin K_n\) for all \(n\ge 1\) —
  **EXACT — HUMAN PROOF** (\(E_n\ge 25 q_{n-1}>\mathrm{hi}(n)\)). Not in \(C(\{0\})\).
- Hub \((-3,-1,0)\) lies in \(\bigcap_n(K_n\cap F)\) —
  **EXACT — HUMAN PROOF** (existing hub liveness). Bounded point of the plane, not
  a member of the kernel family.
- Pisot and non-Pisot systems share the same \(K_0=F\). The 55-set
  meets \(F\) in \(18\) states — **EXACT — HUMAN PROOF**. Structural change is the
  reachable live set, not the terminal predicate.
- Unbounded \(K\) implies unbounded \(L\) —
  **not claimed**. \(t_n\) need not lie on a live path from
  \((0,0,0)\).
- Every forward image under \(\Gamma_{\mathrm{NP}}\) has
  \(s_1'=3s_3\equiv 0\pmod 3\). Hence \(R(0)\subseteq\{s_1\equiv 0\pmod 3\}\)
  — **EXACT — HUMAN PROOF**. Pisot \(B_{\min}\) occupies all three classes of
  \(s_1\bmod 3\).
- \(t_n\in R(0)\) requires \(q_{n-1}\equiv 0\pmod 3\), i.e.
  \(n\equiv 0\pmod 4\). Immediate predecessors of \(t_n\) share
  \(s_1=-q_{n-2}-q_{n-1}/3\); this is \(\not\equiv 0\pmod 3\) except
  \(n\equiv 0\) or \(12\pmod{24}\) — **EXACT — HUMAN PROOF**. Those \(t_n\) are
  unreachable from the origin.
- \(|L_0|=\infty\) — **not proved**. Finite-depth live growth through
  length 18 is an observation, not infinitude. Remaining \(t_n\)
  (\(n\equiv 0,12\pmod{24}\)) have reverse cones that do not hit
  \(0\) at the scanned depths; that is not a global invariant for
  all of \(K\).
- From the origin, \((c_B)_3=-\mathrm{val}(B)\) — **EXACT — LEAN VERIFIED**
  (`particular_s3`, novelty **KNOWN**). So \(\mathrm{val}=0\) iff
  \(c_B\in F=\{s_3=0\}\), not iff \(c_B=0\).
- Shortest complete non-reset zero-value word is \((1,-2)\) with
  \(c_B=(-3,-1,0)\) (the known \(F\to F\) hub) — **EXACT — HUMAN PROOF**.
  Repeating it stays on the bounded ray. Recurrence combos remain
  the identically-zero reset sublattice. A point of \(F\) is not
  \(\lvert L_0\rvert=\infty\).
- MSD consumed sum splits at two starts — **EXACT — LEAN VERIFIED**
  (`consumedSum_append`, novelty **KNOWN**). Complete-word
  \(\mathrm{val}(UV)=\mathrm{val}(V)-E_{\lvert V\rvert}(c_U)\) —
  **EXACT — LEAN VERIFIED** (`val_concat_energy`, novelty **KNOWN**).
- Complete zero-value words form a monoid under concatenation —
  **REFUTED**. Witness \((1,-2)(1,-2)\) has \(\mathrm{val}=5\),
  \(c_B=(-6,-2,-5)\notin F\).
- Live complete remaining-\(0\) of length \(N\) is \(L_0(N)\) —
  **KNOWN** reparameterization of `particular_s3` plus terminal
  \(E_0=s_3\). The \(N=12\) maximizer \((-27,-6,0)\) lies on \(F\)
  off the two-step ray. Finite \(\lvert L_0(N)\rvert\) is not
  \(\lvert L_0\rvert=\infty\).
- From any residual, \((T_B(s))_3=E_{\lvert B\rvert}(s)-\mathrm{val}(B)\)
  — **EXACT — LEAN VERIFIED** (`fold_s3`, novelty **KNOWN**). So
  \(T_B(s)\in F\) iff \(E_k(s)=\mathrm{val}(B)\). This is
  `energy_telescope` at remaining 0, not a new transducer.
  Repeating the hub word from the hub leaves \(F\). Legal two-step
  returns from the hub stay on the bounded ray \((3k,k,0)\).
- Uniform unnormalized \(\lvert z_j\rvert\le C\) on origin-live
  remaining \(0\) — **REFUTED** (ledger
  `OST-np-unnormalized-mode-bound`). Companion \(z'=\lambda z-\lambda^2 w\)
  is the residual `step` in companion coordinates, not a new
  eigenfunctional. Finite-horizon maximizers are not a symbolic
  family. Spectral cancellation as a new track is parked.
- Arbitrarily long origin-accepted words force infinitely many
  distinct terminals — **REFUTED** (ledger
  `OST-np-long-words-infinite-L0`). The family
  \(U_k=(B_\ast)^k\cdot(1,-2)\) is complete live of length \(4k+2\)
  and all land on the hub (Lean `reset_pow_then_hub`, novelty
  **KNOWN**). König of the reset tree stays at the origin. The full
  language still grows \(\lvert L_0(N)\rvert\) at finite horizon;
  that is not \(\lvert L_0\rvert=\infty\).
- Extra terminal congruence on \(F\) beyond \(3\mid a\) — **REFUTED**
  at start remaining \(12\) (ledger `OST-np-extra-terminal-congruence`).
  Observed \(L_0(12)\) spans \(3\mathbb Z\times\mathbb Z\):
  \(\gcd a=3\), \(\gcd b=1\), not all \(9\mid a\), and points off the
  two-step ray (maximizer \((-27,-6,0)\)). Integer reverse is Lean
  `unique_predecessor` (ledger `OST-np-unique-predecessor`), novelty
  **KNOWN**. New terminals \(12\to 16\) are not \(\lvert L_0\rvert=\infty\).
- Origin-reset prefixes do not create new terminals — **EXACT — LEAN VERIFIED**
  (`reset_prefix`, novelty **KNOWN**): \(T_R(0)=0\) implies
  \(T_{RU}(0)=T_U(0)\). Hub first appears at length \(2\), not via
  \((B_\ast)^k\) padding. Primitive image \(P\) equals \(L_0\) by
  shortest realizations; that is not a new census. Finite-horizon
  \(C(N)\) growth is not \(\lvert L_0\rvert=\infty\).
- Length-\(n\) suffix landing on \(F\) is classified by \(E_n\), not
  by residual \(s\) — **EXACT — LEAN VERIFIED** (`same_energy_same_OnF`,
  novelty **KNOWN**): equal \(E_{\lvert v\rvert}\) implies the same
  `OnF`. Myhill–Nerode / Hankel / digit-triple alphabets are not a
  new census. Finite-horizon Ext collapse (22 windows) is not
  \(\lvert L_0\rvert=\infty\).

## Experiments

No registered CLI runner. Phase-0 functions in
`research.ostrowski` and theorem-phase modules
`transition_extremals`, `residual_closure`, `invariant_search`,
`counterexample_search`. Spectral comparison:
`spectral`, `spectral_residual`, `live_growth`, `nonpisot_search`.
Reverse contraction: `reverse_map`, `contraction_certificate`,
`exact_closure`. Accepting boundary: `terminal_set`. Origin versus
\(t_n\): `origin_live`. Zero-value kernel:
`zero_value_kernel` (complete words \(k\le 4\); not a \(Z_k\) DP).
Recurrence family: `recurrence_zero` (`U_k=(B*)^k(1,-2)`).
Tests:
`tests/research/ostrowski/test_triage.py`,
`tests/research/ostrowski/test_residual_closure.py`,
`tests/research/ostrowski/test_spectral.py`,
`tests/research/ostrowski/test_reverse_closure.py`,
`tests/research/ostrowski/test_terminal_set.py`,
`tests/research/ostrowski/test_origin_live.py`.

Recorded fields for each system:

```text
order m
parameter definition
place-value recurrence
digit constraints
canonicality
LSD/MSD direction
raw states
reachable states
minimal states
maximum carry coordinate
transition count
final-state condition
proof status
```

## Conjectures

None registered. Computational observations stay in this dossier.

## Counterexamples

Recorded in `tests/research/ostrowski/test_triage.py`.

- Proposed §5.3 rules on Fibonacci, length 7: 25 colliding values.
  Classical Ostrowski (Def. 2.1) is unique and complete on the same
  range. The order-\(m\) rules do not specialise to Ostrowski
  uniqueness.
- Phase-0 \(\Gamma\), length 3:
  \(\operatorname{val}(0,0,1)=\operatorname{val}(1,2,0)=5=q_2=2q_1+q_0\).
  The recurrence identity is a legal rewrite under rule 3.
- \(|t_m|\le 1\) boxed adder: false rejects at length \(4\) (3 pairs),
  length \(5\) (25 pairs), length \(6\) (185 pairs). The naive copy of
  Theorem 2.2’s \(\{-1,0,1\}\) last coordinate is not sufficient.
- Repeating interior \(w\equiv-4\) from the origin expands
  (\(\lVert T_{(-4)}^4(0)\rVert_\infty=96\)) and leaves \(K_n\) at
  remaining \(8\) after start remaining \(12\). Expanding without
  \(K_n\) is not a live family.
- Length-6 prefixes \((1,-1,-4,-2,1,-3)\) and \((0,1,-3,1,1,-3)\) are
  co-live at start remaining \(20\) and not co-live at \(12\). Finite
  \(H(u)\) is not \(\lvert H(u)\rvert=\infty\).
- Occurring length-4 block \((2,-4,-2,-4)\) expands under three
  repeats from remaining \(18\) and leaves \(K\). Expanding
  \(A^{|B|}\) is not co-live occurrence at unbounded remaining.
- Window endpoints of live Ext restated as \(E_n/q_{n-1}\) do not
  bound \(\lvert s\rvert\) or \(\lvert u\rvert=s_2+2s_3\) at remaining
  \(>1\): origin-reachable co-live nodes at start remaining \(12\)
  have \(\lvert u\rvert\) and \(\lvert s_3\rvert\) growing on nonempty
  windows. \(u\) is \(E_1\) only.
- Crude \(S_k\le 2q_k\) yields real Ext-width \(<6\), not \(<4\).
  Width \(<4\) through remaining \(24\) is computational.
- Euclidean \(\lvert s_{\mathrm{orth}}\rvert\) on origin-reachable
  live slices at remaining \(4\) grows from start remaining \(12\) to
  \(16\) (\(\lVert s\rVert_\infty\) \(15\to 24\); \(166\to 427\)
  states). Complementary \(E_{n-1},E_{n-2}\) also grow. Energy does
  not bound the kernel component.
- Uniform unnormalized mode bound \(\lvert z_j\rvert\le C\) on
  origin-live remaining \(0\) fails from start remaining \(12\) to
  \(16\) (ledger `OST-np-unnormalized-mode-bound`): Perron
  \(\lvert z\rvert\) \(79.15\to 114.02\),
  \(\lVert s\rVert_\infty\) \(27\to 37\), \(\lvert L_0\rvert\)
  \(165\to 379\). Normalized \(\lvert\lambda\rvert^{-k}\lvert z\rvert\)
  is not residual boundedness. Maximizer words at these horizons are
  not a symbolic family.
- The maximizer prefix \(P_m=(2)\cdot(-4)^m\) plus a uniformly bounded
  tail is not an unbounded origin-live family. At tail length
  \(\le 6\), live remaining-0 completions exist for \(m=0,1,2\)
  (65 other terminals; tails unstructured; some hub / two-step-ray
  landings mixed in). For \(m\ge 3\) the prefix itself dies:
  \((2,-4,-4,-4)\) lands on \((6,2,2)\), which is not live. No
  closed-form tail. Finite \(m\) is not \(\lvert L_0\rvert=\infty\).
- Arbitrarily long origin-accepted words force infinitely many
  distinct remaining-0 terminals: false. The family
  \(U_k=(B_\ast)^k\cdot(1,-2)\) of lengths \(4k+2\) is complete live
  and \(\tau(U_k)\) is the hub for every tested \(k\) (ledger
  `OST-np-long-words-infinite-L0`). König of \((B_\ast)^\infty\) stays
  at the origin. Full-language \(\lvert L_0(N)\rvert\) growth is not
  this family and not \(\lvert L_0\rvert=\infty\).
- Extra terminal congruence beyond \(3\mid a\) (equivalently \(9\mid a\)
  or \(\gcd b>1\)) fails on \(L_0(12)\): \(\gcd a=3\), \(\gcd b=1\),
  maximizer \((-27,-6,0)\) off the two-step ray (ledger
  `OST-np-extra-terminal-congruence`). \(L_0(16)\setminus L_0(12)\) is
  nonempty. Small forms \(\alpha a+\beta b\) all grow \(12\to 16\).
  Finite-horizon span of \(3\mathbb Z\times\mathbb Z\) is not
  \(\lvert L_0\rvert=\infty\).
- Unbounded realization length of a terminal is not a new terminal:
  \(T_R(0)=0\) implies \(T_{RU}(0)=T_U(0)\) (ledger `OST-np-reset-prefix`).
  Hub \(\ell_{\min}=2\). \(C(N)\) still grows through remaining \(8\);
  that is not \(\lvert L_0\rvert=\infty\). Primitive \(P=L_0\) is not a
  new set.
- Length-\(n\) suffix acceptance is classified by \(E_n\), not by
  residual coordinates (ledger `OST-np-same-energy-same-OnF`).
  Equal energy implies the same landing on \(F\). Distinct residuals
  with the same \(E_n\) are not Myhill–Nerode-distinct at remaining
  \(n\). Co-live states collapse onto finitely many Ext windows
  (22 types). Finite future quotient does not imply
  \(\lvert L_0\rvert<\infty\). The 3-input adder for one
  non-quadratic \(\alpha\) remains literature **KNOWN negative**.
- Unique control at large \(\lvert s\rvert\) fails on the \(N=12\)
  maximizer prefixes: remaining \(5\), state \((12,-2,-1)\),
  \(\lVert s\rVert_\infty=12\), Ext \((-1,0,1)\). Ext is the energy
  slab, not a residual bound.
- The unique length-4 consecutive place-value relation is a multiple
  of \((3,1,2,-1)\). The \(W\)-valued sign MSD \(B_\ast=(1,-2,-1,-3)\)
  has \(\mathrm{val}=0\) but is a reset \(T_{B_\ast}(0)=0\). Last
  letter \(-3\) is not LSD-legal. All \(11\) length-\(\le 6\)
  shift-combinations in \(W\) are algebraic zero-sum resets, not an
  expanding family.
- \(\mathrm{val}(B)=0\Rightarrow c_B=0\) is false: complete word
  \(B=(1,-2)\) has \(\mathrm{val}=0\) and \(c_B=(-3,-1,0)\). The same
  fiber is already visible as the remaining-\(0\) live slice
  \(\lvert L_0(12)\rvert=165\subset F\).
- Complete zero-value words form a monoid: false. \(U=V=(1,-2)\)
  have \(\mathrm{val}=0\) but \(\mathrm{val}(UV)=5\) and
  \(c_{UV}=(-6,-2,-5)\notin F\) (Lean `complete_zero_not_monoid`).

## Formalization

The Γ_NP origin obstruction is Lean-verified in
`formal/Problems/Ostrowski/NP/` (mathlib v4.33.1, Lean 4.33.1), namespace
`Ostrowski.NP`, theorem `kernel_unreachable_of_not_exceptional`. Zero
`sorry`. `OriginReachable` is unrestricted integer reachability from
`(0,0,0)`, not the live set `L_0`.

Proof summary:

- Every step has first coordinate `3 s_3`, so `R(0) ⊆ {s_1 ≡ 0 (mod 3)}`.
- Place values `q_n` modulo 3 have period 8; `t_n` itself fails the
  residue unless `n ≡ 0 (mod 4)`.
- Integer preimages of `t_n` share first coordinate
  `-q_{n-2} - q_{n-1}/3`. The combination `q_{n-1} + 3 q_{n-2}` modulo
  9 has period 24, and is nonzero off `n ≡ 0, 12 (mod 24)`.
- Those `t_n` cannot be last steps of an origin-reachable path.
- Classes `n ≡ 0, 12 (mod 24)` are not classified as unreachable.
  No theorem about `|L_0|`. The 55-set and the unread-tail slab
  inequalities stay human / Python.

Phase-0 on the exceptional classes (`research.ostrowski.exceptional_kernel`)
did not isolate an alphabet-free invariant or a symbolic bridge. No new
Lean. `kernel_unreachable_of_not_exceptional` is unchanged.

The cumulative energy identity `energy_telescope` is Lean-verified in
the same `Energy.lean` file (ledger `OST-np-energy-telescope`), novelty
**KNOWN**. Defect / `lo`/`hi` recurrences stay Python. Not an `L_0`
theorem.

Co-live control language (`research.ostrowski.control_language`) is a
finite-horizon census.

Live Ext is the energy-slab interval in `w`: Lean
`Ostrowski.NP.energy_control_interval` (ledger
`OST-np-energy-ext-interval`), novelty **KNOWN**. Alphabet-specific
`lo`/`hi` and the width `<4` table stay Python. Not an `L_0` theorem.
`kernel_unreachable_of_not_exceptional`, `energy_step`, and
`energy_telescope` are unchanged.

Homogeneous residual motion is energy-neutral in the sliding index:
Lean `Ostrowski.NP.energy_homogeneous` (ledger
`OST-np-energy-homogeneous`), novelty **KNOWN**. Consecutive adjoints
are independent: Lean `Ostrowski.NP.adjointDet_eq`,
`det(u_n,u_{n-1},u_{n-2})=3^{n-2}` for `n≥2` (ledger
`OST-np-adjoint-window-det`), novelty **KNOWN**. Neighboring energies
invert `s` over `ℚ`. Origin-live `|s_orth|` growth is Python, not an
`L_0` theorem.

From the origin the residual is the control particular: Lean
`Ostrowski.NP.origin_particular` (ledger `OST-np-origin-particular`),
novelty **KNOWN**. `foldSteps ws origin` equals
`−∑ A^{k-1-j} e₃ w_j`. Companion `z`-recurrence and unnormalized
mode growth stay Python. Not an `L_0` theorem.

The origin impulse is the place-value vector: Lean
`Ostrowski.NP.iterateA_e3` (ledger `OST-np-impulse-place`), novelty
**KNOWN**. `A^r e₃ = (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r)`. Scalar
forcings and the reindexed convolution stay Python. Not an `L_0`
theorem. `origin_particular` and the earlier Energy lemmas are
unchanged.

The recurrence word has MSD consumed sum zero: Lean
`Ostrowski.NP.recurrence_word_zero` (ledger
`OST-np-recurrence-word-zero`), novelty **KNOWN**.
`consumedSum (n+4) [1,-2,-1,-3] = 0`. That is `q_rec`. Affine
iteration and liveness stay Python. Not an `L_0` theorem.
`iterateA_e3` and `origin_particular` are unchanged.

From the origin the third particular coordinate is minus the
consumed valuation: Lean `Ostrowski.NP.particular_s3` (ledger
`OST-np-particular-s3`), novelty **KNOWN**.
`(particularSum ws).2.2 = -consumedSum ws.length ws`. Concatenation
`c_{UV}=A^{|V|}c_U+c_V` is `particular_concat` from
`foldSteps_affine`. Shortest complete non-reset, \(k^\ast\), and
\(\lvert L_0\rvert\) stay Python. Not an `L_0` theorem.

MSD consumed sum splits at two starts: Lean
`Ostrowski.NP.consumedSum_append` (ledger
`OST-np-consumed-sum-append`), novelty **KNOWN**. Complete-word
value obeys `val(UV)=val(V)-E_{|V|}(c_U)`: Lean
`Ostrowski.NP.val_concat_energy` (ledger `OST-np-val-concat-energy`),
novelty **KNOWN**. Complete zero-value is not a monoid (ledger
`OST-np-complete-zero-monoid`, `REFUTED`; Lean
`complete_zero_not_monoid`). Hub regression `hub_nonreset` is not
infinitude. Not an `L_0` theorem.

From any incoming residual, the third coordinate after a block is
minus the state-dependent value: Lean `Ostrowski.NP.fold_s3`
(ledger `OST-np-fold-s3`), novelty **KNOWN**.
`(foldSteps ws s).2.2 = energy ws.length s - consumedSum ws.length ws`.
`T_B(s)\in F` iff `E_k(s)=val(B)` (`fold_on_F_iff`). That is
`energy_telescope` at remaining 0. Affine action remains
`foldSteps_affine`. Not an `L_0` theorem.

Uniform unnormalized companion-mode bound on origin-live remaining
0 is **REFUTED** (ledger `OST-np-unnormalized-mode-bound`):
\(\lvert L_0\rvert=165\to 379\), \(\lvert z\rvert\approx 79\to 114\)
from start remaining \(12\to 16\). The companion recurrence is
`step` in companion coordinates. No new Lean. Not an `L_0` theorem.

The recurrence word is a reset: Lean `Ostrowski.NP.recurrence_word_reset`
(ledger `OST-np-reset-pow-then-hub`), novelty **KNOWN**.
`(B*)^k · (1,-2)` has particular the hub (`reset_pow_then_hub`).
Liveness of `U_k` stays Python. Arbitrarily long accepted words do
not force infinitely many terminals (ledger
`OST-np-long-words-infinite-L0`, `REFUTED`). König is not an
`L_0` theorem.

Integer reverse of \(T_w\) is Lean `Ostrowski.NP.unique_predecessor`
(ledger `OST-np-unique-predecessor`), novelty **KNOWN**, with
`predecessor_on_F` on the plane. Extra congruence on origin-live
remaining-0 terminals beyond \(3\mid a\) is **REFUTED** at start
remaining \(12\) (ledger `OST-np-extra-terminal-congruence`).
Python `terminal_span_report`: \(\gcd a=3\), \(\gcd b=1\), not
\(9\mid a\). Not an `L_0` theorem.

An origin reset does not change the particular of a suffix: Lean
`Ostrowski.NP.reset_prefix` (ledger `OST-np-reset-prefix`), novelty
**KNOWN**. `particularSum R = origin` implies
`particularSum (R ++ U) = particularSum U`. Hub first appears at
length 2. Primitive image \(P=L_0\) is shortest-realization
tautology, not a new census. Not an `L_0` theorem.

Length-`n` suffix landing on `F` is classified by `E_n`: Lean
`Ostrowski.NP.same_energy_same_OnF` (ledger
`OST-np-same-energy-same-OnF`), novelty **KNOWN**. Equal
`E_|v|` implies the same `OnF`. Myhill–Nerode / Hankel is
reparameterization of the energy slab at fixed remaining, and of
live union at unbounded length. Not an `L_0` theorem.

Ledger row `OST-np-kernel-unreach`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-energy-step`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-energy-telescope`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-energy-ext-interval`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-energy-homogeneous`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-adjoint-window-det`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-origin-particular`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-impulse-place`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-recurrence-word-zero`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-particular-s3`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-consumed-sum-append`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-val-concat-energy`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-complete-zero-monoid`: `REFUTED`.
Ledger row `OST-np-fold-s3`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-unnormalized-mode-bound`: `REFUTED`.
Ledger row `OST-np-reset-pow-then-hub`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-long-words-infinite-L0`: `REFUTED`.
Ledger row `OST-np-unique-predecessor`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-extra-terminal-congruence`: `REFUTED`.
Ledger row `OST-np-reset-prefix`: `EXACT — LEAN VERIFIED`.
Ledger row `OST-np-same-energy-same-OnF`: `EXACT — LEAN VERIFIED`.

## Results

### Control \(\Gamma_{\mathrm P}\)

Same \(\Gamma\) as Phase 0. Specialized transition:

\[
(s_1,s_2,s_3)\mapsto(s_3,\,s_1+s_3,\,s_2+2s_3-w),
\]

with \(w\in\{-4,\ldots,2\}\) at places \(i\ge 1\) and
\(w\in\{-2,\ldots,1\}\) at the LSD. Unread-tail bounds:

\[
\mathrm{lo}(i)=-4S_{i-1}+2,\qquad
\mathrm{hi}(i)=2S_{i-1}-1
\]

(\(S_{n}=\sum_{j=0}^{n}q_j\); \(\mathrm{lo}(0)=\mathrm{hi}(0)=0\)).
A state at remaining length \(i\) is *live* when
\(\mathrm{lo}(i)\le E_i\le\mathrm{hi}(i)\).

The live reachable set from \((0,0,0)\) is the explicit 55-element
\(B_{\min}\) in `research.ostrowski.residual_closure.B_MIN`. It is
contained in the axis box
\(\lvert s_1\rvert\le 2\), \(-3\le s_2\le 2\), \(\lvert s_3\rvert\le 2\)
(175 lattice points; 120 unused). Last-coordinate projection
\(\lvert s_3\rvert\le 2\) is necessary on live paths and not
sufficient: the Phase-0 85-state \(\lvert s_3\rvert\le 2\) graph is
\(B_{\min}\) plus 30 vectors that are never live.

| field | theorem-phase record |
|---|---|
| order \(m\) | 3 |
| \(B_{\mathrm{reach}}\) | \(B_{\min}\), 55 states, stable for length \(9\)–\(16\) |
| \(B_\square\) | \(\lvert s_1\rvert\le 2,\ \lvert s_2\rvert\le 3,\ \lvert s_3\rvert\le 2\), 175 points |
| \(B_{\min}\) | the 55-element list |
| Phase-0 85-set | \(B_{\min}\) plus 30 never-live states |
| Hopcroft on live graph | 55 live states, no merge |
| \(\lvert s_3\rvert\ge 3\) escape | none on live paths |
| proof status | exterior deadness recurrences, **EXACT — HUMAN PROOF** |

Exterior images of \(B_{\min}\): 108 vectors. Each is overflow
(\(G_i=E_i-\mathrm{hi}(i)\)) or underflow
(\(H_i=\mathrm{lo}(i)-E_i\)). For \(i\ge 4\),

\[
G_i=2G_{i-1}+G_{i-2}+G_{i-3}-5,\qquad
H_i=2H_{i-1}+H_{i-2}+H_{i-3}-10.
\]

Initial gaps \(G_0,\ldots,G_3\ge 1\) and \(H_0,\ldots,H_3\ge 2\) on
every exterior image, so all later gaps stay positive. Therefore
every legal live image of \(B_{\min}\) stays in \(B_{\min}\).

Genuine addition paths are live at every prefix because
\(E_i\) equals the unread legal difference tail. The unrestricted
residual machine still accepts iff \(\sum w_i q_i=0\). Together:
this \(\Gamma\)-addition relation is recognized by a finite 3-input
MSD automaton with state set \(B_{\min}\).

Existence of *some* adder remains `KNOWN` by Pisot theory. The
project-specific object is the explicit Baranwal-coordinate region.

### Test \(\Gamma_{\mathrm{NP}}\)

Same \(d_1=2\), \(d_2=1\), so the memoryless alphabets agree. Only
\(d_3\) changes:

\[
\Gamma_{\mathrm{NP}}=([0;\overline{2}],[0;\overline{1}],[0;\overline{3}]),
\qquad
q_i=2q_{i-1}+q_{i-2}+3q_{i-3}.
\]

Char poly \(x^3-2x^2-x-3\). Integer certificate: irreducible (no
rational root), discriminant \(-439<0\) (one real root, complex
conjugate pair), sign change \(P(2)<0<P(3)\) so \(\lambda\in(2,3)\),
product of roots \(3\), hence conjugate modulus squared
\(3/\lambda>1\). Perron, not Pisot. Not a disguised quadratic.

Transition (same residual semantics):

\[
(s_1,s_2,s_3)\mapsto(3s_3,\,s_1+s_3,\,s_2+2s_3-w)
=As-(0,0,w),
\qquad
A=\begin{pmatrix}0&0&3\\1&0&1\\0&1&2\end{pmatrix}.
\]

All eigenvalues of \(A\) have modulus \(>1\). Control \(A\) has one
expanding eigenvalue and two contracting.

Live BFS from \((0,0,0)\), same alphabets. Control recovers
\(\lvert B_{\min}\rvert=55\) by length 9. For \(\Gamma_{\mathrm{NP}}\)
the live union is strictly increasing through length 16 (867 states
at length 14; 1351 at length 16), with
\(\max\lvert s_3\rvert\ge 3\) from length 6 and all three coordinates
growing. Finite depth is not infinitude.

Hub \((-3,-1,0)\): live at remaining \(0,1\) by direct check; for
\(i\ge 2\), \(E_i=-3q_{i-2}-q_{i-1}<0\le\mathrm{hi}(i)\) and
\(E_i-\mathrm{lo}(i)=4S_{i-1}-3q_{i-2}-q_{i-1}-2\ge 0\) because
\(S_{i-1}\ge q_{i-1}+q_{i-2}+1\) for \(i\ge 3\). The prefix
\((1,-2)\) from remaining \(2m+2\) reaches the hub at remaining
\(2m\), live throughout. No closed-form word family with
\(\lvert s\rvert\to\infty\) is written down. Periodic blocks from the
hub die. Greedy live walks grow but are not a proof.

### Reverse contraction versus the adder live set

Three sets, never mixed:

- \(R_{\le N}\): forward unread-tail live from \((0,0,0)\) in at most
  \(N\) steps (the 55-set analogue). Depth 16 has \(1351\) states and
  is still growing.
- \(C(K)\): backward least fixed point of a seed \(K\).
- \(F=\{s_3=0\}\): accepting slice. An infinite plane. Reverse
  contraction does not bound \(C(F)\).

Exact inverse over \(\mathbb Q\):

\[
A^{-1}=\begin{pmatrix}-1/3&1&0\\-2/3&0&1\\1/3&0&0\end{pmatrix},
\qquad
s=A^{-1}\bigl(t+(0,0,w)\bigr).
\]

Integer reverse: \(t_1\) divisible by \(3\), then
\(s_3=t_1/3\), \(s_1=t_2-s_3\), \(s_2=t_3+w-2s_3\).

Lyapunov matrix (guessed with floats, proved by integer Sylvester):

\[
Q=\begin{pmatrix}10&-3&-7\\-3&11&-3\\-7&-3&12\end{pmatrix},
\qquad
\lvert A^{-1}x\rvert_Q^2\le\frac{49}{50}\lvert x\rvert_Q^2.
\]

Leading minors of \(Q\): \(10,101,457\). Decrement minors:
\(10/9,2/3,5/9\). Crude a priori box for **preimages of the origin**:
\(\rho<99/100\), \(\lvert(0,0,w)\rvert_Q<14\), hence
\(\lvert s\rvert_Q<1386\); \(Q-I\) SPD so \(\lvert s_i\rvert\le 1386\).
The box is not enumerated. It does not bound forward images of
\((0,0,0)\).

The only honest finite seed is \(\{(0,0,0)\}\). Its basin
\(C(\{0\})\) is finite:

| field | record |
|---|---|
| cardinality | \(9164\) |
| stabilization depth | \(67\) |
| extrema | \(s_1\in[-33,32]\), \(s_2\in[-30,29]\), \(s_3\in[-11,10]\) |
| \(\max\lvert s\rvert_1\) | \(57\) |
| \(\max s^{\mathsf T}Qs\) | \(14460\) |
| hub \((-3,-1,0)\) | in the basin |
| \((30,25,0)\) | not in the basin; live accepting in \(R_{\le 16}\) |
| fingerprint | `c4487dbeaab216fd340b54fada7be21d4c57a35648328d62a82f5d516366e70f` |

Check A: every non-origin basin state has a legal \(w\) with
\(T_w(s)\) still in the basin. Check B: no integer preimage leaves
the basin, and no hull point of the computed box steps into it.
Do not call \(C(\{0\})\) the 55-set analogue.

Depth-growth paradox (\(R_{\le N}\) is a transient shell of expanding
\(A\); monotone growth \(\ne\) infinitude):

| \(N\) | \(\lvert R_{\le N}\rvert\) | \(\max\lvert s_i\rvert\) | \(\lvert R\setminus C(\{0\})\rvert\) |
|---|---|---|---|
| 8 | 154 | \((15,14,5)\) | 51 |
| 10 | 310 | \((21,18,7)\) | 120 |
| 12 | 532 | \((27,24,9)\) | 242 |
| 14 | 867 | \((30,31,10)\) | 436 |
| 16 | 1351 | \((36,37,12)\) | 700 |

At depth 14, \(\lvert s_2\rvert=31\) already exits the computed basin
box. Depth 16 remains inside the crude Lyapunov box \(1386\). Those
outside states are forward transients, not points of \(C(\{0\})\).

Pisot vs reverse contraction: for \(\Gamma_{\mathrm P}\), the 55-set
is a **forward** live invariant. For \(\Gamma_{\mathrm{NP}}\),
\(A^{-1}\) is a \(Q\)-norm contraction, but that is a statement about
**preimages of a seed**. It is not the adder mechanism and does not
make Pisot unnecessary for this residual. The control \(B_{\min}\) is
still \(55\).

### Accepting boundary \(K_n\)

Unread-tail identity, \(q_j=0\) for \(j<0\), \(q_0=1\):

\[
E_i=s_1 q_{i-2}+s_2 q_{i-1}+s_3 q_i,\qquad E_0=s_3.
\]

Difference digits remain \(w_j=z_j-(x_j+y_j)\). Four objects:

- \(K_0=F=\{s_3=0\}\). Acceptance after the tape ends. Infinite
  plane. Length-independent. Canonical digits do not enter.
- \(K_n=\{s:\mathrm{lo}(n)\le E_n(s)\le\mathrm{hi}(n)\}\) for
  \(n\ge 1\). Infinite slab. Identical to unread-tail liveness: a
  legal tail realizing \(E_n\) *is* an accepting suffix.
- \(R_{\le N}\): forward live-reachable from \((0,0,0)\).
- \(L\): infinite-horizon live set from the origin. Not established.

LSD last step: \(T_w(s)=(3s_3,\,s_1+s_3,\,s_2+2s_3-w)\) lands in \(F\)
iff \(w=s_2+2s_3\in\{-2,-1,0,1\}\), which is liveness at remaining
\(1\) because \(E_1=s_2+2s_3\).

On \(F\), \(E_n(a,b,0)=a q_{n-2}+b q_{n-1}\) (and \(0\) if \(n=0\)).
The kernel family

\[
t_n=(q_{n-1},-q_{n-2},0)\qquad(n\ge 1)
\]

has \(E_n(t_n)=0\). Signed alphabets give \(\mathrm{lo}(n)<0<\mathrm{hi}(n)\),
so \(t_n\in K_n\cap F\). Place values are strictly increasing, so
\(\lvert t_n\rvert\to\infty\). Separately, \((k,0,0)\in K_0\) for every
integer \(k\). Thus \(\bigcup_n(K_n\cap F)\) is unbounded (Outcome A).
This does **not** prove \(L\) infinite: \(t_n\) need not be reachable
from \((0,0,0)\) on a live path.

\(\lvert K_n\rvert=\infty\) for every \(n\). The table below records
that fact together with a boxed window \(\lvert K_n\cap[-4,4]^3\rvert\),
which is **not** \(\lvert K_n\rvert\). \(K_n\not\subseteq K_{n+1}\).

| \(n\) | \(\lvert K_n\rvert\) | \(\lvert K_n\cap F\rvert\) | \(\mathrm{lo},\mathrm{hi}\) | \(t_n\) | window \(M=4\) |
|---|---|---|---|---|---|
| 0 | \(\infty\) | \(\infty\) | \(0,0\) | — | 81 (all in \(F\)) |
| 1 | \(\infty\) | \(\infty\) | \(-2,1\) | \((1,0,0)\) | 162 |
| 2 | \(\infty\) | \(\infty\) | \(-10,5\) | \((2,-1,0)\) | 260 |
| 3 | \(\infty\) | \(\infty\) | \(-30,15\) | \((5,-2,0)\) | 246 |
| 4 | \(\infty\) | \(\infty\) | \(-90,45\) | \((15,-5,0)\) | 267 |
| 5 | \(\infty\) | \(\infty\) | \(-254,127\) | \((41,-15,0)\) | 281 |
| 6 | \(\infty\) | \(\infty\) | \(-702,351\) | \((112,-41,0)\) | 277 |

#### \((30,25,0)\)

In \(K_0\) because \(s_3=0\). For \(n\ge 1\),
\(E_n=30 q_{n-2}+25 q_{n-1}\ge 25 q_{n-1}\). Place sums satisfy
\(S_k\le 2 q_k\) (base \(S_0=1\le 2\); \(q_n\ge 2 q_{n-1}\) because
\(d_1=2\)), so \(\mathrm{hi}(n)=2S_{n-1}-1\le 4 q_{n-1}-1<25 q_{n-1}\).
Hence not in any \(K_n\) for \(n\ge 1\). It is the LSD image
\(T_0(15,-20,10)=(30,25,0)\), with the predecessor live at remaining
\(1\). Not in \(C(\{0\})\): reverse contraction of the origin does not
reach it. It belongs to the \(K_0\) family of ghost coordinates on
\(F\), not to the kernel family \(t_n\).

#### Hub \((-3,-1,0)\)

Live at every remaining length (existing integer certificate), so it
is a bounded point of \(\bigcap_n(K_n\cap F)\). Reached from the origin
at remaining \(2m\) by the prefix \((1,-2)\). Same plane as \(t_n\),
different role: reachable live residual versus kernel of \(E_n\).

#### Pisot control

\(\Gamma_{\mathrm P}\) has the same alphabets, hence the same
\(K_0=F\) and the same \(\mathrm{lo},\mathrm{hi}\). \(B_{\min}\)
contains \(18\) states with \(s_3=0\). Those are reachable-live
terminals, a proper subset of \(F\). Non-Pisot versus Pisot changes
which live states occur on paths from \((0,0,0)\), not the terminal
predicate.

Reverse contraction around any *fixed* seed cannot imply finite live
closure, because the accepting boundary itself is unbounded. Whether
that forces infinitely many distinct *reachable* live residuals is a
different question and is not answered here.

### Origin-reachable live set versus \(t_n\)

Three relations:

- \(R(0)\): forward images of \((0,0,0)\). For \(\Gamma_{\mathrm{NP}}\),
  \(T_w(s)_1=3s_3\), so \(s_1\equiv 0\pmod 3\) on every reachable
  state.
- \(K_n\): terminal / live slab (previous phase).
- \(L_0\): states on some live path from the origin
  (\(\bigcup_N R_{\le N}\) in the live BFS). Not proved finite or
  infinite.

Place values modulo \(3\) have period \(8\):
\((1,2,2,0,2,1,1,0)\). Hence \(q_{n-1}\equiv 0\pmod 3\) iff
\(n\equiv 0\pmod 4\). The kernel family is incompatible with
\(R(0)\) for all other \(n\).

Every integer preimage of \(t_n\) has the same first coordinate
\(-q_{n-2}-q_{n-1}/3\). Using \(q_n\bmod 9\) (period \(24\)), this
predecessor has \(s_1\not\equiv 0\pmod 3\) except when
\(n\equiv 0\) or \(12\pmod{24}\). Those \(t_n\) cannot be forward
images of origin-reachable states. The same classification is the
Lean theorem `kernel_unreachable_of_not_exceptional` (ledger
`OST-np-kernel-unreach`). Exceptional classes are not claimed
unreachable in Lean.

The remaining progression is not settled by the mod-\(3\) trap.
Reverse BFS from \(t_{12}\) to depth \(5\) has \(774\) states,
minimum \(\ell_1=56541\), and does not contain the origin. That is
not a proof that \(0\) is absent from the infinite reverse tree.

Two-step return to \(F\): \(T_v\circ T_w(s_1,s_2,0)=(3a,a,0)\) with
\(a=s_2-w\), when \(v=s_1+2a\). The kernel family is not on this
ray for \(n\ge 1\).

Pisot control: \(s_1'=s_3\), so \(s_1\equiv 0\pmod 3\) is not
forced. \(B_{\min}\) occupies \(\{0,1,2\}\) in the first coordinate.
The obstruction is the \(d_3=3\) first row of \(A\), not Pisot
contraction.

Live census (growth \(\ne\) infinitude; no \(t_n\) appears):

| \(N\) | \(\lvert L_{\le N}\rvert\) | \(\max\lvert s_i\rvert\) | \(\lvert L\cap F\rvert\) | \(t_n\) hit |
|---|---|---|---|---|
| 12 | 532 | \((27,24,9)\) | 167 | none |
| 16 | 1351 | \((36,37,12)\) | 379 | none |
| 18 | 2036 | \((42,39,14)\) | 529 | none |

All scanned live states have \(s_1\equiv 0\pmod 3\). The hub is in
\(L_{\le N}\). Repeating \(w=1\) from the origin expands but leaves
the unread-tail interval at the second step.

### Exceptional classes \(n\equiv 0\) and \(n\equiv 12\pmod{24}\)

The two progressions are kept separate. They occupy distinct
residues modulo \(9\):

\[
t_{24k}\equiv(6,5,0),\qquad t_{24k+12}\equiv(3,4,0)\pmod 9.
\]

Both residues lie in the forward \(W\)-graph and in the alphabet-free
graph on \((\mathbb Z/9\mathbb Z)^3\) (that graph has \(81\) reachable
states). Coordinatewise moduli \(m\in\{4,8,9,13,18,24,27\}\) do not
separate either class. Affine forms
\(\ell(s)=as_1+bs_2+cs_3\) that transform as
\(\ell(T_w(s))\equiv\lambda\ell(s)+\mu w\pmod m\), other than
reparameterizations of \(s_1\), did not separate the targets on
\(m\in\{8,9,13\}\).

Exact two-step return to \(F\) with both controls in \(W\):
\(T_w(a,b,0)=(0,a,b-w)\) and the unique returning \(v=a+2(b-w)\)
gives \((3\alpha,\alpha,0)\) with \(\alpha=b-w\). Restricting \(v\in W\)
forces \(\alpha=k\) with \(k\in\{-2,-1,0,1\}\). The hub
\((-3,-1,0)\) is on this ray; \(t_n\) is not. A bounded ray is not an
unbounded live family.

Reverse cones of \(t_{12},t_{24},t_{36},t_{48}\) (interior \(W\),
depth \(4\)) do not contain the origin. Minimum \(\ell_1\) stays on
the scale of \(\lvert t_n\rvert\) and strictly above the
\(\ell_1\le 57\) cap of \(C(\{0\})\). Finite reverse depth is not
unreachability. \(C(\{0\})\) is co-reachability of the origin, not
\(R_W(0)\). Short repeating blocks of length \(\le 2\) do not hit
those \(t_n\).

No legal word from the origin to an exceptional \(t_n\) was found, and
no closed invariant excluding them was found. \(\lvert L_0\rvert\) is
not decided.

### Origin-live geometry: time-augmented quotients and slabs

Canonical energy is the residual formula, not a shifted index:

\[
E_i(s)=s_1 q_{i-2}+s_2 q_{i-1}+s_3 q_i
\]

(\(q_j=0\) for \(j<0\)). \(K_n\) is the unread-tail slab in that
energy. LSD alphabet applies only at remaining \(=1\), not remaining
\(\equiv 1\pmod m\).

Track A finite quotient \(G_m=(\mathbb Z/m\mathbb Z)\times(\mathbb Z/m\mathbb Z)^3\)
uses remaining \(r\mapsto r-1\pmod m\) and interior \(W\) at every
phase (over-approximation of LSD). Origin is placed at every phase.
Exceptional targets are \((n\bmod m,\,t_n\bmod m)\). A hit is not
reachability.

| \(m\) | \(\lvert G_m\rvert\) | reachable | \(\lvert T_{\mathrm{exc}}\rvert\) | separates? |
|---|---|---|---|---|
| 8 | 4096 | 4096 | 14 | no |
| 9 | 6561 | 729 | 6 | no |
| 12 | 20736 | 6912 | 14 | no |
| 18 | 104976 | 11664 | 11 | no |
| 24 | 331776 | 110592 | 14 | no |
| 27 | 531441 | 59049 | 18 | no |
| 36 | 1679616 | 186624 | 42 | no |
| 48 | 5308416 | 1769472 | 28 | no |

Affine forms \(\ell=\alpha r+\beta s_1+\gamma s_2+\delta s_3\pmod m\)
on \(G_m\) for \(m\in\{8,9,12,18\}\), discarding \(s_1\)-reparams and
pure time, found no separator. Exact-remaining windows with enough
prefix (max length 52) hit \(t_{12},t_{24},t_{36},t_{48}\) as residues;
a miss at remaining near the horizon is a prefix artifact, not an
obstruction.

Track B layers from a single start remaining \(N\) (live BFS, so
\(R_n=L_n\) on that path). The union census \(\lvert L_{\le N}\rvert\)
is not \(\lvert L_n\rvert\).

Start \(N=12\):

| \(n\) | \(\lvert L_n\rvert\) | \(\max\lvert s\rvert_\infty\) | \(s_n^{\max}\) | hub | \(t_n\) |
|---|---|---|---|---|---|
| 12 | 1 | 0 | \((0,0,0)\) | no | no |
| 10 | 9 | 6 | \((-6,-2,0)\) | yes | no |
| 0 | 165 | 27 | \((-27,-6,0)\) | yes | no |

Start \(N=16\):

| \(n\) | \(\lvert L_n\rvert\) | \(\max\lvert s\rvert_\infty\) | \(s_n^{\max}\) | candidate family |
|---|---|---|---|---|
| 16 | 1 | 0 | \((0,0,0)\) | origin |
| 1 | 492 | 36 | \((-36,0,0)\) | none |
| 0 | 379 | 37 | \((-3,-37,0)\) | none |

Legal-\(w\) without liveness, start \(N=4\): \(\lvert R_0\rvert=1192\),
\(\lvert L_0\rvert=10\). Reachability is much larger than the live
slice. Method A (forward \(T_w\)) and Method B (boxed reverse via
\(A^{-1}\)) agree on \(L_n\cap[-6,6]^3\) for start \(4\) (remaining
\(0..4\)) and start \(6\) remaining \(0\). Finite agreement is not a
proof. Reverse-box miss is not unreachability.

Largest-norm live states do not repeat a single ray: remaining-\(0\)
argmax is \((-27,-6,0)\) from start \(12\) and \((-3,-37,0)\) from
start \(16\). No integer ansatz
\(s_i(n)=\alpha q_n+\beta q_{n-1}+\gamma q_{n-2}+c\) fits the
argmax sequence. The tightest observed coordinate form at start \(16\)
is \(\lvert s_3\rvert\le 12\); that bound grows (\(\max\lvert s_3\rvert=14\)
at the \(N=18\) union census) and is not an invariant. Spectral
pairings with left eigenvectors of \(A\) are floats only and grow on
the live set. The hub is live at remaining \(\le N-2\); it is a
bounded point, not an unbounded family. No \(t_n\) appears in the
layers.

### Length-independent energy geometry

The unread-tail energy is the adjoint pairing
\(E_i(s)=u_i\cdot s\) with \(u_i=(q_{i-2},q_{i-1},q_i)\)
(\(q_j=0\) for \(j<0\)). The residual matrix satisfies
\(u_{i-1}A=u_i\) for \(i\ge 1\), hence the constructional identity

\[
E_{i-1}(T_w s)=E_i(s)-w\,q_{i-1}.
\]

This is Lean-verified as `Ostrowski.NP.energy_step` (ledger
`OST-np-energy-step`). Novelty is **KNOWN**: it is how
`next_state` was derived. Normalized \(E_i/q_i\) on live states
restates the slab \(K_n\), not an origin-live bound.

No three-term combination \(a E_i+b E_{i-1}+c E_{i-2}\) has an
\(i\)-independent coefficient vector in \(s\). Every nonzero integer
form \(as_1+bs_2+cs_3\) with coefficients in \(\{-3,\ldots,3\}\)
(342 forms) grows between start remaining \(16\) and \(20\). In
particular \(\lvert s_3\rvert\) goes \(12\to 19\). Coordinate maxima
go \((36,37,12)\to(57,49,19)\). Live union \(1351\to 2970\). The
empirical projective cloud occupies both signs in every coordinate;
it is not a proper coordinate cone. Method A/B still agree on the
boxed start-\(6\) remaining-\(0\) slice. None of this is
\(\lvert L_0\rvert=\infty\).

### Energy trajectory and live-set fork

The one-step law telescopes. After an MSD word
\(w_{N-1},\ldots,w_i\) from remaining \(N\),

\[
E_i(s)=E_N(s_{\mathrm{start}})-\sum_{j=i}^{N-1} w_j q_j.
\]

From the origin, \(E_N(0)=0\), so \(E_i\) is minus the consumed
prefix valuation. At remaining \(0\), \(E_0=s_3\) and acceptance is
\(\sum_j w_j q_j=0\). Lean `Ostrowski.NP.energy_telescope` (ledger
`OST-np-energy-telescope`) proves the cumulative identity by
induction on `energy_step`. Novelty is **KNOWN**.

Defects \(D_n^+=E_n-\mathrm{hi}(n)\) and \(D_n^-=\mathrm{lo}(n)-E_n\)
obey

\[
D_{n-1}^+(T_w s)=D_n^+(s)+(w^{\max}_{n-1}-w)\,q_{n-1},
\]

and the analogous \(D^-\) identity with \(w-w^{\min}\). Live states
stay at \(D^\pm\le 0\). This is *normalized* control of \(E_n\)
(\(\lvert E_n\rvert\le C q_n\)), not coordinate boundedness
\(\lvert s_i\rvert\le C\) and not a functional bound
\(\lvert\ell(s)\rvert\le C\). Closed forms
\(\mathrm{hi}(n)=2S_{n-1}-1\), \(\mathrm{lo}(n)=-4S_{n-1}+2\) plus
\(S_{n-1}\le 2q_{n-1}\) and \(q_n\ge 2q_{n-1}\) (\(n\ge 2\)) give
\(-4<\mathrm{lo}(n)/q_n\le\mathrm{hi}(n)/q_n<2\). Frozen table
\(n=1..6\): \((q_n,S_{n-1},\mathrm{lo},\mathrm{hi})\) equals
\((2,1,-2,1)\), \((5,3,-10,5)\), \((15,8,-30,15)\),
\((41,23,-90,45)\), \((112,64,-254,127)\), \((310,176,-702,351)\).

At remaining \(1\), \(E_1=s_2+2s_3\in[-2,1]\) on every live state
(start remaining \(20\): \(\lvert L_1\rvert=958\)). That is
length-dependent. It does not bound \(L_0\).

Largest-\(\lvert s_3\rvert\) states on the start-\(20\) slices
\(L_1,L_2,L_3\) are \((-3,-37,19)\), \((21,22,-15)\),
\((9,27,-12)\). Ratios \(s_1/s_3\), \(s_2/s_3\) sit \(O(1)\) off
the expanding eigen-direction of \(A\) (floats only;
\(\lambda\approx 2.757\), \(s_1/s_3\approx 1.088\),
\(s_2/s_3\approx 0.757\)). They do not stabilize to a ray.

Interior repeating blocks of length \(\le 3\), four repeats from
start remaining \(12\): the only energy-compatible orbits are the
zero words (bounded). Expanding blocks such as \(w\equiv-4\) leave
\(K_n\). Expanding without \(K_n\) is not a live family. No
unbounded \(T_B^k(0)\) in \(K\).

### Live control language

A prefix is *co-live* at horizon \(N\) only if it stays in \(K\) and
the endpoint has a legal path to remaining \(0\). The
\((s,\mathrm{remaining})\) graph is a DAG. Live at remaining \(n\)
is not co-live in general; at start remaining \(8,12,16,20\) the
origin-reachable live nodes happen to all be co-live (no live
dead-ends). That is a finite-horizon observation.

\(\lvert\mathcal L_k(N)\rvert\) at \(N=12\):
\(1,4,9,23,59,144,359,912,2271,5564,13197,22411,22411\) for
\(k=0,\ldots,12\). At \(N=20\), \(\lvert\mathcal L_6\rvert=361\) and
there are \(38625503\) accepting words of length \(20\), with
\(729\) distinct remaining-\(0\) states. Growing \(\lvert\mathcal L_k(N)\rvert\)
is not \(\lvert L_0\rvert=\infty\).

Every co-live node has an extension set that is a consecutive window
in \(W=\{-4,\ldots,2\}\), of length at most \(4\). There are exactly
\(22\) such windows (singleton \((-3)\) is missing), stable from
\(N=8\) to \(N=20\). This is not a finite residual automaton:
\(\max\lVert s\rVert_\infty\) on co-live slices still grows as
remaining drops (\(0\to 57\) at \(N=20\)).

All \(49\) interior length-\(2\) factors and all \(343\) length-\(3\)
factors occur on co-live paths already at \(N=12\). No forbidden
short block.

Length \(\le 6\) co-live prefixes of \(N=20\) are all co-live at
\(N=16\) (\(600\) words). Two length-\(6\) words fail at \(N=12\).
Do not call the first class \(\lvert H(u)\rvert=\infty\).

Occurring prefixes of length \(4,5,6\) (\(564\) words), three repeats
from remaining \(18\): \(14\) stay in \(K\) and all return to the
origin (bounded). Expanding occurring blocks such as
\((2,-4,-2,-4)\) leave \(K\). No co-live expanding family.

Left Perron pairing on co-live slices grows as remaining drops
(floats only). Not a cancellation theorem.

### Live Ext from energy_step

Unread-tail values \(V_n\) fill \([\mathrm{lo}(n),\mathrm{hi}(n)]\cap\mathbb Z\)
for \(n\le 12\) (DP, not \(7^n\) brute). So \(F_n(s)=E_n(s)-V_n\) is
an interval translate, and \(0\in F_n(s)\) iff \(s\in K_n\) (live,
not co-live).

One-step live Ext is exact: \(w\in\operatorname{Ext}_{\mathrm{live}}(s,n)\)
iff \(w\) is legal at remaining \(n\) and
\(\mathrm{lo}(n-1)\le E_n(s)-w q_{n-1}\le\mathrm{hi}(n-1)\). Lean
`energy_control_interval` proves that any such \(w\)-set for a fixed
\([\mathrm{lo},\mathrm{hi}]\) is consecutive (\(q>0\)). Intersection
with a consecutive alphabet stays consecutive. Novelty **KNOWN**.

The real \(w\)-interval has length
\((\mathrm{hi}(n-1)-\mathrm{lo}(n-1))/q_{n-1}=(6S_{n-2}-3)/q_{n-1}\)
for \(n\ge 2\). For remaining \(1..24\) this length is \(<4\)
(maximum \(\approx 3.414\)). Crude \(S_k\le 2q_k\) only gives
width \(<6\); the tighter bound is computational through \(24\), not
an induction in Lean. Width \(<4\) is not a residual bound.

The \(22\) origin-reachable windows are every consecutive subinterval
of \(W\) of size \(\le 4\) except singleton \((-3,)\), plus empty.
Singleton \((-3,)\) was not found on origin-reachable co-live nodes
nor on boxed \(K_4\) (\(\mathrm{box}=6\)). On that box, co-live Ext
equalled live Ext (no holes).

The functional \(u=s_2+2s_3\) is \(E_1\). It is bounded on \(K_1\)
only. On origin-reachable windows at start remaining \(12\), both
\(\lvert u\rvert\) and \(\lvert s_3\rvert\) grow. Endpoints of the
\(w\)-interval restate \(E_n/q_{n-1}\), i.e. the slab \(K_n\).

### Complementary coordinates in \(\ker(E_n)\)

For remaining \(n\ge 2\), the matrix with rows \(u_n,u_{n-1},u_{n-2}\)
has determinant \(3^{n-2}\) (Lean `adjointDet_eq`). Neighboring
energies invert \(s\) over \(\mathbb Q\):

\[
(s_1,s_2,s_3)
=
M_n^{-1}(E_n,E_{n-1},E_{n-2}).
\]

Homogeneous motion is energy-neutral in the sliding index (Lean
`energy_homogeneous`, \(w=0\) of `energy_step`):
\(E_n(A^k s)=E_{n+k}(s)\). Expanding \(A^k\) on \(\ker(u_n)\) does not
by itself produce an energy defect; only the control particular can.

The neighboring-energy frame \(M_n^{-1}(0,E_{n-1},E_{n-2})\) is
ill-conditioned. The geometric kernel component is the Euclidean
projection \(s_{\mathrm{orth}}=s-E_n u_n/\lVert u_n\rVert^2\). On
origin-reachable live slices, \(\lvert s_{\mathrm{orth}}\rvert\)
tracks \(\lVert s\rVert_\infty\): live growth sits in \(\ker(u_n)\).
At remaining \(4\), start remaining \(12\to 16\):
\(\lvert L_4\rvert=166\to 427\), \(\lVert s\rVert_\infty=15\to 24\),
max \(\lvert s_{\mathrm{orth}}\rvert=28850/1931\to 46414/1931\), and
max \(\lVert s\rVert_\infty\) within one energy level \(15\to 24\).
At remaining \(2\) from start \(16\), \(584\) live states occupy
\(16\) energy values with \(41\) states in the busiest level.

Short interior words of length \(\le 4\) from the large-kernel seed
\((6,2,-3)\) at remaining \(8\) (start \(12\)) include local
expanders and five \(2\)-repeats that stay live at that horizon.
None is a symbolic family for all remaining.

### Live control of the unstable convolution

From the origin, `T_w(s)=A s − e₃ w` unfolds by variation of constants
(Lean `origin_particular`, novelty **KNOWN**):

\[
s_k = -\sum_{j<k} A^{k-1-j} e_3 w_j.
\]

MSD order matches `apply_word`: the first letter is the highest
remaining place. Energy of this particular is already
`energy_telescope`. Companion embedding
\(z=s_1+s_2\lambda+s_3\lambda^2\) in
\(\mathbb Z[\lambda]/(\lambda^3-2\lambda^2-\lambda-3)\) satisfies
\(z(T_w s)=\lambda z-\lambda^2 w\). All three embeddings have
\(\lvert\lambda_j\rvert>1\) (non-Pisot). Three expanding modes versus
one energy slab is a structural imbalance, not a cancellation
theorem. Normalized \(\lvert\lambda\rvert^{-k}\lvert z\rvert\) bounded
is tautological for \(\lvert\lambda\rvert>1\) and is not residual
boundedness.

On origin-reachable remaining \(0\) (start remaining \(12\) and
\(16\)): \(\lvert L_0\rvert=165\to 379\),
\(\lVert s\rVert_\infty=27\to 37\), max Perron \(\lvert z\rvert\)
\(\approx 79.15\to 114.02\), max complex \(\lvert z\rvert\)
\(\approx 25.83\to 38.61\). Unnormalized \(\lvert z\rvert\) grows, so
uniform \(\lvert z_j\rvert\le C\) is refuted as an \(L_0\) bound.
Normalized Perron \(\lvert z\rvert/\lambda^N\) shrinks; the mildly
expanding complex pair has growing normalized modulus at these
horizons. Remaining \(0\) has \(s_3=0\). Convolution matched recovered
maximizer prefixes. Maximizer words share a \((2,-4,-4,\ldots)\)
prefix and are not constant:

- \(N=12\), \((-27,-6,0)\):
  \((2,-4,-4,0,0,-4,1,1,-4,1,1,-2)\)
- \(N=12\), \((-27,-15,0)\):
  \((2,-4,-4,1,-4,-1,2,1,-3,2,2,-2)\)
- \(N=16\), \((-3,-37,0)\):
  \((2,-4,-4,0,0,-4,2,-2,-4,2,2,-4,0,2,-1,-2)\)
- \(N=16\), \((-12,-37,0)\):
  \((2,-4,-4,0,0,-4,1,1,-4,0,2,-2,-2,2,-3,-1)\)

No symbolic family at this depth. Finite-horizon growth is not
\(\lvert L_0\rvert=\infty\).

### Impulse equals place value

The origin impulse is the place-value vector (Lean `iterateA_e3`,
novelty **KNOWN**):

\[
h_r=A^r e_3=(3 q_{r-1},\; 3 q_{r-2}+q_{r-1},\; q_r),
\]

with \(q_j=0\) for \(j<0\). Checks: \(h_0=(0,0,1)\), \(h_1=(3,1,2)\),
\(h_2=(6,5,5)\). Both convolution orientations match `apply_word`:

\[
s_k=-\sum_{j<k}A^{k-1-j}e_3 w_j=-\sum_{r<k}h_r w_{k-1-r}.
\]

Coordinate form: \(s_k^{(3)}=-\sum q_r w_{k-1-r}\) and
\(s_k^{(1)}=-3\sum q_{r-1}w_{k-1-r}\). Remaining \(0\) is
\(s_N^{(3)}=0\), already `-consumed_sum`. Each coordinate of \(h_r\)
obeys the place-value recurrence. Along a forced trajectory the same
order-3 law holds with local forcing

\[
F=(-3w_{k+1},\;-3w_k-w_{k+1},\;-w_{k+2}).
\]

That is the matrix-free description of origin reachability. It does
not constrain \(\lvert L_0\rvert\). Large \(\lvert s\rvert\) does not
force unique Ext: on the \(N=12\) maximizer word, remaining \(5\),
state \((12,-2,-1)\) has Ext \((-1,0,1)\).

### Recurrence as a zero-sum block

The unique length-4 consecutive identity is a multiple of
\((3,1,2,-1)\). Coefficients \(3\notin W\). The \(W\)-valued sign
LSD \((-3,-1,-2,1)\) is MSD

\[
B_\ast=(1,-2,-1,-3),\qquad
\mathrm{val}(B_\ast)=q_{n+3}-2q_{n+2}-q_{n+1}-3q_n=0
\]

(Lean `recurrence_word_zero`, novelty **KNOWN**). Last letter
\(-3\) is interior-legal and not in the LSD alphabet
\(\{-2,\ldots,1\}\), so a complete remaining-\(4\) word is
alphabet-illegal. As an interior block, \(B_\ast\) is prefix-legal
and live from remaining \(8\), and \(T_{B_\ast}(0)=(0,0,0)\): a
reset. Iteration \(B_\ast^k\) stays at the origin.

Length \(5\)–\(6\) shift-combinations with digits in \(W\) yield
\(11\) words, all algebraic zero-sum, all resets. Four of them end
in \(0\) and are fully live as complete words (LSD-legal resets).
No non-reset live expander. Algebraic zero-sum is not fully live. A
reset is not \(\lvert L_0\rvert=\infty\).

### Zero-value is not a reset

From the origin, \(c_B=T_B(0)\) and Lean `particular_s3` give

\[
(c_B)_3=E_0(c_B)=-\mathrm{val}(B).
\]

So \(\mathrm{val}(B)=0\) iff \(c_B\in F=\{s_3=0\}\). Coordinates
from `iterateA_e3` do not force \(c_1=c_2=0\) when \(c_3=0\).

Identically zero-for-all-alignments remains the recurrence lattice
(all resets). Zero at one alignment is the live fiber on \(F\).
Existing remaining-\(0\) slices already show this:
\(\lvert L_0(12)\rvert=165\subset F\), \(\max\lVert s\rVert_\infty=27\).
That is not a new census.

Complete words (last letter in \(W_{\mathrm{LSD}}\)) through length
\(4\):

| \(k\) | \(\lvert Z_k\rvert\) | resets | non-resets | live non-resets | \(\max\lvert c_B\rvert_\infty\) |
|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 0 | 0 |
| 2 | 2 | 1 | 1 | 1 | 3 |
| 3 | 6 | 1 | 5 | 5 | 6 |
| 4 | 14 | 1 | 13 | 13 | 7 |

Shortest complete non-reset: \(k^\ast=2\),

\[
B=(1,-2),\qquad \mathrm{val}=2-2=0,\qquad c_B=(-3,-1,0)\ne 0,
\]

algebraic zero-sum / LSD-legal / fully live. This is the known hub
on the bounded \(F\to F\) ray \(\alpha\in\{-2,-1,0,1\}\). Iteration
of this 2-step stays on that ray. \(B_\ast\) remains a reset.
A non-reset complete word is an accepted point of \(F\), not
\(\lvert L_0\rvert=\infty\).

### Complete zero-value is not a monoid

MSD `consumedSum` splits at two starts (Lean `consumedSum_append`):

\[
\mathrm{consumedSum}(n+|U|+|V|)(UV)
=\mathrm{consumedSum}(n+|U|+|V|)U
+\mathrm{consumedSum}(n+|V|)V.
\]

This is not \(\mathrm{val}(U)+C_{\lvert U\rvert,\lvert V\rvert}\mathrm{val}(V)\).
Complete-word concatenation (Lean `val_concat_energy`):

\[
\mathrm{val}(UV)=\mathrm{val}(V)-E_{\lvert V\rvert}(c_U),
\]

so \(\mathrm{val}(UV)=0\) iff \(E_{\lvert V\rvert}(c_U)=\mathrm{val}(V)\).
Both complete zeros do not imply the concat is zero. Witness
\(U=V=(1,-2)\):

\[
\mathrm{val}(UV)=5,\qquad c_{UV}=(-6,-2,-5)\notin F.
\]

A reset followed by the hub stays zero-value
(\(E_k(0)=0\)). Identically-zero-for-all-alignments (recurrence)
remains the class that concatenates to zero — already all resets.

Live complete remaining-\(0\) of length \(N\) is \(L_0(N)\), not a
new fiber. The existing maximizer \((-27,-6,0)\) at \(N=12\) lies on
\(F\) and off the two-step legal ray \((3k,k,0)\) with
\(k\in\{-2,-1,0,1\}\). Finite \(\lvert L_0(N)\rvert\) is not
\(\lvert L_0\rvert=\infty\). A concatenation semigroup of complete
zero-value words is the wrong object.

### State-dependent block value is \(-s_3\)

For any incoming residual \(s\), Lean `fold_s3` is
`energy_telescope` at remaining \(0\):

\[
(T_B(s))_3=E_{\lvert B\rvert}(s)-\mathrm{val}(B).
\]

So \(\mathrm{Val}_s(B):=\mathrm{val}(B)-E_{\lvert B\rvert}(s)=-(T_B(s))_3\),
and \(T_B(s)\in F\) iff \(E_k(s)=\mathrm{val}(B)\). At the origin this
is `particular_s3`. After a prefix \(U\), \(\mathrm{Val}_{c_U}(V)=\mathrm{val}(UV)\)
is `val_concat_energy`. The affine action \(T_B(s)=A^k s+c_B\) is
already `foldSteps_affine`.

The hub word from the origin lands on the bounded ray. Repeating
that same word from the hub leaves \(F\) (the monoid witness).
Interior-legal two-step returns from the hub stay on
\((3k,k,0)\) with \(k\in\{0,1,2\}\), still bounded, not a family.
Live complete remaining-\(0\) of length \(N\) remains \(L_0(N)\).

### Spectral cancellation is already parked

The companion embedding \(z=(s_1,s_2,s_3)\) satisfies
\(z(T_w s)=\lambda z(s)-\lambda^2 w\). That is the residual `step`,
not a new left eigenfunctional. Uniform unnormalized
\(\lvert z_j\rvert\le C\) on origin-live remaining \(0\) is
**REFUTED** (ledger `OST-np-unnormalized-mode-bound`): from start
remaining \(12\to 16\), \(\lvert L_0\rvert=165\to 379\),
\(\lVert s\rVert_\infty=27\to 37\), Perron \(\lvert z\rvert\approx 79\to 114\).
Normalized \(\lvert\lambda\rvert^{-k}\lvert z\rvert\) bounded is not
residual boundedness. The \(N=12\) maximizer
\((2,-4,-4,0,0,-4,1,1,-4,1,1,-2)\) is not a symbolic family.
Large \(\lvert s\rvert\) does not force unique Ext. A new IFS
attractor, \(N>16\) remaining-0 BFS, or algebraic-number framework
does not decide \(\lvert L_0\rvert\).

### Arbitrarily long accepted words need not have infinitely many terminals

The MSD words \(U_k=(B_\ast)^k\cdot(1,-2)\) have length \(4k+2\).
Lean `recurrence_word_reset` / `reset_pow_origin` /
`reset_pow_then_hub` (ledger `OST-np-reset-pow-then-hub`, novelty
**KNOWN**) give the algebraic image: each \(B_\ast\) is a reset, so
\(T_{U_k}(0)\) is the hub. Python `fully_live` holds for
\(k=0,\ldots,4\); last letter \(-2\in W_{\mathrm{LSD}}\); interior
\(-3\) occurs at remaining \(\ge 3\). The König branch
\((B_\ast)^\infty\) stays at the origin. This **REFUTES** (ledger
`OST-np-long-words-infinite-L0`) the implication that arbitrarily
long accepted words force infinitely many distinct terminals. It
does not prove \(\lvert L_0\rvert<\infty\): the full remaining-0
census still grows \(\lvert L_0(N)\rvert=165\to 379\) from start
remaining \(12\to 16\). König compactness is not an \(L_0\)
theorem. No prefix-tree engine, pumping search, or \(N>16\) BFS.

### Observed remaining-0 terminals span \(3\mathbb Z\times\mathbb Z\)

The integer reverse of \(T_w\) is already Lean `unique_predecessor` /
`predecessor_on_F` (ledger `OST-np-unique-predecessor`, novelty
**KNOWN**) and Python `integer_preimage`. On \(F\) this is
\(s=(b-a/3,\,w-2a/3,\,a/3)\). That is inversion of `step`, not a
new reverse-graph calculus.

At start remaining \(12\), origin-live remaining-0 states span the
full lattice \(\{3\mid a\}\subset F\): \(\gcd a=3\), \(\gcd b=1\),
not all \(9\mid a\), and the maximizer \((-27,-6,0)\) is off the
two-step ray. Extra congruence beyond \(3\mid a\) is **REFUTED**
(ledger `OST-np-extra-terminal-congruence`). From \(12\to 16\),
\(\lvert L_0\rvert=165\to 379\) with nonempty difference; every
small form \(\alpha a+\beta b\) grows. This is not
\(\lvert L_0\rvert=\infty\) and not a translational pump. No
seven-module terminal-image stack.

### Origin resets do not create new terminals

Lean `reset_prefix` (ledger `OST-np-reset-prefix`, novelty **KNOWN**):
if \(T_R(0)=0\) then \(T_{RU}(0)=T_U(0)\). This is `particular_concat`
at \(c_R=0\). It is not \(T_R(s)=s\) for arbitrary \(s\). Hub
\(\ell_{\min}=2\) via \((1,-2)\); \((B_\ast)^k\) padding is not first
appearance. Every terminal has a shortest realization, so the
primitive image \(P\) equals \(L_0\); that is not a new set.
Cumulative \(C(N)\) still grows through remaining \(8\). Reset-padded
length is not primitive terminal growth. No primitive-DP engine or
pump search.

### Suffix futures are classified by energy

Lean `same_energy_same_OnF` (ledger `OST-np-same-energy-same-OnF`,
novelty **KNOWN**): if \(E_{\lvert v\rvert}(s)=E_{\lvert v\rvert}(t)\)
then \(T_v(s)\) lands on \(F\) iff \(T_v(t)\) does. This is
`fold_on_F_iff`. The suffix energy path is `energy_step`, so
length-\(n\) acceptance injects into the finite slab \(K_n\).
Claims A \(\lvert L_0\rvert=\infty\), B nonregular 3-input relation,
and C this residual construction, are distinct. Finite live closure
implies a finite future quotient (pigeonhole); the converse is
false at fixed remaining (energy kernel). Unbounded-length Myhill–Nerode
index tracks live-union cardinality, not \(\lvert L_0\rvert\).
Python: equal \(E_1\) at the origin and \((0,-2,1)\) share `live_ext`
and `OnF` after LSD \(0\); that letter separates origin from hub.
Co-live states at remaining \(4\) in `dag_at(8)` exceed the number
of Ext windows. No Hankel matrix, digit-triple alphabet, or
Myhill–Nerode engine.

## Open questions

Is \(\lvert L_0\rvert=\infty\)? Origin reachability is the Ostrowski
convolution of \(w\) against \(q\). Complete zero-value is not a
monoid; identically-zero recurrence combos are resets; live complete
zeros at remaining \(0\) are \(L_0(N)\). The maximizer prefix
\(P_m=(2)\cdot(-4)^m\) plus a uniformly bounded tail is **REFUTED**
as that family (dies for \(m\ge 3\)). A contracting functional on
\(\ker(u_n)\cap R(0)\), or a different explicit unbounded
live-from-0 family that is not a recurrence reset and not the
bounded \(F\to F\) ray, is missing. Do not open order 4, Walnut,
or a second example.

## Decision

`PARK` \(\lvert L_0\rvert\). `PROMOTE` the KNOWN identity
`same_energy_same_OnF` only. `CLOSE` Myhill–Nerode / Hankel /
triangular families / digit-triple alphabets as new mathematics
(reparameterization of \(E_n\) at fixed remaining; of live union
at unbounded length). Finite future quotient does not imply
finite \(\lvert L_0\rvert\). The 3-input relation remains
literature **KNOWN negative**. Do not `CLOSE` the Ostrowski
problem. No order 4, CLI, Walnut, or automata stack. Stop. Next
question (not taken up): a contracting functional on
\(\ker(u_n)\). The prefix \(P_m=(2)\cdot(-4)^m\) plus a uniformly
bounded tail is **REFUTED** as a family.

Engineering R1–R2 (2026-08-24) extracted exact affine, block,
phase, and trajectory primitives into `research_engine`. Ostrowski
`transition_affine` / `apply_word` / `matrix_power` / `affine_block`
are compatibility wrappers. Engineering R3 extracted forward /
reverse / live-slice / suffix search with explicit `BOUNDED` vs
`EXACT` scope. `OstrowskiSpec` is a thin adapter; energy formulas
stay Ostrowski-specific. Engineering R4 extracted constant-coefficient
recurrences, integer-matrix inverses, and linear forms; energy
\(E_i=s\cdot(q_{i-2},q_{i-1},q_i)\) and the recurrence word \(B^*\)
stay Ostrowski-specific. Engineering R5 extracted typed
reconnaissance / modular / affine-region / reverse / functional /
block attacks with explicit `ClaimKind` and `SearchScope`.
`s_1\equiv 0\pmod 3` is an exact map law, not live infinitude; a
sample max \(\lvert\ell\rvert\) is never `SUPPORTED`. Engineering R6
added an in-memory hypothesis ledger, negative-knowledge schemas, and
a deterministic planner. `LIVE_SLICE` / `TERMINAL` / `CO_REACHABLE`
evidence cannot `PROMOTE` the parked exact `LIVE` hypothesis
\(\lvert L_0\rvert=\infty\). The named theorem ledger is not migrated.
Engineering R7 made `OstrowskiSpec` the adapter facade (`q`, energy,
digit legality, affine, recurrence, `attack_context`) without moving
the package to `problems/ostrowski_np`. Energy stays Ostrowski-side.
Engineering R8 added five synthetic benchmarks (finite closure,
infinite translation, reset-loop words, modular tripling, expanding
escape). The planner default horizon is 16 so sticky-phase systems
cannot hang; unbounded words do not imply unbounded terminals.
Engineering R9 emits comment/YAML theorem targets from exact
`SUPPORTED` certificates and links the NP modular and hub certificates
to existing Lean `step_fst_dvd_three` / `hub_nonreset`. It does not
generate proofs, write `formal/` files, auto-add ledger rows, or
export the parked `|L_0|` hypothesis.
Engineering R10 adds `btlab research analyze|attack|reproduce|report`
for Ostrowski and the A–E toys. The CLI prints planner statuses and
exportable targets. It does not decide `|L_0|`, write Lean, or auto-prove.
Engineering R11 adds a spectral plug-in: an integer cubic Pisot/Perron
certificate for the companion of `A`. Float root labels are not status.
Expansion is not live infinitude. These extractions are infrastructure
`PROMOTE`. They do not change the mathematical decision above.
The Ostrowski prefix-family search (2026-08-24) tests
\(P_m=(2)\cdot(-4)^m\) plus a uniformly bounded tail. Live remaining-0
completions exist only for \(m=0,1,2\) at tail length \(\le 6\); the
prefix dies for \(m\ge 3\). No closed-form tail. The report is
`OBSERVATION` / `BOUNDED` / `LIVE_SLICE` and does not promote
`|L_0|`. A generic `SymbolicControlAttack` stays deferred.
Auto-prove is not taken up.

## Publication assessment

Status: `STRUCTURAL`. The 55-set remains an exact theorem for one
Pisot \(\Gamma\). The NP accepting boundary is unbounded; the
origin-reachable live set is not proved infinite. Not
`PAPER_CANDIDATE`.
