# Paper B prior art, and what each object is called elsewhere

**Purpose:** internal publication record. This page is not a theorem ledger
and does not change any evidence tag. It exists because this laboratory has
twice named an object that already had a name, and once claimed an object was
missing here when it was present under our own vocabulary.

## The translation table

Every row was checked first-hand. The toolkit column refers to Kazunobu
Hikawa, *Collatz Parity Vector Toolkit* v1.0, 4 July 2026,
[github.com/hikawa94/Collatz-Parity-Vector-Toolkit](https://github.com/hikawa94/Collatz-Parity-Vector-Toolkit),
deposited at [doi:10.5281/zenodo.21186540](https://doi.org/10.5281/zenodo.21186540);
its code was run and its published sample output compared against ours. It is
a declared supplement to his January and July papers, which are unread here;
see the open risk below.

| this laboratory | the literature | Hikawa's toolkit |
|---|---|---|
| accelerated map `T` | shortcut map; Terras's map | the map throughout |
| parity word `w` | parity vector (Terras 1976) | PV |
| odd count `o` of a word | — | Hamming weight `d` |
| survivor count `N_d` | **A076227** | `D_Unconverged` |
| minimal certificate count `M_d = 2 N_(d-1) - N_d` | **A100982**; Winkler's `a_3(r)`, a rational Catalan number | `B_Converged` |
| minimal certificate length | **dropping time** (A126241; A020914, K. Spage comment, 22 Oct 2009); **glide** (Roosendaal) | `Glide` |
| `word_counts(d)[o]`, survivors by odd count | — | Counting by Hamming Weight, `W[d][u]` |
| free length / empty window | the gaps of the Beatty sequence `ceil(d log2 3)` | his zero rows |
| free lengths never adjacent | the defining property of **A022921** | — |
| free lengths | **A054414** (the Beatty complement) | his zero rows |
| nonzero `M_d` in order | **A186009** ("A100982 with 1 prepended") | `W(d)` totals |
| boundary mass `M_d / 2^d` | the frequency comment on **A186008**, T. D. Noe, Feb 2011 | — |
| survivor recursion `stepFlat` | — | `W[k][d] = W[k-1][d] + W[k-1][d-1]` |

One row carries three outside names and a fourth that only we use: the
minimal certificate length is the dropping time in the Collatz literature, the
glide among people who compute them, and `Glide` in his toolkit.

**Conventions differ and must be checked on data, not on the word.** 27 first
falls below itself after 59 steps of the accelerated map and 96 of the standard
`3x+1`. His toolkit reports 59, so his glide is our convention; Roosendaal's is
not automatically so. A shared name over a different map is a false
identification.

## What is priority-destroying

- **Terras (1976), for the mechanism; Lagarias (1985), for the exponent.**
  Proposition J applied to Collatz reproduces the classical theorem because of
  Terras's parity bijection on `Z/2^d`, which gives `E_d(N) = O(1)` and hence
  density one, jointly with Everett 1977. But the `0.050044` in
  `N^(1 - 0.050044)` is **not** Terras's: it enters only through
  `N_d/2^d <= theta^d`, and that bound is Lagarias 1985, Theorem D, with
  `eta = 1 - H((log_2 3)^(-1)) = 0.0500444728...`. "Known since 1976" holds for
  the density and not for the rate, which is known since 1985. Recorded at
  `J-proposition-j-on-collatz-is-terras`, corrected on branch
  `claude/goofy-kare-1a92fd`. The caveat travels with it: Terras 1976 itself
  could not be read here (matwbn is behind an anti-bot gate), so this rests on
  Lagarias's annotation of Terras rather than on Terras's text.
- **The OEIS sequences.** `N_d` is A076227 and `M_d` is A100982; neither is
  ours. That the gaps of A020914 are 1 or 2 is the *defining property* of
  A022921, elementary and in OEIS since 2009 — so the level-zero shadow of
  `J-free-lengths-are-never-adjacent` is not new, whatever is true at level
  `Lambda`.
- **Winkler (September 2026),** *Admissible qx+1 Sequences, Semiconvergents,
  and Rational Catalan Numbers*, and his A100982 comment of 15 September 2026:
  the sandwich `(1/n) C(m_n - 1, n - 1) <= a(n) <= (1/n) C(m_n, n - 1)` with
  equality exactly at the one-sided convergents and semiconvergents. Checked
  against our counts at `J-winkler-sandwich-holds-on-the-laboratory-counts`.
- **Hikawa's toolkit (4 July 2026)** computes four of this cluster's objects:
  the survivor recursion, `N_d`, `M_d` with its zeros at the free lengths, and
  the odd-count refinement `word_counts`. All four verified by running his code
  and comparing, not by reading.

## What the toolkit does not settle

The toolkit **computes**; that is not the same as the papers **proving**. A
column of zeros exhibits zeros and asserts nothing; the empty-window theorem
says a free length forces the alive set to be a full cylinder and hence that
every additive functional of it factorises. Both toolkit manuals were fetched
and read: seven pages each, pure installation instructions, no mathematics —
their only two occurrences of "Conjecture" are the name of the problem.

So the **objects** have prior art from 4 July 2026 and the **theorems** are not
settled by it. No novelty disclaimer should be widened past that line on the
strength of this page.

## The open risk, stated plainly

There are **three** ResearchGate papers, not two, and no full text of any of
them has been read here. But "unread" was too strong when first written on
this page, and the correction matters more than the overstatement: a peer
session on branch `claude/goofy-kare-1a92fd` read the **author-written version
notes** on the ResearchGate records in the browser pane on 19 September, while
that route was still open, and read **Nakanishi's Jxiv paper in full**. What
follows below is largely settled because of that, not because of anything on
main.

The metadata, though, is now first-hand — DataCite and OpenAlex both answer
where ResearchGate does not, checked 20 September 2026:

| DOI | title | date | authors |
|---|---|---|---|
| [10.13140/RG.2.2.12065.06240](https://doi.org/10.13140/RG.2.2.12065.06240) | Parity Vector Analysis in the Study of the Collatz Conjecture | **2026-01** | Hikawa and **Kazuo Nakanishi** |
| [10.13140/RG.2.2.29894.84804](https://doi.org/10.13140/RG.2.2.29894.84804) | Finite-Dimensional Combinatorial and Arithmetic Structures of Parity Vectors for the Accelerated Collatz Map | 2026-07-04 | Hikawa |
| [10.13140/RG.2.2.24486.28480](https://doi.org/10.13140/RG.2.2.24486.28480) | Finite Parity-Vector Structures in the Accelerated Collatz Map | 2026-09-12 | Hikawa |

Three corrections follow. **The line starts in January 2026, not July** — the
toolkit's README names only the first two papers, so reading the README alone
put the clock six months late. **The January paper has a co-author, Kazuo
Nakanishi**, who appeared nowhere in our records and must not be dropped from a
citation. And **the September paper is a third work**, invisible from the
toolkit entirely; the title we had recorded for it was one agent's secondhand
reading, and this is the first confirmation that the title and the DOI belong
together. The toolkit is a declared supplement to the January and July papers
(Zenodo `relatedIdentifiers`), not to the September one.

**The one route that worked has closed.** On 19 September the in-app browser
pane could load a ResearchGate publication page and return the abstract and
the author's version note, and that is how several of the secondhand claims
about Theorem 7.3 and Conjecture 9.1 entered the record. On 20 September the
same request returns a network security check instead. No attempt was made to
pass it and none should be: completing a bot check is off-limits whatever the
PDF is worth. **This is now a thing to hand to a human.** Anyone with an
ordinary browser can open these three pages in seconds, and doing so would
settle the open question below outright.

## The limit theory: how much of it is prior

This page first said the question was open. It is largely not, and the answer
sits on `claude/goofy-kare-1a92fd` rather than on main. From the July paper's
author-written version note, read while the browser route was open:

- **Section 6, PROVED:** `log_2 W(d) = gamma d + O(log d)` with
  `gamma = lambda H(1/lambda) ~ 1.5056`, `lambda = log_2 3`, `H` the binary
  entropy — a cycle-lemma argument plus standard entropy estimates, stated in
  the **weight basis** with a length-basis analogue. The decay rate
  `c = lambda(1 - H(1/lambda)) ~ 0.0793` is the length-basis `eta` of Lagarias
  1985 divided by `beta`.
- **Section 7, Conjecture 7.1:** `W(d) = Theta(d^(-3/2) 2^(gamma d))`,
  motivated numerically over `100 <= d <= 10000` by the residual agreeing with
  the ballot correction `-(3/2) log_2 d` to within 0.3 bits. **This is a prior
  statement of the `d^(-3/2)`.**

So the exponent is not ours to claim. What has **no** counterpart there is
everything that makes the laboratory's version a limit theorem rather than a
shape: it is a `Theta` and not an asymptotic, it is conjectural and numerical
rather than proved, and it carries **no oscillation, no almost-periodicity and
no amplitude constant** — the 0.3-bit tolerance is wide enough to hide a
bounded oscillating prefactor without seeing one. `psi`, the meander
prefactor, the phase-indexed quasi-stationary profile, `R_d`,
`chernoff_rate_at` and the rational barriers have no counterpart in any of it.
The September paper carries the same Section 6 result and says outright that
the sequence values are not claimed as new.

Nakanishi's separate Jxiv paper — *A Structural Study of Parity Vectors in the
Collatz Conjecture*, [doi:10.51094/jxiv.3096](https://doi.org/10.51094/jxiv.3096),
v2 of 7 September 2026 — **was read in full** (Jxiv is not blocked). It also
classifies by number of 1s rather than by length, proves for each finite `d`
that the constructed sequences contain no unconverged sub-parity vector of
length `G_d` with exactly `d` ones (Theorem 6), explicitly does not establish
the conjecture, and contains **no asymptotic anywhere**.

One more attribution worth carrying: Hikawa and Nakanishi are the authors of
the **A076227 b-file** against which this laboratory checked `N_d` on all 3509
terms.

**What is still genuinely unread:** the bodies of all three ResearchGate
papers. Theorem 7.3, Equation 48 and Table 4 remain secondhand, and the
version notes are not the papers.

## How the two naming errors happened

Recorded because the shapes are opposite and both are cheap to repeat.

1. **Searching outward in our own words.** Nobody had proved the lab's
   level-`Lambda` statements, so "has anyone proved this" correctly returned
   nothing and the answer felt like novelty. But "what is this called" is a
   different search, and it was never run. The dropping-time identification was
   a two-line OEIS *comment*, not an entry title.
2. **Searching inward in someone else's words.** On 20 September, comparing the
   toolkit against the repository, the grep used `hamming`, `by_weight`,
   `num_ones`, `popcount` — every one of them his vocabulary — found nothing,
   and a commit claimed no odd-count-refined survivor count existed here. It
   does: `paper_b_prefix_count.word_counts(d)` returns exactly it, and it is
   the base of the entire boundary-fraction cluster. This laboratory never
   writes "Hamming weight"; it writes the odd count.

The rule that covers both: before claiming novelty or absence, write down what
the *other* side would call the object, and search in those words as well as
your own.
