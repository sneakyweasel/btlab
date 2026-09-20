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
its code was run and its published sample output compared against ours.

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

- **Terras (1976).** Proposition J applied to Collatz *is* Terras: the parity
  map is a bijection on `Z/2^d`, so `E_d(N) = O(1)` and the non-descending
  starts are `N^(1 - 0.050044)`. This is the quantitative density-one stopping
  time theorem and it is fifty years old. Recorded at
  `J-proposition-j-on-collatz-is-terras`.
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

Hikawa's two papers — *Parity Vector Analysis in the Study of the Collatz
Conjecture* and *Finite-Dimensional Combinatorial and Arithmetic Structures of
Parity Vectors for the Accelerated Collatz Map* — are **unread here**. They are
on ResearchGate, which returns 403 to this environment; the Zenodo deposit is
the software only. Nobody in this laboratory has seen Theorem 7.3, Equation 48,
Conjecture 9.1 or Table 4.

Everything below the toolkit line is therefore provisional. In particular this
page does **not** assert that the limit theory is absent from his work. What
can be said is only that it is absent from the toolkit: the quasi-stationary
theory built on `word_counts` — the boundary fraction `R_d`, the phase-indexed
profile, its linear-times-geometric closed form, `chernoff_rate_at`, the
rational barriers, `psi` and the meander prefactor — has no counterpart in any
file of HIS repository or in either of his manuals. Resolving this needs the PDFs.

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
