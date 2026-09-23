# Recovery of the identified literature gaps

Checked 23 September 2026. This pass adds ten missing registry records and
expands the existing Wirsching record. It recovers bibliographic identities,
primary-source access routes and specific points of comparison with the lab.
It is not a full proof review or a finding of novelty. No paper theorem,
evidence label or numerical bound changes as a result of this pass.

Reading coverage is explicit: six works have selected primary-text sections
checked, three have abstract/introduction coverage, and two books have only
publisher previews checked. Finding a full-text link does not mean its proof
has been read. Only metadata, links and original summaries belong in this
repository; downloaded scans used for inspection are outside tracked content.

## Recovered sources and actual reading scope

| Work and registry record | Primary source and scope checked | Relevance and boundary |
|---|---|---|
| [Applegate–Lagarias I, 1995](../../literature/applegate-lagarias-1995-tree-search.json) | [Author manuscript](https://websites.umich.edu/~lagarias/doc/applegateI.pdf), introduction and Section 2 through Theorem 2.1. | Weighted inverse trees and finite ternary residue classes are established counting machinery. Repeated labels at cyclic roots require care when counting distinct ancestors. |
| [Applegate–Lagarias II, 1995](../../literature/applegate-lagarias-1995-krasikov-inequalities.json) | [Author manuscript](https://websites.umich.edu/~lagarias/doc/applegateII.pdf), Theorem 1.1, height/residue definitions, LP formulation and numerical discussion. | Direct predecessor of the later Krasikov–Lagarias bounds. Signed height control still needs its own argument. |
| [Krasikov, 1989](../../literature/krasikov-1989-difference-inequalities.json) | [Original article mirrored as OCR](https://www.researchgate.net/publication/26535243_How_Many_Numbers_Satisfy_the_3x_1_Conjecture), abstract and introduction. Lemma 4 and Theorem 1 located; formula extraction is damaged. | Original difference-inequality source; the abstract's counting bound is **c x^(3/7)** with c > 0. Detailed proof reading remains pending. |
| [Steiner, 1978 proceedings](../../literature/steiner-1978-syracuse.json) | [Annotated scan of the original](https://drive.google.com/file/d/1tIFKsm5tvlvvLdEQiqqLHImK0wKAM5d2/view), seven printed pages visually inspected, especially Theorems 3–4. Annotations were excluded as evidence. | Positive one-circuit exclusion, using logarithmic estimates and continued fractions. The printed computation was not rerun; this does not exclude arbitrary m-cycles. |
| [Böhm–Sontacchi, 1978](../../literature/bohm-sontacchi-1978-cycles.json) | [BDIM record](https://www.bdim.eu/item?id=RLINA_1978_8_64_3_260_0); original scan recovered from a [mirror](https://github.com/tcosmo/BohmSontacchi1978_lean/blob/main/BohmSontacchi1978.pdf). Introduction and Section 2, with visual checks of Propositions 4–7. | Classical cycle/iterate parametrization over integers, including negative cycles. Proposition 6's bound uses shortcut length, not the number of odd blocks. |
| [Laurent, 2008](../../literature/laurent-2008-two-logarithms.json) | [Publisher full text](https://www.impan.pl/shop/en/publication/transaction/download/product/82485), Theorem 2 hypotheses, Corollaries 1–2 and Table 1. | A sharper general two-logarithm tool than LMN. Improvement of the lab's specialized bounds has not been established. |
| [Matveev, 2000](../../literature/matveev-2000-logarithms-ii.json) | [MathNet record](https://www.mathnet.ru/eng/im314), abstract and indexed first-page introduction. Linked PDF retrieval failed. | General explicit logarithmic-form bounds. Constants and hypotheses have not been checked for a lab application. |
| [Lagarias–Weiss, 1992](../../literature/lagarias-weiss-1992-stochastic-models.json) | [Author upload](https://www.researchgate.net/publication/265672392_The_3x_1_Problem_Two_Stochastic_Models), abstract and introductory page 231. Full scan located; Sections 2–5 not read. | Forward random walks and backward branching walks; their limit constants belong to the models. They are not deterministic Collatz stopping-time theorems. |
| [Kontorovich–Sinai, 2002](../../literature/kontorovich-sinai-2002-dgh-maps.json) | [Author text](https://arxiv.org/pdf/math/0601622), framework, Theorem 1.2, and Theorem 3.2 with its density-limit setup. | Exact finite valuation-path coding, explicitly including 3x−1. The density limit is taken before the path-length limit; no uniform growing-depth Juggler estimate follows. |
| [Graham–Kolesnik, 1991](../../literature/graham-kolesnik-1991-exponential-sums.json) | [Publisher frontmatter](https://assets.cambridge.org/97805213/39278/frontmatter/9780521339278_frontmatter.pdf) and contents only. | Relevant chapters located for exponent pairs, applications and optimization. A particular derivative hypothesis or averaged-shift bound remains unchecked. |
| [Wirsching, 1998](../../literature/wirsching-1998-dynamical-system.json) | Publisher frontmatter and previews: [II](https://page-one.springer.com/pdf/preview/10.1007/BFb0095988), [III](https://page-one.springer.com/pdf/preview/10.1007/BFb0095989), [IV](https://page-one.springer.com/pdf/preview/10.1007/BFb0095990). Full chapters remain access-restricted. | Inverse coding, 3-adic averages and a Markov-chain/integral-kernel formulation are directly relevant prior art. A spectral gap has not been checked or inferred. |

## Consequences for our papers and dossiers

**Collatz fibres and ancestor density:** the chain Krasikov 1989 →
Applegate–Lagarias 1995 → Krasikov–Lagarias 2003 is now represented in the
registry. Compare counting objects and truncations before comparing exponents.
Part II uses absolute-height path counts in (2.1), but scales by `2^y a` in
(2.2); its broad introductory notation does not settle the signed transfer.
The lab's existing [signed-height correction](../problems/juggler_negative_preimage_density.md)
therefore remains essential. A sublinear ancestor-count lower bound alone
does not imply divergent reciprocal mass.

Wirsching's Chapter IV preview identifies a specific operator-method source
for the comparison requested by the audit. Its earlier registration did not
establish that the lab had used or compared this machinery. Whether its
operator agrees with the lab's operator needs a full-text comparison of the
state space, weights and height normalization. The
[fibre dossier](../problems/collatz_fibre_mass.md) already labels its elementary
parametrization and Tao operator as known and makes no priority claim for its
finite-weight obstruction; this pass supplies no reason to upgrade that claim.

**Paper D and cycle identities:** cite Böhm–Sontacchi for the classical affine
formula and Steiner for the one-circuit predecessor. Böhm–Sontacchi explicitly
connects negative integers with positive 3x−1 dynamics. Its `|x| < 3^n` bound
uses the shortcut map's period-dividing length n. Translating between that n,
odd-return length and Paper D's m requires explicit definitions.

**Papers A and D, logarithmic estimates:** Laurent 2008 is a concrete missing
comparison source. Its selectable table constant is coupled to other terms in
the bound; taking the smallest constant alone is invalid. A useful future
comparison must instantiate the full degree, height, coefficient and max-term
hypotheses, then compare with the specialized bound actually used. Merely
registering Laurent or Matveev does not reopen the
[Diophantine wall](../negative_knowledge/diophantine-walls.md).

**Paper C and probabilistic analogies:** Kontorovich–Sinai concerns an affine
accelerated family and a particular order of limits. The nonlinear Juggler map
does not inherit its progression coding or a quantitative rate. Lagarias–Weiss
provides model theorems, not the required deterministic estimate. Also, the lab
already had [Kontorovich–Lagarias 2009](../../literature/kontorovich-lagarias-2009-stochastic-models.json),
a related survey. The missing earlier primary papers are now registered;
their recovery improves coverage, not Paper C's unproved quantitative hypotheses.

**Paper B:** Graham–Kolesnik supplies a standard reference to consult against
the precise assumptions of the [two-monomial question](../theory/exponent_pair_two_monomial.md).
The preview does not establish whether an averaged-shift variant succeeds or
has already been treated. That question remains unassessed, not promoted.

## Dates, versions and remaining retrieval work

- Steiner's conference was in 1977; [Lagarias's bibliography](https://arxiv.org/abs/math/0309224)
  dates the proceedings to 1978. The record preserves both dates.
- Both inspected Applegate–Lagarias manuscripts are dated December 1993;
  their journal publication is 1995. Part I's inspected Theorem 1.2 gives
  exponent 0.65, whereas Part II's introduction cites 0.643 for the preceding
  tree-search result. Resolve against the journal versions before quoting a
  numerical historical progression.
- Kontorovich–Sinai was published in 2002 and deposited on arXiv in 2006.
  Graham–Kolesnik was printed in 1991; its online publication date is 2010.
  Matveev's English and Russian versions have different pagination and DOIs.
- The highest-value remaining access task is Wirsching Chapters II–IV, followed
  by Graham–Kolesnik's actual exponent-pair chapters. Obtain lawful full access
  before citing unseen theorem details.
- Recover readable Krasikov and Matveev PDFs, then inspect the definitions and
  complete hypotheses. Read Lagarias–Weiss Sections 2–5 before any detailed
  comparison with deterministic rate assumptions.

The bibliographic omissions named in the audit are now recorded. The full-text
and theorem-comparison gaps listed above remain explicit; no external review,
formal verification, numerical reproduction or manuscript revision is claimed.
