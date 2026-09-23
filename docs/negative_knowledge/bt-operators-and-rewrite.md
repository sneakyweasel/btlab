# BT operators and rewrite

Standing methodology examples live here: sample minimization is not
exact Myhill–Nerode minimization; naive recursive reduction of \(x^3\)
fails; \(Q\) admits no bounded residue / valuation / \(B_t\) classifier;
nonzero cross-depth overlap is not exhausted by the zero spine;
valuations do not determine 3-adic lifting behaviour.

### Operators

Killed claim: \(W\) is an involution; \(W(3n)=3W(n)\); \(W\) commutes
with accelerated \(T\); \(S\circ D=\mathrm{id}\); \(D\) is floor-division.
Kill: \(W(3)=1\) and \(W(W(3))=1\neq 3\); \(W(3)\neq 3W(1)\);
\(W(T(3))\neq T(W(3))\); \(S\circ D\) fails on \(\mathbb Z\);
\(D(2)=1\neq\lfloor 2/3\rfloor\).
Kind: `REFUTED`.
Do not reopen: BT warp as a conjugacy; reversal as a Collatz intertwiner.
Witness: \(n=3\) (involution, commute); \(n=1\) for \(W(3n)\).
Pinned: [tests/regression/test_counterexamples.py](../../tests/regression/test_counterexamples.py).

Members: `BT-W-not-involution`, `W_not_involution`, `W_three_n`,
`W_commutes_T`, `W_R_reverse_itinerary`, `S_circ_D_id`.

### Rewrite confluence and semantic NF

Killed claim: a small operator-fragment or word table is locally
confluent / a unique semantic representative.
Kill: distinct irreducibles agree under `evaluate`; unary plus push-in
\(S\) through Add/Mul is not LC; \(N\)-through-Add is not a semantic
NF; factor-out Add (binary or AC) is not semantically complete;
one-way \(N\circ D\) plus stock \(W/K_3\) or SIMP is not LC.
Kind: `REFUTED`.
Do not reopen: tree-rule NF as integer-operator uniqueness.

Members: `BTC-op-fragment-semantic-nf`, `op_fragment_semantic_nf`,
`BTC-add-s-push-lc`, `add_s_push_lc`, `BTC-mul-s-push-lc`,
`mul_s_push_lc`, `BTC-add-n-push-semantic`, `add_n_push_semantic`,
`BTC-w-nd-word-lc`, `w_nd_word_lc`, `BTC-add-factor-binary-semantic`,
`add_factor_binary_semantic`, `BTC-add-factor-ac-semantic`,
`add_factor_ac_semantic`, `BTC-word-full-lc`, `word_full_lc`,
`BTC-word-simp-nd-lc`, `word_simp_nd_lc`.

---

