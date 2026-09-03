"""Orientation page for the Streamlit laboratory."""

from __future__ import annotations

import streamlit as st


def overview_page() -> None:
    st.header("Laboratory map")
    st.caption(
        "Balanced ternary is the core. Exact arithmetic first. Bounded "
        "computations are labelled and are not proofs."
    )

    with st.container(horizontal=True):
        st.metric("Core object", "Canonical BT word", border=True)
        st.metric("Alphabet", "+, 0, −", border=True)
        st.metric("Primary tool", "Calculator", border=True)

    left, right = st.columns(2)
    with left:
        with st.container(border=True):
            st.subheader("What balanced ternary is")
            st.markdown(
                r"""
Every integer has a unique canonical expansion

$$n = \sum_i a_i 3^i,\qquad a_i \in \{-1,0,+1\}$$

with no leading zeros (except $n=0$). Display uses `+`, `0`, `-`
(most-significant digit first). Mathematical positions are indexed from
the least-significant digit $a_0$.
                """
            )
    with right:
        with st.container(border=True):
            st.subheader("What to open first")
            st.markdown(
                """
1. **Calculator** — add, subtract, scale by 2 or 3, and apply `S`, `N`, `D`, `W`, `M2`, `H2`, …
2. **Encode / analyze** — integer ↔ word round-trip and digit metrics.
3. **Operators** — domain, involution, and integer/word agreement for each map.
4. **Rewrite calculus** — unary stepper and Add/carry witnesses from the paper candidate.
5. **Residual explorer** — prefix tree, Newton classes, and depth-deficit visibility.
6. **Juggler cycles** — Paper A companion: finance, walk charge, period ≥ 780239, leftover families.
7. Collatz pages stay available as one application of the same words.
                """
            )

    st.subheader("Implemented layers")
    st.dataframe(
        [
            {
                "layer": "Balanced ternary",
                "object": "Canonical words, arithmetic, metrics, residue automata",
                "status": "EXACT — HUMAN PROOF / exact implementation",
            },
            {
                "layer": "Operators",
                "object": "S, N, D, W, Wz, Wt, M2, H2, H3, K3, Im, Ip",
                "status": "EXACT — HUMAN PROOF on the stated domains",
            },
            {
                "layer": "Rewrite calculus",
                "object": "Unary {D, I_a, S, N} stepper and Add/carry witnesses",
                "status": "Paper companion; Lean remains the proof authority",
            },
            {
                "layer": "Residual calculus",
                "object": "Prefix residuals, Newton classes, fibres, depth deficit",
                "status": "Visualized; Lean remains the proof authority",
            },
            {
                "layer": "Juggler finite dynamics",
                "object": "Parity finance + floor 10^6 ⇒ L ≥ 25781; walk charge + N0 = 350000000 ⇒ L ≥ 780239; even-count ≥ 4",
                "status": "Paper A companion; Theorem 4.6 and Corollary 5.11 are verified computations",
            },
            {
                "layer": "Finite-state Collatz",
                "object": "2-adic valuation classifiers and division transducers",
                "status": "EXACT — HUMAN PROOF with bounded model sizes",
            },
            {
                "layer": "Exponent codes",
                "object": "Cylinders, affine formula, canonical realizers, lift digits",
                "status": "EXACT — LEAN VERIFIED for key statements",
            },
            {
                "layer": "Compatibility",
                "object": "2-adic start, 3-adic endpoint, BT(R), real drift",
                "status": "Exact; strong BT independence refuted",
            },
            {
                "layer": "Affine-center geometry",
                "object": "Fixed center, centered scaling, regime inequalities",
                "status": "Exact identities plus bounded censuses",
            },
            {
                "layer": "BT word maps",
                "object": "OEIS reversal W, tail-reverse, commutator with T",
                "status": "Exact word algebra; W/T commutation refuted",
            },
        ],
        hide_index=True,
        width="stretch",
    )

    st.info(
        "Nothing in this laboratory proves convergence of Collatz trajectories. "
        "Contraction of the homogeneous factor is not a Lyapunov function.",
        icon=":material/info:",
    )


overview_page()
