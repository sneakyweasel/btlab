"""Argument parsers for all Collatz command families."""

from __future__ import annotations

import argparse


def add_collatz_subparser(subparsers: argparse._SubParsersAction) -> None:
    p = subparsers.add_parser(
        "collatz",
        help="Accelerated Collatz research module (balanced ternary / 2-adic)",
    )
    c = p.add_subparsers(dest="collatz_cmd", required=True)

    p_an = c.add_parser("analyze", help="one accelerated step and feature transition")
    p_an.add_argument("n", type=int)

    p_tr = c.add_parser("trajectory", help="bounded accelerated trajectory")
    p_tr.add_argument("n", type=int)
    p_tr.add_argument("--max-steps", type=int, default=100)

    p_inv = c.add_parser("inverse", help="bounded inverse predecessor tree")
    p_inv.add_argument("m", type=int)
    p_inv.add_argument("--depth", type=int, default=5)
    p_inv.add_argument("--k-max", type=int, default=20, dest="k_max")
    p_inv.add_argument("--max-nodes", type=int, default=50_000, dest="max_nodes")

    p_invar = c.add_parser(
        "test-invariants",
        help="verify Collatz identities on odd n in [1, limit]",
    )
    p_invar.add_argument("--limit", type=int, default=100_000)

    p_auto = c.add_parser(
        "automaton",
        help="inspect TwoAdicDigitAutomaton(K)",
    )
    p_auto.add_argument("--precision", type=int, default=8)
    p_auto.add_argument(
        "--word",
        default=None,
        help="optional balanced ternary word to trace (default: encode(27))",
    )

    p_exp = c.add_parser(
        "experiment",
        help="exhaustive feature-transition experiment A (optional write)",
    )
    p_exp.add_argument("--limit", type=int, default=1000)
    p_exp.add_argument(
        "--write",
        action="store_true",
        help="write JSONL/JSON under experiments/collatz/",
    )

    p_th = c.add_parser("theorems", help="Layer A: BT(3n+1) = BT(n)+")
    p_th.add_argument("n", type=int)

    p_op = c.add_parser("odd-part", help="Layer B: x -> x/2^{v2(x)} on a BT word")
    p_op.add_argument("x", type=int)

    p_tu = c.add_parser("transducer", help="verify /2^k transducer vs integer arithmetic")
    p_tu.add_argument("--k", type=int, default=3)
    p_tu.add_argument("--limit", type=int, default=5000)

    p_vs = c.add_parser(
        "valuation-shift",
        help="Layer C: admissible valuation prefixes and growth budget",
    )
    p_vs.add_argument("--precision", type=int, default=12)
    p_vs.add_argument("--k-max", type=int, default=6, dest="k_max")
    p_vs.add_argument("--length", type=int, default=5)

    p_jg = c.add_parser("joint", help="Layer D: truncated w --k--> w' graph")
    p_jg.add_argument("--limit", type=int, default=500)
    p_jg.add_argument("--k-max", type=int, default=8, dest="k_max")
    p_jg.add_argument("--precision", type=int, default=8)
    p_jg.add_argument("--pattern-length", type=int, default=2, dest="pattern_length")
    p_jg.add_argument("--sync-length", type=int, default=2, dest="sync_length")

    p_cyl = c.add_parser(
        "cylinder",
        help="Milestone 3: valuation cylinder residues, density, budget",
    )
    p_cyl.add_argument(
        "--ks",
        required=True,
        help="comma-separated valuation prefix, e.g. 1,2,1",
    )
    p_cyl.add_argument("--leftover", type=int, default=1, dest="leftover")

    p_ent = c.add_parser(
        "entropy",
        help="Milestone 3: padded BT word counts and H_L of a cylinder",
    )
    p_ent.add_argument("--ks", default="", help="valuation prefix (empty = all odds)")
    p_ent.add_argument("--length", type=int, default=6)
    p_ent.add_argument("--leftover", type=int, default=1, dest="leftover")

    p_cx = c.add_parser(
        "complexity",
        help="Milestone 3: /2^k and L_k complexity spectrum",
    )
    p_cx.add_argument("--k-max", type=int, default=6, dest="k_max")
    p_cx.add_argument(
        "--write",
        action="store_true",
        help="write JSON under experiments/collatz/reports/",
    )

    p_sg = c.add_parser(
        "symbolic-graph",
        help="Milestone 3: symbolic futures (prefix, r, P)",
    )
    p_sg.add_argument("--max-length", type=int, default=4, dest="max_length")
    p_sg.add_argument("--k-max", type=int, default=5, dest="k_max")
    p_sg.add_argument("--leftover", type=int, default=1, dest="leftover")

    p_it = c.add_parser("itinerary", help="exact affine T^m formula")
    p_it.add_argument("ks", help="comma-separated valuations, e.g. 1,1,2,3")

    p_rz = c.add_parser("realizer", help="minimum positive realizer R(k)")
    p_rz.add_argument("ks", help="comma-separated valuations")

    p_en = c.add_parser(
        "enumerate-itineraries",
        help="exhaust signatures of length-m words",
    )
    p_en.add_argument("--length", type=int, default=4)
    p_en.add_argument("--max-k", type=int, default=3, dest="max_k")
    p_en.add_argument("--write", action="store_true")

    p_fb = c.add_parser(
        "fixed-budget",
        help="all compositions of K into m parts",
    )
    p_fb.add_argument("--length", type=int, default=5)
    p_fb.add_argument("--sum-k", type=int, default=8, dest="sum_k")
    p_fb.add_argument("--write", action="store_true")

    p_pm = c.add_parser("permutations", help="order dependence of C and R")
    p_pm.add_argument("ks", help="comma-separated multiset, e.g. 1,1,2,3")
    p_pm.add_argument("--write", action="store_true")

    p_ex = c.add_parser(
        "exceptional-search",
        help="census of expanding valuation words",
    )
    p_ex.add_argument("--length", type=int, default=6)
    p_ex.add_argument("--max-k", type=int, default=2, dest="max_k")
    p_ex.add_argument("--epsilon", type=float, default=0.1)

    p_zl = c.add_parser(
        "zero-lift",
        help="Milestone 5: exact lift digits and zero-lift successor",
    )
    p_zl.add_argument(
        "--ks",
        default="",
        help="comma-separated starting prefix (default: empty)",
    )
    p_zl.add_argument("--steps", type=int, default=8)
    p_zl.add_argument(
        "--candidate-k",
        type=int,
        default=None,
        dest="candidate_k",
        help="optional extension to classify from finite state",
    )
    p_zl.add_argument("--precision", type=int, default=4)

    p_pi = c.add_parser(
        "periodic-itinerary",
        help="Milestone 5: exact compatibility of a periodic valuation word",
    )
    p_pi.add_argument("ks", help="comma-separated period")

    p_zc = c.add_parser(
        "zero-lift-census",
        help="Milestone 5: bounded regressions and finite-state collision search",
    )
    p_zc.add_argument("--max-length", type=int, default=4, dest="max_length")
    p_zc.add_argument("--max-k", type=int, default=4, dest="max_k")
    p_zc.add_argument("--precision", type=int, default=4)

    p_dc = c.add_parser(
        "dual-code",
        help="Milestone 6: exact valuation/lift mixed-radix coding",
    )
    p_dc.add_argument("ks", help="comma-separated valuations")

    p_lt = c.add_parser(
        "lift-tree",
        help="Milestone 6: bounded cylinder lift tree",
    )
    p_lt.add_argument("--max-depth", type=int, default=3, dest="max_depth")
    p_lt.add_argument("--max-k", type=int, default=3, dest="max_k")
    p_lt.add_argument("--max-nodes", type=int, default=100_000, dest="max_nodes")

    p_pd = c.add_parser(
        "periodic-dual",
        help="Milestone 6: dual-code trace of a repeated valuation period",
    )
    p_pd.add_argument("ks", help="comma-separated nonempty period")
    p_pd.add_argument("--repeats", type=int, default=8)

    p_st = c.add_parser(
        "suffix-test",
        help="Milestone 6: bounded BT(R) suffix determination census",
    )
    p_st.add_argument("--max-length", type=int, default=4, dest="max_length")
    p_st.add_argument("--max-k", type=int, default=4, dest="max_k")
    p_st.add_argument("--suffix-max", type=int, default=8, dest="suffix_max")

    p_dd = c.add_parser(
        "dual-dataset",
        help="Milestone 6: reproducible finite dual-code dataset",
    )
    p_dd.add_argument("--length", type=int, default=4)
    p_dd.add_argument("--max-k", type=int, default=3, dest="max_k")
    p_dd.add_argument("--write", action="store_true")

    p_fc = c.add_parser(
        "compatibility",
        help="exact 2-adic/3-adic/BT/drift diagnostic for an exponent code",
    )
    p_fc.add_argument("ks", help="comma-separated valuations")

    p_cg = c.add_parser(
        "compatibility-graph",
        help="bounded exact four-coordinate prefix graph",
    )
    p_cg.add_argument("--max-depth", type=int, default=3, dest="max_depth")
    p_cg.add_argument("--max-k", type=int, default=3, dest="max_k")
    p_cg.add_argument("--root", default="", help="optional comma-separated root prefix")

    p_rb = c.add_parser(
        "rational-base",
        help="compare balanced ternary with canonical rational base 3/2",
    )
    p_rb.add_argument("n", type=int)

    p_ic = c.add_parser(
        "information-test",
        help="test BT observables against exact and truncated compatibility states",
    )
    p_ic.add_argument("--max-length", type=int, default=4, dest="max_length")
    p_ic.add_argument("--max-k", type=int, default=4, dest="max_k")
    p_ic.add_argument("--precision-max", type=int, default=4, dest="precision_max")
    p_ic.add_argument("--write", action="store_true")

    p_nc = c.add_parser(
        "near-critical",
        help="generate reproducible exact-drift compatibility datasets",
    )
    p_nc.add_argument("--max-length", type=int, default=4, dest="max_length")
    p_nc.add_argument("--max-k", type=int, default=4, dest="max_k")
    p_nc.add_argument("--random-length", type=int, default=16, dest="random_length")
    p_nc.add_argument("--random-count", type=int, default=32, dest="random_count")
    p_nc.add_argument("--seed", type=int, default=0)
    p_nc.add_argument("--write", action="store_true")

    p_ac = c.add_parser(
        "affine-center",
        help="exact fixed-center geometry for one exponent code",
    )
    p_ac.add_argument("ks", help="comma-separated nonempty valuations")
    p_ac.add_argument("--critical-gap", type=int, default=1, dest="critical_gap")

    p_acc = c.add_parser(
        "affine-center-census",
        help="exhaust exact center inequalities across bounded exponent codes",
    )
    p_acc.add_argument("--max-length", type=int, default=4, dest="max_length")
    p_acc.add_argument("--max-k", type=int, default=4, dest="max_k")
    p_acc.add_argument("--critical-gap", type=int, default=1, dest="critical_gap")
    p_acc.add_argument("--closest-count", type=int, default=10, dest="closest_count")
    p_acc.add_argument("--write", action="store_true")

    p_fi = c.add_parser(
        "fixed-integer",
        help="Milestone 10: exact affine-center ledger of one odd start",
    )
    p_fi.add_argument("n", type=int)
    p_fi.add_argument("--max-steps", type=int, default=40)
    p_fi.add_argument("--critical-gap", type=int, default=1, dest="critical_gap")

    p_fic = c.add_parser(
        "fixed-integer-census",
        help="Milestone 10: n_* <= n search on actual odd trajectories",
    )
    p_fic.add_argument("--limit", type=int, default=1000)
    p_fic.add_argument("--max-steps", type=int, default=80)
    p_fic.add_argument("--critical-gap", type=int, default=1, dest="critical_gap")
    p_fic.add_argument("--write", action="store_true")

    p_ag = c.add_parser(
        "affine-gap",
        help="Milestone 10: integer affine gap G along an actual orbit",
    )
    p_ag.add_argument("n", type=int)
    p_ag.add_argument("--max-steps", type=int, default=40)

    p_pc = c.add_parser(
        "periodic-code",
        help="Milestone 10: periodic-code fixed-point identity",
    )
    p_pc.add_argument("ks", help="comma-separated period, e.g. 2 or 1,1")

    p_cy = c.add_parser(
        "cycle",
        help="Milestone 11: exact periodic exponent-code cycle test",
    )
    p_cy.add_argument("ks", help="comma-separated exponent word")

    p_cyc = c.add_parser(
        "cycle-census",
        help="Milestone 11: prune exponent words for exact cycles",
    )
    p_cyc.add_argument("--max-p", type=int, default=5, dest="max_p")
    p_cyc.add_argument("--k-max", type=int, default=4, dest="k_max")
    p_cyc.add_argument(
        "--additive-bound",
        type=int,
        default=-1,
        dest="additive_bound",
        help="keep amplitude <= bound; negative means unbounded",
    )
    p_cyc.add_argument("--write", action="store_true")

    p_cylang = c.add_parser(
        "cycle-language",
        help="Milestone 11: L_A for a fixed additive amplitude bound",
    )
    p_cylang.add_argument("--additive", type=int, default=0)
    p_cylang.add_argument("--max-p", type=int, default=4, dest="max_p")
    p_cylang.add_argument("--k-max", type=int, default=3, dest="k_max")

    p_wp = c.add_parser(
        "warp",
        help="Milestone 9: W, T, and the domain-aware commutator at n",
    )
    p_wp.add_argument("n", type=int)

    p_wpc = c.add_parser(
        "warp-census",
        help="Milestone 9: commutator census on odd n in [1, limit]",
    )
    p_wpc.add_argument("--limit", type=int, default=10_000)
    p_wpc.add_argument("--identity-length", type=int, default=6, dest="identity_length")
    p_wpc.add_argument("--write", action="store_true")

    p_wpr = c.add_parser(
        "warp-realizer",
        help="Milestone 9: W(R) versus R of a transformed itinerary",
    )
    p_wpr.add_argument("ks", help="comma-separated valuations")

    p_wprc = c.add_parser(
        "warp-realizer-census",
        help="Milestone 9: bounded W(R) versus reverse/tail itineraries",
    )
    p_wprc.add_argument("--max-length", type=int, default=3, dest="max_length")
    p_wprc.add_argument("--max-k", type=int, default=3, dest="max_k")
    p_wprc.add_argument("--write", action="store_true")

    p_wps = c.add_parser(
        "warp-semigroup",
        help="Milestone 9: T, W, Wt words up to a given length",
    )
    p_wps.add_argument("--length", type=int, default=6)
    p_wps.add_argument("--sample-limit", type=int, default=80, dest="sample_limit")

    p_wpp = c.add_parser(
        "warp-palindrome",
        help="Milestone 9: palindrome flags along an accelerated orbit",
    )
    p_wpp.add_argument("n", type=int)
    p_wpp.add_argument("--max-steps", type=int, default=40)

    p_wpt = c.add_parser(
        "warp-trajectory",
        help="Milestone 9: n -> W(n) -> T(W(n)) -> ...",
    )
    p_wpt.add_argument("n", type=int)
    p_wpt.add_argument("--max-steps", type=int, default=40)

    c.add_parser(
        "warp-counterexamples",
        help="Milestone 9: preserved counterexamples to naive W identities",
    )
