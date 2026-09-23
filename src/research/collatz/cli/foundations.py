"""Foundational, automata, and symbolic Collatz commands."""

from __future__ import annotations

import argparse
from pathlib import Path

from bt.representation import encode
from research.collatz.automata.joint_graph import layer_d_report
from research.collatz.automata.symbolic_graph import build_symbolic_graph
from research.collatz.automata.two_adic import TwoAdicDigitAutomaton
from research.collatz.automata.valuation_shift import AdmissibleValuationAutomaton
from research.collatz.cylinders import valuation_cylinder
from research.collatz.experiments.complexity_spectrum import run_complexity_spectrum
from research.collatz.languages.cylinder_dfa import entropy_report
from bt.arithmetic import lsd_add_one_case, multiply_by_three
from research.collatz.core import require_positive_odd
from research.collatz.experiments.exhaustive import run_exhaustive_experiment
from research.collatz.features import extract_features
from research.collatz.inverse import build_inverse_tree, format_inverse_tree
from research.collatz.invariants import verify_collatz_invariants
from research.collatz.theorems import append_plus, predicted_features_after_append_plus
from research.collatz.trajectory import collatz_trajectory
from bt.transducers.divide_by_two import DivideByTwoTransducer, LeftoverCarryError
from bt.transducers.divide_by_two_power import DivideByTwoPowerTransducer
from research.collatz.transducers.odd_part import odd_part_word
from research.collatz.transitions import NUMERIC_FEATURE_NAMES, feature_transition
from research.collatz.valuation import v2
from research.experiments.paths import collatz_data_dir


def _analyze(n: int) -> int:
    n = require_positive_odd(n)
    trans = feature_transition(n)
    word_n = encode(n)
    shifted = multiply_by_three(word_n).word()
    lines = [
        "Accelerated Collatz analysis (odd-only map T)",
        f"n = {trans.n}",
        f"BT(n) = {trans.balanced_ternary_n}",
        "",
        f"3n+1 = {trans.three_n_plus_one}",
        f"BT(3n+1) = {trans.balanced_ternary_three_n_plus_one}",
        f"v2(3n+1) = {trans.v2_three_n_plus_one}",
        "",
        f"T(n) = {trans.T_n}",
        f"BT(T(n)) = {trans.balanced_ternary_T_n}",
        "",
        "Ternary decomposition of 3n+1:",
        f"  multiply-by-3 shift BT(3n) = {shifted}",
        f"  LSD add-+1 case (on n): {lsd_add_one_case(word_n)}",
        f"  shift-then-add-one matches BT(3n+1): "
        f"{str(trans.ternary_shift_add_one_matches).lower()}",
        f"  BT(3n+1) = BT(n)+  (append-plus theorem): "
        f"{str(trans.append_plus_matches).lower()}",
        f"  closed-form 3n+1 features match: "
        f"{str(trans.append_plus_features_match).lower()}",
        "",
        "Digit alignment (LSD / right-aligned):",
        *_digit_alignment(
            trans.balanced_ternary_n,
            shifted,
            trans.balanced_ternary_three_n_plus_one,
            trans.balanced_ternary_T_n,
        ),
        "",
        "Features (n -> 3n+1 -> T(n)) and deltas F(T(n)) - F(n):",
    ]
    fn = trans.features_n.as_dict()
    fy = trans.features_three_n_plus_one.as_dict()
    ft = trans.features_T_n.as_dict()
    for name in NUMERIC_FEATURE_NAMES:
        lines.append(
            f"  {name}: {fn[name]} -> {fy[name]} -> {ft[name]}  "
            f"delta={trans.deltas[f'delta_{name}']}"
        )
    lines.append("")
    print("\n".join(lines))
    return 0


def _digit_alignment(bt_n: str, bt_3n: str, bt_y: str, bt_t: str) -> list[str]:
    width = max(len(bt_n), len(bt_3n), len(bt_y), len(bt_t), 8)
    return [
        f"  BT(n)     {bt_n.rjust(width)}",
        f"  BT(3n)    {bt_3n.rjust(width)}",
        f"  BT(3n+1)  {bt_y.rjust(width)}",
        f"  BT(T(n))  {bt_t.rjust(width)}",
    ]


def _trajectory(n: int, max_steps: int) -> int:
    n = require_positive_odd(n)
    traj = collatz_trajectory(n, max_steps)
    print(
        f"Accelerated trajectory of {n}  max_steps={max_steps}  "
        f"reached_one={str(traj.reached_one).lower()}  "
        f"truncated={str(traj.truncated).lower()}"
    )
    print(f"{'i':>4}  {'n':>12}  {'BT(n)':<24}  {'v2':>4}  {'T(n)':>12}  deltas")

    for i, step in enumerate(traj.steps):
        rec = feature_transition(step.n)
        delta_bits = " ".join(
            f"{name}={rec.deltas[f'delta_{name}']:+d}"
            for name in ("length", "weight", "signed_digit_sum", "number_of_runs")
        )
        print(
            f"{i:>4}  {step.n:>12}  {step.balanced_ternary_n:<24}  "
            f"{step.v2_three_n_plus_one:>4}  {step.T_n:>12}  {delta_bits}"
        )
    if not traj.steps:
        print(f"   0  {n:>12}  {encode(n).word():<24}  (terminal or max_steps=0)")
    print(f"values: {', '.join(str(v) for v in traj.values)}")
    return 0


def _inverse(m: int, depth: int, k_max: int, max_nodes: int) -> int:
    tree = build_inverse_tree(m, depth=depth, k_max=k_max, max_nodes=max_nodes)
    print(format_inverse_tree(tree), end="")
    return 0


def _invariants(limit: int) -> int:
    print(f"Checking Collatz invariants for odd n in [1, {limit}] ...")
    report = verify_collatz_invariants(limit)
    print(f"Checked {report.checked_odd} odd integers.")
    if report.ok:
        print("All invariants passed.")
        return 0
    print(f"FAILED with {len(report.failures)} failure(s). First:")
    f = report.failures[0]
    print(f"  {f.name} at n={f.n}: {f.detail}")
    return 1


def _automaton(precision: int, word: str | None) -> int:
    auto = TwoAdicDigitAutomaton(precision)
    example = word if word is not None else encode(27)
    print(auto.format_report(example), end="")
    return 0


def _experiment(limit: int, write: bool) -> int:
    out_dir: Path | None = None
    if write:
        out_dir = collatz_data_dir()
    result = run_exhaustive_experiment(limit, output_dir=out_dir)
    print(f"experiment: {result.experiment_name}")
    print(f"range: {result.integer_range}")
    print(f"checked: {result.checked}")
    print(f"timestamp: {result.timestamp}")
    print(f"code_version: {result.code_version}")
    print(f"weight_parity_failures: {result.weight_parity_failures}")
    print(f"ternary_shift_failures: {result.ternary_shift_failures}")
    if result.output_metadata:
        print(f"metadata: {result.output_metadata}")
        print(f"rows: {result.output_rows}")
    status = (
        "ok" if result.weight_parity_failures == 0 and result.ternary_shift_failures == 0
        else "FAILED"
    )
    print(f"status: {status}")
    return 0 if status == "ok" else 1


def _theorems(n: int) -> int:
    if isinstance(n, bool) or not isinstance(n, int) or n == 0:
        raise SystemExit("n must be a nonzero integer")
    word = encode(n)
    plus = append_plus(word)
    actual = encode(3 * n + 1)
    pred = predicted_features_after_append_plus(word)
    feat = extract_features(actual)
    lines = [
        "Layer A: BT(3n+1) = BT(n)+   [EXACT — HUMAN PROOF for n != 0]",
        f"n = {n}",
        f"BT(n)  = {word.word()}",
        f"BT(n)+ = {plus.word()}",
        f"BT(3n+1) = {actual.word()}",
        f"append_plus matches encode(3n+1): {str(plus == actual).lower()}",
        "",
        "Closed-form features of 3n+1 vs extract(encode(3n+1)):",
        f"  predicted == actual: {str(pred == feat).lower()}",
        f"  length {feat.length} (n+1)",
        f"  weight {feat.weight} (n+1)",
        f"  signed_digit_sum {feat.signed_digit_sum} (n+1)",
        f"  positive {feat.positive_digit_count} (n+1)  "
        f"negative {feat.negative_digit_count} (unchanged)  "
        f"zeros {feat.zero_count} (unchanged)",
        f"  S^(2) {feat.position_class_sums_period_2}",
        f"  S^(3) {feat.position_class_sums_period_3}",
        "",
    ]
    print("\n".join(lines))
    return 0 if plus == actual and pred == feat else 1


def _odd_part(x: int) -> int:
    if isinstance(x, bool) or not isinstance(x, int):
        raise SystemExit("x must be int")
    word = encode(x)
    k = v2(x)
    print("Layer B: odd-part  x -> x / 2^{v2(x)}")
    print(f"x = {x}")
    print(f"BT(x) = {word.word()}")
    print(f"v2(x) = {'∞' if k is None else k}")
    if x == 0:
        print("odd part of 0 is 0 (valuation infinity)")
        return 0
    if x % 2 != 0:
        print("x is odd; odd-part is x itself.")
        print(f"BT(odd-part) = {odd_part_word(word).word()}")
        return 0
    trans = DivideByTwoTransducer()
    print("LSD /2 trace (carry_in, input, output, carry_out):")
    try:
        for row in trans.trace(word):
            print(f"  {row}")
        got = odd_part_word(word)
        print(f"BT(odd-part) = {got.word()}")
        print(f"integer odd-part = {x // (1 << k)}")
        print(f"match: {str(got == encode(x // (1 << k))).lower()}")
    except LeftoverCarryError as exc:
        print(f"leftover carry (not a finite even integer image): {exc}")
        return 1
    return 0


def _transducer(k: int, limit: int) -> int:
    machine = DivideByTwoPowerTransducer(k)
    report = machine.complexity_report()
    print(f"DivideByTwoPowerTransducer k={k}")
    print(
        f"naive_bound={report['naive_bound']}  reachable={report['reachable']}  "
        f"minimized={report['minimized']}  [reachable/minimized: COMPUTATIONALLY VERIFIED]"
    )
    failures = 0
    checked = 0
    for n in range(-limit, limit + 1):
        x = n * (1 << k)
        checked += 1
        if machine.apply(encode(x)) != encode(n):
            failures += 1
            if failures == 1:
                print(f"FAIL at n={n} x={x}")
    print(f"checked {checked} integers n in [{-limit}, {limit}], x=n*2^{k}")
    print("ok" if failures == 0 else f"FAILED ({failures})")
    return 0 if failures == 0 else 1


def _valuation_shift(precision: int, k_max: int, length: int) -> int:
    auto = AdmissibleValuationAutomaton(precision, k_max)
    report = auto.enumerate_admissible(length)
    print(report.format(), end="")
    return 0


def _joint(
    limit: int,
    k_max: int,
    precision: int,
    pattern_length: int,
    sync_length: int,
) -> int:
    print(
        layer_d_report(
            limit=limit,
            k_max=k_max,
            precision=precision,
            pattern_length=pattern_length,
            sync_length=sync_length,
        ),
        end="",
    )
    return 0


def _cylinder(ks: str, leftover: int) -> int:
    cyl = valuation_cylinder(ks, leftover_q=leftover)
    print(cyl.format(), end="")
    return 0


def _entropy(ks: str, length: int, leftover: int) -> int:
    report = entropy_report(ks, length, leftover_q=leftover)
    print(report.format(), end="")
    return 0


def _complexity(k_max: int, write: bool) -> int:
    out_dir = collatz_data_dir() if write else None
    result = run_complexity_spectrum(k_max, output_dir=out_dir)
    print(result.format(), end="")
    if result.output_path:
        print(f"wrote {result.output_path}")
    return 0


def _symbolic_graph(max_length: int, k_max: int, leftover: int) -> int:
    graph = build_symbolic_graph(
        max_length=max_length, k_max=k_max, leftover_q=leftover
    )
    print(graph.format(), end="")
    return 0
