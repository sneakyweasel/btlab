"""Command-line interface for the Balanced Ternary Mathematical Laboratory."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

from bt.arithmetic import format_factorization, is_prime
from bt.metrics import (
    automaton_residue,
    lsd_nonzero_index,
    signed_digit_sum,
    v3,
    verify_invariants,
    weight,
)
from bt.representation import decode, encode, is_canonical
from bt.sequences import bt_reverse, bt_reverse_tail
from cli.calculus import add_calculus_subparser, run_calculus
from cli.congruence import add_congruence_subparser, run_congruence
from cli.normalize import add_normalize_subparser, run_normalize
from cli.operators import add_operators_subparser, run_operators
from cli.research import add_research_subparser, run_research
from research.collatz.cli import add_collatz_subparser, run_collatz


def main(argv: list[str] | None = None) -> int:
    from research.scope import include_archive
    argv = sys.argv[1:] if argv is None else argv
    historical = include_archive() or '--include-archive' in argv
    parser = argparse.ArgumentParser(
        prog="btlab",
        description=(
            "Juggler–Collatz Mathematical Laboratory: exact dynamics, "
            "formal proofs and reproducible papers. "
            "This tool does not claim a solution of Collatz or any other "
            "open problem."
        ),
    )
    parser.add_argument('--include-archive', action='store_true',
                        help='show historical balanced-ternary and other research commands')
    sub = parser.add_subparsers(dest="cmd", required=True)

    _add_bt_leaf_commands(sub)
    if historical:
        add_operators_subparser(sub)
        add_calculus_subparser(sub)
        add_congruence_subparser(sub)
        add_normalize_subparser(sub)
    add_research_subparser(sub)
    add_collatz_subparser(sub)
    _add_bt_namespace(sub)
    if historical:
        _add_research_namespaces(sub)
    _add_lab_namespaces(sub)

    args = parser.parse_args(argv)
    previous = os.environ.get('BTLAB_INCLUDE_ARCHIVE')
    try:
        if historical:
            os.environ['BTLAB_INCLUDE_ARCHIVE'] = '1'
        return _dispatch(parser, args)
    finally:
        if previous is None:
            os.environ.pop('BTLAB_INCLUDE_ARCHIVE', None)
        else:
            os.environ['BTLAB_INCLUDE_ARCHIVE'] = previous


def _add_bt_leaf_commands(sub: argparse._SubParsersAction) -> None:
    p_enc = sub.add_parser("encode", help="integer -> canonical balanced ternary")
    p_enc.add_argument("n", type=int)

    p_dec = sub.add_parser("decode", help="balanced ternary word -> integer")
    p_dec.add_argument("word")

    p_an = sub.add_parser("analyze", help="print digit metrics of an integer")
    p_an.add_argument("n", type=int)

    p_res = sub.add_parser("residue", help="automaton residue of a word modulo q")
    p_res.add_argument("word")
    p_res.add_argument("--mod", type=int, required=True, dest="modulus")

    p_inv = sub.add_parser(
        "test-invariants",
        help="exhaustively verify balanced-ternary identities on [-limit, limit]",
    )
    p_inv.add_argument("--limit", type=int, default=100_000)

    p_rev = sub.add_parser("reverse", help="A134028: reverse canonical balanced ternary digits (W)")
    p_rev.add_argument("n", type=int)

    p_revt = sub.add_parser(
        "reverse-tail",
        help="A351702: reverse all balanced ternary digits except the MSD",
    )
    p_revt.add_argument("n", type=int)


def _add_bt_namespace(sub: argparse._SubParsersAction) -> None:
    p = sub.add_parser("bt", help="core balanced-ternary commands")
    inner = p.add_subparsers(dest="bt_cmd", required=True)
    _add_bt_leaf_commands(inner)


def _add_research_namespaces(sub: argparse._SubParsersAction) -> None:
    p_pr = sub.add_parser("primes", help="sparse-prime helpers")
    pr = p_pr.add_subparsers(dest="primes_cmd", required=True)
    p_list = pr.add_parser("sparse", help="weight-bounded primes")
    p_list.add_argument("--k", type=int, default=2)
    p_list.add_argument("--bound", type=int, default=10_000)

    p_pp = sub.add_parser("perfect-powers", help="sparse squares and cubes")
    pp = p_pp.add_subparsers(dest="pp_cmd", required=True)
    p_sq = pp.add_parser("squares", help="weight-bounded squares")
    p_sq.add_argument("--k", type=int, default=2)
    p_sq.add_argument("--bound", type=int, default=10_000)
    p_cu = pp.add_parser("cubes", help="weight-bounded cubes")
    p_cu.add_argument("--k", type=int, default=2)
    p_cu.add_argument("--bound", type=int, default=10_000)
    pp.add_parser("weight-one", help="exact W_1 square classification")

    p_ad = sub.add_parser("additive", help="digit-restricted sumsets")
    p_ad.add_argument("--k", type=int, default=4)

    p_po = sub.add_parser("polynomials", help="P_n evaluations")
    p_po.add_argument("n", type=int)


def _add_lab_namespaces(sub: argparse._SubParsersAction) -> None:
    p_ex = sub.add_parser("experiments", help="list/run/inspect registered experiments")
    ex = p_ex.add_subparsers(dest="exp_cmd", required=True)
    ex.add_parser("list", help="registered experiment ids")
    p_run = ex.add_parser("run", help="print how to run a registered experiment")
    p_run.add_argument("id")
    p_ins = ex.add_parser("inspect", help="print a registered spec or a manifest file")
    p_ins.add_argument("target")

    p_cj = sub.add_parser("conjectures", help="conjecture registry")
    cj = p_cj.add_subparsers(dest="conj_cmd", required=True)
    p_cjl = cj.add_parser("list", help="list conjectures")
    p_cjl.add_argument("--status", default="")
    p_cjs = cj.add_parser("show", help="show one conjecture")
    p_cjs.add_argument("id")

    p_lit = sub.add_parser("literature", help="literature registry")
    lit = p_lit.add_subparsers(dest="lit_cmd", required=True)
    lit.add_parser("list", help="list literature records")
    p_ls = lit.add_parser("show", help="show one record")
    p_ls.add_argument("id")

    sub.add_parser("formal", help="Lean toolchain / build hint")
    sub.add_parser("status", help="laboratory status summary")
    sub.add_parser("ui", help="launch the Streamlit laboratory")


def _dispatch(parser: argparse.ArgumentParser, args: argparse.Namespace) -> int:
    cmd = args.cmd
    if cmd in {"encode", "decode", "analyze", "residue", "test-invariants", "reverse", "reverse-tail"}:
        return _run_bt_leaf(cmd, args)
    if cmd == "bt":
        return _run_bt_leaf(args.bt_cmd, args)
    if cmd == "collatz":
        return run_collatz(args)
    if cmd == "operators":
        return run_operators(args)
    if cmd == "calculus":
        return run_calculus(args)
    if cmd == "congruence":
        return run_congruence(args)
    if cmd == "normalize":
        return run_normalize(args)
    if cmd == "research":
        return run_research(args)
    if cmd == "primes":
        from research.primes import sparse_primes

        print(sparse_primes(args.k, args.bound))
        return 0
    if cmd == "perfect-powers":
        from research.perfect_powers import sparse_cubes, sparse_squares, weight_one_squares

        if args.pp_cmd == "weight-one":
            print(weight_one_squares())
            return 0
        if args.pp_cmd == "squares":
            print(sparse_squares(args.k, int(args.bound**0.5)))
            return 0
        print(sparse_cubes(args.k, int(args.bound ** (1 / 3))))
        return 0
    if cmd == "additive":
        args.op_cmd = "additive"
        return run_operators(args)
    if cmd == "polynomials":
        args.op_cmd = "poly"
        return run_operators(args)
    if cmd == "experiments":
        return _run_experiments(args)
    if cmd == "conjectures":
        return _run_conjectures(args)
    if cmd == "literature":
        return _run_literature(args)
    if cmd == "formal":
        return _run_formal()
    if cmd == "status":
        return _run_status()
    if cmd == "ui":
        from visualization.app import launch

        return launch()
    parser.error(f"unknown command {cmd!r}")
    return 2


def _run_bt_leaf(cmd: str, args: argparse.Namespace) -> int:
    if cmd == "encode":
        print(encode(args.n).word())
        return 0
    if cmd == "decode":
        print(decode(args.word))
        return 0
    if cmd == "analyze":
        print(_analyze_text(args.n), end="")
        return 0
    if cmd == "residue":
        print(automaton_residue(args.word, args.modulus))
        return 0
    if cmd == "test-invariants":
        return _run_invariants(args.limit)
    if cmd == "reverse":
        print(bt_reverse(args.n))
        return 0
    if cmd == "reverse-tail":
        print(bt_reverse_tail(args.n))
        return 0
    raise ValueError(f"unknown bt command {cmd!r}")


def _analyze_text(n: int) -> str:
    word = encode(n)
    displayed = word.word()
    canonical = "yes" if is_canonical(displayed) else "no"
    assert decode(displayed) == n
    w = weight(word)
    lsd_nz = lsd_nonzero_index(word)
    val3 = v3(n)
    v3_display = "∞" if val3 is None else str(val3)
    lsd_display = "none" if lsd_nz is None else str(lsd_nz)
    prime = is_prime(n)
    lines = [
        f"Integer: {n}",
        f"Balanced ternary: {displayed}",
        f"Canonical: {canonical}",
        "",
        f"Weight: {w}",
        f"Weight parity: {w % 2}",
        f"Signed digit sum: {signed_digit_sum(word)}",
        "",
        f"v3(n): {v3_display}",
        f"Least significant nonzero digit position: {lsd_display}",
        "",
        f"Prime: {str(prime).lower()}",
        f"Factorization: {format_factorization(n)}",
        "",
        "Residues:",
    ]
    for q in (2, 3, 5, 7):
        lines.append(f"  mod {q}: {n % q}")
    lines.append("")
    return "\n".join(lines)


def _run_invariants(limit: int) -> int:
    print(f"Checking invariants for n in [{-limit}, {limit}] ...")
    report = verify_invariants(limit)
    print(f"Checked {report.checked} integers.")
    if report.ok:
        print("All invariants passed.")
        return 0
    print(f"FAILED with {len(report.failures)} failure(s). First:")
    f = report.failures[0]
    print(f"  {f.name} at n={f.n}: {f.detail}")
    return 1


def _run_experiments(args: argparse.Namespace) -> int:
    from cli.experiments import get_experiment, inspect_artifact, list_experiments

    if args.exp_cmd == "list":
        for spec in list_experiments():
            print(f"{spec.id}: {spec.name} [{spec.problem}]")
            print(f"  {spec.notes}")
        return 0
    if args.exp_cmd == "run":
        spec = get_experiment(args.id)
        print(f"{spec.id}: {spec.name}")
        print(spec.notes)
        print("This registry does not rewrite runners. Use the documented CLI.")
        return 0
    target = Path(args.target)
    if target.exists():
        print(inspect_artifact(target))
        return 0
    spec = get_experiment(args.target)
    print(f"{spec.id}: {spec.name}")
    print(f"problem: {spec.problem}")
    print(spec.notes)
    return 0


def _run_conjectures(args: argparse.Namespace) -> int:
    from research.conjectures import get_conjecture, list_conjectures

    if args.conj_cmd == "list":
        status = args.status or None
        for rec in list_conjectures(status=status):
            print(f"{rec['id']}: {rec['title']} [{rec['status']}]")
        return 0
    rec = get_conjecture(args.id)
    for key in ("id", "title", "status", "statement", "tested_range", "notes"):
        print(f"{key}: {rec.get(key)}")
    return 0


def _run_literature(args: argparse.Namespace) -> int:
    from research.literature import get_reference, list_references

    if args.lit_cmd == "list":
        for rec in list_references():
            print(f"{rec['id']}: {rec['title']} ({rec.get('year', '')})")
        return 0
    rec = get_reference(args.id)
    for key in ("id", "title", "authors", "year", "project_relationship", "notes"):
        print(f"{key}: {rec.get(key)}")
    return 0


def _run_formal() -> int:
    toolchain = Path(__file__).resolve().parents[2] / "formal" / "lean-toolchain"
    print("Lake package: balanced-ternary-formal")
    if toolchain.exists():
        print(f"toolchain: {toolchain.read_text(encoding='utf-8').strip()}")
    print("Build: python tools/lab.py build")
    print("The project contains no sorry or admit.")
    return 0


def _run_status() -> int:
    version = "0.2.2"
    try:
        from importlib.metadata import version as pkg_version

        version = pkg_version("balanced-ternary")
    except Exception:
        pass
    print(f"core version: {version}")
    print("tests: run `pytest` (not executed by status)")
    print("Lean: run `python tools/lab.py build`")
    try:
        from research.open_problems import list_problems

        problems = list_problems()
        print(f"active research problems: {len(problems)}")
        for problem in problems:
            print(f"  {problem.id}: {problem.status}")
    except Exception as exc:
        print(f"active research problems: unavailable ({exc})")
    try:
        from research.conjectures import list_conjectures

        recs = list_conjectures()
        active = [r for r in recs if r.get("status") in {"ACTIVE", "COMPUTATIONALLY_SUPPORTED"}]
        print(f"conjecture records: {len(recs)} (active/supported: {len(active)})")
    except Exception as exc:
        print(f"conjecture records: unavailable ({exc})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
