"""juggler-atlas CLI. Prints experiment_id, range, counts, checksum."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas import api
from research.juggler_sequence.atlas.storage import DEFAULT_DATA_DIR


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="juggler-atlas",
        description=(
            "Juggler word atlas. GPU discovery and host certification. "
            "Not a termination theorem and not a forbidden-factor claim."
        ),
    )
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=DEFAULT_DATA_DIR,
        help="atlas data directory",
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_build = sub.add_parser("build", help="run a trajectory census")
    p_build.add_argument("--k-max", type=int, default=12)
    p_build.add_argument("--n-max", type=int, default=1_000_000)
    p_build.add_argument("--n-begin", type=int, default=1)
    p_build.add_argument("--pe-n-max", type=int, default=None)
    p_build.add_argument(
        "--backend",
        choices=("auto", "cpu", "cuda", "native-cpu"),
        default="auto",
    )

    p_sci = sub.add_parser("science", help="scientific census and Markdown report")
    p_sci.add_argument("--k-max", type=int, default=20)
    p_sci.add_argument("--n-max", type=int, default=100_000_000)
    p_sci.add_argument("--pe-n-max", type=int, default=None)
    p_sci.add_argument("--r-max", type=int, default=8)
    p_sci.add_argument(
        "--backend",
        choices=("auto", "cpu", "cuda", "native-cpu"),
        default="cuda",
    )

    p_val = sub.add_parser("validate", help="three-way fixture validation")
    p_val.add_argument("--experiment-id")
    p_val.add_argument("--native-tsv", type=Path)

    p_fac = sub.add_parser("factors", help="factor complexity query")
    p_fac.add_argument("--language", required=True)
    p_fac.add_argument("--r", type=int, required=True)
    p_fac.add_argument("--experiment-id")

    p_cont = sub.add_parser("continuations", help="continuation histogram")
    p_cont.add_argument("--language", required=True)
    p_cont.add_argument("--experiment-id")

    p_bench = sub.add_parser("benchmark", help="time a small census")
    p_bench.add_argument("--k-max", type=int, default=8)
    p_bench.add_argument("--n-max", type=int, default=10_000)
    p_bench.add_argument(
        "--backend",
        choices=("auto", "cpu", "cuda", "native-cpu"),
        default="cpu",
    )

    p_harv = sub.add_parser(
        "harvest",
        help="first-descent leftover-class histogram (not an word-atlas recensus)",
    )
    p_harv.add_argument("--k-max", type=int, default=20)
    p_harv.add_argument("--n-max", type=int, default=400)
    p_harv.add_argument("--n-begin", type=int, default=2)
    p_harv.add_argument(
        "--backend",
        choices=("python", "cpu", "cuda"),
        default="python",
    )

    args = parser.parse_args(argv)
    if args.cmd == "build":
        payload = api.build(
            k_max=args.k_max,
            n_max=args.n_max,
            n_begin=args.n_begin,
            backend=args.backend,
            pe_n_max=args.pe_n_max,
            data_dir=args.data_dir,
        )
        _print_run(payload, args.data_dir)
        return 0
    if args.cmd == "science":
        from research.juggler_sequence.atlas.science import run_science

        report = run_science(
            k_max=args.k_max,
            n_max=args.n_max,
            pe_n_max=args.pe_n_max,
            backend=args.backend,
            data_dir=args.data_dir,
            r_max=args.r_max,
        )
        _print_run(
            {
                "experiment_id": report["experiment_id"],
                "k_max": report["k_max"],
                "n_max": report["n_max"],
                "configuration": {"r_max": args.r_max, "backend": args.backend},
                "search_limits": {"k_max": report["k_max"], "n_max": report["n_max"]},
                "record_counts": report.get("build", {}).get("record_counts"),
                "markdown_path": report.get("markdown_path"),
                "p_r": report.get("p_r"),
                "p_pe": report.get("p_pe"),
            },
            args.data_dir,
        )
        return 0
    if args.cmd == "validate":
        report = api.validate(
            experiment_id=args.experiment_id,
            data_dir=args.data_dir,
            native_tsv=args.native_tsv,
        )
        _print_run(report, args.data_dir)
        return 0 if report.get("ok") else 1
    if args.cmd == "factors":
        words = api.factor_set(
            args.language,
            args.r,
            experiment_id=args.experiment_id,
            data_dir=args.data_dir,
        )
        payload = {
            "experiment_id": args.experiment_id,
            "configuration": {"language": args.language, "r": args.r},
            "input_range": {"r": args.r},
            "output_location": str(args.data_dir),
            "record_counts": {"p_r": len(words)},
            "checksum": None,
            "factors": words,
        }
        _print_run(payload, args.data_dir)
        return 0
    if args.cmd == "continuations":
        rows = api.continuations(
            args.language,
            experiment_id=args.experiment_id,
            data_dir=args.data_dir,
        )
        payload = {
            "experiment_id": args.experiment_id or (rows[0]["experiment_id"] if rows else None),
            "configuration": {"language": args.language},
            "input_range": None,
            "output_location": str(args.data_dir),
            "record_counts": {"rows": len(rows)},
            "checksum": None,
            "histogram": rows,
        }
        _print_run(payload, args.data_dir)
        return 0
    if args.cmd == "harvest":
        from research.juggler_sequence.certificate_harvest import probe_payload

        payload = probe_payload(
            n_max=args.n_max,
            k_max=args.k_max,
            backend=args.backend,
            data_dir=args.data_dir,
        )
        _print_run(
            {
                "experiment_id": None,
                "k_max": args.k_max,
                "n_max": args.n_max,
                "backend": args.backend,
                "configuration": {"mode": "harvest", "n_begin": args.n_begin},
                "search_limits": {"n_begin": args.n_begin, "n_max": args.n_max},
                "record_counts": payload["scan"]["coarse"],
                "decision": payload["decision"],
            },
            args.data_dir,
        )
        return 0
    if args.cmd == "benchmark":
        payload = api.benchmark(
            k_max=args.k_max,
            n_max=args.n_max,
            backend=args.backend,
        )
        payload.update(
            {
                "experiment_id": None,
                "configuration": {"k_max": args.k_max, "n_max": args.n_max},
                "input_range": {"n_max": args.n_max, "k_max": args.k_max},
                "output_location": str(args.data_dir),
                "record_counts": {"realized": payload.get("realized")},
                "checksum": None,
            }
        )
        _print_run(payload, args.data_dir)
        return 0
    return 2


def _print_run(payload: dict[str, Any], data_dir: Path) -> None:
    checksums = payload.get("checksums")
    checksum = None
    if isinstance(checksums, dict) and checksums:
        checksum = checksums.get("manifest.json") or next(iter(checksums.values()))
    report = {
        "experiment_id": payload.get("experiment_id"),
        "configuration": {
            "k_max": payload.get("k_max"),
            "n_max": payload.get("n_max"),
            "backend": payload.get("backend"),
            "schema_version": payload.get("schema_version"),
            **(payload.get("configuration") or {}),
        },
        "input_range": payload.get("search_limits") or payload.get("input_range"),
        "output_location": payload.get("manifest_path") or str(data_dir),
        "record_counts": payload.get("record_counts"),
        "checksum": checksum or payload.get("checksum"),
    }
    extra = {
        k: payload[k]
        for k in (
            "ok",
            "errors",
            "claims",
            "factors",
            "histogram",
            "seconds",
            "native",
            "markdown_path",
            "p_r",
            "p_pe",
            "decision",
        )
        if k in payload
    }
    print(json.dumps(report | extra, indent=2, sort_keys=True))


if __name__ == "__main__":
    sys.exit(main())
