"""Audit paper numerics through a fresh, real Arb MCP stdio connection.

Writes separate reports and actual-run manifests. The service performs all
transcendental evaluations; this client uses integers/Fractions for enumeration
and enclosure bookkeeping. Publication sources and releases are not modified.
"""
from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
from pathlib import Path
import sys

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from arb_paper_audit_core.client import Audit
from research.experiments.provenance import write_manifest

PAPERS = {
    "A": ("juggler", "juggler_finite_dynamics_note.md"),
    "B": ("juggler", "juggler_parity_discrepancy_note.md"),
    "C": ("juggler", "juggler_fate_almost_all_note.md"),
    "D": ("collatz", "collatz_3n_minus_1_m_cycles_note.md"),
    "E": ("collatz", "juggler_signed_collatz_note.md"),
    "Beatty": ("juggler", "juggler_beatty_first_passage_note.md"),
}


async def run(args):
    from arb_paper_audit_core.paper_a import paper_a
    from arb_paper_audit_core.scalars import paper_b, paper_c, paper_e
    functions = {"A": paper_a, "B": paper_b, "C": paper_c, "E": paper_e}
    if "D" in args.paper:
        from arb_paper_audit_core.paper_d import paper_d
        functions["D"] = paper_d
    if "Beatty" in args.paper:
        from arb_paper_audit_core.beatty import beatty
        functions["Beatty"] = beatty
    params = StdioServerParameters(command=sys.executable, args=["-B", str(ROOT / "tools/arb_mcp.py")],
                                   env={"PYTHONUTF8": "1", "PYTHONDONTWRITEBYTECODE": "1"})
    logdir = args.output_root / ".build/arb-paper-audit"
    logdir.mkdir(parents=True, exist_ok=True)
    with (logdir / ("server-" + "-".join(args.paper) + ".log")).open("w", encoding="utf-8") as err:
        async with stdio_client(params, errlog=err) as (read, write):
            async with ClientSession(read, write) as session:
                await session.initialize()
                caps = await session.call_tool("arb_capabilities", {})
                if caps.isError or Path(caps.structuredContent["root"]).resolve() != ROOT:
                    raise RuntimeError("MCP did not bind this checkout")
                semaphore = asyncio.Semaphore(2)
                for paper in args.paper:
                    programme, note = PAPERS[paper]
                    note_path = ROOT / "docs/theory" / note
                    sources = [Path(__file__), *sorted((ROOT / "tools/arb_paper_audit_core").glob("*.py")),
                               ROOT / "tools/arb_mcp.py", ROOT / "tools/arb_worker.py",
                               ROOT / "src/research_engine/arb_expressions.py", ROOT / "src/research_engine/intervals.py"]
                    inputs = [note_path]
                    if paper == "D":
                        inputs.append(ROOT / "data/research/juggler/negative_m_cycles/summary.json")
                    if paper == "C":
                        sources.append(ROOT / "tools/check_paper_c_intervals.py")
                    def hashes():
                        return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in [*sources, *inputs]}
                    before = hashes()
                    start_hash = hashlib.sha256(note_path.read_bytes()).hexdigest()
                    audit = Audit(session, semaphore)
                    print(f"Starting {paper} through Arb MCP", flush=True)
                    summary = await functions[paper](audit)
                    if hashes() != before:
                        raise RuntimeError(f"Paper {paper} inputs changed during the run; rerun")
                    for call in audit.calls.values():
                        for path, digest in call["result"]["source_sha256"].items():
                            if before[path] != digest:
                                raise RuntimeError(f"MCP source changed during Paper {paper}: {path}")
                    end_hash = hashlib.sha256(note_path.read_bytes()).hexdigest()
                    payload = {"schema": "btlab.paper-arb-audit.v1", "paper": paper,
                               "transport": "MCP stdio via tools/arb_mcp.py",
                               "scope": "Finite expression certificates and explicitly stated derived consequences; no new Lean proof or termination result.",
                               "paper_source_sha256": {"before": start_hash, "after": end_hash},
                               "paper_unchanged_during_run": start_hash == end_hash,
                               "input_source_sha256": before,
                               "summary": summary, "mcp_call_count": len(audit.calls),
                               "checks": dict(sorted(audit.calls.items()))}
                    output = args.output_root / f"data/research/{programme}/arb_paper_audit/{paper.lower()}.json"
                    output.parent.mkdir(parents=True, exist_ok=True)
                    output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8", newline="\n")
                    write_manifest(output.with_suffix(".research.json"), programme=programme,
                                   scope=f"Paper {paper}: {summary['progress']}", outputs=[output],
                                   inputs=inputs, sources=sources,
                                   parameters={"paper": paper, "transport": "MCP stdio", "default_precision_bits": 256},
                                   command=["python", "tools/check_papers_arb.py", "--paper", paper,
                                            "--output-root", "." if args.output_root == ROOT else str(args.output_root)])
                    print(json.dumps({"paper": paper, "mcp_calls": len(audit.calls),
                                      "progress": summary["progress"], "output": str(output)}, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", nargs="+", choices=list(PAPERS), default=list(PAPERS))
    parser.add_argument("--output-root", type=Path, default=ROOT)
    args = parser.parse_args()
    args.output_root = args.output_root.resolve()
    asyncio.run(run(args))


if __name__ == "__main__":
    main()
