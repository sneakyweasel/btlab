"""Score every seed proof by a language model's surprise, given its statement.

usage: python tools/seed/score_proofs.py [N] [--out data/seed/proof_scores.csv] [--header-only]

For each tactic-mode record in ``data/seed/seed.jsonl`` the setup is, by default, the last
MAX_PREFIX_TOKENS tokens of the source file before the declaration (so definitions and
lemma names made earlier in the file are visible), then the docstring and the statement up
to ``:= by``. With ``--header-only`` the setup is only the header context the extractor
recorded (opens, namespaces, variables), which measures how much of the proof needed names
the statement alone does not give. The punch is the proof. Per record:

* ``n_tokens``            proof length in tokens (proofs are cut at MAX_PROOF_TOKENS)
* ``surprise_given``      total surprise (nats) of the proof given the setup
* ``mean_surprise``       the same per token
* ``surprise_alone``      total surprise of the proof with no setup
* ``pmi``                 surprise_alone - surprise_given: how much the setup earns the proof
* ``mean_pmi``            the same per token (total pmi is almost pure length)
* ``max_incongruity``     max over tokens of surprise minus entropy: confident and wrong
* ``first_step_surprise`` surprise of the first tactic word given the setup: the opening move
* ``max_rank``            rank of the least expected token among the vocabulary

The summary checks the length confound (Spearman of the per-token measures with length)
and lists the most and least surprising proofs among those long enough to mean anything.
No training happens here. The kernel has already accepted every record; this only asks
how far each proof was from obvious.
"""
from __future__ import annotations

import csv
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import numpy as np  # noqa: E402

from lm import TAG, tok, token_stats  # noqa: E402
from stats import spearman  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
SEED = ROOT / "data" / "seed" / "seed.jsonl"
MAX_PROOF_TOKENS = 1024
MAX_PREFIX_TOKENS = 1536
MIN_TOKENS_FOR_RANKING = 12
_FILES: dict[str, list[str]] = {}


def file_prefix(r: dict) -> str:
    """The source file up to the declaration, cut to its last MAX_PREFIX_TOKENS tokens."""
    if r["file"] not in _FILES:
        _FILES[r["file"]] = (ROOT / r["file"]).read_text(encoding="utf-8").splitlines()
    start = int(r["span"][0]) if isinstance(r["span"], list) else int(json.loads(r["span"])[0])
    text = "\n".join(_FILES[r["file"]][: start - 1])
    ids = tok.encode(text, add_special_tokens=False)
    if len(ids) > MAX_PREFIX_TOKENS:
        text = tok.decode(ids[-MAX_PREFIX_TOKENS:])
    return text


def setup_text(r: dict, header_only: bool) -> str:
    parts = [r["context"]] if header_only else [file_prefix(r)]
    parts = [p for p in parts if p]
    if r["doc"] and header_only:
        parts.append(f"/-- {r['doc']} -/")
    parts.append(r["statement"])
    return "\n".join(parts)


def score(r: dict, header_only: bool) -> dict | None:
    proof = r["proof"]
    ids = tok.encode(proof, add_special_tokens=False)
    truncated = len(ids) > MAX_PROOF_TOKENS
    if truncated:
        proof = tok.decode(ids[:MAX_PROOF_TOKENS])
    s_g, h_g, rank, toks = token_stats(setup_text(r, header_only), proof)
    if len(toks) == 0:
        return None
    s_0, _, _, _ = token_stats("", proof)
    first = next((i for i, t in enumerate(toks) if t.strip()), 0)
    n = len(toks)
    return {
        "name": r["name"],
        "module": r["module"],
        "file": r["file"],
        "line": r["line"],
        "first_tactic": r["first_tactic"],
        "n_tokens": n,
        "truncated": int(truncated),
        "surprise_given": s_g.sum().item(),
        "mean_surprise": s_g.mean().item(),
        "surprise_alone": s_0.sum().item(),
        "pmi": (s_0.sum() - s_g.sum()).item(),
        "mean_pmi": (s_0.sum() - s_g.sum()).item() / n,
        "max_incongruity": (s_g - h_g).max().item(),
        "first_step_surprise": s_g[first].item(),
        "max_rank": int(rank.max().item()),
    }


def write_progress(job: str, done: int, total: int, rate, finished: bool = False) -> None:
    """A small JSON that narrowing/progress.py renders as a bar."""
    p = {"job": job, "unit": "proofs", "done": done, "total": total, "finished": finished,
         "updated": time.strftime("%H:%M:%S")}
    if rate:
        p["rate_per_min"] = rate * 60
        p["eta_min"] = (total - done) / rate / 60
    (ROOT / "data" / "seed" / "progress.json").write_text(json.dumps(p), encoding="utf-8")


def summary(rows: list[dict], header_only: bool) -> str:
    long = [x for x in rows if x["n_tokens"] >= MIN_TOKENS_FOR_RANKING and not x["truncated"]]
    mode = "header-only setup" if header_only else "file-prefix setup"
    out = [f"{len(rows)} proofs scored with {TAG}, {mode}; {len(long)} with at least "
           f"{MIN_TOKENS_FOR_RANKING} tokens and not truncated",
           f"Spearman(mean_surprise, n_tokens) = "
           f"{spearman([x['mean_surprise'] for x in rows], [x['n_tokens'] for x in rows]):.3f}",
           f"Spearman(mean_pmi, n_tokens) = "
           f"{spearman([x['mean_pmi'] for x in rows], [x['n_tokens'] for x in rows]):.3f}",
           f"median mean_surprise = {np.median([x['mean_surprise'] for x in rows]):.3f} nats/token",
           f"median mean_pmi = {np.median([x['mean_pmi'] for x in rows]):.3f} nats/token",
           ""]

    def block(title, key, reverse, n=20):
        out.append(title)
        for x in sorted(long, key=lambda x: x[key], reverse=reverse)[:n]:
            out.append(f"  {x[key]:7.3f}  {x['n_tokens']:5d} tok  {x['first_tactic']:10} "
                       f"{x['name']}  ({x['file']}:{x['line']})")
        out.append("")

    block("MOST SURPRISING PROOFS (mean surprise per token, given the setup)",
          "mean_surprise", True)
    block("MOST INEVITABLE PROOFS (lowest mean surprise)", "mean_surprise", False)
    block("PROOFS THE SETUP EARNS MOST (mean pmi per token)", "mean_pmi", True)
    block("PROOFS THE SETUP EARNS LEAST (lowest mean pmi)", "mean_pmi", False)
    block("BOLDEST OPENING MOVES (surprise of the first tactic word)",
          "first_step_surprise", True)
    by_tactic: dict[str, list[float]] = {}
    for x in rows:
        by_tactic.setdefault(x["first_tactic"], []).append(x["mean_surprise"])
    out.append("MEAN SURPRISE BY FIRST TACTIC (n >= 20)")
    for t, v in sorted(by_tactic.items(), key=lambda kv: -np.mean(kv[1])):
        if len(v) >= 20:
            out.append(f"  {np.mean(v):6.3f}  n={len(v):4d}  {t}")
    return "\n".join(out)


def main() -> None:
    header_only = "--header-only" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("--") and a.isdigit()]
    n = int(args[0]) if args else None
    out_path = ROOT / "data" / "seed" / "proof_scores.csv"
    if "--out" in sys.argv:
        out_path = Path(sys.argv[sys.argv.index("--out") + 1])
    records = [json.loads(line) for line in open(SEED, encoding="utf-8")]
    if n:
        records = records[:n]
    rows, t0 = [], time.time()
    job = "proof scoring (header)" if header_only else "proof scoring (prefix)"
    for i, r in enumerate(records):
        x = score(r, header_only)
        if x:
            rows.append(x)
        if (i + 1) % 50 == 0:
            rate = (i + 1) / (time.time() - t0)
            write_progress(job, i + 1, len(records), rate)
            print(f"  {i + 1}/{len(records)}  {rate:.1f}/s  "
                  f"eta {(len(records) - i - 1) / rate / 60:.1f} min", file=sys.stderr, flush=True)
    write_progress(job, len(records), len(records), None, finished=True)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    text = summary(rows, header_only)
    out_path.with_suffix(".summary.txt").write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
