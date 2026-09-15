"""Separate the three kinds of "surprising" proof and write a rating sheet of the rest.

usage: python tools/seed/rank_unusual.py [data/seed/proof_scores.csv]

The most surprising proofs in proof_scores.csv are of three kinds the surprise number does
not distinguish:

* template   the first proof of a family; later proofs in the same file copy it nearly
             verbatim and score near zero
* certificate a short computation: decide, norm_num, or a numeral-heavy body
* unusual    neither, which is the class a reader should judge

This script tags every scored proof, prints how the top of the ranking splits, writes
data/seed/proof_kinds.csv, and writes data/seed/rating_sheet.md with the twenty most
surprising unusual proofs, statement and proof included, for a human to rate.
"""
from __future__ import annotations

import csv
import difflib
import json
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SEED = ROOT / "data" / "seed" / "seed.jsonl"
COPY_THRESHOLD = 0.05         # mean surprise below this = near-verbatim copy
TEMPLATE_SIMILARITY = 0.80    # difflib ratio for "this copy came from that proof"
MIN_TOKENS = 12


def load(scores_path):
    rows = list(csv.DictReader(open(scores_path, encoding="utf-8")))
    proofs = {}
    for line in open(SEED, encoding="utf-8"):
        r = json.loads(line)
        proofs[r["name"]] = r
    return rows, proofs


def is_certificate(r, proof_text):
    digits = sum(c.isdigit() for c in proof_text) / max(1, len(proof_text))
    short = int(r["n_tokens"]) < 60
    return (r["first_tactic"] in ("decide", "norm_num") and short) or digits > 0.12


def find_templates(rows, proofs):
    """For every near-copy, the earlier proof in the same file it most resembles."""
    by_file = defaultdict(list)
    for r in rows:
        by_file[r["file"]].append(r)
    templates = set()
    for file, rs in by_file.items():
        rs.sort(key=lambda r: int(r["line"]))
        for i, r in enumerate(rs):
            if float(r["mean_surprise"]) >= COPY_THRESHOLD:
                continue
            text = proofs[r["name"]]["proof"]
            best, best_ratio = None, 0.0
            for q in rs[:i]:
                ratio = difflib.SequenceMatcher(None, text, proofs[q["name"]]["proof"]).ratio()
                if ratio > best_ratio:
                    best, best_ratio = q, ratio
            if best is not None and best_ratio >= TEMPLATE_SIMILARITY:
                templates.add(best["name"])
    return templates


def main(scores_path):
    rows, proofs = load(scores_path)
    templates = find_templates(rows, proofs)
    for r in rows:
        text = proofs[r["name"]]["proof"]
        if float(r["mean_surprise"]) < COPY_THRESHOLD:
            r["kind"] = "copy"
        elif r["name"] in templates:
            r["kind"] = "template"
        elif is_certificate(r, text):
            r["kind"] = "certificate"
        else:
            r["kind"] = "unusual"
    out = ROOT / "data" / "seed" / "proof_kinds.csv"
    with open(out, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    rankable = [r for r in rows if int(r["n_tokens"]) >= MIN_TOKENS and not int(r["truncated"])]
    rankable.sort(key=lambda r: -float(r["mean_surprise"]))
    counts = defaultdict(int)
    for r in rows:
        counts[r["kind"]] += 1
    print("all proofs:", dict(counts))
    for n in (20, 50, 100):
        c = defaultdict(int)
        for r in rankable[:n]:
            c[r["kind"]] += 1
        print(f"top {n} by surprise:", dict(c))

    unusual = [r for r in rankable if r["kind"] == "unusual"][:20]
    lines = ["# Rating sheet: the twenty most surprising proofs that are not copies, templates "
             "or certificates", "",
             "Mark each: **routine** (I'd have written this), **neat** (a move I'd remember), "
             "or **wrong-list** (this is a template or certificate the filter missed).", ""]
    for i, r in enumerate(unusual, 1):
        p = proofs[r["name"]]
        proof_lines = p["proof"].strip("\n").splitlines()
        shown = "\n".join(proof_lines[:14]) + ("\n  ..." if len(proof_lines) > 14 else "")
        lines += [f"## {i}. `{r['name']}`  ({r['file']}:{r['line']})",
                  f"mean surprise {float(r['mean_surprise']):.2f} nats/token, "
                  f"{r['n_tokens']} tokens, first tactic `{r['first_tactic']}`", "",
                  "```lean", p["statement"].strip(), shown, "```", "", "Rating: ", ""]
    (ROOT / "data" / "seed" / "rating_sheet.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"\nrating sheet: {len(unusual)} proofs -> data/seed/rating_sheet.md")
    print("\nTOP 20 UNUSUAL (mean surprise, tokens, first tactic, name)")
    for r in unusual:
        print(f"  {float(r['mean_surprise']):5.2f} {int(r['n_tokens']):5d}  {r['first_tactic']:10} "
              f"{r['name']}")
    print("\nTOP 10 BY INCONGRUITY (confident and wrong), unusual only")
    inc = sorted((r for r in rankable if r["kind"] == "unusual"),
                 key=lambda r: -float(r["max_incongruity"]))[:10]
    for r in inc:
        print(f"  {float(r['max_incongruity']):5.2f} {int(r['n_tokens']):5d}  {r['first_tactic']:10} "
              f"{r['name']}")


if __name__ == "__main__":
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "data" / "seed" / "proof_scores.csv")
