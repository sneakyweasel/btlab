"""Compare the header-only and file-prefix scorings of the same proofs.

usage: python tools/seed/compare_setups.py

The file-prefix setup shows the model the 1536 tokens of the file before the declaration;
the header-only setup shows only opens, namespaces and variables. The difference per proof
is how much of its surprise was about names and definitions made earlier in the same file.
Prints the rank correlation of the two scorings, the mean drop, the proofs that gain most
from seeing the file (the most file-dependent), and the proofs that gain nothing (surprising
regardless of what the file says, which is the residue that might be called elegance).
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import numpy as np  # noqa: E402

from stats import spearman  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
PREFIX = ROOT / "data" / "seed" / "proof_scores.csv"
HEADER = ROOT / "data" / "seed" / "proof_scores_header.csv"
KINDS = ROOT / "data" / "seed" / "proof_kinds.csv"


def main():
    prefix = {r["name"]: r for r in csv.DictReader(open(PREFIX, encoding="utf-8"))}
    header = {r["name"]: r for r in csv.DictReader(open(HEADER, encoding="utf-8"))}
    kinds = {r["name"]: r["kind"] for r in csv.DictReader(open(KINDS, encoding="utf-8"))}
    names = [n for n in prefix if n in header
             and int(prefix[n]["n_tokens"]) >= 12 and not int(prefix[n]["truncated"])]
    p = np.array([float(prefix[n]["mean_surprise"]) for n in names])
    h = np.array([float(header[n]["mean_surprise"]) for n in names])
    print(f"{len(names)} proofs scored both ways")
    print(f"mean surprise: header-only {h.mean():.3f}, file-prefix {p.mean():.3f} nats/token; "
          f"median drop {np.median(h - p):.3f}")
    print(f"Spearman(header, prefix) = {spearman(h, p):.3f}")
    drop = h - p
    order = np.argsort(-drop)
    print("\nMOST FILE-DEPENDENT (surprise the file prefix removes)")
    for i in order[:15]:
        n = names[i]
        print(f"  {drop[i]:5.2f}  {h[i]:5.2f} -> {p[i]:5.2f}  {kinds.get(n, '?'):11} {n}")
    print("\nSURPRISING REGARDLESS (high with the prefix, and the prefix removed little)")
    resid = [(p[i], drop[i], names[i]) for i in range(len(names))
             if kinds.get(names[i]) == "unusual"]
    resid.sort(key=lambda t: -(t[0] - 0.5 * max(t[1], 0)))
    for pv, d, n in resid[:15]:
        print(f"  prefix {pv:5.2f}  removed {d:5.2f}  {n}")
    print("\nSHARE OF SURPRISE EXPLAINED BY THE FILE, BY KIND")
    for kind in ("unusual", "template", "certificate", "copy"):
        idx = [i for i, n in enumerate(names) if kinds.get(n) == kind]
        if idx:
            hh, pp = h[idx], p[idx]
            print(f"  {kind:11} n={len(idx):4d}  header {hh.mean():5.2f}  prefix {pp.mean():5.2f}  "
                  f"explained {(1 - pp.mean() / max(hh.mean(), 1e-6)):5.1%}")


if __name__ == "__main__":
    main()
