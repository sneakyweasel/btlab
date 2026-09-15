"""Where in a proof does the surprise sit: on lemma names, on tactics, or on structure?

usage: python tools/seed/surprise_by_token.py [N] [data/seed/proof_kinds.csv]

Re-scores the N most surprising "unusual" proofs and N proofs from the middle of the ranking
with the file-prefix setup, keeps the per-token surprise, and sorts every token into one of
five classes: identifier (a name that is not a tactic keyword), tactic keyword, numeral,
structure (punctuation, brackets, arrows), and whitespace. Prints, for each group, the share
of total surprise carried by each class and the mean surprise per token of each class. If
the top proofs are surprising because of which lemma they call, the identifier class will
carry most of their surprise and little of the middle group's.
"""
from __future__ import annotations

import csv
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import numpy as np  # noqa: E402

from lm import tok, token_stats  # noqa: E402
from score_proofs import MAX_PROOF_TOKENS, setup_text  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
SEED = ROOT / "data" / "seed" / "seed.jsonl"
TACTICS = set("""
simp simpa rw rwa exact refine have obtain intro intros unfold cases rcases rintro induction
omega linarith nlinarith norm_num decide apply constructor ext ring ring_nf calc by_contra
by_cases set let use exists show suffices specialize subst symm trans positivity field_simp
push_cast norm_cast exact_mod_cast congr gcongr funext generalize wlog interval_cases fin_cases
contradiction exfalso trivial rfl aesop tauto left right and_intro split_ifs split at with
using only fun match this at_h assumption change clear revert classical nofun nomatch native_decide
""".split())
IDENT = re.compile(r"^\s*[A-Za-z_][A-Za-z0-9_'.!?]*$")
NUMERAL = re.compile(r"^\s*\d+$")


def classify(token: str) -> str:
    if token.strip() == "":
        return "whitespace"
    if NUMERAL.match(token):
        return "numeral"
    if IDENT.match(token):
        return "tactic" if token.strip() in TACTICS else "identifier"
    return "structure"


def per_class(records):
    total = defaultdict(float)
    count = defaultdict(int)
    for r in records:
        proof = r["proof"]
        ids = tok.encode(proof, add_special_tokens=False)
        if len(ids) > MAX_PROOF_TOKENS:
            proof = tok.decode(ids[:MAX_PROOF_TOKENS])
        s, _, _, toks = token_stats(setup_text(r, header_only=False), proof)
        for value, t in zip(s.tolist(), toks):
            c = classify(t)
            total[c] += value
            count[c] += 1
    grand = sum(total.values())
    return {c: (total[c] / grand, total[c] / max(1, count[c]), count[c]) for c in total}


def main(n, kinds_path):
    rows = list(csv.DictReader(open(kinds_path, encoding="utf-8")))
    proofs = {json.loads(l)["name"]: json.loads(l) for l in open(SEED, encoding="utf-8")}
    rankable = [r for r in rows if int(r["n_tokens"]) >= 12 and not int(r["truncated"])]
    rankable.sort(key=lambda r: -float(r["mean_surprise"]))
    unusual = [r for r in rankable if r["kind"] == "unusual"]
    top = unusual[:n]
    mid_start = len(unusual) // 2 - n // 2
    middle = unusual[mid_start:mid_start + n]
    for label, group in (("TOP", top), ("MIDDLE", middle)):
        stats = per_class([proofs[r["name"]] for r in group])
        print(f"\n{label} {len(group)} unusual proofs: share of surprise / mean nats per token / tokens")
        for c in ("identifier", "tactic", "numeral", "structure", "whitespace"):
            share, mean, cnt = stats.get(c, (0.0, 0.0, 0))
            print(f"  {c:11} {share:6.1%}   {mean:5.2f}   {cnt:6d}")


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 200
    path = Path(sys.argv[2]) if len(sys.argv) > 2 else ROOT / "data" / "seed" / "proof_kinds.csv"
    main(n, path)
