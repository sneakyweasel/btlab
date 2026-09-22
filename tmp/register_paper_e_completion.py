from pathlib import Path
import json

root = Path(__file__).resolve().parents[1]
path = root / "docs/theory/theorem_ledger.json"
rows = json.loads(path.read_text(encoding="utf-8"))
row = {
    "id": "J-paper-e-formal-notation-bridges",
    "tag": "EXACT — HUMAN PROOF",
    "statement": "Paper E's compatible-residue 2-adic code has the infinite sum over exactly its odd Juggler times, indexed by the number of earlier odd times; a telescoping remainder has norm at most 2^(-k), including finite or empty odd-time sets. Exact finite-source cylinder equality transfers all limiting-frequency statements. The eventual ordinary ancestor bound is proved with real exponent 21/25, and the fixed-grid hypotheses imply the logarithmic ceiling below 99/100. Every finite full binary prefix tree has fair mass and multiplier moment one. The minimal stopping words themselves have fair mass one and multiplier moment at most 3/4, with summability proved before regrouping by length. These close presentation gaps without adding a mathematical novelty claim. The six manuscript-facing declarations compile and their dependency audit uses only the standard kernel axioms. Theorem 4.1's equidistribution and actual modular-return family remain written, outside this module. Ledger retagging awaits advisory coverage review.",
    "source": "docs/problems/juggler_signed_collatz_paper.md",
    "lean": "Problems/Juggler/PaperECompletion.lean",
    "decl": [
        "code_hasSum_odd_times", "all_frequency_limits_iff",
        "ancestor_density_real", "certificate_log_ceiling",
        "full_prefix_tree_masses", "stopping_word_masses"
    ],
    "lean_trust": "kernel",
    "tests": [
        "tests/unit/test_paper_e_release.py",
        "tests/research/juggler_sequence/test_layer_architecture.py"
    ],
    "related_conjectures": []
}
assert not any(r["id"] == row["id"] for r in rows)
rows.insert(0, row)
path.write_text(json.dumps(rows, indent=1, ensure_ascii=False)+"\n", encoding="utf-8", newline="\n")
