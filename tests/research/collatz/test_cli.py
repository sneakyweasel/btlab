"""CLI smoke tests for ``btlab collatz ...``."""

from __future__ import annotations

import io
import json
from contextlib import redirect_stdout
from pathlib import Path

import pytest

from cli.main import main
from bt.representation import encode
from research.collatz.core import collatz_step
from research.experiments import paths


def _run(*args: str) -> str:
    buf = io.StringIO()
    with redirect_stdout(buf):
        code = main(list(args))
    assert code == 0
    return buf.getvalue()


@pytest.mark.parametrize("arguments, subdirectory", [
    (("dual-dataset", "--length", "1", "--max-k", "2"), "raw"),
    (("complexity", "--k-max", "1"), "reports"),
])
def test_write_uses_source_checkout_from_another_directory(
    tmp_path, monkeypatch, arguments, subdirectory
):
    checkout = tmp_path / "selected checkout"
    source = checkout / "src/research/experiments/paths.py"
    source.parent.mkdir(parents=True)
    source.touch()
    monkeypatch.setattr(paths, "__file__", str(source))
    elsewhere = tmp_path / "unrelated directory"
    elsewhere.mkdir()
    monkeypatch.chdir(elsewhere)

    output = checkout / "data/research/collatz"
    _run("collatz", *arguments)
    assert not output.exists()
    _run("collatz", *arguments, "--write")
    assert list((output / subdirectory).glob("*.json"))
    assert not list(elsewhere.iterdir())
    assert not (checkout / "experiments").exists()
    for manifest in output.glob("raw/*_manifest.json"):
        payload = json.loads(manifest.read_text(encoding="utf-8"))
        for artifact in payload["artifacts"].values():
            if artifact:
                assert Path(artifact).is_relative_to(output)
                assert Path(artifact).is_file()


def test_collatz_analyze_27():
    out = _run("collatz", "analyze", "27")
    word = encode(27).word()
    assert "n = 27" in out
    assert f"BT(n) = {word}" in out
    assert "T(n) = 41" in out
    assert f"BT(T(n)) = {encode(41).word()}" in out
    assert "v2(3n+1) = 1" in out
    assert "shift-then-add-one matches BT(3n+1): true" in out
    assert "BT(3n+1) = BT(n)+  (append-plus theorem): true" in out
    assert "delta=" in out


def test_collatz_trajectory_27():
    out = _run("collatz", "trajectory", "27", "--max-steps", "5")
    assert "Accelerated trajectory of 27" in out
    assert str(collatz_step(27)) in out
    assert "values:" in out


def test_collatz_inverse_one():
    out = _run("collatz", "inverse", "1", "--depth", "2", "--k-max", "10")
    assert "root=1" in out
    assert "cycle k=2 -> 1" in out
    assert "5" in out


def test_collatz_test_invariants():
    out = _run("collatz", "test-invariants", "--limit", "300")
    assert "All invariants passed." in out
    assert "Checked 150 odd integers." in out


def test_collatz_automaton():
    out = _run("collatz", "automaton", "--precision", "4")
    assert "precision K=4" in out
    assert "modulus=2^4=16" in out
    assert "AT_LEAST_K" in out
    assert "Path for word" in out
    assert "odd residues" in out


def test_collatz_theorems():
    out = _run("collatz", "theorems", "27")
    assert "BT(n)+" in out
    assert "append_plus matches encode(3n+1): true" in out


def test_collatz_odd_part():
    out = _run("collatz", "odd-part", "82")
    assert "v2(x) = 1" in out
    assert "BT(odd-part)" in out


def test_collatz_transducer():
    out = _run("collatz", "transducer", "--k", "2", "--limit", "80")
    assert "naive_bound=9" in out
    assert "ok" in out


def test_collatz_valuation_shift():
    out = _run(
        "collatz", "valuation-shift",
        "--precision", "6", "--k-max", "4", "--length", "3",
    )
    assert "Admissible valuation prefixes" in out
    assert "contracting=" in out


def test_collatz_joint():
    out = _run(
        "collatz", "joint",
        "--limit", "50", "--k-max", "4", "--precision", "6",
        "--pattern-length", "1", "--sync-length", "1",
    )
    assert "Joint digit/valuation graph" in out
    assert "images ≡ 0 (mod 3): 0" in out


def test_collatz_cylinder():
    out = _run("collatz", "cylinder", "--ks", "1,1")
    assert "ks=(1, 1)" in out
    assert "matches Haar" in out
    assert "admissible: true" in out


def test_collatz_entropy():
    out = _run("collatz", "entropy", "--ks", "1", "--length", "4")
    assert "H_L (base 3)" in out
    assert "COMPUTATIONALLY VERIFIED" in out


def test_collatz_complexity():
    out = _run("collatz", "complexity", "--k-max", "3")
    assert "N_k" in out
    assert "CONJECTURE" in out


def test_collatz_symbolic_graph():
    out = _run(
        "collatz", "symbolic-graph",
        "--max-length", "2", "--k-max", "3",
    )
    assert "Symbolic Collatz futures" in out
    assert "nodes=" in out


def test_collatz_itinerary():
    out = _run("collatz", "itinerary", "1,2")
    assert "Valuation itinerary" in out
    assert "EXACT" in out
    assert "C=" in out


def test_collatz_realizer():
    out = _run("collatz", "realizer", "1,1")
    assert "R=7" in out or "R=7 " in out
    assert "Nested cylinders" in out


def test_collatz_permutations():
    out = _run("collatz", "permutations", "1,2")
    assert "C_min" in out
    assert "C extremal are sorted" in out


def test_collatz_fixed_budget():
    out = _run("collatz", "fixed-budget", "--length", "3", "--sum-k", "5")
    assert "Fixed (m,K)" in out
    assert "R varies across compositions" in out


def test_collatz_zero_lift():
    out = _run(
        "collatz",
        "zero-lift",
        "--ks",
        "1",
        "--steps",
        "2",
        "--candidate-k",
        "2",
        "--precision",
        "3",
    )
    assert "lift_digits=" in out
    assert "finite lift certificate" in out
    assert "Deterministic zero-lift successor trace" in out
    assert "accelerated Collatz orbit of R" in out


def test_collatz_periodic_itinerary():
    out = _run("collatz", "periodic-itinerary", "2")
    assert "compatible=true" in out
    assert "n=1" in out


def test_collatz_zero_lift_census():
    out = _run(
        "collatz",
        "zero-lift-census",
        "--max-length",
        "2",
        "--max-k",
        "3",
        "--precision",
        "3",
    )
    assert "mismatches=0" in out
    assert "OBSERVATION" in out


def test_collatz_dual_code():
    out = _run("collatz", "dual-code", "1,4,2")
    assert "Collatz dual code" in out
    assert "lift_digits=" in out
    assert "reconstruction=" in out


def test_collatz_lift_tree():
    out = _run(
        "collatz",
        "lift-tree",
        "--max-depth",
        "2",
        "--max-k",
        "3",
    )
    assert "Cylinder lift tree" in out
    assert "ZERO_LIFT" in out
    assert "valid finite extensions" in out


def test_collatz_periodic_dual():
    out = _run("collatz", "periodic-dual", "2", "--repeats", "3")
    assert "Periodic dual-code trace" in out
    assert "infinite compatibility=True" in out


def test_collatz_suffix_test():
    out = _run(
        "collatz",
        "suffix-test",
        "--max-length",
        "2",
        "--max-k",
        "3",
        "--suffix-max",
        "3",
    )
    assert "suffix determination" in out
    assert "REFUTED" in out


def test_collatz_dual_dataset_no_write():
    out = _run(
        "collatz",
        "dual-dataset",
        "--length",
        "2",
        "--max-k",
        "3",
    )
    assert "rows=9" in out
    assert "no files written" in out


def test_collatz_four_coordinate_compatibility():
    out = _run("collatz", "compatibility", "1,4,2")
    assert "Four-coordinate exponent-code diagnostic" in out
    assert "Kramer r=" in out
    assert "Kramer M=" in out
    assert "[EXACT]" in out


def test_collatz_compatibility_graph():
    out = _run(
        "collatz",
        "compatibility-graph",
        "--max-depth",
        "2",
        "--max-k",
        "2",
    )
    assert "nodes=7 edges=6" in out
    assert "valid=True" in out


def test_collatz_rational_base():
    out = _run("collatz", "rational-base", "7")
    assert "base_3/2=2122" in out
    assert "odd (3n+1)/2 appends 1: True" in out


def test_collatz_information_content():
    out = _run(
        "collatz",
        "information-test",
        "--max-length",
        "2",
        "--max-k",
        "4",
        "--precision-max",
        "2",
    )
    assert "S1 determines BT(R)=True" in out
    assert "H_BT strong independence: REFUTED EXACTLY" in out


def test_collatz_near_critical():
    out = _run(
        "collatz",
        "near-critical",
        "--max-length",
        "2",
        "--max-k",
        "3",
        "--random-length",
        "8",
        "--random-count",
        "3",
        "--seed",
        "17",
    )
    assert "Near-critical four-coordinate dataset" in out
    assert "seed=17" in out
    assert "OBSERVATIONS" in out


def test_collatz_affine_center():
    out = _run("collatz", "affine-center", "1", "--critical-gap", "1")
    assert "Affine-center geometry" in out
    assert "C=1  R=3  X=5  M=2" in out
    assert "2^K-3^m=-1" in out
    assert "n*=-1/1" in out
    assert "all exact inequalities=True" in out


def test_collatz_affine_center_census():
    out = _run(
        "collatz",
        "affine-center-census",
        "--max-length",
        "2",
        "--max-k",
        "3",
        "--critical-gap",
        "1",
        "--closest-count",
        "3",
    )
    assert "Affine-center census" in out
    assert "rows=12" in out
    assert "theorem-backed inequality failures=0" in out


def test_collatz_fixed_integer():
    out = _run("collatz", "fixed-integer", "7", "--max-steps", "4")
    assert "Fixed-integer affine geometry of n=7" in out
    assert "G=" in out
    assert "regime=" in out


def test_collatz_fixed_integer_census():
    out = _run(
        "collatz",
        "fixed-integer-census",
        "--limit",
        "20",
        "--max-steps",
        "10",
    )
    assert "Fixed-integer affine census" in out
    assert "n_*<=n failure count=" in out


def test_collatz_affine_gap():
    out = _run("collatz", "affine-gap", "7", "--max-steps", "3")
    assert "Integer affine gap G of n=7" in out
    assert "G = n(2^K - 3^m) - C" in out


def test_collatz_periodic_code():
    out = _run("collatz", "periodic-code", "2")
    assert "Periodic-code fixed-point identity" in out
    assert "positive affine candidate=1" in out
    assert "does not prove Collatz" in out


def test_collatz_cycle():
    out = _run("collatz", "cycle", "2")
    assert "exact_cycle=True" in out
    assert "candidate=1" in out or "candidate=1/1" in out


def test_collatz_cycle_language():
    out = _run(
        "collatz",
        "cycle-language",
        "--additive",
        "0",
        "--max-p",
        "2",
        "--k-max",
        "2",
    )
    assert "L_A additive A=0" in out
    assert "exact cycles=" in out


def test_collatz_warp_one():
    out = _run("collatz", "warp", "1")
    assert "W(n)=1" in out
    assert "Comm_WT=0" in out
    assert "T defined=true" in out


def test_collatz_warp_census():
    out = _run("collatz", "warp-census", "--limit", "40", "--identity-length", "2")
    assert "BT warp commutator census" in out
    assert "smallest zero=1" in out
    assert "W W = id" in out


def test_collatz_warp_realizer():
    out = _run("collatz", "warp-realizer", "1")
    assert "R=3" in out
    assert "W(R)=" in out


def test_collatz_warp_semigroup():
    out = _run("collatz", "warp-semigroup", "--length", "2", "--sample-limit", "20")
    assert "Composition semigroup" in out
    assert "W W vs id counterexample=3" in out


def test_collatz_warp_counterexamples():
    out = _run("collatz", "warp-counterexamples")
    assert "W_W_equals_id" in out
    assert "counterexample': 3" in out or "counterexample\": 3" in out or "3" in out
