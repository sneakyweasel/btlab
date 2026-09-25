"""Validate Paper E's exact finite data, manuscript references, and selected Lean proof dependencies.

Default: read-only checks, including freshness of the saved Lean audit.
--refresh: regenerate the report with a fresh paper-target build and axiom audit.
The report describes local verification, never independent review or priority.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd, isqrt
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from paper_e_common import AXIOMS, CERTIFICATE, REPORT, ROOT, SOURCE, declarations, lean_hashes


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def juggler(n: int) -> int:
    return isqrt(n if n % 2 == 0 else n**3)


def minus(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3*n-1)//2


def finite_checks(root: Path) -> dict:
    # Load the established independent checker, not floating-point search diagnostics.
    sys.path.insert(0, str(root / "src"))
    from research.juggler_sequence.negative_preimage_density import verify_grid_certificate
    cert = json.loads((root / CERTIFICATE).read_text(encoding="utf-8"))
    verified = verify_grid_certificate(cert)
    require(verified["all_integer_inequalities_hold"], "signed weight certificate fails")
    require((cert["k"], cert["p"], cert["q"]) == (12, 5059, 5000), "unexpected rate or level")
    require((len(cert["weights"]), min(cert["weights"]), max(cert["weights"])) ==
            (177147, 7307142888, 10**12), "manuscript certificate statistics changed")
    grid_source = (root / "formal/Problems/Collatz/PreimageGrid.lean").read_text(encoding="utf-8")
    block = grid_source.split("def table : List ℕ :=", 1)[1].split("def rung", 1)[0]
    table = [int(x) for x in re.findall(r"\d+", block)]
    require(len(table) == 50, "cap table must have fifty entries")
    cap = lambda t: 2**(t//50) * table[t % 50]
    for t in range(50):
        require(8193*cap(t+29) <= 12288*cap(t), f"advanced cap fails at {t}")
        require(16386*cap(t) <= 12288*cap(t+21), f"retarded cap fails at {t}")
    require(2**291 * 8193**498 < 12288**498, "root-measure slack fails")
    require(2**21 * 5000**1250 < 5059**1250, "density rate gap fails")
    require(2**423 * 5000**25000 < 5059**25000 < 2**424 * 5000**25000,
            "Remark 5.5 exponent 423/500 is not the certificate's best")
    low, high = Fraction(5069, 5000), Fraction(507, 500)
    mean = lambda x: x**-100 + (x**29 + x**-21)/3
    require(mean(low) < 1 and mean(high) < 1, "ceiling endpoint comparison fails")
    require(low**50 < 2 < high**50 and low**5000 < 2**99, "ceiling power comparison fails")
    require(2**79 < 3**50, "harmonic contradiction fails")
    # A bounded exhaustive construction verifies a forward-closed finite set.
    states = set(range(1, 4096))
    queue = list(states)
    for n in queue:
        child = minus(n)
        require(0 < child < 2**19, f"small-orbit barrier fails at {n}")
        if child not in states:
            states.add(child)
            queue.append(child)
    require(all(minus(n) in states for n in states), "barrier is not forward closed")
    # Record actual state cardinality, rather than trust an old summary.
    require(max(states) == 417718, "barrier maximum differs from manuscript")
    for start, expected in [(3, Fraction(83, 27)), (4, Fraction(4)), (6, Fraction(4))]:
        parities, n = [], start
        while n != 1:
            parities.append(n % 2)
            n = juggler(n)
            require(len(parities) < 100, "rational example failed to reach one")
        value = Fraction(1)
        for odd in reversed(parities):
            value = (2*value+1)/3 if odd else 2*value
        require(value == expected, f"wrong orbit code at {start}")
    # Three actual prefixes, increasing denominator precision; no cycle inference.
    witnesses = []
    for precision, t in [(1, 9), (2, 318), (3, 12589)]:
        a, b, denominator = 3, 1, 11
        modulus = denominator**precision
        s = 1+2*modulus*t
        start = s**(2**(a-1))
        n, word, minimum = start, [], start
        for _ in range(a+b):
            word.append(n % 2)
            n = juggler(n)
            minimum = min(minimum, n)
        require(word == [1, 1, 1, 0] and n > start and minimum == start and
                n % (2*modulus) == start % (2*modulus) == 1,
                f"modular witness fails at precision {precision}")
        require((3**a-2**(a+b))//gcd(3**a-2**a, 2**b-1) == denominator,
                "periodic-word denominator mismatch")
        witnesses.append({"a": a, "b": b, "precision": precision, "t": t})
    manuscript = (root / SOURCE).read_text(encoding="utf-8")
    table_match = re.search(r"~~~text\n((?:\d+[ \n]+)+)~~~", manuscript)
    require(table_match is not None and list(map(int, table_match[1].split())) == table,
            "printed cap table differs from Lean")
    require("\t" not in manuscript and "\x08" not in manuscript and "\x0c" not in manuscript,
            "mangled LaTeX escape")
    require("version 0.8.0" in manuscript.lower(), "missing version")
    require(str(len(states)) in manuscript, "printed small-orbit cardinality differs")
    labels = re.findall(r"^\*\*(?:Theorem|Lemma|Corollary|Proposition|Example) (\d+\.\d+)", manuscript, re.M)
    require(len(labels) == len(set(labels)), "duplicate statement number")
    for label in re.findall(r"(?:Theorem|Lemma|Corollary|Proposition|Example) (\d+\.\d+)", manuscript):
        # External references carry their own labels inside square brackets.
        if label not in labels:
            require(label in {"1.1", "1.3", "1.12"}, f"unresolved statement number {label}")
    body, bibliography = manuscript.split("## References\n", 1)
    for key in re.findall(r"\[([A-Z][A-Za-z0-9]*)(?:, [^\]]+)?\]", body):
        require(f"[{key}]" in bibliography, f"missing bibliography entry {key}")
    for name in declarations(root):
        module, short = name.rsplit(".", 1)
        path = root / "formal" / (module.replace(".", "/") + ".lean")
        text = path.read_text(encoding="utf-8")
        require(re.search(r"\btheorem\s+" + re.escape(short) + r"\b", text) is not None,
                f"missing declaration {name}")
    return {"certificate": verified, "grid_phases_checked": 50,
            "barrier_positive_states": len(states), "barrier_maximum": max(states),
            "rational_examples_checked": 3, "modular_witnesses": witnesses,
            "exact_rate_and_ceiling_comparisons": "pass",
            "manuscript_references_and_table": "pass",
            "audited_declarations": len(declarations(root))}


def audit_lean(root: Path, lake: str | None = None) -> dict:
    executable = lake or shutil.which("lake")
    if not executable:
        fallback = Path(os.environ.get("USERPROFILE", "")) / ".elan/bin/lake.exe"
        if fallback.is_file():
            executable = str(fallback)
    require(bool(executable), "lake unavailable; pass --lake")
    initial = lean_hashes(root)
    work = root / ".build/paper_e"
    work.mkdir(parents=True, exist_ok=True)
    for name, args in [
        ("lean-build", ["build", "Problems.JugglerCollatzPaper"]),
        ("lean-axioms", ["env", "lean", Path(AXIOMS).name]),
    ]:
        run = subprocess.run([executable, *args], cwd=root / "formal", capture_output=True,
                             text=True, encoding="utf-8", errors="replace")
        output = run.stdout + run.stderr
        (work / f"{name}.txt").write_text(output, encoding="utf-8")
        require(run.returncode == 0, f"{name} failed; see {work / (name + '.txt')}")
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    none = re.findall(r"'([^']+)' does not depend on any axioms", output)
    actual = {name: sorted(x.strip() for x in deps.split(",") if x.strip()) for name, deps in entries}
    actual.update({name: [] for name in none})
    require(set(actual) == set(declarations(root)), "axiom audit did not cover the whole inventory")
    require(all(set(deps) <= permitted for deps in actual.values()), "unexpected Lean dependency")
    require(initial == lean_hashes(root), "Lean inputs changed during audit; rerun")
    return {"status": "passed", "scope": "Local paper-target build and selected theorem dependency audit",
            "toolchain": (root / "formal/lean-toolchain").read_text().strip(),
            "declarations": actual, "input_sha256": initial}


def check(root: Path = ROOT) -> dict:
    report = json.loads((root / REPORT).read_text(encoding="utf-8"))
    require(report["finite"] == finite_checks(root), "saved finite report is stale; run --refresh")
    require(report["lean"]["status"] == "passed", "Lean audit has not passed")
    require(report["lean"]["input_sha256"] == lean_hashes(root),
            "Lean proof inputs changed; run tools/check_paper_e.py --refresh")
    require(set(report["lean"]["declarations"]) == set(declarations(root)), "stale theorem inventory")
    require(all(set(x) <= {"propext", "Classical.choice", "Quot.sound"}
                for x in report["lean"]["declarations"].values()), "unexpected saved Lean dependency")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--refresh", action="store_true")
    parser.add_argument("--lake")
    args = parser.parse_args()
    if args.refresh:
        report = {"schema": 1, "finite": finite_checks(ROOT), "lean": audit_lean(ROOT, args.lake),
                  "independent_review": "pending", "priority_review": "pending",
                  "written_only": ["Theorem 4.1: classical fixed-function equidistribution"]}
        (ROOT / REPORT).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    report = check(ROOT)
    print(f"Paper E: {report['finite']['certificate']['inequalities_checked']} exact certificate rows; "
          f"{report['finite']['audited_declarations']} audited Lean declarations; all checks pass.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(exc, file=sys.stderr)
        sys.exit(1)
