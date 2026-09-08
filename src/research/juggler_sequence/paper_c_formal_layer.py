"""Paper C's Lean surface: the barrel, the axiom artifact, and the paper's own Lean column.

Papers A and B each have a barrel module and an ``AxiomCheck`` artifact, so a reader can build
the formal side of either paper on its own and see what every cited name rests on.  Paper C
(``docs/theory/juggler_fate_almost_all_note.md``) had neither, and its verification table had
drifted: Proposition 9.3 stayed "human proof" after ``TiltedShare.lean`` proved it.  This probe
reads the three things that now exist and reports whether they agree.

1. **The barrel.**  ``formal/Problems/JugglerFatePaper.lean`` must import exactly the modules
   Paper C's Appendix A names, and nothing else.
2. **The axiom artifact.**  ``formal/AxiomCheckPaperC.expected`` records, for every declaration
   ``AxiomCheckPaperC.lean`` asks about, the axioms it depends on.  Each list must be a subset of
   Mathlib's three (``propext``, ``Classical.choice``, ``Quot.sound``); ``sorryAx`` and
   ``Lean.ofReduceBool`` (``native_decide``) must not appear.
3. **The paper's Lean column.**  Every backticked name in Appendix A must be declared in the
   corpus, live in a module reachable from the Paper C root, and be interrogated by the artifact;
   and the verification table's ``Lean`` rows must match the modules that exist.

The formalpedia surface (``tools/formalpedia.py``) supplies reachability and trust.  Nothing
here proves a theorem; the probe records what the Lean checks and what it does not.  Run
``python -m research.juggler_sequence.paper_c_formal_layer``.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_THEORY, FORMAL_DIR, REPO_ROOT

TOOLS = REPO_ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import formalpedia as fp  # noqa: E402

DATA_DIR = DATA_ROOT / "paper_c_formal_layer"
PAPER = DOCS_THEORY / "juggler_fate_almost_all_note.md"
BARREL = FORMAL_DIR / "Problems" / "JugglerFatePaper.lean"
AXIOM_CHECK = FORMAL_DIR / "AxiomCheckPaperC.lean"
AXIOM_EXPECTED = FORMAL_DIR / "AxiomCheckPaperC.expected"
ROOT_MODULE = "Problems.JugglerFatePaper"
MATHLIB_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

#: the modules Paper C cites; the barrel must import exactly these
CITED_MODULES = (
    "Problems.Juggler.TerminationFloor257",
    "Problems.Juggler.FateContagion",
    "Problems.Juggler.CubeFiber",
    "Problems.Juggler.TiltedShare",
    "Problems.Juggler.FateRecursion",
    "Problems.Juggler.FateFirstLetter",
    "Problems.Juggler.FateSweep",
    "Problems.Juggler.FateChernoff",
    "Problems.Juggler.FatePressure",
    "Problems.Juggler.FateTaoReduction",
    "Problems.Juggler.FateSeed",
)

#: verification-table rows the paper marks Lean, with the module that carries each
TABLE_LEAN_ROWS = {
    "Lemma 2.1": "FateContagion",
    "Lemma 3.1": "FateContagion",
    "Lemma 3.2": "FateContagion",
    "Theorem 6.1": "FateContagion",
    "Lemma 8.1": "FateContagion",
    "Lemma 4.1)": "FateSweep",
    "Lemma 4.7": "CubeFiber",
    "Lemma 5.1": "FateRecursion",
    "Proposition 6.3(i)": "FateFirstLetter",
    "Proposition 9.3": "TiltedShare",
    "Lemma 8.2": "FateChernoff",
    "Theorem 8.3": "FateChernoff",
    "Theorem 9.2": "FatePressure",
    "Lemma 5.2": "FateSeed",
    "Theorem 7.2": "FateTaoReduction",
}

_IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)
_PRINT = re.compile(r"^#print axioms ([A-Za-z0-9_'.]+)$", re.M)
_RESULT = re.compile(r"^'([A-Za-z0-9_'.]+)' depends on axioms: \[(.*)\]$")
_TICK = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*)`")


def barrel_imports() -> list[str]:
    return _IMPORT.findall(BARREL.read_text(encoding="utf-8"))


def axiom_check_names() -> list[str]:
    return _PRINT.findall(AXIOM_CHECK.read_text(encoding="utf-8"))


def axiom_check_results() -> dict[str, list[str]]:
    """Recorded output: short declaration name -> the axiom list it depends on."""
    out: dict[str, list[str]] = {}
    for line in AXIOM_EXPECTED.read_text(encoding="utf-8").splitlines():
        m = _RESULT.match(line.strip())
        if not m:
            continue
        name = m.group(1)
        if name.startswith("Problems.Juggler."):
            name = name[len("Problems.Juggler."):]
        axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
        out[name] = axioms
    return out


def appendix_a_names() -> list[str]:
    """Backticked identifiers in Appendix A of the paper."""
    text = PAPER.read_text(encoding="utf-8")
    start = text.index("## Appendix A. Lean names")
    end = text.index("## Appendix B.", start)
    names: list[str] = []
    for line in text[start:end].splitlines():
        if not line.startswith("|") or line.startswith("| Statement") or line.startswith("|---"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 2:
            continue
        for n in _TICK.findall(cells[1]):
            if n not in names:
                names.append(n)
    return names


def verification_table() -> list[tuple[str, str]]:
    """The (result, status) rows of Section 1.4."""
    text = PAPER.read_text(encoding="utf-8")
    start = text.index("### 1.4 Verification")
    end = text.index("![Logical dependencies", start)
    rows: list[tuple[str, str]] = []
    for line in text[start:end].splitlines():
        if line.startswith("| ") and not line.startswith("| Result"):
            cells = [c.strip() for c in line.strip("|").split("|")]
            if len(cells) == 2:
                rows.append((cells[0], cells[1]))
    return rows


def _short(name: str) -> str:
    return name[len("Problems.Juggler."):] if name.startswith("Problems.Juggler.") else name


def audit() -> dict[str, Any]:
    index = fp.build()
    reach = fp.reachable(index)
    reached = reach.get(ROOT_MODULE, set()) | {ROOT_MODULE}
    decl_module: dict[str, str] = {}
    decl_trust: dict[str, str] = {}
    decl_kind: dict[str, str] = {}
    for d in index["declarations"]:
        # the index records bare names; Appendix A qualifies the `Sweep.*` machinery
        decl_module.setdefault(d["name"], d["module"])
        decl_trust.setdefault(d["name"], d["trust"])
        decl_kind.setdefault(d["name"], d.get("kind", ""))

    problems: list[dict[str, str]] = []

    imports = barrel_imports()
    if imports != list(CITED_MODULES):
        problems.append({"kind": "barrel", "why": "imports differ from the cited modules",
                         "detail": ", ".join(imports)})

    asked = axiom_check_names()
    results = axiom_check_results()
    for name in asked:
        if name not in results:
            problems.append({"kind": "artifact", "why": "asked, but no recorded result", "detail": name})
            continue
        extra = [a for a in results[name] if a not in MATHLIB_AXIOMS]
        if extra:
            problems.append({"kind": "artifact", "why": "rests on more than Mathlib's three",
                             "detail": f"{name}: {results[name]}"})
    for name in results:
        if name not in asked:
            problems.append({"kind": "artifact", "why": "recorded but not asked", "detail": name})

    cited = appendix_a_names()
    for name in cited:
        bare = name.split(".")[-1]
        mod = decl_module.get(bare)
        if mod is None:
            problems.append({"kind": "paper", "why": "cited in Appendix A but not declared", "detail": name})
            continue
        if mod not in reached:
            problems.append({"kind": "paper", "why": "declared but not reachable from the root",
                             "detail": f"{name} in {mod}"})
        if decl_trust.get(bare) != "kernel":
            problems.append({"kind": "paper", "why": "not kernel-checked", "detail": name})
        is_def = decl_kind.get(bare) in ("def", "abbrev", "structure", "noncomputable def")
        if not is_def and name not in asked:
            problems.append({"kind": "artifact", "why": "cited theorem the artifact does not ask about",
                             "detail": name})

    table = verification_table()
    lean_rows = [r for r in table if r[1].startswith("Lean")]
    for key, module in TABLE_LEAN_ROWS.items():
        hit = [r for r in lean_rows if key in r[0]]
        if not hit:
            problems.append({"kind": "table", "why": "expected a Lean row", "detail": key})
        if f"Problems.Juggler.{module}" not in reached:
            problems.append({"kind": "table", "why": "row's module not reachable", "detail": module})
    human_rows = [r for r in table if r[1].startswith("human")]

    surface = fp.paper_surface(index)["Paper C"]
    return {
        "root": ROOT_MODULE,
        "barrel_imports": imports,
        "artifact": {
            "asked": len(asked),
            "recorded": len(results),
            "axiom_lists": sorted({", ".join(v) for v in results.values()}),
        },
        "appendix_a_names": len(cited),
        "surface": {k: surface[k] for k in ("modules", "declarations", "compiler_trusted",
                                           "compiler_dependent", "open")},
        "table": {
            "rows": len(table),
            "lean": [r[0] for r in lean_rows],
            "human": [r[0] for r in human_rows],
            "other": [r[0] for r in table if not (r[1].startswith("Lean") or r[1].startswith("human"))],
        },
        "problems": problems,
    }


def summary() -> dict[str, Any]:
    from research.juggler_sequence.cycle_finance import git_commit

    result = audit()
    ok = not result["problems"]
    result["classification"] = {
        "clean": ok,
        "label": "PAPER_C_LEAN_SURFACE_CONSISTENT" if ok else "PAPER_C_LEAN_SURFACE_INCONSISTENT",
        "problems": len(result["problems"]),
    }
    result["git_commit"] = git_commit()
    return result


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n",
                                           encoding="utf-8")
    print(f"root {result['root']}: {result['surface']['modules']} modules, "
          f"{result['surface']['declarations']} declarations reachable")
    print(f"artifact: {result['artifact']['asked']} asked, {result['artifact']['recorded']} recorded; "
          f"axiom lists {result['artifact']['axiom_lists']}")
    print(f"Appendix A: {result['appendix_a_names']} names; table: {len(result['table']['lean'])} Lean rows, "
          f"{len(result['table']['human'])} human-proof rows")
    print(f"classification {result['classification']['label']}")
    for p in result["problems"]:
        print(f"  {p['kind']}: {p['why']} -- {p['detail']}")


if __name__ == "__main__":
    main()
