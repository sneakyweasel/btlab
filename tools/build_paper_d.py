"""Build Paper D from docs/theory and validate/synchronize its generated exports.

Paper D is *No m-cycles of the 3n-1 map for m <= 58*, the Simons-de Weger template
transposed to the negative side from the laboratory's own verification floor.

Requires Pandoc and XeLaTeX only for a build. --check and --sync use the Python standard
library. Text hashes normalize line endings for Git on Windows. The manifest establishes
provenance and consistency, not mathematical correctness: what the paper rests on is Rhin's
measure (external), the floor (a computation of this laboratory), and the exact arithmetic
of the tables, which `tools/check_3n_minus_1_note_numeric.py` recomputes by a second route.

The pinned inputs are the manuscript and its build chain, the probe that computes the
tables, the tables themselves, the independent check and its report, the Lean module behind
Lemmas 1 and 3, and the floor certificate the theorem's hypothesis is: a change to any of
them stales the PDF, which is the hole Paper C's gate was written to close.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
from html import escape
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


# Reproducible output. XeLaTeX stamps a build time into the PDF's compressed metadata, so
# without this a no-op rebuild changes the bytes and therefore the sha256 in the manifest.
_SOURCE_DATE_EPOCH = "1789948800"  # 21 September 2026, the date this version carries


def _pin_build_date() -> None:
    os.environ.setdefault("SOURCE_DATE_EPOCH", _SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")


ROOT = Path(__file__).resolve().parents[1]
STEM = "collatz_3n_minus_1_m_cycles_note"
SOURCE = f"docs/theory/{STEM}.md"
PDF = f"juggler_review/{STEM}.pdf"
TEX = "docs/theory/cochin-3n-minus-1-m-cycles.tex"
MANIFEST = "docs/theory/paper_d_release.json"
METADATA = "docs/theory/paper_d_zenodo.json"
OUTPUTS = [PDF, TEX, METADATA]
EDITORIAL = [SOURCE, "docs/theory/PAPER_D_BUILD.md"]
BUILD_INPUTS = [
    "tools/build_paper_d.py", "tools/paper_d/article.tex", "tools/paper_d/layout.lua",
    "tools/check_3n_minus_1_note_numeric.py",
    "src/research/juggler_sequence/negative_m_cycles.py",
    "src/research/juggler_sequence/negative_floor_gpu.py",
    "data/research/juggler/negative_m_cycles/summary.json",
    "data/research/juggler/negative_m_cycles/manuscript_check.json",
    "data/research/juggler/negative_floor_3x1/gpu_runs.json",
    "data/research/juggler/negative_floor_3x1/gpu_calibration/summary.json",
    "data/research/juggler/negative_floor_3x1/gpu_calibration/spot_checks_2p44_2p51.json",
    "data/research/juggler/negative_floor_3x1/summary.json",
    "data/research/juggler/negative_floor_3x1/verify_3x1_gpu.cu",
    "formal/Problems/Collatz/NegativeMCycles.lean",
]
KIT = "juggler_review/zenodo_paper_d"
#: the deposit carries the PDF under a readable name; the repository keeps one copy, in
#: juggler_review/, and this is a byte-identical alias of it.
DEPOSIT_PDF = f"{KIT}/No_m_cycles_of_the_3n_minus_1_map.pdf"
PDF_EXPORTS = [DEPOSIT_PDF]
VERSION = "1.0.0"
#: Zenodo takes the bare identifier, not the URL, beside the creator's name.
ORCID = "0009-0004-1939-3382"


def digest(path: Path, mode: str = "binary") -> str:
    data = path.read_bytes()
    if mode == "text" and path.suffix.lower() not in {".png", ".pdf"}:
        data = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def input_files(root: Path) -> list[str]:
    return sorted(set(EDITORIAL + BUILD_INPUTS))


def safe_path(root: Path, name: str) -> Path:
    p = (root / name).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError(f"Path outside repository: {name}")
    return p


def read_release(root: Path) -> dict:
    release = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    if release.get("schema") != 1 or release.get("canonical_source") != SOURCE:
        raise ValueError("Unrecognized Paper D release manifest")
    required = set(input_files(root))
    recorded = {row["path"] for row in release["inputs"]}
    if required != recorded:
        missing = sorted(required - recorded) or sorted(recorded - required)
        raise ValueError(f"Paper D input inventory changed ({missing}); rebuild required")
    for row in release["inputs"] + release["outputs"]:
        p = safe_path(root, row["path"])
        if not p.is_file() or digest(p, row["mode"]) != row["sha256"]:
            raise ValueError(f"Stale or missing Paper D file: {row['path']}; rebuild required")
    if {row["path"] for row in release["outputs"]} != set(OUTPUTS):
        raise ValueError("Incomplete Paper D output manifest")
    return release


def export_pairs(root: Path):
    pairs = [(name, "juggler_review/" + Path(name).name) for name in EDITORIAL]
    pairs.extend((PDF, name) for name in PDF_EXPORTS)
    return pairs


def zenodo_fields(meta: dict) -> str:
    return ("GENERATED FROM docs/theory/; do not edit this export.\n"
            "Prepared local metadata only; this build does not create or update an external record.\n\n"
            f"TITLE\n{meta['title']}\n\nCREATOR\n{meta['creators'][0]['name']}\n"
            f"ORCID: {meta['creators'][0]['orcid']} (https://orcid.org/{meta['creators'][0]['orcid']})\n"
            "Affiliation: none\n\nRESOURCE TYPE\nPublication / Preprint\n\n"
            f"VERSION\n{meta['version']}\n\nLICENSE\n{meta['license']}\n\n"
            "PUBLICATION DATE\nUse the actual date this version is first made public.\n\n"
            "KEYWORDS\n" + "\n".join(meta["keywords"]) + "\n\nDESCRIPTION (HTML)\n"
            + meta["description"] + "\n\nRELATED IDENTIFIERS\n"
            + "\n".join(f"{r['relation']}: {r['identifier']}" for r in meta["related_identifiers"])
            + "\n")


def checksums(root: Path) -> str:
    lines = ["# sha256 of the files in this kit and of the PDF they alias.",
             "# Regenerate with `python tools/build_paper_d.py --sync`."]
    for name in [DEPOSIT_PDF, PDF]:
        lines.append(f"{digest(root / name, 'binary')}  {name}")
    return "\n".join(lines) + "\n"


def sync(root: Path) -> None:
    read_release(root)
    for source, target in export_pairs(root):
        p = root / target
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / source, p)
    meta = json.loads((root / METADATA).read_text(encoding="utf-8"))
    (root / KIT / "ZENODO_FIELDS.txt").write_text(zenodo_fields(meta), encoding="utf-8")
    (root / KIT / "SHA256SUMS.txt").write_text(checksums(root), encoding="utf-8")


def check(root: Path, exports: bool = True) -> None:
    read_release(root)
    if not exports:
        return
    for source, target in export_pairs(root):
        mode = "text" if target.endswith(".md") else "binary"
        if not (root / target).is_file() or digest(root / source, mode) != digest(root / target, mode):
            raise ValueError(f"Stale generated copy: {target}; run --sync")
    meta = json.loads((root / METADATA).read_text(encoding="utf-8"))
    if (root / KIT / "ZENODO_FIELDS.txt").read_text(encoding="utf-8") != zenodo_fields(meta):
        raise ValueError("Stale Zenodo fields; run --sync")
    if (root / KIT / "SHA256SUMS.txt").read_text(encoding="utf-8") != checksums(root):
        raise ValueError("Stale checksums; run --sync")


def write_metadata(root: Path, pandoc: str) -> None:
    source = (root / SOURCE).read_text(encoding="utf-8")
    title = re.search(r'^title: "(.*)"$', source, re.M).group(1)
    author = re.search(r"^author: (.*)$", source, re.M).group(1)
    abstract = source.split("## Abstract\n", 1)[1].split("**2020 Mathematics", 1)[0]
    acknowledgment = source.split("## Acknowledgments and use of AI\n", 1)[1].split("## Availability", 1)[0]
    plain = subprocess.check_output(
        [pandoc, "--from=markdown+tex_math_single_backslash", "--to=plain", "--wrap=none"],
        input=abstract + "\n" + acknowledgment, encoding="utf-8")
    description = "\n".join("<p>" + escape(p.replace("\n", " ")) + "</p>"
                            for p in plain.strip().split("\n\n"))
    # A reusable field sheet, not an API call and not a claim of a published DOI.
    meta = {
        "title": title,
        "creators": [{"name": author.rsplit(" ", 1)[1] + ", " + author.rsplit(" ", 1)[0],
                      "orcid": ORCID}],
        "upload_type": "publication", "publication_type": "preprint", "access_right": "open",
        "license": "cc-by-4.0", "language": "eng", "version": VERSION,
        "keywords": ["3n-1 map", "Collatz cycles", "m-cycles",
                     "linear forms in logarithms", "verification floor"],
        "description": description,
        "related_identifiers": [
            {"identifier": "https://github.com/sneakyweasel/btlab", "relation": "isSupplementTo",
             "scheme": "url"},
            {"identifier": "10.5281/zenodo.22676453", "relation": "cites", "scheme": "doi"},
        ],
    }
    (root / METADATA).write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def executable(name: str, explicit: str | None) -> str:
    path = explicit or shutil.which(name)
    if path:
        return path
    candidates = []
    if os.name == "nt":
        if name == "pandoc":
            candidates = [Path(os.environ.get("PROGRAMFILES", "C:/Program Files")) / "Pandoc/pandoc.exe"]
        elif name == "xelatex":
            candidates = [Path(os.environ.get("LOCALAPPDATA", "")) / "Programs/MiKTeX/miktex/bin/x64/xelatex.exe"]
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate)
    raise ValueError(f"{name} not found; install it or pass --{name}")


LAYOUT_FAILURE = re.compile(r"^!|Overfull \\[hv]box|Missing character:|undefined references|multiply defined")


def build(root: Path, args) -> None:
    _pin_build_date()
    previous = root / MANIFEST
    publication = (json.loads(previous.read_text(encoding="utf-8")).get("publication")
                   if previous.is_file() else None)
    initial_inputs = {p: digest(root / p, "text") for p in input_files(root)}
    pandoc = executable("pandoc", args.pandoc)
    xelatex = executable("xelatex", args.xelatex)
    work = Path(args.build_dir).resolve() if args.build_dir else root / ".build/paper_d"
    work.mkdir(parents=True, exist_ok=True)
    tex = work / Path(TEX).name
    subprocess.run([pandoc, str(root / SOURCE),
                    "--from=markdown+tex_math_single_backslash+autolink_bare_uris",
                    "--to=latex", "--standalone", "--no-highlight", "--ascii",
                    "--template", str(root / "tools/paper_d/article.tex"),
                    "--lua-filter", str(root / "tools/paper_d/layout.lua"),
                    "--output", str(tex)], check=True, cwd=root)
    latex = tex.read_text(encoding="utf-8")
    latex = latex.replace("\\bottomrule\\noalign{}\n\\endlastfoot",
                          "\\bottomrule\\noalign{}\n\\endfoot\n\\bottomrule\\noalign{}\n\\endlastfoot")
    latex = re.sub(r"\\\\\n(\\end\{longtable\})", r"\\\\*\n\1", latex)
    tex.write_text(latex, encoding="utf-8")
    versions = {name: subprocess.check_output([exe, "--version"], encoding="utf-8",
                                              errors="replace").splitlines()[0]
                for name, exe in (("pandoc", pandoc), ("xelatex", xelatex))}
    for iteration in range(1, 4):
        run = subprocess.run([xelatex, "-no-shell-escape", "-interaction=nonstopmode",
                              "-halt-on-error", tex.name], cwd=work, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        (work / f"xelatex-pass-{iteration}.txt").write_text(run.stdout, encoding="utf-8")
        if run.returncode:
            raise ValueError(f"XeLaTeX failed; see {work / f'xelatex-pass-{iteration}.txt'}")
    log = tex.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
    failures = [line for line in log.splitlines() if LAYOUT_FAILURE.search(line)]
    if failures and not args.allow_layout_warnings:
        raise ValueError("Fix layout before release:\n" + "\n".join(failures))
    if args.allow_layout_warnings:
        print(f"Draft preview only; no release updated. Logs: {work}")
        return
    if initial_inputs != {p: digest(root / p, "text") for p in input_files(root)}:
        raise ValueError("Paper D inputs changed during compilation; rebuild required")
    pages = re.search(r"Output written on .*?\((\d+) pages?", log)
    shutil.copyfile(tex, root / TEX)
    (root / PDF).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(tex.with_suffix(".pdf"), root / PDF)
    write_metadata(root, pandoc)
    release = {
        "schema": 1, "canonical_source": SOURCE,
        "status": "preprint; no external deposit performed",
        "verification_scope": "File provenance only. The mathematical trust boundaries are in the "
                              "manuscript and in PAPER_D_BUILD.md.",
        "pages": int(pages.group(1)) if pages else None,
        "tools": versions,
        "inputs": [{"path": p, "mode": "text", "sha256": digest(root / p, "text")}
                   for p in input_files(root)],
        "outputs": [{"path": p, "mode": "binary" if p == PDF else "text",
                     "sha256": digest(root / p, "binary" if p == PDF else "text")} for p in OUTPUTS],
    }
    if publication is not None:
        release["publication"] = publication
    (root / MANIFEST).write_text(json.dumps(release, indent=2) + "\n", encoding="utf-8")
    sync(root)
    check(root)
    print(f"Built and synchronized Paper D ({release['pages']} pages). Logs: {work}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--sync", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    parser.add_argument("--build-dir")
    parser.add_argument("--pandoc")
    parser.add_argument("--xelatex")
    parser.add_argument("--allow-layout-warnings", action="store_true", help="Draft preview only")
    args = parser.parse_args()
    if args.check:
        check(args.root)
        print(f"Paper D matches its source and manifest.")
    elif args.sync:
        sync(args.root)
        print("Synchronized Paper D exports.")
    else:
        build(args.root, args)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, FileNotFoundError, subprocess.CalledProcessError) as exc:
        print(exc, file=sys.stderr)
        sys.exit(1)
