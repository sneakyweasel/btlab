"""Build Paper A from docs/theory and validate/synchronize its generated exports.

Requires Pandoc and XeLaTeX only for a build. --check and --sync use the
Python standard library. Text hashes normalize line endings for Git on Windows.
The manifest establishes provenance and consistency, not mathematical correctness.
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
import runpy
import shutil
import subprocess


# Reproducible output.  XeLaTeX stamps a build time into the PDF's compressed metadata, so
# without this a no-op rebuild changes the bytes and therefore the sha256 in the manifest.
# The epoch is fixed to the version the build guide records rather than taken from git,
# because a git-derived date lags one build behind an edit and merely relocates the churn.
_SOURCE_DATE_EPOCH = "1788912000"  # Paper A version 1.0.0, 9 September 2026


def _pin_build_date() -> None:
    """Pin SOURCE_DATE_EPOCH unless the caller already set one."""
    os.environ.setdefault("SOURCE_DATE_EPOCH", _SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")

ROOT = Path(__file__).resolve().parents[1]
STEM = "juggler_finite_dynamics_note"
SOURCE = f"docs/theory/{STEM}.md"
PDF = f"juggler_review/{STEM}.pdf"
TEX = "docs/theory/cochin-juggler.tex"
MANIFEST = "docs/theory/paper_a_release.json"
METADATA = "docs/theory/paper_a_zenodo.json"
OUTPUTS = [PDF, TEX, METADATA]
EDITORIAL = [SOURCE, "docs/theory/juggler_finite_dynamics_formalization.md",
             "docs/theory/juggler_finite_dynamics_reviewer_packet.md"]
BUILD_INPUTS = ["tools/build_paper_a.py", "tools/paper_a/article.tex",
                "tools/paper_a/layout.lua", "tools/check_paper_a_numeric.py",
                "tools/trust_boundary.py",
                "src/research/juggler_sequence/paper_a_audit.py",
                "src/research/juggler_sequence/cycle_rank_curvature.py",
                "data/research/juggler/cycle_rank_curvature/controls.json",
                "data/research/juggler/negative_floor_3x1/chunks.json",
                "data/research/juggler/negative_floor_3x1/runs.json",
                "data/research/juggler/negative_floor_3x1/verify_3x1.c",
                "data/research/juggler/negative_floor_3x1/verify_3x1_jump.c",
                # The finance record that Section 1.2 names as the computation and that
                # Appendix B sends the reader to.  It sat outside the manifest until
                # 21 September 2026, which is exactly why the provenance pin could go on
                # naming a commit that held neither table: nothing compared them to
                # anything.  The probe writes the three tables.
                "src/research/juggler_sequence/cycle_finance.py",
                "data/research/juggler/cycle_finance/exceptions_parity.json",
                "data/research/juggler/cycle_finance/budget_opt.json",
                "data/research/juggler/cycle_finance/summary.json"]
# The PDF lives in `juggler_review/` now, and is exported only under the
# historical name the Zenodo deposit carries. The companion site links the
# published DOIs instead of serving its own copy, so `public/papers/` and
# `dist/papers/` are gone.
#: Zenodo takes the bare identifier, not the URL, beside the creator's name.
ORCID = "0009-0004-1939-3382"
PDF_EXPORTS = ["juggler_review/zenodo_paper_a/Lower_bounds_for_nontrivial_cycles_of_the_Juggler_map.pdf"]


def digest(path: Path, mode: str = "binary") -> str:
    data = path.read_bytes()
    if mode == "text":
        data = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def input_files(root: Path) -> list[str]:
    """Pin the actual transitive Paper A Lean imports, including their audit."""
    names = set(EDITORIAL + BUILD_INPUTS + ["formal/lean-toolchain",
                "formal/lake-manifest.json", "formal/AxiomCheckPaperA.lean",
                "formal/AxiomCheckPaperA.expected"])
    audit = runpy.run_path(str(Path(__file__).with_name("trust_boundary.py")))
    modules = audit["reachable_module_names"](
        root / "formal/Problems/JugglerPaper.lean", formal_root=root / "formal")
    names.update("formal/" + module.replace(".", "/") + ".lean" for module in modules)
    return sorted(names)


def safe_path(root: Path, name: str) -> Path:
    p = (root / name).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError(f"Path outside repository: {name}")
    return p


def read_release(root: Path) -> dict:
    release = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    if release.get("schema") != 1 or release.get("canonical_source") != SOURCE:
        raise ValueError("Unrecognized Paper A release manifest")
    required = set(input_files(root))
    recorded = {row["path"] for row in release["inputs"]}
    if required != recorded:
        raise ValueError("Paper A input inventory changed; rebuild required")
    for row in release["inputs"] + release["outputs"]:
        p = safe_path(root, row["path"])
        if not p.is_file() or digest(p, row["mode"]) != row["sha256"]:
            raise ValueError(f"Stale or missing Paper A file: {row['path']}; rebuild required")
    if {row["path"] for row in release["outputs"]} != set(OUTPUTS):
        raise ValueError("Incomplete Paper A output manifest")
    return release


def export_pairs(root: Path):
    pairs = [(name, "juggler_review/" + Path(name).name) for name in EDITORIAL]
    pairs.extend((PDF, name) for name in PDF_EXPORTS)
    return pairs


def sync(root: Path) -> None:
    read_release(root)
    for source, target in export_pairs(root):
        p = root / target
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / source, p)
    fields = zenodo_fields(json.loads((root / METADATA).read_text(encoding="utf-8")))
    (root / "juggler_review/zenodo_paper_a/ZENODO_FIELDS.txt").write_text(fields, encoding="utf-8", newline="")


def check(root: Path, exports: bool = True) -> None:
    read_release(root)
    if exports:
        for source, target in export_pairs(root):
            mode = "text" if target.endswith(".md") else "binary"
            if not (root / target).is_file() or digest(root / source, mode) != digest(root / target, mode):
                raise ValueError(f"Stale generated copy: {target}; run --sync")
        fields = (root / "juggler_review/zenodo_paper_a/ZENODO_FIELDS.txt").read_text(encoding="utf-8")
        if fields != zenodo_fields(json.loads((root / METADATA).read_text(encoding="utf-8"))):
            raise ValueError("Stale Zenodo fields; run --sync")


def zenodo_fields(meta: dict) -> str:
    """Render the upload form fields from the prepared metadata.

    Three states, because two were never enough. A row naming its own `doi` describes
    a version that is deposited. A row with no `doi` but a `conceptdoi` describes a
    revision prepared on top of a record that already exists -- the state every paper
    here is normally in, and the one the old binary printed as "no external record has
    been created", underneath four published DOIs. A row with neither is a kit prepared
    before any upload. Nothing is asserted that the metadata does not carry.
    """
    row = meta.get('metadata', meta)
    doi, published = row.get('doi'), row.get('publication_date')
    concept, latest = row.get('conceptdoi'), row.get('latest_deposit') or {}
    if doi:
        standing = (f'Describes the deposit at doi:{doi}; this build does not upload '
                    f'a new version.\n\n')
    elif concept:
        standing = (
            f'Version {row["version"]} is prepared and is not deposited. The record '
            f'exists: concept doi:{concept} resolves to the latest version, which is '
            f'{latest.get("version", "unknown")} at doi:{latest.get("doi", "unknown")} '
            f'of {latest.get("publication_date", "unknown")}. A new version goes up '
            f'through the new-version operation of that record, which keeps the '
            f'concept DOI.\n\n')
    else:
        standing = 'Prepared metadata only; no external record has been created.\n\n'
    date_field = (f'PUBLICATION DATE\n{published}\n\n' if published else
                  'PUBLICATION DATE\nUse the actual date this version is first made '
                  'public.\n\n')
    who = row['creators'][0]
    orcid = (f'ORCID: {who["orcid"]} (https://orcid.org/{who["orcid"]})\n'
             if who.get('orcid') else '')
    record = f'RECORD\n{row["record_url"]}\n\n' if row.get('record_url') else ''
    related = '\n'.join(f'{r["relation"]}: {r["identifier"]}'
                        for r in row.get('related_identifiers', ()))
    return (
        'GENERATED FROM docs/theory/; do not edit this export.\n'
        + standing
        + f'TITLE\n{row["title"]}\n\nCREATOR\n{who["name"]}\n' + orcid
        + 'Affiliation: none\n\nRESOURCE TYPE\nPublication / Preprint\n\n'
        + f'VERSION\n{row["version"]}\n\nLICENSE\n{row["license"]}\n\n'
        + record + date_field
        + 'KEYWORDS\n' + '\n'.join(row['keywords']) + '\n\nDESCRIPTION (HTML)\n'
        + row['description'] + '\n\nRELATED WORKS\n' + related + '\n')

#: Fields the build cannot know and must not invent: they describe an external record.
#: Regenerating them is what reset the version to the manuscript date and dropped the
#: ORCID, the concept DOI and the sibling relations on every single build.
CARRIED_FROM_METADATA = ("version", "doi", "publication_date", "conceptdoi",
                         "record_url", "latest_deposit", "related_identifiers")


def carry_forward(root: Path, meta: dict) -> dict:
    """Keep the deposit facts the metadata file already records.

    Absent file or absent key means the builder default stands, so a first build still
    works; present means the recorded value wins, because the build has no way to learn
    a DOI. The metadata file is tracked, so the facts are not held only in a kit.
    """
    path = root / METADATA
    if not path.is_file():
        return meta
    old = json.loads(path.read_text(encoding="utf-8"))
    old = old.get("metadata", old)
    for key in CARRIED_FROM_METADATA:
        if key in old:
            meta[key] = old[key]
    recorded = (old.get("creators") or [{}])[0].get("orcid")
    if recorded:
        meta["creators"][0]["orcid"] = recorded
    return meta

def write_metadata(root: Path, pandoc: str) -> None:
    source = (root / SOURCE).read_text(encoding="utf-8")
    title = re.search(r'^title: "(.*)"$', source, re.M).group(1)
    author = re.search(r'^author: (.*)$', source, re.M).group(1)
    date = re.search(r'^date: (.*)$', source, re.M).group(1)
    abstract = source.split('## Abstract\n', 1)[1].split('**2020 Mathematics', 1)[0]
    acknowledgment = source.split('## 7. Acknowledgments and use of AI\n', 1)[1].split('## References', 1)[0]
    plain = subprocess.check_output([pandoc, '--from=markdown+tex_math_single_backslash',
        '--to=plain', '--wrap=none'], input=abstract + '\n' + acknowledgment, encoding='utf-8')
    description = '\n'.join('<p>' + escape(p.replace('\n', ' ')) + '</p>' for p in plain.strip().split('\n\n'))
    # A reusable field sheet, not an API call or a claim of a published DOI.
    meta = {"title": title,
            "creators": [{"name": author.rsplit(' ', 1)[1] + ', ' + author.rsplit(' ', 1)[0],
                          "orcid": ORCID}],
            "upload_type": "publication", "publication_type": "preprint", "access_right": "open",
            "license": "cc-by-4.0", "language": "eng", "version": datetime.strptime(date, '%d %B %Y').date().isoformat(),
            "keywords": ['Juggler map', 'Juggler sequence', 'floor-power map', 'cycle financing', 'integer dynamics'],
            "description": description,
            "related_identifiers": [{"identifier": "https://github.com/sneakyweasel/btlab", "relation": "isSupplementTo", "scheme": "url"}]}
    meta = carry_forward(root, meta)
    (root / METADATA).write_text(json.dumps(meta, ensure_ascii=False, indent=2) + '\n', encoding="utf-8", newline="")


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


def build(root: Path, args) -> None:
    initial_inputs = {p: digest(root / p, "text") for p in input_files(root)}
    pandoc = executable("pandoc", args.pandoc)
    xelatex = executable("xelatex", args.xelatex)
    work = Path(args.build_dir).resolve() if args.build_dir else root / ".build/paper_a"
    work.mkdir(parents=True, exist_ok=True)
    tex = work / "cochin-juggler.tex"
    subprocess.run([pandoc, str(root / SOURCE), "--from=markdown+tex_math_single_backslash+autolink_bare_uris",
                    "--to=latex", "--standalone", "--no-highlight", "--ascii",
                    "--template", str(root / "tools/paper_a/article.tex"),
                    "--lua-filter", str(root / "tools/paper_a/layout.lua"),
                    "--output", str(tex)], check=True, cwd=root)
    # Reserve the bottom-rule height on every page, including the last. A
    # last-foot-only rule can otherwise spill to a header-only continuation.
    latex = tex.read_text(encoding="utf-8")
    latex = latex.replace(
        "\\bottomrule\\noalign{}\n\\endlastfoot",
        "\\bottomrule\\noalign{}\n\\endfoot\n\\bottomrule\\noalign{}\n\\endlastfoot",
    )
    latex = re.sub(r"\\\\\n(\\end\{longtable\})", r"\\\\*\n\1", latex)
    tex.write_text(latex, encoding="utf-8", newline="")
    versions = {}
    for name, exe in [("pandoc", pandoc), ("xelatex", xelatex)]:
        versions[name] = subprocess.check_output([exe, "--version"], encoding="utf-8", errors="replace").splitlines()[0]
    for iteration in range(1, 4):
        run = subprocess.run([xelatex, "-no-shell-escape", "-interaction=nonstopmode",
                              "-halt-on-error", tex.name], cwd=work,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        (work / f"xelatex-pass-{iteration}.txt").write_text(run.stdout, encoding="utf-8", newline="")
        if run.returncode:
            raise ValueError(f"XeLaTeX failed; see {work / f'xelatex-pass-{iteration}.txt'}")
    log = tex.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
    failures = [line for line in log.splitlines() if
                re.search(r"^!|Overfull \\[hv]box|Missing character:|undefined references|multiply defined", line)]
    if failures and not args.allow_layout_warnings:
        raise ValueError("Fix layout before release:\n" + "\n".join(failures))
    if args.allow_layout_warnings:
        print(f"Draft preview only; no release updated. Logs: {work}")
        return
    if initial_inputs != {p: digest(root / p, "text") for p in input_files(root)}:
        raise ValueError("Paper A inputs changed during compilation; rebuild required")
    shutil.copyfile(tex, root / TEX)
    shutil.copyfile(tex.with_suffix(".pdf"), root / PDF)
    write_metadata(root, pandoc)
    release = {"schema": 1, "canonical_source": SOURCE,
               "status": "local preprint revision; no new version uploaded by this build",
               "verification_scope": "File provenance only. Mathematical trust boundaries are in the manuscript and reviewer packet.",
               "tools": versions,
               "inputs": [{"path": p, "mode": "text", "sha256": digest(root / p, "text")} for p in input_files(root)],
               "outputs": [{"path": p, "mode": "binary" if p == PDF else "text",
                            "sha256": digest(root / p, "binary" if p == PDF else "text")} for p in OUTPUTS]}
    (root / MANIFEST).write_text(json.dumps(release, indent=2) + "\n", encoding="utf-8", newline="")
    sync(root)
    check(root)
    print(f"Built and synchronized Paper A. Logs: {work}")


def main():
    _pin_build_date()
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--sync", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    parser.add_argument("--build-dir")
    parser.add_argument("--pandoc")
    parser.add_argument("--xelatex")
    parser.add_argument("--allow-layout-warnings", action="store_true", help="Draft preview only")
    args = parser.parse_args()
    try:
        if args.check:
            check(args.root)
            print("Paper A source, build inputs, canonical outputs, and generated copies agree.")
        elif args.sync:
            sync(args.root)
            check(args.root)
            print("Synchronized Paper A exports from the validated canonical build.")
        else:
            build(args.root, args)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"Paper A: {exc}\n")


if __name__ == "__main__":
    main()
