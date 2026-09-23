"""Build Paper C from docs/theory and validate/synchronize its generated exports.

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
import shutil
import subprocess


# Reproducible output.  XeLaTeX stamps a build time into the PDF's compressed metadata, so
# without this a no-op rebuild changes the bytes and therefore the sha256 in the manifest.
# The epoch is fixed to the version the build guide records rather than taken from git,
# because a git-derived date lags one build behind an edit and merely relocates the churn.
_SOURCE_DATE_EPOCH = "1790035200"  # Local revision, 22 September 2026


def _pin_build_date() -> None:
    """Pin SOURCE_DATE_EPOCH unless the caller already set one."""
    os.environ.setdefault("SOURCE_DATE_EPOCH", _SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")

ROOT = Path(__file__).resolve().parents[1]
STEM = "juggler_fate_almost_all_note"
SOURCE = f"docs/theory/{STEM}.md"
PDF = f"preprints/{STEM}.pdf"
TEX = "docs/theory/cochin-juggler-fates.tex"
MANIFEST = "docs/theory/paper_c_release.json"
METADATA = "docs/theory/paper_c_zenodo.json"
OUTPUTS = [PDF, TEX, METADATA]
EDITORIAL = [SOURCE, "docs/theory/PAPER_C_BUILD.md"]
BUILD_INPUTS = ["docs/theory/juggler_ooee_poor_fibre_tail_note.md",
                "docs/theory/juggler_ooee_contagion_note.md",
                "docs/theory/juggler_ooee_mixed_modes_note.md",
                "formal/AxiomCheckOOEEMixedModes.lean",
                "formal/AxiomCheckOOEEMixedModes.expected",
                "formal/AxiomCheckScaleAverage.lean",
                "formal/AxiomCheckScaleAverage.expected",
                "tools/build_paper_c.py", "tools/paper_c/article.tex",
                "tools/paper_c/layout.lua", "tools/check_paper_c_numeric.py",
                "src/research/juggler_sequence/paper_c_audit.py",
                "src/research/juggler_sequence/paper_c_formal_layer.py",
                "docs/theory/figures/render_paper_c_figures.py",
                "data/research/juggler/paper_c_publication_review/validation.json"]
FIGURES = ["paper_c_productions.png", "paper_c_decomposition.png", "paper_c_dependencies.png"]
# The PDF lives in `preprints/` now, and is exported only under the
# historical name the Zenodo deposit carries. The companion site links the
# published DOIs instead of serving its own copy, so `public/papers/` and
# `dist/papers/` are gone.
#: Zenodo takes the bare identifier, not the URL, beside the creator's name.
ORCID = "0009-0004-1939-3382"
PDF_EXPORTS = ["preprints/zenodo_paper_c/Fate_Contagion_Juggler_Map.pdf"]


def digest(path: Path, mode: str = "binary") -> str:
    data = path.read_bytes()
    if mode == "text" and path.suffix.lower() not in {".png", ".pdf"}:
        data = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def input_files(root: Path) -> list[str]:
    """Pin the actual transitive Paper C Lean imports, including their audit."""
    names = set(EDITORIAL + BUILD_INPUTS + ["formal/lean-toolchain",
                "formal/lake-manifest.json", "formal/AxiomCheckPaperC.lean",
                "formal/AxiomCheckPaperC.expected"])
    pending = ["formal/Problems/JugglerFatePaper.lean",
               "formal/Problems/Juggler/FateOOEEAssembly.lean",
               "formal/Problems/Juggler/FateOEWeighted.lean",
               "formal/Problems/Juggler/OOEEMixedModes.lean",
               "formal/Problems/Juggler/FateScaleAverage.lean"]
    while pending:
        name = pending.pop()
        if name in names:
            continue
        names.add(name)
        text = (root / name).read_text(encoding="utf-8")
        for module in re.findall(r"^import\s+((?:Problems|BTCalculus)\.[\w.]+)", text, re.M):
            pending.append("formal/" + module.replace(".", "/") + ".lean")
    names.update("docs/theory/figures/" + name for name in FIGURES)
    source_text = (root / SOURCE).read_text(encoding="utf-8")
    for name in re.findall(r"^- `([^`]+)`\n\n  SHA-256:", source_text, re.M):
        names.add(name)
    return sorted(names)


def safe_path(root: Path, name: str) -> Path:
    p = (root / name).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError(f"Path outside repository: {name}")
    return p


def read_release(root: Path) -> dict:
    release = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    if release.get("schema") != 1 or release.get("canonical_source") != SOURCE:
        raise ValueError("Unrecognized Paper C release manifest")
    required = set(input_files(root))
    recorded = {row["path"] for row in release["inputs"]}
    if required != recorded:
        raise ValueError("Paper C input inventory changed; rebuild required")
    for row in release["inputs"] + release["outputs"]:
        p = safe_path(root, row["path"])
        if not p.is_file() or digest(p, row["mode"]) != row["sha256"]:
            raise ValueError(f"Stale or missing Paper C file: {row['path']}; rebuild required")
    if {row["path"] for row in release["outputs"]} != set(OUTPUTS):
        raise ValueError("Incomplete Paper C output manifest")
    return release


def export_pairs(root: Path):
    return [(PDF, name) for name in PDF_EXPORTS]


def sync(root: Path) -> None:
    read_release(root)
    for source, target in export_pairs(root):
        p = root / target
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / source, p)
    fields = zenodo_fields(json.loads((root / METADATA).read_text(encoding="utf-8")))
    (root / "preprints/zenodo_paper_c/ZENODO_FIELDS.txt").write_text(fields, encoding="utf-8", newline="")


def check(root: Path, exports: bool = True) -> None:
    read_release(root)
    if exports:
        for source, target in export_pairs(root):
            mode = "text" if target.endswith(".md") else "binary"
            if not (root / target).is_file() or digest(root / source, mode) != digest(root / target, mode):
                raise ValueError(f"Stale generated copy: {target}; run --sync")
        fields = (root / "preprints/zenodo_paper_c/ZENODO_FIELDS.txt").read_text(encoding="utf-8")
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
    acknowledgment = source.split('## Acknowledgments and use of AI\n', 1)[1].split('## Availability', 1)[0]
    plain = subprocess.check_output([pandoc, '--from=markdown+tex_math_single_backslash',
        '--to=plain', '--wrap=none'], input=abstract + '\n' + acknowledgment, encoding='utf-8')
    description = '\n'.join('<p>' + escape(p.replace('\n', ' ')) + '</p>' for p in plain.strip().split('\n\n'))
    # A reusable field sheet, not an API call or a claim of a published DOI.
    meta = {"title": title,
            "creators": [{"name": author.rsplit(' ', 1)[1] + ', ' + author.rsplit(' ', 1)[0],
                          "orcid": ORCID}],
            "upload_type": "publication", "publication_type": "preprint", "access_right": "open",
            "license": "cc-by-4.0", "language": "eng", "version": datetime.strptime(date, '%d %B %Y').date().isoformat(),
            "keywords": ['Juggler map', 'preimage sets', 'logarithmic counting', 'parity cylinders', 'integer dynamics'],
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
    previous_release = root / MANIFEST
    publication = (json.loads(previous_release.read_text(encoding="utf-8")).get("publication")
                   if previous_release.is_file() else None)
    initial_inputs = {p: digest(root / p, "text") for p in input_files(root)}
    pandoc = executable("pandoc", args.pandoc)
    xelatex = executable("xelatex", args.xelatex)
    work = Path(args.build_dir).resolve() if args.build_dir else root / ".build/paper_c"
    work.mkdir(parents=True, exist_ok=True)
    tex = work / "cochin-juggler-fates.tex"
    subprocess.run([pandoc, str(root / SOURCE), "--from=markdown+tex_math_single_backslash+autolink_bare_uris",
                    "--to=latex", "--standalone", "--no-highlight", "--ascii",
                    "--template", str(root / "tools/paper_c/article.tex"),
                    "--lua-filter", str(root / "tools/paper_c/layout.lua"),
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
    figure_dir = work / "figures"
    figure_dir.mkdir(exist_ok=True)
    for name in FIGURES:
        shutil.copyfile(root / "docs/theory/figures" / name, figure_dir / name)
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
        raise ValueError("Paper C inputs changed during compilation; rebuild required")
    shutil.copyfile(tex, root / TEX)
    shutil.copyfile(tex.with_suffix(".pdf"), root / PDF)
    write_metadata(root, pandoc)
    release = {"schema": 1, "canonical_source": SOURCE,
               "status": "preprint; no external deposit performed",
               "verification_scope": "File provenance only. Mathematical trust boundaries are in the manuscript and PAPER_C_BUILD.md.",
               "tools": versions,
               "inputs": [{"path": p, "mode": "binary" if p.endswith(".png") else "text", "sha256": digest(root / p, "text")} for p in input_files(root)],
               "outputs": [{"path": p, "mode": "binary" if p == PDF else "text",
                            "sha256": digest(root / p, "binary" if p == PDF else "text")} for p in OUTPUTS]}
    if publication is not None:
        release["publication"] = publication
    (root / MANIFEST).write_text(json.dumps(release, indent=2) + "\n", encoding="utf-8", newline="")
    sync(root)
    check(root)
    print(f"Built and synchronized Paper C. Logs: {work}")


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
            print("Paper C source, build inputs, canonical outputs, and generated copies agree.")
        elif args.sync:
            sync(args.root)
            check(args.root)
            print("Synchronized Paper C exports from the validated canonical build.")
        else:
            build(args.root, args)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"Paper C: {exc}\n")


if __name__ == "__main__":
    main()
