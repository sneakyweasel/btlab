"""Build the living Paper E and validate its proofs, provenance, and exports.

Paper E compares exact coding, arithmetic transport, and signed ancestor counts.

Requires Pandoc and XeLaTeX only for a build. --check and --sync use the Python standard
library. Text hashes normalize line endings for Git on Windows. The manifest establishes
provenance and consistency. A separate fresh local Lean audit and exact finite
checks are required before the builder accepts mathematical inputs.

The input set includes the complete transitive local Lean import closure and exact
certificate. A deterministic ZIP archives the inputs. No external submission occurs.
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
import io
import zipfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_e_common import lean_inputs, REPORT
from check_paper_e import check as check_mathematics


# Reproducible output. XeLaTeX stamps a build time into the PDF's compressed metadata, so
# without this a no-op rebuild changes the bytes and therefore the sha256 in the manifest.
_SOURCE_DATE_EPOCH = "1790035200"  # Local revision, 22 September 2026


def _pin_build_date() -> None:
    os.environ.setdefault("SOURCE_DATE_EPOCH", _SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")


ROOT = Path(__file__).resolve().parents[1]
STEM = "juggler_signed_collatz_note"
SOURCE = f"docs/theory/{STEM}.md"
PDF = f"juggler_review/{STEM}.pdf"
TEX = "docs/theory/cochin-juggler-signed-collatz.tex"
MANIFEST = "docs/theory/paper_e_release.json"
METADATA = "docs/theory/paper_e_zenodo.json"
OUTPUTS = [PDF, TEX, METADATA]
EDITORIAL = [SOURCE, "docs/theory/PAPER_E_BUILD.md", "docs/theory/paper_e_review.md"]
BUILD_INPUTS = [
    "tools/build_paper_e.py", "tools/paper_e_common.py", "tools/check_paper_e.py",
    "tools/paper_e/article.tex", "tools/paper_e/layout.lua",
    "tools/generate_signed_grid_certificate.py",
    "src/research/juggler_sequence/negative_preimage_density.py",
    "src/research/__init__.py", "src/research/juggler_sequence/__init__.py",
    "src/research/juggler_sequence/lean_paths.py",
    "data/research/juggler/negative_preimage_density/grid_k12_certificate.json",
    "data/research/juggler/negative_preimage_density/README.md",
    "docs/problems/juggler_cycle_denominator_coupling.md",
    "docs/problems/juggler_negative_preimage_density.md",
    "literature/bernstein-lagarias-1996-conjugacy-map.json",
    "literature/krasikov-lagarias-2003-difference-inequalities.json",
    "literature/boshernitzan-1994-hardy-fields.json",
    "literature/terras-1976-stopping-time.json",
    "literature/prasad-prasad-2025-juggler-like.json",
    "docs/theory/finite_weyl_differencing_note.md",
    "docs/theory/qualitative_weyl_cancellation_note.md",
    "docs/theory/first_derivative_power_cancellation_note.md",
    "docs/theory/mixed_power_cancellation_note.md",
    "docs/theory/fourier_box_recurrence_note.md",
    "docs/theory/paper_e_counting_corollaries_note.md",
    "docs/theory/juggler_effective_modular_return_note.md",
    "docs/theory/juggler_effective_modular_return_audit.md",
    "docs/theory/finite_fejer_box_note.md",
    "literature/arias-de-reyna-2024-explicit-derivative-estimate.json",
    "formal/AxiomCheckPaperECorollaries.lean", "formal/AxiomCheckPaperECorollaries.expected",
    "LICENSE", "pyproject.toml", REPORT,
    "tests/unit/test_paper_e_release.py",
    "juggler_review/zenodo_paper_e/README.md",
]
KIT = "juggler_review/zenodo_paper_e"
#: the deposit carries the PDF under a readable name; the repository keeps one copy, in
#: juggler_review/, and this is a byte-identical alias of it.
DEPOSIT_PDF = f"{KIT}/Juggler_and_signed_Collatz.pdf"
SOURCE_ZIP = f"{KIT}/Sources_and_certificate.zip"
PDF_EXPORTS = [DEPOSIT_PDF]
VERSION = "0.6.0"
#: Zenodo takes the bare identifier, not the URL, beside the creator's name.
ORCID = "0009-0004-1939-3382"


def digest(path: Path, mode: str = "binary") -> str:
    data = path.read_bytes()
    if mode == "text" and path.suffix.lower() not in {".png", ".pdf"}:
        data = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def input_files(root: Path) -> list[str]:
    return sorted(set(EDITORIAL + BUILD_INPUTS + lean_inputs(root)))


def safe_path(root: Path, name: str) -> Path:
    p = (root / name).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError(f"Path outside repository: {name}")
    return p


def read_release(root: Path) -> dict:
    release = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    if release.get("schema") != 1 or release.get("canonical_source") != SOURCE:
        raise ValueError("Unrecognized Paper E release manifest")
    required = set(input_files(root))
    recorded = {row["path"] for row in release["inputs"]}
    if required != recorded:
        missing = sorted(required - recorded) or sorted(recorded - required)
        raise ValueError(f"Paper E input inventory changed ({missing}); rebuild required")
    for row in release["inputs"] + release["outputs"]:
        p = safe_path(root, row["path"])
        if not p.is_file() or digest(p, row["mode"]) != row["sha256"]:
            raise ValueError(f"Stale or missing Paper E file: {row['path']}; rebuild required")
    if {row["path"] for row in release["outputs"]} != set(OUTPUTS):
        raise ValueError("Incomplete Paper E output manifest")
    return release


def export_pairs(root: Path):
    pairs = [(name, "juggler_review/" + Path(name).name) for name in EDITORIAL]
    pairs.extend((PDF, name) for name in PDF_EXPORTS)
    return pairs


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

def checksums(root: Path) -> str:
    lines = ["# sha256 of the files in this kit and of the PDF they alias.",
             "# Regenerate with `python tools/build_paper_e.py --sync`."]
    for name in [DEPOSIT_PDF, PDF, SOURCE_ZIP]:
        lines.append(f"{digest(root / name, 'binary')}  {name}")
    return "\n".join(lines) + "\n"


def source_archive(root: Path) -> bytes:
    """Stable timestamps and normalized text make the supplement reproducible."""
    buffer = io.BytesIO()
    names = sorted(set(input_files(root) + [TEX, METADATA, MANIFEST]))
    with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in names:
            info = zipfile.ZipInfo(name, time.gmtime(int(_SOURCE_DATE_EPOCH))[:6])
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            data = (root / name).read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
            archive.writestr(info, data)
    return buffer.getvalue()


def sync(root: Path) -> None:
    read_release(root)
    for source, target in export_pairs(root):
        p = root / target
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / source, p)
    meta = json.loads((root / METADATA).read_text(encoding="utf-8"))
    (root / KIT / "ZENODO_FIELDS.txt").write_text(zenodo_fields(meta), encoding="utf-8", newline="")
    (root / SOURCE_ZIP).write_bytes(source_archive(root))
    (root / KIT / "SHA256SUMS.txt").write_text(checksums(root), encoding="utf-8", newline="")


def check(root: Path, exports: bool = True) -> None:
    read_release(root)
    meta = json.loads((root / METADATA).read_text(encoding="utf-8"))
    if meta["version"] != VERSION or f"Version {VERSION}" not in (root / SOURCE).read_text(encoding="utf-8"):
        raise ValueError("Paper E version differs between manuscript, builder, and metadata")
    if not exports:
        return
    for source, target in export_pairs(root):
        mode = "text" if target.endswith(".md") else "binary"
        if not (root / target).is_file() or digest(root / source, mode) != digest(root / target, mode):
            raise ValueError(f"Stale generated copy: {target}; run --sync")
    meta = json.loads((root / METADATA).read_text(encoding="utf-8"))
    if (root / KIT / "ZENODO_FIELDS.txt").read_text(encoding="utf-8") != zenodo_fields(meta):
        raise ValueError("Stale Zenodo fields; run --sync")
    if not (root / SOURCE_ZIP).is_file() or (root / SOURCE_ZIP).read_bytes() != source_archive(root):
        raise ValueError("Stale source-and-certificate archive; run --sync")
    if (root / KIT / "SHA256SUMS.txt").read_text(encoding="utf-8") != checksums(root):
        raise ValueError("Stale checksums; run --sync")


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
        "title": title + ": Exact Coding and Arithmetic Obstructions",
        "creators": [{"name": author.rsplit(" ", 1)[1] + ", " + author.rsplit(" ", 1)[0],
                      "orcid": ORCID}],
        "upload_type": "publication", "publication_type": "preprint", "access_right": "open",
        "license": "cc-by-4.0", "language": "eng", "version": VERSION,
        "keywords": ["Juggler map", "signed Collatz maps", "2-adic parity coding",
                     "inverse trees", "computer-assisted proof", "Lean"],
        "description": description,
        "related_identifiers": [
            {"identifier": "https://github.com/sneakyweasel/btlab", "relation": "isSupplementTo",
             "scheme": "url"},
            {"identifier": "10.5281/zenodo.22676452", "relation": "cites", "scheme": "doi"},
            {"identifier": "10.5281/zenodo.22864933", "relation": "cites", "scheme": "doi"},
            {"identifier": "10.5281/zenodo.22678164", "relation": "cites", "scheme": "doi"},
            {"identifier": "10.5281/zenodo.22876189", "relation": "cites", "scheme": "doi"},
        ],
    }
    meta = carry_forward(root, meta)
    (root / METADATA).write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="")


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
    check_mathematics(root)
    previous = root / MANIFEST
    publication = (json.loads(previous.read_text(encoding="utf-8")).get("publication")
                   if previous.is_file() else None)
    initial_inputs = {p: digest(root / p, "text") for p in input_files(root)}
    pandoc = executable("pandoc", args.pandoc)
    xelatex = executable("xelatex", args.xelatex)
    work = Path(args.build_dir).resolve() if args.build_dir else root / ".build/paper_e"
    work.mkdir(parents=True, exist_ok=True)
    tex = work / Path(TEX).name
    subprocess.run([pandoc, str(root / SOURCE),
                    "--from=markdown+tex_math_single_backslash+autolink_bare_uris",
                    "--to=latex", "--standalone", "--no-highlight", "--ascii",
                    "--template", str(root / "tools/paper_e/article.tex"),
                    "--lua-filter", str(root / "tools/paper_e/layout.lua"),
                    "--output", str(tex)], check=True, cwd=root)
    latex = tex.read_text(encoding="utf-8")
    latex = latex.replace("\\bottomrule\\noalign{}\n\\endlastfoot",
                          "\\bottomrule\\noalign{}\n\\endfoot\n\\bottomrule\\noalign{}\n\\endlastfoot")
    latex = re.sub(r"\\\\\n(\\end\{longtable\})", r"\\\\*\n\1", latex)
    tex.write_text(latex, encoding="utf-8", newline="")
    versions = {name: subprocess.check_output([exe, "--version"], encoding="utf-8",
                                              errors="replace").splitlines()[0]
                for name, exe in (("pandoc", pandoc), ("xelatex", xelatex))}
    for iteration in range(1, 4):
        run = subprocess.run([xelatex, "-no-shell-escape", "-interaction=nonstopmode",
                              "-halt-on-error", tex.name], cwd=work, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
        (work / f"xelatex-pass-{iteration}.txt").write_text(run.stdout, encoding="utf-8", newline="")
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
        raise ValueError("Paper E inputs changed during compilation; rebuild required")
    pages = re.search(r"Output written on .*?\((\d+) pages?", log)
    shutil.copyfile(tex, root / TEX)
    (root / PDF).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(tex.with_suffix(".pdf"), root / PDF)
    write_metadata(root, pandoc)
    release = {
        "schema": 1, "canonical_source": SOURCE,
        "status": "living preprint; independent review pending; no external deposit",
        "verification_scope": "File provenance only. The mathematical trust boundaries are in the "
                              "manuscript and in PAPER_E_BUILD.md.",
        "pages": int(pages.group(1)) if pages else None,
        "tools": versions,
        "inputs": [{"path": p, "mode": "text", "sha256": digest(root / p, "text")}
                   for p in input_files(root)],
        "outputs": [{"path": p, "mode": "binary" if p == PDF else "text",
                     "sha256": digest(root / p, "binary" if p == PDF else "text")} for p in OUTPUTS],
    }
    if publication is not None:
        release["publication"] = publication
    (root / MANIFEST).write_text(json.dumps(release, indent=2) + "\n", encoding="utf-8", newline="")
    sync(root)
    check(root)
    print(f"Built and synchronized Paper E ({release['pages']} pages). Logs: {work}")


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
        print(f"Paper E matches its source and manifest.")
    elif args.sync:
        sync(args.root)
        print("Synchronized Paper E exports.")
    else:
        build(args.root, args)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(exc, file=sys.stderr)
        sys.exit(1)
