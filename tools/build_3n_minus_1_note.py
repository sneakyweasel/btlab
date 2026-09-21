"""Build the 3n-1 m-cycle note to PDF, or verify that the PDF matches its source.

Pandoc + XeLaTeX, the Paper C chain: the same reader extensions, the note's own
copies of the article template and layout filter under ``tools/collatz_note/``,
three XeLaTeX passes, and a refusal to release on overfull boxes, missing
characters or unresolved references unless ``--allow-layout-warnings`` (draft
preview, nothing copied) is given. The PDF is
``juggler_review/collatz_3n_minus_1_m_cycles_note.pdf``; the TeX, the logs and
the manifest live in ``.build/collatz_3n_minus_1_note/``. ``--check`` recomputes
the manifest's digests, so a manuscript edit shipped without a rebuild fails.
The manifest records provenance, not mathematical correctness.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STEM = "collatz_3n_minus_1_m_cycles_note"
SOURCE = f"docs/theory/{STEM}.md"
PDF = f"juggler_review/{STEM}.pdf"
WORK = ".build/collatz_3n_minus_1_note"
TEX_NAME = "cochin-3n-minus-1-m-cycles.tex"
TEMPLATE = "tools/collatz_note/article.tex"
FILTER = "tools/collatz_note/layout.lua"
MANIFEST = f"{WORK}/manifest.json"
INPUTS = [SOURCE, TEMPLATE, FILTER, "tools/build_3n_minus_1_note.py"]
# XeLaTeX stamps a build time into the PDF; pin it to the note's date so a
# no-op rebuild reproduces the bytes (21 September 2026, 00:00 UTC).
SOURCE_DATE_EPOCH = "1789948800"
LAYOUT_FAILURE = re.compile(r"^!|Overfull \\[hv]box|Missing character:|undefined references|multiply defined")


def digest(path: Path, mode: str) -> str:
    data = path.read_bytes()
    if mode == "text":
        data = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(data).hexdigest()


def digests(root: Path) -> dict:
    return {"inputs": {p: digest(root / p, "text") for p in INPUTS},
            "outputs": {PDF: digest(root / PDF, "binary")}}


def executable(name: str, explicit: str | None) -> str:
    if explicit:
        return explicit
    found = shutil.which(name)
    if found:
        return found
    if name == "pandoc":
        candidates = [Path(os.environ.get("PROGRAMFILES", "C:/Program Files")) / "Pandoc/pandoc.exe"]
    else:
        candidates = [Path(os.environ.get("LOCALAPPDATA", "")) / "Programs/MiKTeX/miktex/bin/x64/xelatex.exe"]
    for c in candidates:
        if c.is_file():
            return str(c)
    raise FileNotFoundError(f"{name} not found; pass --{name}")


def build(root: Path, args) -> None:
    os.environ.setdefault("SOURCE_DATE_EPOCH", SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")
    pandoc = executable("pandoc", args.pandoc)
    xelatex = executable("xelatex", args.xelatex)
    work = root / WORK
    work.mkdir(parents=True, exist_ok=True)
    tex = work / TEX_NAME
    subprocess.run([pandoc, str(root / SOURCE), "--from=markdown+tex_math_single_backslash+autolink_bare_uris",
                    "--to=latex", "--standalone", "--no-highlight", "--ascii",
                    "--template", str(root / TEMPLATE), "--lua-filter", str(root / FILTER),
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
        run = subprocess.run([xelatex, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
                              tex.name], cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             encoding="utf-8", errors="replace")
        (work / f"xelatex-pass-{iteration}.txt").write_text(run.stdout, encoding="utf-8")
        if run.returncode:
            raise ValueError(f"XeLaTeX failed; see {work / f'xelatex-pass-{iteration}.txt'}")
    log = tex.with_suffix(".log").read_text(encoding="utf-8", errors="replace")
    failures = [line for line in log.splitlines() if LAYOUT_FAILURE.search(line)]
    if failures and not args.allow_layout_warnings:
        raise ValueError("Fix layout before release:\n" + "\n".join(failures))
    if args.allow_layout_warnings:
        print(f"Draft preview only; nothing copied. PDF and logs: {work}")
        return
    pages = re.search(r"Output written on .*?\((\d+) pages?", log)
    (root / PDF).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(tex.with_suffix(".pdf"), root / PDF)
    manifest = {"schema": 1, "canonical_source": SOURCE, "status": "laboratory draft; no external deposit",
                "source_date_epoch": SOURCE_DATE_EPOCH, "tools": versions,
                "pages": int(pages.group(1)) if pages else None, **digests(root)}
    (root / MANIFEST).write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Built {PDF} ({manifest['pages']} pages). Logs and manifest: {work}")


def check(root: Path) -> None:
    manifest = json.loads((root / MANIFEST).read_text(encoding="utf-8"))
    current = digests(root)
    stale = [p for p, h in current["inputs"].items() if manifest["inputs"].get(p) != h]
    stale += [p for p, h in current["outputs"].items() if manifest["outputs"].get(p) != h]
    if stale:
        raise ValueError("Out of date against the manifest; rebuild with python tools/build_3n_minus_1_note.py: "
                         + ", ".join(stale))
    print(f"{PDF} matches its source and manifest ({manifest.get('pages')} pages).")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--allow-layout-warnings", action="store_true", help="Draft preview only")
    parser.add_argument("--pandoc")
    parser.add_argument("--xelatex")
    args = parser.parse_args()
    if args.check:
        check(ROOT)
    else:
        build(ROOT, args)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, FileNotFoundError, subprocess.CalledProcessError) as exc:
        print(exc, file=sys.stderr)
        sys.exit(1)
