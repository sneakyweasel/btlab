"""Build, check and package any of the laboratory's papers with one procedure.

    python tools/build_paper.py A                  build the PDF, metadata, manifest and kit
    python tools/build_paper.py A --check          verify release and kit against the manifest
    python tools/build_paper.py A --check-release  verify the release only (an extracted archive)
    python tools/build_paper.py A --sync           regenerate the kit from a current release

Everything particular to a paper lives in `tools/papers/<letter>.json`: its files, its
Lean roots, its Zenodo fields, its LaTeX settings and the checks it runs first. The steps
are the same for every paper. Requires Pandoc and XeLaTeX only for a build; the checks use
the standard library. The manifest establishes provenance and consistency, not mathematical
correctness.
"""
from __future__ import annotations

import argparse
from datetime import date, datetime, timezone
import hashlib
from html import escape, unescape
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
BUILDER = "tools/build_paper.py"
BINARY = {".png", ".pdf", ".zip", ".jpg"}
LAYOUT_FAILURE = re.compile(
    r"^!|Overfull \\[hv]box|Missing character:|undefined references|multiply defined")
#: Facts about an external record; the build cannot learn them and must not invent them.
CARRIED = ("doi", "publication_date", "conceptdoi", "record_url", "latest_deposit")
#: Zenodo takes the bare identifier, not the URL, beside the creator's name.
ORCID = "0009-0004-1939-3382"
#: The upload form's labels for the relation and resource-type codes the metadata stores.
FORM_RELATIONS = {"isSupplementTo": "Is supplement to", "cites": "Cites", "isCitedBy": "Is cited by"}
FORM_RESOURCE_TYPES = {"software": "Software", "publication-preprint": "Publication / Preprint"}


def digest(path: Path, mode: str = "text") -> str:
    """Text is hashed with normalised line endings, so a CRLF checkout agrees with LF."""
    return hashlib.sha256(payload(path, mode)).hexdigest()


def payload(path: Path, mode: str = "text") -> bytes:
    data = path.read_bytes()
    if mode == "text" and path.suffix.lower() not in BINARY:
        data = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return data


def mode_of(name: str) -> str:
    return "binary" if Path(name).suffix.lower() in BINARY else "text"


def carry(meta: dict, old: dict) -> dict:
    """Keep the deposit facts the previous metadata records; only a deposit can supply them."""
    old = old.get("metadata", old)
    return {**meta, **{key: old[key] for key in CARRIED if key in old}}


def lean_closure(root: Path, roots: list[str]) -> set[str]:
    """The given Lean files and every repository-local module they import, transitively."""
    found: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in found:
            continue
        found.add(name)
        text = (root / name).read_text(encoding="utf-8")
        for module in re.findall(r"^import\s+([\w.]+)", text, re.M):
            candidate = "formal/" + module.replace(".", "/") + ".lean"
            if (root / candidate).is_file():
                pending.append(candidate)
    return found


class Paper:
    """One paper's settings, with the attributes the pin and preprint gates read."""

    def __init__(self, letter: str, root: Path = ROOT):
        self.letter = letter.lower()
        self.root = root
        self.config_path = f"tools/papers/{self.letter}.json"
        c = json.loads((root / self.config_path).read_text(encoding="utf-8"))
        self.c = c
        self.STEM = c["stem"]
        self.SOURCE = f"docs/theory/{self.STEM}.md"
        self.PDF = f"preprints/{self.STEM}.pdf"
        self.TEX = c["tex"]
        self.MANIFEST = f"docs/theory/paper_{self.letter}_release.json"
        self.METADATA = f"docs/theory/paper_{self.letter}_zenodo.json"
        self.OUTPUTS = [self.PDF, self.TEX, self.METADATA]
        self.EDITORIAL = [self.SOURCE, *c.get("editorial", [])]
        self.KIT = f"preprints/zenodo_paper_{self.letter}"
        self.DEPOSIT_PDF = f"{self.KIT}/{c['deposit_pdf']}"
        self.ARCHIVE = f"{self.KIT}/paper_{self.letter}_sources.zip"
        self.FIELDS = f"{self.KIT}/ZENODO_FIELDS.txt"
        self.SUMS = f"{self.KIT}/SHA256SUMS.txt"
        self.KIT_DOCS = [f"{self.KIT}/README.md", f"{self.KIT}/AFTER_ZENODO.md"]
        self.version = c["version"]
        self.epoch = str(int(datetime.combine(date.fromisoformat(c["date"]), datetime.min.time(),
                                              tzinfo=timezone.utc).timestamp()))
        self.assets = f"tools/paper_{self.letter}"
        self.__name__ = f"Paper {self.letter.upper()}"

    # ------------------------------------------------------------------ inventory
    def input_files(self, root: Path | None = None) -> list[str]:
        root = root or self.root
        names = set(self.EDITORIAL + self.c.get("inputs", []) + self.c.get("figures", []))
        names.update([BUILDER, self.config_path, f"{self.assets}/article.tex",
                      f"{self.assets}/layout.lua"])
        names.update(lean_closure(root, self.c.get("lean_roots", [])))
        if self.c.get("manuscript_artifacts"):
            text = (root / self.SOURCE).read_text(encoding="utf-8")
            names.update(re.findall(r"^- `([^`]+)`\n\n  SHA-256:", text, re.M))
        return sorted(names)

    def archive_members(self, root: Path) -> list[str]:
        return sorted(set(self.input_files(root) + self.OUTPUTS + [self.MANIFEST]
                          + self.c.get("archive_extra", [])))

    # ------------------------------------------------------------------ release
    def read_release(self, root: Path) -> dict:
        path = root / self.MANIFEST
        if not path.is_file():
            raise ValueError(f"No release manifest {self.MANIFEST}; build the paper")
        release = json.loads(path.read_text(encoding="utf-8"))
        if release.get("schema") != 2 or release.get("canonical_source") != self.SOURCE:
            raise ValueError(f"Unrecognized release manifest {self.MANIFEST}; rebuild required")
        required, recorded = set(self.input_files(root)), {r["path"] for r in release["inputs"]}
        if required != recorded:
            raise ValueError(f"{self.__name__} input inventory changed "
                             f"({sorted(required ^ recorded)[:6]}); rebuild required")
        if {r["path"] for r in release["outputs"]} != set(self.OUTPUTS):
            raise ValueError(f"Incomplete {self.__name__} output manifest")
        for row in release["inputs"] + release["outputs"]:
            p = root / row["path"]
            if not p.is_file() or digest(p, row["mode"]) != row["sha256"]:
                raise ValueError(f"Stale or missing {self.__name__} file: {row['path']}; rebuild required")
        return release

    def check_release(self, root: Path) -> dict:
        release = self.read_release(root)
        text = (root / self.SOURCE).read_text(encoding="utf-8").lower()
        if f"version {self.version}" not in text or release.get("version") != self.version:
            raise ValueError(f"{self.__name__}: version {self.version} differs between "
                             f"{self.config_path}, the manuscript and the manifest")
        return release

    # ------------------------------------------------------------------ metadata
    def metadata(self, root: Path, pandoc: str) -> dict:
        source = (root / self.SOURCE).read_text(encoding="utf-8")
        author = re.search(r"^author: (.*)$", source, re.M).group(1).strip()
        abstract = source.split("## Abstract\n", 1)[1]
        ends = [i for i in (abstract.find("**2020 Mathematics"), abstract.find("\n## ")) if i >= 0]
        abstract = abstract[:min(ends)] if ends else abstract
        plain = subprocess.check_output(
            [pandoc, "--from=markdown+tex_math_single_backslash", "--to=plain", "--wrap=none"],
            input=abstract, encoding="utf-8")
        # Abstract only: the acknowledgments and the AI disclosure are in the paper itself.
        description = "\n".join("<p>" + escape(p.replace("\n", " ")) + "</p>"
                                for p in plain.strip().split("\n\n"))
        z = self.c["zenodo"]
        meta = {"title": z["title"],
                "creators": [{"name": author.rsplit(" ", 1)[1] + ", " + author.rsplit(" ", 1)[0],
                              "orcid": ORCID}],
                "upload_type": "publication", "publication_type": "preprint",
                "access_right": "open", "license": "cc-by-4.0", "language": "eng",
                "version": self.version, "keywords": z["keywords"], "description": description,
                "related_identifiers": z["related"]}
        old_path = root / self.METADATA
        if old_path.is_file():
            meta = carry(meta, json.loads(old_path.read_text(encoding="utf-8")))
        return meta

    # ------------------------------------------------------------------ kit
    def fields(self, meta: dict) -> str:
        doi, published = meta.get("doi"), meta.get("publication_date")
        concept, latest = meta.get("conceptdoi"), meta.get("latest_deposit") or {}
        deposited = doi and meta.get("latest_deposit", {}).get("version") == meta["version"]
        if deposited:
            standing = f"Describes the deposit at doi:{doi}; this build does not upload a new version.\n\n"
        elif concept:
            standing = (f"Version {meta['version']} is prepared and is not deposited. Upload it through "
                        f"the new-version operation of the existing record; concept doi:{concept} "
                        f"resolves to the latest version, {latest.get('version', 'unknown')} at "
                        f"doi:{latest.get('doi', 'unknown')}.\n\n")
        else:
            standing = "Prepared metadata only; no external record has been created.\n\n"
        date_field = (f"PUBLICATION DATE\n{published}\n\n" if deposited else
                      "PUBLICATION DATE\nUse the actual date this version is first made public.\n\n")
        who = meta["creators"][0]
        record = f"RECORD\n{meta['record_url']}\n\n" if deposited and meta.get("record_url") else ""
        related = []
        for r in meta.get("related_identifiers", ()):
            kind = r.get("resource_type") or ("software" if r.get("scheme") == "url" else "publication-preprint")
            related.append(f"Relation: {FORM_RELATIONS.get(r['relation'], r['relation'])}\n"
                           f"Identifier: {r['identifier']}\n"
                           f"Scheme: {r.get('scheme', 'doi').upper()}\n"
                           f"Resource type: {FORM_RESOURCE_TYPES.get(kind, kind)}")
        text = re.sub(r"</p>\s*<p>", "\n\n", meta["description"])
        text = re.sub(r"<[^>]+>", "", text)
        paragraphs = [" ".join(p.split()) for p in unescape(text).split("\n\n")]
        return ("GENERATED BY tools/build_paper.py; do not edit this export.\n" + standing
                + f"TITLE\n{meta['title']}\n\nCREATOR\n{who['name']}\n"
                + (f"ORCID: {who['orcid']}\n" if who.get("orcid") else "")
                + "Affiliation: none\n\nRESOURCE TYPE\nPublication / Preprint\n\n"
                + f"VERSION\n{meta['version']}\n\nLICENSE\n{meta['license']}\n\n"
                + record + date_field
                + "KEYWORDS\n" + "\n".join(meta["keywords"]) + "\n\n"
                + "FILES\n" + Path(self.DEPOSIT_PDF).name + "\n" + Path(self.ARCHIVE).name + "\n\n"
                + "DESCRIPTION (plain text)\n" + "\n\n".join(p for p in paragraphs if p) + "\n\n"
                + "RELATED WORKS\n" + "\n\n".join(related) + "\n")

    def archive_readme(self, root: Path, release: dict) -> str:
        meta = json.loads((root / self.METADATA).read_text(encoding="utf-8"))
        L = self.letter.upper()
        lean = [n for n in release["inputs"] if n["path"].endswith(".lean")]
        lines = [f"# Paper {L}: sources", "",
                 f"{meta['title']}, {meta['creators'][0]['name']}, version {self.version}.",
                 "This archive preserves repository paths; extract it into an empty directory.", "",
                 "## Contents", "",
                 f"- `{self.SOURCE}`, the canonical manuscript, with the generated LaTeX "
                 f"`{self.TEX}` and the PDF `{self.PDF}`.",
                 f"- `{self.MANIFEST}`, the SHA-256 of all {len(release['inputs'])} inputs and "
                 f"{len(release['outputs'])} outputs, and `{self.METADATA}`, the Zenodo metadata.",
                 f"- `{BUILDER}` with `{self.config_path}`, the same builder every laboratory paper "
                 "uses, and the template and layout filter in "
                 f"`{self.assets}/`."]
        if lean:
            lines.append(f"- {len(lean)} Lean files: the paper's local import closure and its "
                         "axiom audits. Mathlib and the Lean toolchain are not included; Lake "
                         "fetches the versions `formal/lake-manifest.json` pins.")
        for item in self.c.get("readme_contents", []):
            lines.append(f"- {item}")
        lines += ["- `SHA256SUMS.txt`, the digest of every other member.", "",
                  "Third-party software, private correspondence and unpublished manuscripts are "
                  "not included. Links in the documents to other laboratory records refer to "
                  "the repository https://github.com/sneakyweasel/btlab.", "",
                  "## Verify", "", "Python 3.11 or later, standard library only. From the extracted root:",
                  "", "```text", f"python {BUILDER} {L} --check-release"]
        lines += self.c.get("verify", [])
        lines += ["```", "",
                  "The first command checks every input and output against the release manifest."]
        if self.c.get("verify_note"):
            lines.append(self.c["verify_note"])
        if self.c.get("lean_build"):
            lines += ["", "For the formal proofs, install elan, then from `formal/`:", "", "```text",
                      "lake exe cache get", *self.c["lean_build"], "```"]
        tools = release.get("tools", {})
        lines += ["", "## Rebuild", "",
                  f"With Pandoc and XeLaTeX installed, `python {BUILDER} {L}` rebuilds the PDF, "
                  "LaTeX, metadata and manifest. The build fixes `SOURCE_DATE_EPOCH`; with "
                  f"{tools.get('pandoc', 'the recorded Pandoc')} and "
                  f"{tools.get('xelatex', 'the recorded XeLaTeX')} it reproduces the PDF byte for byte.",
                  "", "## Scope", "", self.c["scope"], "",
                  "The manuscript is licensed CC BY 4.0 and the software under the repository `LICENSE`.",
                  ""]
        return "\n".join(lines)

    def archive_bytes(self, root: Path) -> bytes:
        release = json.loads((root / self.MANIFEST).read_text(encoding="utf-8"))
        body = {name: payload(root / name, mode_of(name)) for name in self.archive_members(root)}
        body["README.md"] = self.archive_readme(root, release).encode("utf-8")
        body["SHA256SUMS.txt"] = "".join(
            f"{hashlib.sha256(data).hexdigest()}  {name}\n" for name, data in sorted(body.items())
        ).encode("utf-8")
        stamp = time.gmtime(int(self.epoch))[:6]
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            for name, data in sorted(body.items()):
                info = zipfile.ZipInfo(name, stamp)
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                z.writestr(info, data)
        return buffer.getvalue()

    def sums(self, root: Path) -> str:
        names = [self.DEPOSIT_PDF, self.ARCHIVE, self.FIELDS,
                 *[d for d in self.KIT_DOCS if (root / d).is_file()]]
        lines = ["# sha256 of the files in this kit. Regenerate with "
                 f"`python {BUILDER} {self.letter.upper()} --sync`."]
        lines += [f"{hashlib.sha256((root / n).read_bytes()).hexdigest()}  {Path(n).name}"
                  for n in sorted(names)]
        return "\n".join(lines) + "\n"

    def kit_files(self) -> list[str]:
        return [self.DEPOSIT_PDF, self.ARCHIVE, self.FIELDS, self.SUMS, *self.KIT_DOCS]

    def sync(self, root: Path) -> None:
        self.check_release(root)
        (root / self.KIT).mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / self.PDF, root / self.DEPOSIT_PDF)
        meta = json.loads((root / self.METADATA).read_text(encoding="utf-8"))
        (root / self.FIELDS).write_text(self.fields(meta), encoding="utf-8", newline="")
        (root / self.ARCHIVE).write_bytes(self.archive_bytes(root))
        (root / self.SUMS).write_text(self.sums(root), encoding="utf-8", newline="")

    def check(self, root: Path | None = None) -> None:
        root = root or self.root
        self.check_release(root)
        kit_pdf = root / self.DEPOSIT_PDF
        if not kit_pdf.is_file() or kit_pdf.read_bytes() != (root / self.PDF).read_bytes():
            raise ValueError(f"Stale or missing kit PDF {self.DEPOSIT_PDF}; run --sync")
        meta = json.loads((root / self.METADATA).read_text(encoding="utf-8"))
        if not (root / self.FIELDS).is_file() or \
                (root / self.FIELDS).read_text(encoding="utf-8") != self.fields(meta):
            raise ValueError(f"Stale Zenodo fields {self.FIELDS}; run --sync")
        if not (root / self.ARCHIVE).is_file() or \
                not archive_matches(root / self.ARCHIVE, self.archive_bytes(root)):
            raise ValueError(f"Stale source archive {self.ARCHIVE}; run --sync")
        if not (root / self.SUMS).is_file() or \
                (root / self.SUMS).read_text(encoding="utf-8") != self.sums(root):
            raise ValueError(f"Stale kit checksums {self.SUMS}; run --sync")

    # ------------------------------------------------------------------ build
    def build(self, root: Path, args) -> None:
        os.environ["SOURCE_DATE_EPOCH"] = self.epoch
        os.environ["FORCE_SOURCE_DATE"] = "1"
        for command in self.c.get("prebuild", []):
            subprocess.run([sys.executable, *command.split()], cwd=root, check=True)
        initial = {p: digest(root / p, mode_of(p)) for p in self.input_files(root)}
        pandoc = executable("pandoc", args.pandoc)
        xelatex = executable("xelatex", args.xelatex)
        work = Path(args.build_dir).resolve() if args.build_dir else root / f".build/paper_{self.letter}"
        work.mkdir(parents=True, exist_ok=True)
        tex = work / Path(self.TEX).name
        subprocess.run([pandoc, str(root / self.SOURCE),
                        "--from=markdown+tex_math_single_backslash+autolink_bare_uris",
                        "--to=latex", "--standalone", "--no-highlight", "--ascii",
                        "--template", str(root / self.assets / "article.tex"),
                        "--lua-filter", str(root / self.assets / "layout.lua"),
                        "--output", str(tex)], check=True, cwd=root)
        latex = tex.read_bytes().decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
        if self.c["latex"].get("longtable_foot", True):
            # Reserve the bottom-rule height on every page, including the last; a
            # last-foot-only rule can otherwise spill to a header-only continuation.
            latex = latex.replace("\\bottomrule\\noalign{}\n\\endlastfoot",
                                  "\\bottomrule\\noalign{}\n\\endfoot\n\\bottomrule\\noalign{}\n\\endlastfoot")
            latex = re.sub(r"\\\\\n(\\end\{longtable\})", r"\\\\*\n\1", latex)
        tex.write_bytes(latex.encode("utf-8"))
        for figure in self.c.get("figures", []):
            (work / "figures").mkdir(exist_ok=True)
            shutil.copyfile(root / figure, work / "figures" / Path(figure).name)
        versions = {name: subprocess.check_output([exe, "--version"], encoding="utf-8",
                                                  errors="replace").splitlines()[0]
                    for name, exe in (("pandoc", pandoc), ("xelatex", xelatex))}
        for iteration in range(1, self.c["latex"]["passes"] + 1):
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
        if initial != {p: digest(root / p, mode_of(p)) for p in self.input_files(root)}:
            raise ValueError(f"{self.__name__} inputs changed during compilation; rebuild required")
        pages = re.search(r"Output written on .*?\((\d+) pages?", log)
        shutil.copyfile(tex, root / self.TEX)
        (root / self.PDF).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(tex.with_suffix(".pdf"), root / self.PDF)
        meta = self.metadata(root, pandoc)
        (root / self.METADATA).write_text(json.dumps(meta, ensure_ascii=False, indent=2) + "\n",
                                          encoding="utf-8", newline="")
        release = {
            "schema": 2, "canonical_source": self.SOURCE, "version": self.version,
            "status": "preprint; this build performs no external deposit",
            "verification_scope": "File provenance only. Mathematical trust boundaries are in the "
                                  "manuscript and its build guide.",
            "pages": int(pages.group(1)) if pages else None, "tools": versions,
            "inputs": [{"path": p, "mode": mode_of(p), "sha256": digest(root / p, mode_of(p))}
                       for p in self.input_files(root)],
            "outputs": [{"path": p, "mode": mode_of(p), "sha256": digest(root / p, mode_of(p))}
                        for p in self.OUTPUTS]}
        latest = meta.get("latest_deposit")
        if latest:
            release["publication"] = {"doi": latest["doi"], "published_date": latest["publication_date"],
                                      "version": latest["version"]}
        (root / self.MANIFEST).write_text(json.dumps(release, indent=2) + "\n", encoding="utf-8", newline="")
        if (root / self.KIT).is_dir():
            self.sync(root)
            self.check(root)
        else:
            self.check_release(root)
        print(f"Built {self.__name__} ({release['pages']} pages). Logs: {work}")


def archive_matches(path: Path, expected: bytes) -> bool:
    """Same members, order, metadata and contents; nothing appended.

    Deflate output depends on the zlib build, so an unchanged archive is compared by
    members rather than by compressed bytes.
    """
    data = path.read_bytes()
    end = data.rfind(b"PK\x05\x06")
    if end < 0 or end + 22 + int.from_bytes(data[end + 20:end + 22], "little") != len(data):
        return False
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as found, zipfile.ZipFile(io.BytesIO(expected)) as fresh:
            fields = ("filename", "date_time", "external_attr", "compress_type", "CRC", "file_size")
            if [[getattr(i, f) for f in fields] for i in found.infolist()] != \
                    [[getattr(i, f) for f in fields] for i in fresh.infolist()]:
                return False
            return all(found.read(i.filename) == fresh.read(i.filename) for i in fresh.infolist())
    except zipfile.BadZipFile:
        return False


def executable(name: str, explicit: str | None) -> str:
    path = explicit or shutil.which(name)
    if path:
        return path
    if os.name == "nt":
        candidate = (Path(os.environ.get("PROGRAMFILES", "C:/Program Files")) / "Pandoc/pandoc.exe"
                     if name == "pandoc" else
                     Path(os.environ.get("LOCALAPPDATA", "")) / "Programs/MiKTeX/miktex/bin/x64/xelatex.exe")
        if candidate.is_file():
            return str(candidate)
    raise ValueError(f"{name} not found; install it or pass --{name}")


def letters(root: Path = ROOT) -> list[str]:
    return sorted(p.stem for p in (root / "tools/papers").glob("*.json"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paper", help="paper letter, e.g. A")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--check-release", action="store_true")
    mode.add_argument("--sync", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    parser.add_argument("--build-dir")
    parser.add_argument("--pandoc")
    parser.add_argument("--xelatex")
    parser.add_argument("--allow-layout-warnings", action="store_true", help="Draft preview only")
    args = parser.parse_args()
    paper = Paper(args.paper, args.root)
    try:
        if args.check:
            paper.check(args.root)
            print(f"{paper.__name__} {paper.version}: release and kit agree with the manifest.")
        elif args.check_release:
            paper.check_release(args.root)
            print(f"{paper.__name__} {paper.version}: every input and output matches the manifest.")
        elif args.sync:
            paper.sync(args.root)
            paper.check(args.root)
            print(f"Synchronized the {paper.__name__} kit.")
        else:
            paper.build(args.root, args)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"{paper.__name__}: {exc}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
