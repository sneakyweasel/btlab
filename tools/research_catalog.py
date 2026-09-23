"""Live, read-only research navigation derived from canonical dossiers and claims."""
from __future__ import annotations

import ast
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from research.experiments.provenance import check_manifest, write_manifest
from research.knowledge import journal_errors, negative_entries, negative_errors, negative_paths
from research.claims import ClaimError, claim_files, load_claims, EXPORT, render_json

LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)(?:\s+[^)]*)?\)")
PATH = re.compile(r"\b(?:src|tests|formal|docs|literature|data/research)/[A-Za-z0-9_./-]+\.(?:py|lean|md|json|yaml|csv|tsv|parquet|jsonl)\b")
SECTIONS = ("overview", "claims", "sources", "data", "obstructions", "questions", "commands", "papers")
LIMITATION = "Navigation and recorded evidence only. No tests, Lean compilation, coverage review, or mathematical verification were run."


def page(items: list, limit: int, offset: int) -> dict:
    if type(limit) is not int or not 1 <= limit <= 30 or type(offset) is not int or offset < 0:
        raise ValueError("limit must be 1..30 and offset must be nonnegative")
    return {"items": items[offset:offset + limit], "total": len(items), "offset": offset,
            "next_offset": offset + limit if offset + limit < len(items) else None}


def excerpt(text: str, size: int = 1400) -> dict:
    return {"text": text[:size], "truncated": len(text) > size}


def sections(text: str) -> list[dict]:
    lines = text.splitlines()
    starts = [(i, re.sub(r"^#+\s*", "", line).strip()) for i, line in enumerate(lines)
              if re.match(r"^#{1,3} ", line)]
    return [{"heading": heading, "line": start + 1,
             "body": "\n".join(lines[start + 1:(starts[n + 1][0] if n + 1 < len(starts) else len(lines))]).strip()}
            for n, (start, heading) in enumerate(starts)]


def programme(path: Path) -> str | None:
    if path.stem.startswith("juggler_"):
        return "juggler"
    if path.stem.startswith("collatz") or path.stem == "syracuse":
        return "collatz"
    return None


def file_kind(path: str) -> str:
    for prefix, kind in (("tests/", "test"), ("src/", "source"), ("formal/", "lean_module"),
                         ("data/", "data"), ("literature/", "literature"),
                         ("docs/theory/", "theory"), ("docs/problems/", "dossier")):
        if path.startswith(prefix):
            return kind
    return "reference"


class ResearchCatalogue:
    def __init__(self, root: Path = ROOT):
        self.root = root.resolve()
        self._stamp = None
        self._payload = None
        self._references_cache = {}

    def _files(self) -> list[Path]:
        root = self.root
        files = [*claim_files(root), root / EXPORT, root / "docs/research_journal.md", *negative_paths(root),
                 root / "src/research/juggler_sequence/branch_index.py"]
        files += [p for p in (root / "docs/problems").glob("*.md") if programme(p)]
        files += [p for p in (root / "literature").glob("*.json") if not p.name.endswith(".private.json")]
        for parent, dirs, names in os.walk(root / "formal", followlinks=False):
            dirs[:] = [d for d in dirs if d not in {".lake", ".git"} and not (Path(parent) / d).is_symlink()]
            files += [Path(parent) / name for name in names if name.endswith(".lean")]
        for folder in ("src/research/juggler_sequence", "src/research/collatz", "src/research/syracuse",
                       "src/research/collatz_finite_descent", "tests/research/juggler_sequence",
                       "tests/research/collatz", "tests/research/syracuse", "tests/research/collatz_finite_descent"):
            files += list((root / folder).rglob("*.py"))
        for app in ("juggler", "collatz"):
            for parent, dirs, names in os.walk(root / "data/research" / app, followlinks=False):
                dirs[:] = sorted(d for d in dirs if d not in {"chunks", "ranges", "__pycache__", ".git"}
                                 and not (Path(parent) / d).is_symlink())
                files += [Path(parent) / name for name in names if name.endswith(".research.json")]
                # Directory membership matters even when it contains only legacy data.
                files.append(Path(parent))
        return sorted(set(p for p in files if p.exists() and p.resolve().is_relative_to(root)))

    def snapshot(self) -> dict:
        for _ in range(3):
            files = self._files()
            stamp = [(str(p), p.stat().st_mtime_ns, p.stat().st_size) for p in files]
            if stamp == self._stamp:
                return self._payload
            result = self._build(files)
            after = self._files()
            if stamp == [(str(p), p.stat().st_mtime_ns, p.stat().st_size) for p in after]:
                result["snapshot"] = hashlib.sha256(json.dumps(
                    [result, stamp], sort_keys=True, ensure_ascii=False).encode()).hexdigest()[:20]
                self._stamp, self._payload = stamp, result
                return result
        raise RuntimeError("Research sources changed while indexing; retry after edits settle")

    def _reference(self, raw: str, owner: Path) -> str | None:
        raw = raw.split("#", 1)[0].strip("<>")
        if not raw or ":" in raw or raw.startswith(("/", "\\")):
            return None
        key = (raw, str(owner.parent))
        if key in self._references_cache:
            return self._references_cache[key]
        candidate = (self.root / raw if raw.startswith(("src/", "tests/", "formal/", "docs/", "data/", "literature/"))
                     else owner.parent / raw).resolve()
        result = candidate.relative_to(self.root).as_posix() if candidate.is_relative_to(self.root) else None
        self._references_cache[key] = result
        return result

    def _references(self, text: str, owner: Path) -> set[str]:
        return {ref for raw in [*LINK.findall(text), *PATH.findall(text)]
                if (ref := self._reference(raw, owner)) is not None}

    def _claim_references(self, row: dict, owner: Path) -> set[str]:
        """Read reference fields as text, never mathematical statements or serialized JSON."""
        fields = [row.get("source"), row.get("lean"), *(row.get("tests") or [])]
        return {ref for value in fields if isinstance(value, str)
                for ref in self._references(value, owner)}

    def _build(self, files: list[Path]) -> dict:
        self._references_cache.clear()
        root = self.root
        texts = {p.relative_to(root).as_posix(): p.read_text(encoding="utf-8")
                 for p in files if p.is_file() and p.suffix in {".md", ".json"}}
        ledger_path = EXPORT
        errors, ledger, locations = [], [], {}
        try:
            claims = load_claims(root, required=False)
            ledger, locations = claims.entries, claims.locations
        except ClaimError as exc:
            errors.extend(exc.issues)
        by_path = defaultdict(list)
        for row in ledger:
            for ref in self._references(str(row.get("source", "")), root / ledger_path):
                by_path[ref].append(row)
            for ref in row.get("tests") or []:
                by_path[str(ref).replace("\\", "/")].append(row)
        aliases, slogans = {}, {}
        alias_path = root / "src/research/juggler_sequence/branch_index.py"
        if alias_path.is_file():
            for node in ast.parse(alias_path.read_text(encoding="utf-8")).body:
                if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
                    if node.target.id == "DOSSIER_ALIASES":
                        aliases = ast.literal_eval(node.value)
                    elif node.target.id == "SLOGAN_ALIASES":
                        slogans = ast.literal_eval(node.value)
        negative = negative_entries(root, texts)
        errors.extend(negative_errors(root, texts))
        errors.extend(journal_errors(texts.get("docs/research_journal.md", "")))
        negative_by_ref = defaultdict(list)
        for part in negative:
            for ref in self._references(part["body"], root / part["file"]):
                negative_by_ref[ref].append(part)
        manifests = []
        for file, body in texts.items():
            if file.endswith(".research.json"):
                try:
                    data = json.loads(body)
                    manifests.append({"path": file, "metadata": data})
                except ValueError as exc:
                    errors.append({"path": file, "error": f"Invalid manifest JSON: {exc}"})
        records = []
        for dossier in sorted((root / "docs/problems").glob("*.md")):
            app = programme(dossier)
            if app is None or not dossier.resolve().is_relative_to(root):
                continue
            file = dossier.relative_to(root).as_posix()
            body = texts[file]
            parts = sections(body)
            stem = dossier.stem.removeprefix(app + "_")
            if stem == "collatz":
                stem = "overview"
            identifier = f"{app}/{stem}"
            probe_stems = [stem] + ([k for k, v in aliases.items() if v == stem] if app == "juggler" else [])
            names = sorted(set(probe_stems + [k for k, v in slogans.items()
                                              if app == "juggler" and v in probe_stems]))
            refs = {ref: "dossier reference" for ref in self._references(body, dossier)}
            package = "juggler_sequence" if app == "juggler" else "collatz"
            if app == "collatz" and stem in {"finite_descent", "syracuse"}:
                package = "collatz_finite_descent" if stem == "finite_descent" else "syracuse"
            candidates = []
            for probe in probe_stems:
                candidates += [f"src/research/{package}/{probe}.py", f"tests/research/{package}/test_{probe}.py",
                               f"data/research/{app}/{probe}", f"data/research/{app}/{probe}.json"]
            for ref in candidates:
                if (root / ref).exists():
                    refs.setdefault(ref, "filename convention")
            matches = {}
            for ref in [file, *(p for p in refs if file_kind(p) in {"source", "test"})]:
                for row in by_path.get(ref, []):
                    matches[row.get("id", "")] = row
            claims = []
            for key, row in sorted(matches.items()):
                declarations = row.get("decl") or []
                if isinstance(declarations, str):
                    declarations = [declarations]
                claims.append({"id": key, "tag": row.get("tag"), "statement": excerpt(str(row.get("statement", ""))),
                               "lean_file": row.get("lean"), "declaration_references": declarations[:16],
                               "declaration_reference_count": len(declarations),
                               "declaration_references_truncated": len(declarations) > 16,
                               "basis": "ledger source/test association; not a statement-coverage audit",
                               "claim_location": locations[key],
                               "lookup": {"tool": "formalpedia_claim", "ledger_id": key}})
                for ref in self._claim_references(row, root / ledger_path):
                    refs.setdefault(ref, "linked ledger record")
            decision_part = next((p for p in parts if p["heading"].casefold() == "decision"), None)
            decision = None
            if decision_part is not None:
                match = re.search(r"\b(PROMOTE|PARK|CLOSE)\b", decision_part["body"])
                decision = match[1] if match else None
            else:
                # Only an explicitly labelled introductory status/decision is used.
                intro = "\n".join(body.splitlines()[:12])
                match = re.search(r"(?:Status:|Decision:)\s*[*`]*(PROMOTE|PARK|CLOSE)\b", intro)
                if match:
                    decision = match[1]
                    decision_part = {"line": 1, "body": intro, "heading": "Introductory decision"}
            def selected(headings):
                return [{"file": file, "line": p["line"], "heading": p["heading"], **excerpt(p["body"])}
                        for p in parts if p["heading"].casefold() in headings and p["body"]]
            obstructions = selected({"counterexamples", "already killed by?", "decision"})
            for part in negative_by_ref.get(file, []):
                obstructions.append({"id": part["id"], "file": part["file"], "line": part["line"],
                                     "heading": part["heading"], **excerpt(part["body"])})
            sources = [{"path": ref, "kind": file_kind(ref), "basis": basis,
                        "exists": (root / ref).exists()} for ref, basis in sorted(refs.items())]
            datasets = [dict(s, provenance="legacy or unrecorded; inspect the linked files")
                        for s in sources if s["kind"] == "data"]
            recorded_commands = []
            for manifest in manifests:
                metadata = manifest["metadata"]
                if not isinstance(metadata, dict):
                    continue
                if metadata.get("research_id") == identifier or any(
                        (root / manifest["path"]).is_relative_to(root / d["path"])
                        for d in datasets if (root / d["path"]).is_dir()):
                    datasets.append({"path": manifest["path"], "kind": "manifest", "basis": "manifest id or data directory",
                                     "schema": metadata.get("schema"), "provenance": "recorded; integrity not checked by discovery",
                                     "scope": excerpt(str(metadata.get("scope", "")), 700)})
                    generator = metadata.get("generator")
                    command = generator.get("command") if isinstance(generator, dict) else None
                    if isinstance(command, list) and command and all(isinstance(v, str) for v in command):
                        recorded_commands.append({"argv": command if sum(map(len, command)) <= 2000 else None,
                                                  "basis": "recorded generator invocation", "manifest": manifest["path"],
                                                  "execution": "not run by discovery", "complete_argv_in_manifest": True})
            commands = [{"argv": ["python", "tools/lab.py", "test", "--", s["path"]],
                         "basis": s["basis"], "execution": "not run"}
                        for s in sources if s["kind"] == "test" and s["exists"] and s["path"].endswith(".py")]
            commands.extend(recorded_commands)
            records.append({"id": identifier, "programme": app, "title": (parts[0]["heading"] if parts else stem),
                            "dossier": file, "aliases": names, "decision": decision,
                            "decision_source": ({"file": file, "line": decision_part["line"],
                                                 **excerpt(decision_part["body"])} if decision_part else None),
                            "question": selected({"problem"}), "claims": claims, "sources": sources,
                            "data": datasets, "obstructions": obstructions,
                            "questions": selected({"open questions", "conjectures", "exact statement"}),
                            "commands": commands, "papers": [s for s in sources if s["kind"] == "theory"],
                            "_search": " ".join([identifier, *names, body,
                                                   *(p["heading"] + " " + p["body"] for p in negative_by_ref.get(file, [])),
                                                   *(str(r.get("statement", "")) for r in matches.values())]).casefold()})
        from research.literature import REQUIRED
        for file, body in texts.items():
            if file.startswith("literature/"):
                try:
                    reference = json.loads(body)
                    if not isinstance(reference, dict):
                        raise ValueError("Expected a JSON object")
                    missing = [key for key in REQUIRED if key not in reference]
                    if missing:
                        errors.append({"path": file, "error": f"Missing literature fields: {missing}"})
                except (ValueError, TypeError) as exc:
                    errors.append({"path": file, "error": f"Invalid literature record: {exc}"})
        for part in negative:
            part["sources"] = sorted(self._references(part["body"], root / part["file"]))
            part["programmes"] = sorted({app for ref in part["sources"] if (app := programme(Path(ref)))})
        return {"records": records, "obstructions": negative, "manifests": manifests, "ledger": ledger, "claim_locations": locations, "errors": errors,
                "source_hash": hashlib.sha256(json.dumps(texts, sort_keys=True).encode()).hexdigest()}

    def _current(self, snapshot: str | None) -> dict:
        data = self.snapshot()
        if snapshot is not None and snapshot != data["snapshot"]:
            raise ValueError("Research snapshot changed; restart pagination")
        return data

    def search(self, query: str, programme: str | None = None, decision: str | None = None,
               limit: int = 10, offset: int = 0, snapshot: str | None = None,
               kind: str = "research") -> dict:
        if kind not in {"research", "obstruction"}:
            raise ValueError("kind must be research or obstruction")
        if programme not in {None, "juggler", "collatz"} or decision not in {None, "PROMOTE", "PARK", "CLOSE"}:
            raise ValueError("Invalid programme or decision filter")
        if len(query) > 500:
            raise ValueError("Query exceeds 500 characters")
        data = self._current(snapshot)
        terms = re.findall(r"[\w]+", query.casefold())
        if kind == "obstruction":
            if decision is not None:
                raise ValueError("Decision filters apply to research dossiers, not obstruction records")
            selected = [p for p in data["obstructions"]
                        if (programme is None or programme in p["programmes"])
                        and all(t in (p["heading"] + " " + p["body"]).casefold() for t in terms)]
            selected.sort(key=lambda p: (-sum(t in p["heading"].casefold() for t in terms), p["id"]))
            results = [{"id": "obstruction/" + p["id"], "title": p["heading"], "file": p["file"],
                        "line": p["line"], "programmes": p["programmes"]} for p in selected]
            return {"snapshot": data["snapshot"], **page(results, limit, offset), "limitations": LIMITATION}
        selected = [r for r in data["records"] if (programme is None or r["programme"] == programme)
                    and (decision is None or r["decision"] == decision)
                    and all(term in r["_search"] for term in terms)]
        def rank(row):
            score = 1000 if query.casefold() in [row["id"], *row["aliases"]] else 0
            score += sum(100 for t in terms if t in row["id"])
            score += sum(50 for t in terms if t in row["title"].casefold())
            score += sum(10 for t in terms if any(t in q["text"].casefold() for q in row["question"]))
            return -score, row["id"]
        selected.sort(key=rank)
        results = [{k: r[k] for k in ("id", "programme", "title", "dossier", "decision")}
                   | {"question": r["question"][:1]} for r in selected]
        return {"snapshot": data["snapshot"], **page(results, limit, offset), "limitations": LIMITATION}

    def context(self, identifier: str, section: str = "overview", limit: int = 10,
                offset: int = 0, snapshot: str | None = None) -> dict:
        if section not in SECTIONS:
            raise ValueError("Unknown section; use " + ", ".join(SECTIONS))
        data = self._current(snapshot)
        if identifier.startswith("obstruction/"):
            parts = [p for p in data["obstructions"] if "obstruction/" + p["id"] == identifier]
            items = []
            if parts:
                part = parts[0]
                if section == "overview":
                    items = [{"id": identifier, "title": part["heading"], "file": part["file"],
                              "programmes": part["programmes"], "decision": None,
                              "sections": {"obstructions": 1, "sources": len(part["sources"])}}]
                elif section == "obstructions":
                    items = [{"id": identifier, "file": part["file"], "line": part["line"],
                              "heading": part["heading"], **excerpt(part["body"])}]
                elif section == "sources":
                    items = [{"path": ref, "kind": file_kind(ref), "exists": (self.root / ref).exists(),
                              "basis": "obstruction reference"} for ref in part["sources"]]
            return {"status": "found" if parts else "not_found", "id": identifier,
                    "snapshot": data["snapshot"], **page(items, limit, offset), "limitations": LIMITATION}
        exact = [r for r in data["records"] if r["id"] == identifier]
        candidates = exact or [r for r in data["records"] if identifier in r["aliases"]]
        result = {"snapshot": data["snapshot"], "limitations": LIMITATION}
        if len(candidates) != 1:
            return result | {"status": "ambiguous" if candidates else "not_found",
                             **page([{"id": r["id"], "dossier": r["dossier"]} for r in candidates], limit, offset)}
        row = candidates[0]
        if section == "overview":
            values = [{k: row[k] for k in ("id", "programme", "title", "dossier", "decision", "decision_source")}
                      | {"question": row["question"][:1],
                         "sections": {s: len(row[s]) for s in SECTIONS if s != "overview"}}]
        else:
            values = row[section]
        return result | {"status": "found", "id": row["id"], "section": section, **page(values, limit, offset)}

    def check(self, *, hashes: bool = False, limit: int = 30, offset: int = 0,
              snapshot: str | None = None) -> dict:
        data = self._current(snapshot)
        issues = [dict(i, severity="error") for i in data["errors"]]
        for identifier, count in Counter(r['id'] for r in data['records']).items():
            if not identifier or count > 1:
                issues.append({'severity': 'error', 'error': f'Invalid/duplicate research id: {identifier}'})
        for row in data["ledger"]:
            for ref in self._claim_references(row, self.root / EXPORT):
                if not (self.root / ref).exists():
                    issues.append({"severity": "error", "path": ref, "error": f"Missing claim reference: {row['id']}"})
        aggregate = self.root / EXPORT
        if (self.root / 'docs/claims').is_dir() and aggregate.exists() and not data['errors']:
            if aggregate.read_text(encoding='utf-8') != render_json(data['ledger']):
                issues.append({'severity': 'error', 'path': EXPORT,
                               'error': 'Generated claim aggregate is stale; run tools/render_theorem_ledger.py'})
        known = {r["id"] for r in data["records"]}
        for manifest in data["manifests"]:
            metadata = manifest["metadata"]
            check = check_manifest(self.root / manifest["path"], self.root, hashes=hashes)
            for severity, field in (("error", "errors"), ("warning", "warnings")):
                issues.extend({"severity": severity, "path": manifest["path"], "error": message}
                              for message in check[field])
            research_id = metadata.get("research_id") if isinstance(metadata, dict) else None
            if isinstance(research_id, str) and research_id and research_id not in known:
                issues.append({"severity": "error", "path": manifest["path"], "error": "Unknown research_id"})
        for row in data["records"]:
            for ref in row["sources"]:
                if not ref["exists"]:
                    issues.append({"severity": "warning", "path": row["dossier"],
                                   "error": f"Unresolved dossier reference: {ref['path']}"})
            if row["decision"] is None:
                issues.append({"severity": "warning", "path": row["dossier"], "error": "No explicit branch decision found"})
        counts = Counter(i["severity"] for i in issues)
        return {"status": "failed" if counts["error"] else "ok", "snapshot": data["snapshot"],
                "errors": counts["error"], "warnings": counts["warning"], "hashes_checked": hashes,
                "coverage": {"dossiers": len(data["records"]), "programmes": dict(Counter(r["programme"] for r in data["records"])),
                             "obstruction_records": len(data["obstructions"]),
                             "standard_manifests": len(data["manifests"]),
                             "legacy_data": "Not retroactively certified; only *.research.json uses the new contract"},
                **page(issues, limit, offset), "limitations": LIMITATION}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    search = commands.add_parser("search", help="search live dossier text and linked claims")
    search.add_argument("query")
    search.add_argument("--kind", choices=("research", "obstruction"), default="research")
    search.add_argument("--programme", choices=("juggler", "collatz"))
    search.add_argument("--decision", choices=("PROMOTE", "PARK", "CLOSE"))
    context = commands.add_parser("context", help="read one section of a research record")
    context.add_argument("identifier")
    context.add_argument("--section", choices=SECTIONS, default="overview")
    check = commands.add_parser("check", help="validate structure without running research")
    check.add_argument("--hashes", action="store_true", help="also stream and verify output/input/source hashes")
    for command in (search, context, check):
        command.add_argument("--limit", type=int, default=10)
        command.add_argument("--offset", type=int, default=0)
        command.add_argument("--snapshot", help="reject a changed pagination snapshot")
    manifest = commands.add_parser("manifest", help="record a newly completed run; never invent historical provenance")
    manifest.add_argument("--output", type=Path, required=True)
    manifest.add_argument("--programme", choices=("juggler", "collatz"), required=True)
    manifest.add_argument("--research-id", required=True)
    manifest.add_argument("--artifact", type=Path, action="append", required=True)
    manifest.add_argument("--artifact-root", type=Path)
    manifest.add_argument("--source", type=Path, action="append", default=[])
    manifest.add_argument("--input", type=Path, action="append", default=[])
    manifest.add_argument("--scope", required=True)
    manifest.add_argument("--parameters", type=json.loads, default={})
    manifest.add_argument("--command-json", type=json.loads, required=True, help="argv array for the computation that just ran")
    args = parser.parse_args(argv)
    catalogue = ResearchCatalogue()
    try:
        if args.command == "manifest":
            if not args.output.name.endswith(".research.json"):
                parser.error("manifest filenames must end in .research.json")
            if catalogue.context(args.research_id)["status"] != "found":
                parser.error("Unknown or ambiguous research id")
            path = write_manifest(args.output, programme=args.programme, research_id=args.research_id,
                                  outputs=args.artifact, inputs=args.input, sources=args.source,
                                  scope=args.scope, parameters=args.parameters, command=args.command_json,
                                  artifact_root=args.artifact_root)
            print(path)
            return 0
        kwargs = {"limit": args.limit, "offset": args.offset}
        if args.command == "search":
            result = catalogue.search(args.query, programme=args.programme, decision=args.decision,
                                      snapshot=args.snapshot, kind=args.kind, **kwargs)
        elif args.command == "context":
            result = catalogue.context(args.identifier, section=args.section, snapshot=args.snapshot, **kwargs)
        else:
            result = catalogue.check(hashes=args.hashes, snapshot=args.snapshot, **kwargs)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return int(result.get("status") in {"failed", "not_found", "ambiguous"})
    except (ValueError, OSError, RuntimeError) as exc:
        parser.exit(2, f"{exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
