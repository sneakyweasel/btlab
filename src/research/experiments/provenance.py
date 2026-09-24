"""Portable output manifests; file integrity is separate from mathematical evidence."""
from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess
import sys
import tempfile

from research.repository import query as git_query

SCHEMA = "btlab-output/v2"
SCHEMAS = {"btlab-output/v1", SCHEMA}
TEXT_SUFFIXES = {'.py', '.lean', '.md', '.json', '.jsonl', '.toml', '.yaml', '.yml', '.txt', '.csv', '.tsv'}
ROOT = Path(__file__).resolve().parents[3]
_COMMAND = ContextVar("research_command", default=None)


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


@contextmanager
def recording_run(command: list[str]):
    """Supply a reproducible argv explicitly; never collect the environment or secrets."""
    token = _COMMAND.set(command)
    try:
        yield
    finally:
        _COMMAND.reset(token)


def _git(root: Path, *args: str) -> str | None:
    try:
        result = git_query(root, *args, text=True, timeout=15)
        return result.stdout.strip() if result.returncode == 0 else None
    except (OSError, subprocess.TimeoutExpired):
        return None


def text_identity(path: Path) -> dict:
    raw = path.read_bytes()
    raw.decode('utf-8')  # Strict: no replacement decoding, BOM removal or whitespace changes.
    if b'\0' in raw:
        raise ValueError('Text fingerprint cannot cover NUL-containing data')
    normalized = raw.replace(b'\r\n', b'\n')
    return {'normalization': 'utf8-crlf-to-lf', 'sha256': hashlib.sha256(normalized).hexdigest(),
            'bytes': len(normalized)}


def descriptor(path: Path, base: Path, *, text: bool = False) -> dict:
    path, base = path.resolve(), base.resolve()
    if not path.is_relative_to(base) or not path.is_file():
        raise ValueError(f"Artifact must be an existing file beneath {base}: {path}")
    result = {"path": path.relative_to(base).as_posix(), "sha256": sha256(path),
              "bytes": path.stat().st_size}
    if text and path.suffix in TEXT_SUFFIXES:
        try:
            result['text'] = text_identity(path)
        except (UnicodeError, ValueError):
            pass  # Nontext inputs retain exact-byte verification.
    return result


def source_state(root: Path, sources=()) -> dict:
    """Fingerprint loaded local Python plus explicit inputs, without claiming full closure."""
    root = root.resolve()
    paths = {Path(p).resolve() for p in sources}
    for module in tuple(sys.modules.values()):
        name = getattr(module, "__file__", None)
        if name:
            path = Path(name).resolve()
            if path.suffix == ".py" and path.is_relative_to(root / "src"):
                paths.add(path)
    for name in ("pyproject.toml", "tools/lab.py", "tools/requirements-lab.lock", "tools/requirements-lab.json"):
        if (root / name).is_file():
            paths.add(root / name)
    revision = _git(root, "rev-parse", "HEAD") if (root / ".git").exists() else None
    state = _git(root, "status", "--porcelain=v1", "--untracked-files=normal") if revision else None
    return {"revision": revision, "dirty": bool(state) if state is not None else None,
            "coverage": "loaded local Python, project configuration, and explicit sources at manifest creation; not an execution or dependency audit",
            "files": [descriptor(p, root, text=True) for p in sorted(paths)]}


def write_manifest(path: Path, *, programme: str, scope: str, outputs,
                   parameters: dict | None = None, command: list[str] | None = None,
                   research_id: str | None = None, inputs=(), sources=(),
                   artifact_root: Path | None = None, root: Path = ROOT) -> Path:
    """Record a completed run. Unknown invocation or Git state remains explicitly null.

    Call after closing output files. Commands are argv arrays, never shell strings.
    Sources and inputs are repository-relative; output paths are relative to artifact_root.
    Existing historical results must not be assigned newly invented run provenance.
    """
    path, root = Path(path).resolve(), root.resolve()
    artifact_root = Path(artifact_root or path.parent).resolve()
    if not path.is_relative_to(artifact_root):
        raise ValueError("The manifest must be beneath its artifact root")
    outputs = list(outputs)
    if any(Path(p).resolve() == path for p in outputs):
        raise ValueError("A manifest cannot hash itself")
    inherited = os.environ.get("BTLAB_RUN_COMMAND")
    invocation = command if command is not None else _COMMAND.get()
    if invocation is None and inherited:
        invocation = json.loads(inherited)
    payload = {
        "schema": SCHEMA, "programme": programme, "research_id": research_id,
        "created_utc": datetime.now(timezone.utc).isoformat(), "scope": scope,
        "artifact_root": Path(os.path.relpath(artifact_root, path.parent)).as_posix(),
        "generator": {"command": invocation,
                      "parameters": parameters or {}, "python": platform.python_version()},
        "source": source_state(root, sources),
        "inputs": [descriptor(Path(p), root, text=True) for p in inputs],
        "outputs": [descriptor(Path(p), artifact_root) for p in outputs],
        "verification": "Outputs are byte-exact. Explicit text fingerprints on inputs/sources accept only UTF-8 CRLF-to-LF representation changes, which are reported. No theorem or compilation status is asserted.",
    }
    errors = schema_errors(payload)
    if errors:
        raise ValueError("; ".join(errors))
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n", dir=path.parent,
                                         prefix=".manifest-", suffix=".tmp", delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(payload, stream, indent=2, ensure_ascii=False)
            stream.write("\n")
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return path


def _relative(value) -> bool:
    return (isinstance(value, str) and bool(value) and "\\" not in value
            and not PurePosixPath(value).is_absolute() and ".." not in PurePosixPath(value).parts
            and ":" not in value)


def schema_errors(data) -> list[str]:
    """Validate v1/v2 envelopes; v1 stays byte-exact and v2 text identity is explicit."""
    if not isinstance(data, dict):
        return ["Manifest must be an object"]
    errors = []
    for key in ("schema", "programme", "research_id", "created_utc", "scope", "artifact_root",
                "generator", "source", "inputs", "outputs", "verification"):
        if key not in data:
            errors.append(f"Missing {key}")
    if not isinstance(data.get('schema'), str) or data.get("schema") not in SCHEMAS:
        errors.append("Unsupported manifest schema")
    app = data.get("programme")
    if not isinstance(app, str) or app not in {"juggler", "collatz"}:
        errors.append("programme must be juggler or collatz")
    research_id = data.get("research_id")
    if research_id is not None and (not isinstance(research_id, str) or not re.fullmatch(
            r"(juggler|collatz)/[a-z0-9_]+", research_id) or research_id.split("/")[0] != app):
        errors.append("research_id must be null or a programme-qualified dossier id")
    for key in ("scope", "created_utc", "verification", "artifact_root"):
        if not isinstance(data.get(key), str) or not data[key].strip():
            errors.append(f"Missing or invalid {key}")
    try:
        if datetime.fromisoformat(data.get("created_utc", "")).utcoffset() is None:
            errors.append("created_utc must include a timezone")
    except (ValueError, TypeError):
        errors.append("created_utc must be an ISO timestamp")
    base = data.get("artifact_root")
    if isinstance(base, str) and (Path(base).is_absolute() or ":" in base or "\\" in base):
        errors.append("artifact_root must be a portable relative path")
    generator = data.get("generator")
    if not isinstance(generator, dict) or not isinstance(generator.get("parameters"), dict):
        errors.append("generator.parameters must be an object")
    else:
        if not isinstance(generator.get("python"), str) or not generator["python"]:
            errors.append("generator.python must be recorded")
        if "command" not in generator:
            errors.append("generator.command must be explicitly recorded, even when null")
        command = generator.get("command")
        if command is not None and (not isinstance(command, list) or not command
                                   or any(not isinstance(v, str) for v in command)):
            errors.append("generator.command must be null or a nonempty argv array")
    source = data.get("source")
    if not isinstance(source, dict):
        errors.append("Missing source state")
        source = {}
    for key in ("revision", "dirty", "coverage"):
        if key not in source:
            errors.append(f"source.{key} must be explicitly recorded")
    if source.get("dirty") is not None and not isinstance(source["dirty"], bool):
        errors.append("source.dirty must be boolean or null")
    if not isinstance(source.get("coverage"), str) or not source["coverage"]:
        errors.append("source.coverage must describe the fingerprint scope")
    if source.get("revision") is not None and (not isinstance(source["revision"], str) or not re.fullmatch(
            r"(?:[0-9a-f]{40}|[0-9a-f]{64})", source["revision"])):
        errors.append("source.revision must be a full Git hash or null")
    for name, entries in (("outputs", data.get("outputs")), ("inputs", data.get("inputs")),
                          ("source.files", source.get("files"))):
        if not isinstance(entries, list) or (name == "outputs" and not entries):
            errors.append(f"{name} must be a list" + (" with at least one output" if name == "outputs" else ""))
            continue
        seen = set()
        for entry in entries:
            if not isinstance(entry, dict) or not _relative(entry.get("path")):
                errors.append(f"Unsafe {name} path")
                continue
            if entry["path"] in seen:
                errors.append(f"Duplicate {name} path: {entry['path']}")
            seen.add(entry["path"])
            if not isinstance(entry.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]):
                errors.append(f"Invalid {name} SHA-256: {entry['path']}")
            if type(entry.get("bytes")) is not int or entry["bytes"] < 0:
                errors.append(f"Invalid {name} size: {entry['path']}")
            if 'text' in entry:
                value = entry['text']
                if data.get('schema') != SCHEMA or name == 'outputs':
                    errors.append(f'Text identity is only allowed on v2 inputs and sources: {entry["path"]}')
                if (not isinstance(value, dict) or value.get('normalization') != 'utf8-crlf-to-lf'
                        or set(value) != {'normalization', 'sha256', 'bytes'}
                        or not isinstance(value.get('sha256'), str) or not re.fullmatch(r'[0-9a-f]{64}', value['sha256'])
                        or type(value.get('bytes')) is not int or value['bytes'] < 0):
                    errors.append(f'Invalid text identity: {entry["path"]}')
    return errors


def check_manifest(path: Path, root: Path = ROOT, *, hashes: bool = False) -> dict:
    """Read-only structural/integrity check; source changes are reported as staleness."""
    path, root = path.resolve(), root.resolve()
    if not path.is_relative_to(root):
        raise ValueError("Manifest is outside the selected root")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return {"path": path.relative_to(root).as_posix(), "errors": [str(exc)], "warnings": []}
    errors, warnings = schema_errors(data), []
    result = {"path": path.relative_to(root).as_posix(), "errors": errors, "warnings": warnings,
              "hashes_checked": hashes, "mathematical_verification": "not assessed"}
    if errors:
        return result
    base = (path.parent / data["artifact_root"]).resolve()
    if not base.is_relative_to(root):
        errors.append("Artifact root escapes the selected repository")
        return result
    for name, entries, anchor in (("outputs", data["outputs"], base), ("inputs", data["inputs"], root),
                                  ("source", data["source"]["files"], root)):
        for entry in entries:
            file = (anchor / entry["path"]).resolve()
            if not file.is_relative_to(anchor):
                errors.append(f"{name} path escapes its root: {entry['path']}")
            elif not file.is_file():
                (warnings if name == "source" else errors).append(f"Missing {name}: {entry['path']}")
            else:
                changed_size = file.stat().st_size != entry['bytes']
                if hashes:
                    raw_matches = sha256(file) == entry['sha256'] and not changed_size
                    text_matches = False
                    if 'text' in entry:
                        try:
                            text_matches = text_identity(file) == entry['text']
                        except (UnicodeError, ValueError):
                            pass
                        if raw_matches and not text_matches:
                            errors.append(f'Inconsistent text fingerprint for {name}: {entry["path"]}')
                    if not raw_matches:
                        if text_matches:
                            warnings.append(f'Text representation changed for {name}; declared UTF-8/LF content matches: {entry["path"]}')
                        else:
                            (warnings if name == 'source' else errors).append(f'Changed {name}: {entry["path"]}')
                elif changed_size:
                    if 'text' in entry:
                        warnings.append(f'Changed {name} byte size; use --hashes to check declared text identity: {entry["path"]}')
                    elif name != 'source':
                        errors.append(f'Changed {name} size: {entry["path"]}')
    if data["generator"]["command"] is None:
        warnings.append("Reproduction command was not recorded")
    if data["source"]["revision"] is None:
        warnings.append("Git revision was unavailable")
    if not data["source"]["files"]:
        warnings.append("No source fingerprints were recorded")
    return result
