"""Canonical topic claims, consistent validation, and checkout-local read-only snapshots.

Generated theorem_ledger.json is an export, never an input to live discovery.
Claim content is copied verbatim; storage location is separate editorial metadata.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json
import os
import stat
from pathlib import Path
import re

from research.claim_dependencies import validate as validate_dependencies

ROOT = Path(__file__).resolve().parents[2]
CLAIMS = 'docs/claims'
EXPORT = 'docs/theory/theorem_ledger.json'
TAGS = ('EXACT — LEAN VERIFIED', 'EXACT — HUMAN PROOF', 'COMPUTATIONALLY VERIFIED',
        'CONJECTURE', 'OBSERVATION', 'REFUTED', 'REPARAMETERIZATION')


class ClaimError(ValueError):
    """Structured file/record errors suitable for CLI and MCP diagnostics."""
    def __init__(self, issues: list[dict]):
        self.issues = issues
        super().__init__('Invalid claims: ' + '; '.join(
            f"{i['path']}{i.get('pointer', '')}: {i['error']}" for i in issues[:20]))


def claim_files(root: Path = ROOT) -> tuple[Path, ...]:
    """Inventory all topic files, rejecting links and malformed storage locations."""
    root = root.resolve()
    directory = root / CLAIMS
    if not directory.exists():
        return ()
    if directory.is_symlink() or not directory.resolve().is_relative_to(root):
        raise ClaimError([{'path': CLAIMS, 'error': 'Claim directory must stay inside this checkout'}])
    paths, issues = [], []
    for folder, directories, names in os.walk(directory, followlinks=False):
        for name in sorted(directories + names):
            path = Path(folder) / name
            relative = path.relative_to(directory)
            metadata = path.lstat()
            linked = stat.S_ISLNK(metadata.st_mode) or bool(
                getattr(metadata, 'st_file_attributes', 0) & getattr(stat, 'FILE_ATTRIBUTE_REPARSE_POINT', 0))
            if linked:
                if name in directories:
                    directories.remove(name)
                issues.append({'path': path.relative_to(root).as_posix(), 'error': 'Links are not claim sources'})
            elif stat.S_ISREG(metadata.st_mode) and path.suffix == '.json':
                if (len(relative.parts) != 2 or relative.parts[0] not in {'juggler', 'collatz', 'shared'}
                        or not re.fullmatch(r'[a-z0-9][a-z0-9_]*\.json', relative.name)):
                    issues.append({'path': path.relative_to(root).as_posix(),
                                   'error': 'Expected docs/claims/{juggler,collatz,shared}/topic.json'})
                else:
                    paths.append(path)
    if issues:
        raise ClaimError(issues)
    return tuple(sorted(paths))


def _constant(value):
    raise ValueError(f"Nonfinite JSON number {value}")


def _pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'Duplicate JSON key {key!r}')
        result[key] = value
    return result


def row_errors(row) -> list[str]:
    if not isinstance(row, dict):
        return ['Claim must be an object']
    errors = []
    for key in ('id', 'statement', 'source'):
        if not isinstance(row.get(key), str) or not row[key].strip():
            errors.append(f'{key} must be a nonempty string')
    if not isinstance(row.get('tag'), str) or row['tag'] not in TAGS:
        errors.append(f'Unknown evidence tag {row.get("tag")!r}')
    if row.get('lean') is not None and not isinstance(row['lean'], str):
        errors.append('lean must be a string or null')
    for key in ('tests', 'related_conjectures', 'compiler_decls'):
        if key in row and (not isinstance(row[key], list) or any(not isinstance(x, str) or not x for x in row[key])):
            errors.append(f'{key} must be a list of nonempty strings')
    if 'decl' in row and not (isinstance(row['decl'], str) and row['decl'] or
            isinstance(row['decl'], list) and all(isinstance(x, str) and x for x in row['decl'])):
        errors.append('decl must be a name or list of names')
    if 'lean_trust' in row and row['lean_trust'] not in ('kernel', 'mixed', 'unverified'):
        errors.append('Unknown lean_trust')
    return errors


@dataclass(frozen=True)
class ClaimLedger:
    root: Path
    files: tuple[Path, ...]
    snapshot: str
    _rows: tuple[dict, ...]
    _locations: dict[str, dict]

    @property
    def entries(self) -> list[dict]:
        """A caller-owned copy; annotations cannot mutate another consumer's view."""
        return deepcopy(list(self._rows))

    def get(self, identifier: str) -> dict:
        for row in self._rows:
            if row['id'] == identifier:
                return deepcopy(row)
        raise KeyError(identifier)

    def location(self, identifier: str) -> dict:
        return dict(self._locations[identifier])

    @property
    def locations(self) -> dict[str, dict]:
        return deepcopy(self._locations)


def _stamp(paths):
    result = []
    for path in paths:
        metadata = path.stat()
        result.append((path.as_posix(), metadata.st_size, metadata.st_mtime_ns, metadata.st_ctime_ns))
    return result


def load_claims(root: Path = ROOT, *, required: bool = True, check_sources: bool = False) -> ClaimLedger:
    """Read one bounded-retry snapshot; invalid data never falls back to an old export.

    Optional source-pin verification is for audit gates. Discovery retains stale
    annotations for explicit freshness reporting. Neither mode checks a proof.
    """
    root = root.resolve()
    for _ in range(3):
        paths = claim_files(root)
        if not paths and (required or (root / CLAIMS).exists() or (root / EXPORT).exists()):
            raise ClaimError([{'path': CLAIMS, 'error': 'No canonical claim files found'}])
        before = _stamp(paths)
        raw = {p: p.read_bytes() for p in paths}
        if before == _stamp(claim_files(root)):
            break
    else:
        raise ClaimError([{'path': CLAIMS, 'error': 'Claim files changed while reading; retry after edits settle'}])
    rows, locations, issues = [], {}, []
    digest = hashlib.sha256()
    for path, content in raw.items():
        relative = path.relative_to(root).as_posix()
        digest.update(relative.encode() + b'\0' + hashlib.sha256(content).digest())
        try:
            records = json.loads(content.decode('utf-8'), object_pairs_hook=_pairs, parse_constant=_constant)
            if not isinstance(records, list):
                raise ValueError('Topic must contain a JSON array of claims')
        except (ValueError, UnicodeError) as exc:
            issues.append({'path': relative, 'error': str(exc)})
            continue
        for position, row in enumerate(records):
            location = {'path': relative, 'pointer': '/' + str(position)}
            name = row.get('id') if isinstance(row, dict) else None
            duplicate = isinstance(name, str) and name in locations
            if duplicate:
                previous = locations[name]
                issues.append(location | {'error': f'Duplicate claim ID {name}; first at {previous["path"]}{previous["pointer"]}'})
            elif isinstance(name, str) and name:
                locations[name] = location
            bad = row_errors(row)
            issues.extend(location | {'error': error} for error in bad)
            if bad or duplicate:
                continue
            rows.append(row)
    # Run cross-file rules once, after basic row validation makes their input safe.
    if not issues:
        for error in validate_dependencies(rows, root, check_sources=check_sources):
            name = error.split(':', 1)[0].split('/', 1)[0]
            issues.append(locations.get(name, {'path': CLAIMS}) | {'error': error})
    if issues:
        raise ClaimError(issues)
    return ClaimLedger(root, paths, digest.hexdigest(), tuple(sorted(rows, key=lambda r: r['id'])), locations)


def render_json(entries: list[dict]) -> str:
    return json.dumps(entries, indent=1, ensure_ascii=False) + '\n'
