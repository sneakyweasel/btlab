"""Recorded English-proof routes, independent of the module/import graph.

Completeness describes dependency annotation, never mathematical correctness.
Compiled evidence is a separate overlay: it cannot discharge English premises.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any

EDGE_KINDS = {'proof', 'statement', 'assumption', 'computation'}
COVERAGE = {'complete', 'partial', 'unknown'}
LIMITATIONS = (
    'Written edges are recorded readings of the named proof passage, not verified implications. '
    'Complete means immediate dependencies were enumerated at the recorded claim granularity. '
    'A fresh passage hash is not a proof audit. Missing annotations are unknown, not empty. '
    'Compiled edges describe declaration use, not English statement coverage or discharged premises. '
    'Evidence labels are copied, never promoted. Alternative routes are not combined.'
)


def digest(value: Any) -> str:
    """Stable content fingerprint for a query, not a mathematical certificate."""
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def source_passage(root: Path, source: dict) -> tuple[str, int]:
    """Read one uniquely delimited passage; forbid paths outside the checkout."""
    relative = source.get('path')
    if not isinstance(relative, str) or not relative or '\\' in relative:
        raise ValueError('source.path must be a checkout-relative POSIX path')
    path = (root / relative).resolve()
    if Path(relative).is_absolute() or '..' in Path(relative).parts or not path.is_relative_to(root.resolve()):
        raise ValueError('source.path must stay inside the checkout')
    start, end = source.get('start'), source.get('end')
    if not isinstance(start, str) or not start or not isinstance(end, str) or not end:
        raise ValueError('source.start and source.end must be nonempty unique delimiters')
    text = path.read_text(encoding='utf-8')
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError('source delimiters must each occur exactly once')
    a, b = text.index(start), text.index(end)
    if a >= b:
        raise ValueError('source.end must follow source.start')
    return text[a:b], text.count('\n', 0, a) + 1


def source_state(root: Path, source: dict) -> dict:
    """Expose stale annotations without silently replacing their fingerprint."""
    try:
        text, line = source_passage(root, source)
        actual = hashlib.sha256(text.encode()).hexdigest()
        return {'status': 'current' if actual == source.get('sha256') else 'stale',
                'actual_sha256': actual, 'line': line}
    except (OSError, ValueError, UnicodeError) as exc:
        return {'status': 'unavailable', 'reason': str(exc)}


def validate(ledger: list[dict], root: Path, *, check_sources: bool = True) -> list[str]:
    """Validate optional routes, references, source pins and potential circular support."""
    errors: list[str] = []
    ids = [row.get('id') for row in ledger]
    if any(not isinstance(i, str) or not i for i in ids) or len(set(ids)) != len(ids):
        return ['claim dependency validation requires unique nonempty ledger IDs']
    rows = {row['id']: row for row in ledger}
    adjacency: dict[str, set[str]] = {i: set() for i in ids}
    for row in ledger:
        name = row['id']
        conditions = row.get('conditions', [])
        if not isinstance(conditions, list) or any(not isinstance(c, str) or not c.strip() for c in conditions):
            errors.append(f'{name}: conditions must be a list of nonempty mathematical premises')
        if not isinstance(row.get('claim_kind', 'result'), str) or row.get('claim_kind', 'result') not in {'result', 'hypothesis'}:
            errors.append(f'{name}: unknown claim_kind')
        if row.get('claim_kind') == 'hypothesis' and row.get('tag') != 'CONJECTURE':
            errors.append(f'{name}: an open hypothesis must retain the CONJECTURE tag')
        if 'proof_routes' not in row:
            continue
        routes = row['proof_routes']
        if not isinstance(routes, list) or not routes:
            errors.append(f'{name}: proof_routes must be a nonempty list; omit for unknown coverage')
            continue
        seen = set()
        for route in routes:
            if not isinstance(route, dict):
                errors.append(f'{name}: proof route must be an object')
                continue
            rid = route.get('id')
            label = f'{name}/{rid}'
            if not isinstance(rid, str) or not re.fullmatch(r'[a-z0-9][a-z0-9-]*', rid) or rid in seen:
                errors.append(f'{label}: invalid or duplicate route ID')
            else:
                seen.add(rid)
            if route.get('method') != 'written':
                errors.append(f'{label}: persisted routes must be written; compiled edges are derived')
            if not isinstance(route.get('coverage'), str) or route.get('coverage') not in COVERAGE:
                errors.append(f'{label}: invalid coverage')
            if not isinstance(route.get('notes'), str) or not route['notes'].strip():
                errors.append(f'{label}: notes must explain the scope or remaining boundary')
            source = route.get('source')
            if not isinstance(source, dict) or not re.fullmatch(r'[0-9a-f]{64}', str(source.get('sha256', ''))):
                errors.append(f'{label}: source needs path, delimiters and a SHA-256 pin')
            elif check_sources:
                state = source_state(root, source)
                if state['status'] != 'current':
                    errors.append(f'{label}: source passage {state["status"]}; review dependencies before repinning')
            uses = route.get('uses')
            if not isinstance(uses, list):
                errors.append(f'{label}: uses must be an explicit list')
                continue
            targets = set()
            for edge in uses:
                if not isinstance(edge, dict):
                    errors.append(f'{label}: dependency must be an object')
                    continue
                target, kind = edge.get('claim'), edge.get('kind')
                if not isinstance(target, str) or target not in rows:
                    errors.append(f'{label}: unknown dependency {target!r}')
                    continue
                if not isinstance(kind, str):
                    errors.append(f'{label}: dependency kind must be a string')
                    continue
                if target == name or (target, kind) in targets:
                    errors.append(f'{label}: self or duplicate dependency {target}')
                targets.add((target, kind))
                if kind not in EDGE_KINDS:
                    errors.append(f'{label}: unknown dependency kind {kind!r}')
                if kind == 'computation' and rows[target].get('tag') != 'COMPUTATIONALLY VERIFIED':
                    errors.append(f'{label}: computation edge must name a computational claim')
                if rows[target].get('claim_kind') == 'hypothesis' and kind != 'assumption':
                    errors.append(f'{label}: hypothesis {target} needs an assumption edge')
                adjacency[name].add(target)
    # Persisted support must be acyclic even across alternatives. Equivalence
    # arguments should reference their proved implications, not circular support.
    users: dict[str, set[str]] = {name: set() for name in ids}
    degree = {name: len(children) for name, children in adjacency.items()}
    for name, children in adjacency.items():
        for child in children:
            users[child].add(name)
    ready = [name for name, count in degree.items() if count == 0]
    while ready:
        child = ready.pop()
        for user in users[child]:
            degree[user] -= 1
            if degree[user] == 0:
                ready.append(user)
    blocked = sorted(name for name, count in degree.items() if count)
    if blocked:
        errors.append('Circular written-proof support affects: ' + ', '.join(blocked[:20]))
    return errors

