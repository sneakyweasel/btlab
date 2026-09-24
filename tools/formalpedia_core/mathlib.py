"""Mathlib search through Loogle, checked against the Mathlib this repository pins.

Formalpedia indexes this repository only. Loogle (https://loogle.lean-lang.org) finds Mathlib
declarations by name, type pattern or subexpression, but it indexes a recent Mathlib, not the
revision ``formal/lake-manifest.json`` pins: a hit can be renamed, restated or absent here.
Each hit is therefore checked against the pinned package sources when they are installed
(``formal/.lake/packages``) and labelled with what that check found.

This is the one formalpedia operation that contacts an external service. The query text is
sent to the public Loogle server; nothing else from the repository is.
"""
from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any, Callable
from urllib.error import URLError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

from . import workspace as _fp_workspace


ENDPOINT = os.environ.get('LOOGLE_URL', 'https://loogle.lean-lang.org/json')

Fetch = Callable[[str, float], dict]

LIMITATIONS = ('Hits come from the public Loogle index of a recent Mathlib, not this repository\'s '
               'pinned revision. `pinned` records whether the declaration was found in the pinned '
               'package sources by a source scan; generated names (to_additive, simps, structure '
               'projections) can exist without appearing literally. Confirm with #check through '
               'lean-lsp before relying on a hit.')

# Module roots and the Lake package directory that provides each; core modules come with the
# toolchain rather than a package.
PACKAGE_OF = {'Mathlib': 'mathlib', 'Batteries': 'batteries', 'Aesop': 'aesop', 'Qq': 'Qq',
              'Plausible': 'plausible', 'ProofWidgets': 'proofwidgets',
              'ImportGraph': 'importGraph', 'LeanSearchClient': 'LeanSearchClient'}
CORE_ROOTS = {'Init', 'Std', 'Lean', 'Lake'}

_DECL = r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|alias)'


def fetch_json(url: str, timeout: float) -> dict:
    request = Request(url, headers={'User-Agent': 'btlab-formalpedia/1 (+mathlib_search)',
                                    'Accept': 'application/json'})
    with urlopen(request, timeout=timeout) as response:  # noqa: S310 - fixed https endpoint
        body = response.read(4_000_001)
        if len(body) > 4_000_000:
            raise ValueError('Loogle response exceeds 4 MB')
        return json.loads(body.decode('utf-8'))


def pinned_revisions(root: Path | None = None) -> dict[str, str | None]:
    formal = (root or _fp_workspace.ROOT) / 'formal'
    try:
        manifest = json.loads((formal / 'lake-manifest.json').read_text(encoding='utf-8'))
    except (OSError, ValueError):
        return {}
    return {p['name']: p.get('rev') for p in manifest.get('packages', [])}


def _toolchain_source(root: Path) -> Path | None:
    try:
        pin = (root / 'formal/lean-toolchain').read_text(encoding='utf-8').strip()
    except OSError:
        return None
    elan = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan'))
    folder = pin.replace('/', '--').replace(':', '---')
    source = elan / 'toolchains' / folder / 'src' / 'lean'
    return source if source.is_dir() else None


def module_file(module: str, root: Path | None = None) -> tuple[Path | None, str]:
    """The pinned source file for a module, and why it could not be located if not."""
    root = root or _fp_workspace.ROOT
    if not re.fullmatch(r"[^\W\d]\w*(?:\.[^\W\d][\w']*)*", module):
        return None, 'invalid module name'
    first = module.split('.', 1)[0]
    if first in CORE_ROOTS:
        base = _toolchain_source(root)
        if base is None:
            return None, 'toolchain sources not installed'
    elif first in PACKAGE_OF:
        base = root / 'formal/.lake/packages' / PACKAGE_OF[first]
        if not base.is_dir():
            return None, f'package {PACKAGE_OF[first]} not installed under formal/.lake/packages'
    else:
        return None, f'no pinned package provides {first}'
    path = (base / (module.replace('.', '/') + '.lean')).resolve()
    if not path.is_relative_to(base.resolve()):
        return None, 'module path leaves its package'
    return path, ''


def check_pinned(name: str, module: str, root: Path | None = None) -> dict[str, Any]:
    """Does the pinned source of ``module`` declare ``name``? A source scan, not elaboration."""
    path, reason = module_file(module, root)
    if path is None:
        return {'status': 'unchecked', 'reason': reason}
    if not path.is_file():
        return {'status': 'module_missing',
                'reason': f'{module} does not exist at the pinned revision'}
    from trust_boundary import source_commands
    text = '\n'.join(source_commands(path.read_text(encoding='utf-8', errors='replace')))
    parts = name.split('.')
    # A declaration may be written fully qualified, relative to an open namespace, or bare.
    suffixes = ['.'.join(parts[i:]) for i in range(len(parts))]
    for suffix in suffixes:
        pattern = rf'\b{_DECL}\s+(?:_root_\.)?{re.escape(suffix)}(?![\w.\'!?])'
        if re.search(pattern, text):
            return {'status': 'declared', 'file': (path.relative_to((root or _fp_workspace.ROOT).resolve()).as_posix()
                    if path.is_relative_to((root or _fp_workspace.ROOT).resolve()) else str(path))}
    return {'status': 'not_declared_literally',
            'reason': 'module exists but the name is not declared literally; it may be generated '
                      '(to_additive, simps, fields) or renamed at the pinned revision'}


def search(query: str, *, limit: int = 20, root: Path | None = None,
           fetch: Fetch = fetch_json, timeout: float = 20.0) -> dict[str, Any]:
    if not query.strip():
        raise ValueError('query must not be empty')
    if len(query) > 1000:
        raise ValueError('query must not exceed 1000 characters')
    if not 1 <= limit <= 100:
        raise ValueError('limit must be between 1 and 100')
    root = root or _fp_workspace.ROOT
    pins = pinned_revisions(root)
    base = {'query': query, 'service': ENDPOINT, 'mathlib_pinned_rev': pins.get('mathlib'),
            'limitations': LIMITATIONS}
    url = ENDPOINT + '?' + urlencode({'q': query})
    try:
        payload = fetch(url, timeout)
    except (URLError, TimeoutError, OSError, ValueError) as exc:
        return dict(base, status='unreachable', reason=str(exc),
                    remedy=('Allow loogle.lean-lang.org in the environment\'s network access, '
                            'or use #loogle through lean-lsp on a machine that can reach it.'))
    if not isinstance(payload, dict):
        return dict(base, status='error', reason='unexpected response shape')
    if payload.get('error'):
        return dict(base, status='query_error', reason=str(payload['error']),
                    suggestions=list(payload.get('suggestions') or [])[:10])
    raw = payload.get('hits') or []
    if not isinstance(raw, list) or any(not isinstance(hit, dict) for hit in raw[:limit]):
        return dict(base, status='error', reason='unexpected hits shape')
    hits = []
    for hit in raw[:limit]:
        name, module = hit.get('name', ''), hit.get('module', '')
        if not isinstance(name, str) or not isinstance(module, str):
            return dict(base, status='error', reason='hit name/module must be text')
        hits.append({'name': name, 'module': module, 'type': hit.get('type', ''),
                     'doc': (hit.get('doc') or '')[:400],
                     'pinned': check_pinned(name, module, root) if name and module else
                               {'status': 'unchecked', 'reason': 'hit lacks a name or module'}})
    return dict(base, status='found' if hits else 'no_hits', header=payload.get('header', ''),
                total=payload.get('count', len(raw)), returned=len(hits), hits=hits,
                suggestions=list(payload.get('suggestions') or [])[:10])
