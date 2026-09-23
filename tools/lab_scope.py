"""Juggler/Collatz applications, ledger-cited results and their shared dependencies.

Scope filters describe the checkout, not Git history or mathematical truth tags.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from research.claims import load_claims
POLICY = ROOT / 'data/lab_scope.json'
SCOPES = ('active', 'archive', 'all')


def policy(root: Path = ROOT) -> dict:
    path = root / 'data/lab_scope.json'
    if not path.is_file():
        return {}
    rules = json.loads(path.read_text(encoding='utf-8'))
    texts = []
    capsule = root / 'attacks/juggler/index.json'
    if capsule.is_file():
        texts.append(capsule.read_text(encoding='utf-8'))
    for row in load_claims(root, required=False).entries:
        lean = str(row.get('lean') or '')
        if str(row.get('id', '')).startswith('J-') or 'Problems/Collatz/' in lean or 'Problems/Juggler/' in lean:
            texts.append(json.dumps(row, ensure_ascii=False))
    # Associations preserve dossiers whose names don't contain the application's name.
    rules['_active_documents'] = sorted({p for text in texts for p in
        re.findall(r'docs/(?:problems|theory)/[A-Za-z0-9_./-]+\.md', text)})
    return rules


def active_lean_modules(index: dict, root: Path | None = None) -> set[str]:
    modules = index['modules']
    roots = {name for name in modules if name.startswith(('Problems.Juggler', 'Problems.Collatz.'))}
    roots.update(set(modules) & {'Core', 'Representation', 'Operators', 'BTCalculus', 'Problems'})
    if roots:
        for row in load_claims(root or ROOT, required=False).entries:
            name = str(row.get('lean') or '').removeprefix('formal/').removesuffix('.lean').replace('/', '.')
            if name in modules:
                roots.add(name)
    # Small standalone catalogues and tests have no laboratory roots.
    if not roots:
        return set(modules)
    active, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name in active or name not in modules:
            continue
        active.add(name)
        todo.extend(modules[name]['imports'])
    return active


def validate_scope(scope: str) -> None:
    if scope not in SCOPES:
        raise ValueError('scope must be active, archive or all')


def path_scope(file: str, root: Path = ROOT, rules: dict | None = None) -> str:
    rules = policy(root) if rules is None else rules
    if not rules or rules.get('physical_cleanup'):
        return 'active'
    parts = file.replace('\\', '/').split('/')
    if len(parts) > 2 and parts[:2] in (['src', 'research'], ['tests', 'research']):
        return 'archive' if parts[2] in rules['archived_research'] else 'active'
    if file in rules.get('archived_test_files', []):
        return 'archive'
    if file.startswith(('archive/', 'docs/archive/')):
        return 'archive'
    if file in rules.get('_active_documents', []):
        return 'active'
    if file.startswith(('docs/problems/', 'docs/theory/')):
        leaf = parts[-1].lower()
        if any(word in leaf for word in ('juggler', 'collatz', 'syracuse', 'paper_', 'cochin-',
                                         'theorem_ledger', 'zenodo', 'template', 'readme')):
            return 'active'
        return 'archive'
    return 'active'


def inventory() -> dict:
    from formalpedia_core import source as fp_source
    index = fp_source.build()
    active = active_lean_modules(index)
    rules = policy()
    return {'archive_revision': rules['archive_revision'],
            'active_research': rules['active_research'], 'support_research': rules['support_research'],
            'archived_research': rules['archived_research'],
            'lean': {'active': sorted(active), 'archive': sorted(set(index['modules']) - active)},
            'declarations': dict(Counter('active' if d['module'] in active else 'archive'
                                        for d in index['declarations']))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = inventory()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'active_research': len(result['active_research']),
                      'support_research': len(result['support_research']),
                      'archived_research': len(result['archived_research']),
                      'lean': {k: len(v) for k, v in result['lean'].items()},
                      'declarations': result['declarations']}, indent=2))


if __name__ == '__main__':
    main()
