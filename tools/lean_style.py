"""Enforce documented public Lean interfaces without renaming legacy mathematics.

The baseline records individual existing violations at a reviewed Git revision.
It never exempts an entire file, namespace, or future declaration.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import formalpedia as fp
import lean_source

BASELINE = fp.ROOT / 'data/research/formalpedia/style_baseline.json'
RULES = {
    'public_doc': 'Add a docstring explaining the public result and its important hypotheses.',
    'namespace': 'Place the declaration in its mathematical namespace.',
    'type_case': 'Use UpperCamelCase for types, classes and predicates.',
    'value_case': 'Use lowerCamelCase for functions and values.',
    'theorem_case': 'Start theorem names in lower case; preserve existing object-name tokens.',
    'descriptive_name': 'Describe the mathematics; put paper numbers and proof-stage labels in metadata.',
}


def violations(index: dict) -> list[dict]:
    result = []
    object_tokens = {lean_source.name_parts(d.get('source_name', d['name']))[-1]
                     for d in index['declarations']
                     if d['kind'] in {'def', 'abbrev', 'opaque'}}
    object_tokens |= {'Icc', 'Ico', 'Ioc', 'Ioo', 'Ici', 'Ioi', 'Iic', 'Iio'}
    for d in index['declarations']:
        if d.get('visibility') == 'private' or d.get('deprecated'):
            continue
        name = d.get('qualified_name') or d.get('source_name') or d['name']
        leaf = lean_source.name_parts(name)[-1]
        rules = []
        if not d.get('doc'):
            rules.append('public_doc')
        if len(lean_source.name_parts(name)) == 1:
            rules.append('namespace')
        if re.fullmatch(r'(?:main|result|aux|helper|(?:theorem|lemma|result|helper)\d+)', leaf):
            rules.append('descriptive_name')
        # Escaped mathematical names need human review, not an ASCII-only regex.
        if not leaf.startswith('«'):
            if d['kind'] in {'theorem', 'lemma'}:
                if not leaf[0].islower() and leaf.split('_')[0] not in object_tokens:
                    rules.append('theorem_case')
            elif d['kind'] in {'structure', 'class', 'inductive'}:
                if not leaf[0].isupper() or '_' in leaf:
                    rules.append('type_case')
            elif d['kind'] in {'def', 'abbrev', 'opaque'}:
                codomain = lean_source.result_type(d.get('signature', ''))
                if codomain is not None:
                    proposition = re.search(r'(?:^|→|->)\s*(?:Prop|Type(?:\s+\w+)?|Sort\s+\w+)\s*$', codomain)
                    if proposition:
                        if not leaf[0].isupper() or '_' in leaf:
                            rules.append('type_case')
                    elif not leaf[0].islower() or '_' in leaf:
                        rules.append('value_case')
        # Whitespace-only edits do not create a new declaration for baseline purposes.
        fingerprint = hashlib.sha256(' '.join(d.get('signature', '').split()).encode()).hexdigest()[:16]
        for rule in rules:
            result.append({'id': name, 'rule': rule, 'fingerprint': fingerprint,
                           'file': d['file'], 'line': d['line'], 'message': RULES[rule]})
    return sorted(result, key=lambda d: (d['id'], d['rule'], d['file']))


def key(row: dict) -> tuple:
    return row['id'], row['file'], row['rule'], row['fingerprint']


def report(index: dict, baseline: dict) -> dict:
    old = {key(d) for d in baseline.get('violations', [])}
    current = violations(index)
    new = [d for d in current if key(d) not in old]
    return {'baseline_revision': baseline.get('revision'), 'new_violations': new,
            'new_count': len(new), 'legacy_count': len(current) - len(new),
            'total_count': len(current),
            'note': 'Checks naming and documentation, not mathematical correctness or proof style.'}


def committed_index(revision: str) -> tuple[str, dict]:
    """Read committed blobs in one Git process; never baseline a peer's draft edits."""
    git = ['git', '-c', f'safe.directory={fp.ROOT.as_posix()}']
    resolved = subprocess.check_output(git + ['rev-parse', '--verify', revision + '^{commit}'],
                                       cwd=fp.ROOT, text=True).strip()
    paths = subprocess.check_output(git + ['ls-tree', '-r', '--name-only', resolved, 'formal'],
                                   cwd=fp.ROOT, text=True).splitlines()
    paths = [p for p in paths if p.endswith('.lean') and
             p.split('/')[1].removesuffix('.lean') in fp.LIBRARIES]
    payload = ''.join(f'{resolved}:{p}\n' for p in paths).encode()
    output = subprocess.check_output(git + ['cat-file', '--batch'], input=payload, cwd=fp.ROOT)
    cursor, declarations = 0, []
    for path in paths:
        end = output.index(b'\n', cursor)
        size = int(output[cursor:end].split()[-1])
        source = output[end + 1:end + 1 + size].decode('utf-8').replace('\r\n', '\n')
        module = path[len('formal/'):].removesuffix('.lean').replace('/', '.')
        declarations.extend(lean_source.scan(source, module, path))
        cursor = end + size + 2
    return resolved, {'declarations': declarations}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true')
    parser.add_argument('--baseline', type=Path, default=BASELINE)
    parser.add_argument('--write-baseline', metavar='COMMIT',
                        help='explicitly replace exemptions from a committed revision; review the diff')
    args = parser.parse_args(argv)
    if args.write_baseline:
        revision, index = committed_index(args.write_baseline)
        data = {'schema': 1, 'revision': revision,
                'policy': 'Existing violations only; additions require explicit review.',
                'violations': [{k: d[k] for k in ('id', 'file', 'rule', 'fingerprint')}
                               for d in violations(index)]}
        args.baseline.parent.mkdir(parents=True, exist_ok=True)
        args.baseline.write_text(fp.render(data), encoding='utf-8')
        print(f"Recorded {len(data['violations'])} existing violations at {revision}")
        return 0
    if not args.baseline.is_file():
        parser.error('Missing reviewed style baseline')
    result = report(fp.build(), json.loads(args.baseline.read_text(encoding='utf-8')))
    if args.json:
        print(fp.render(result), end='')
    else:
        for row in result['new_violations']:
            print(f"{row['file']}:{row['line']}: {row['id']} [{row['rule']}] {row['message']}")
        print(f"{result['new_count']} new violations; {result['legacy_count']} reviewed legacy exemptions")
    return int(bool(result['new_count']))


if __name__ == '__main__':
    raise SystemExit(main())
