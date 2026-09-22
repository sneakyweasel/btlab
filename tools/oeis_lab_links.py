"""Live local OEIS mentions in papers, dossiers, ledger rows and Lean docstrings."""
from __future__ import annotations

import hashlib
from collections import Counter
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

import lean_source
from oeis_catalog import bounds
from oeis_index import ROOT
from oeis_source import aid
from lab_scope import active_lean_modules, path_scope, policy, validate_scope

KINDS = ('paper', 'dossier', 'negative_knowledge', 'lean', 'theory', 'source',
         'literature', 'ledger', 'bibliography', 'laboratory_reference')


def mention_kind(file: str, root: Path) -> str:
    path = Path(file)
    if path.suffix == '.tex' or (path.suffix == '.md' and (root / path).with_suffix('.tex').is_file()):
        return 'paper'
    if path.suffix == '.bib':
        return 'bibliography'
    if file == 'docs/negative_knowledge.md':
        return 'negative_knowledge'
    if path.name in {'theorem_ledger.md', 'theorem_ledger.json'}:
        return 'ledger'
    for prefix, kind in [('docs/problems/', 'dossier'), ('docs/theory/', 'theory'),
                         ('src/', 'source'), ('literature/', 'literature')]:
        if file.startswith(prefix):
            return kind
    return 'lean' if path.suffix == '.lean' else 'laboratory_reference'


def find_mentions(identifier: str, root: Path):
    directories = [name for name in ('docs', 'formal', 'src', 'literature', 'attacks')
                   if (root / name).is_dir()]
    pattern = re.compile(r'\b' + identifier + r'\b')
    if shutil.which('rg') and directories:
        types = [arg for ext in ('md', 'tex', 'bib', 'lean', 'py', 'json')
                 for arg in ('--type-add', f'oeislab:*.{ext}')]
        command = ['rg', '--json', '--no-ignore-dot', '-n', '-e', pattern.pattern,
                   *types, '--type', 'oeislab',
                   '-g', '!**/.lake/**', '-g', '!docs/research/*.json', '--', *directories]
        try:
            result = subprocess.run(command, cwd=root, capture_output=True, text=True,
                                    encoding='utf-8', timeout=20, stdin=subprocess.DEVNULL)
        except OSError:
            result = None  # Some clients cannot launch the host's rg; use the same local scope.
        if result is not None and result.returncode not in (0, 1):
            raise ValueError('Local reference search failed: ' + result.stderr[:500])
        for line in result.stdout.splitlines() if result is not None else []:
            event = json.loads(line)
            if event['type'] == 'match':
                data = event['data']
                yield data['path']['text'].replace('\\', '/'), data['line_number'], data['lines']['text'].rstrip('\n')
        if result is not None:
            return
    # Git supplies the same private/generated-file exclusions when rg cannot run.
    candidates = None
    if shutil.which('git'):
        try:
            result = subprocess.run(['git', '-c', f'safe.directory={root.resolve().as_posix()}',
                                     'ls-files', '--cached', '--others', '--exclude-standard', '-z',
                                     '--', *directories], cwd=root, capture_output=True,
                                    text=True, encoding='utf-8', timeout=20, stdin=subprocess.DEVNULL)
            if result.returncode == 0:
                candidates = {p for p in result.stdout.split('\0') if p}
        except OSError:
            pass
    for directory in directories:
        for parent, dirs, files in os.walk(root / directory):
            dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '__pycache__'}]
            for filename in sorted(files):
                path = Path(parent) / filename
                if path.suffix not in {'.md', '.tex', '.bib', '.lean', '.py', '.json'}:
                    continue
                if not path.resolve().is_relative_to(root.resolve()):
                    continue
                relative = path.relative_to(root).as_posix()
                if candidates is not None and relative not in candidates:
                    continue
                if relative.startswith('docs/research/') and path.suffix == '.json':
                    continue
                for number, text in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
                    if pattern.search(text):
                        yield relative, number, text


def lab_links(identifier: str, limit: int = 30, offset: int = 0, root: Path = ROOT,
              kinds: list[str] | None = None, scope: str = 'active'):
    identifier = aid(identifier)
    bounds(limit, offset)
    validate_scope(scope)
    if kinds is not None and (not kinds or set(kinds) - set(KINDS)):
        raise ValueError('Mention kinds: ' + ', '.join(KINDS))
    pattern = re.compile(r'\b' + identifier + r'\b')
    mentions = list(find_mentions(identifier, root))
    rules = policy(root)
    scope_by_file = {file: path_scope(file, root, rules) for file, _, _ in mentions}
    active_lean = None
    if rules and any(file.startswith('formal/') for file, _, _ in mentions):
        import formalpedia as fp
        # Import graph only: no need to parse thousands of declaration bodies.
        paths = fp.sources()
        known = {fp.module_of(p) for p in paths}
        active_lean = active_lean_modules({'modules': {
            fp.module_of(p): {'imports': fp.imports(p, known)} for p in paths}})
        for file in scope_by_file:
            if file.startswith('formal/') and file.endswith('.lean'):
                scope_by_file[file] = ('active' if file[7:-5].replace('/', '.') in active_lean else 'archive')
    all_mentions = mentions
    mentions = [m for m in mentions if scope == 'all' or scope_by_file[m[0]] == scope]
    kind_by_file = {file: mention_kind(file, root) for file, _, _ in mentions}
    mentions.sort(key=lambda m: (KINDS.index(kind_by_file[m[0]]), m[0], m[1]))
    selected = [m for m in mentions if kinds is None or kind_by_file[m[0]] in kinds]
    results = []
    for file, line, text in selected[offset:offset + limit]:
        match = pattern.search(text)
        start = max(0, match.start() - 150) if match else 0
        results.append({'file': file, 'line': line, 'kind': kind_by_file[file],
                        'excerpt': text[start:start + 650], 'excerpt_truncated': len(text) > 650})
    selected_files = {file for file, _, _ in mentions}
    declarations = []
    for file in sorted(selected_files):
        if not file.startswith('formal/') or not file.endswith('.lean'):
            continue
        source = (root / file).read_text(encoding='utf-8')
        module = file[len('formal/'):].removesuffix('.lean').replace('/', '.')
        for d in lean_source.scan(source, module, file):
            matched = [field for field in ('doc', 'signature') if pattern.search(d[field])]
            if matched:
                declarations.append({key: d[key] for key in
                    ('id', 'qualified_name', 'visibility', 'module', 'file', 'line')} |
                    {'match_basis': matched, 'formalpedia_lookup': {'name': d['id'], 'module': module,
                                                                  'include_private': d['visibility'] == 'private'}})
    ledger_file = root / 'docs/theory/theorem_ledger.json'
    rows = json.loads(ledger_file.read_text(encoding='utf-8')) if ledger_file.is_file() else []
    def claim_in_scope(row):
        if scope == 'all' or not rules:
            return True
        lean = str(row.get('lean') or '').removeprefix('formal/').removesuffix('.lean').replace('/', '.')
        if lean and active_lean is not None:
            return (lean in active_lean) == (scope == 'active')
        source = str(row.get('source') or '')
        return path_scope(source, root, rules) == scope

    claims = [{'id': row['id'], 'tag': row.get('tag'), 'lean_file': row.get('lean'),
               'declaration_references': row.get('decl'), 'statement_excerpt': row.get('statement', '')[:1000]}
              for row in rows if pattern.search(json.dumps(row, ensure_ascii=False)) and claim_in_scope(row)]
    digest = hashlib.sha256()
    digest.update(json.dumps([scope, kinds, rules], sort_keys=True).encode())
    for file in sorted(selected_files):
        info = (root / file).stat()
        digest.update(f'{file}:{info.st_mtime_ns}:{info.st_size}\n'.encode())
    return {'aid': identifier, 'source': 'live laboratory working tree',
            'scope': scope, 'all_scope_mentions': len(all_mentions),
            'scope_counts': dict(Counter(scope_by_file[m[0]] for m in all_mentions)),
            'reference_snapshot': digest.hexdigest(), 'total_mentions': len(mentions),
            'mention_counts': dict(Counter(kind_by_file[m[0]] for m in mentions)),
            'filtered_mentions': len(selected), 'kinds': kinds,
            'mentions': results, 'next_offset': offset + limit if offset + limit < len(selected) else None,
            'lean_declarations': declarations[:50], 'total_lean_declarations': len(declarations),
            'ledger_claims': claims[:50], 'total_ledger_claims': len(claims),
            'related_results_truncated': len(declarations) > 50 or len(claims) > 50,
            'notice': 'These are textual references, not new proof or claim-coverage judgments. '
                      'Use formalpedia_show with the name and module to inspect complete hypotheses. '
                      'Check existing dossiers and negative knowledge before reopening a direction.'}
