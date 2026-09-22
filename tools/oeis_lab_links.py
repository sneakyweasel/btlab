"""Live local OEIS mentions in papers, dossiers, ledger rows and Lean docstrings."""
from __future__ import annotations

import hashlib
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


def find_mentions(identifier: str, root: Path):
    directories = [name for name in ('docs', 'formal', 'src', 'literature', 'attacks')
                   if (root / name).is_dir()]
    pattern = re.compile(r'\b' + identifier + r'\b')
    if shutil.which('rg') and directories:
        command = ['rg', '--json', '--no-ignore-parent', '-n', '-e', pattern.pattern,
                   '-g', '*.md', '-g', '*.lean', '-g', '*.py', '-g', '*.json',
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
    for directory in directories:
        for parent, dirs, files in os.walk(root / directory):
            dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '__pycache__'}]
            for filename in sorted(files):
                path = Path(parent) / filename
                if path.suffix not in {'.md', '.lean', '.py', '.json'}:
                    continue
                if not path.resolve().is_relative_to(root.resolve()):
                    continue
                relative = path.relative_to(root).as_posix()
                if relative.startswith('docs/research/') and path.suffix == '.json':
                    continue
                for number, text in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
                    if pattern.search(text):
                        yield relative, number, text


def lab_links(identifier: str, limit: int = 30, offset: int = 0, root: Path = ROOT):
    identifier = aid(identifier)
    bounds(limit, offset)
    pattern = re.compile(r'\b' + identifier + r'\b')
    mentions = sorted(find_mentions(identifier, root))
    results = []
    for file, line, text in mentions[offset:offset + limit]:
        match = pattern.search(text)
        start = max(0, match.start() - 150) if match else 0
        kind = ('lean' if file.endswith('.lean') else 'dossier' if file.startswith('docs/problems/')
                else 'paper_or_theory' if file.startswith('docs/theory/') and file.endswith('.md')
                else 'laboratory_reference')
        results.append({'file': file, 'line': line, 'kind': kind,
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
    claims = [{'id': row['id'], 'tag': row.get('tag'), 'lean_file': row.get('lean'),
               'declaration_references': row.get('decl'), 'statement_excerpt': row.get('statement', '')[:1000]}
              for row in rows if pattern.search(json.dumps(row, ensure_ascii=False))]
    digest = hashlib.sha256()
    for file in sorted(selected_files):
        info = (root / file).stat()
        digest.update(f'{file}:{info.st_mtime_ns}:{info.st_size}\n'.encode())
    return {'aid': identifier, 'source': 'live laboratory working tree',
            'reference_snapshot': digest.hexdigest(), 'total_mentions': len(mentions),
            'mentions': results, 'next_offset': offset + limit if offset + limit < len(mentions) else None,
            'lean_declarations': declarations[:50], 'total_lean_declarations': len(declarations),
            'ledger_claims': claims[:50], 'total_ledger_claims': len(claims),
            'related_results_truncated': len(declarations) > 50 or len(claims) > 50,
            'notice': 'These are textual references, not new proof or claim-coverage judgments. '
                      'Use formalpedia_show with the name and module to inspect complete hypotheses. '
                      'Check existing dossiers and negative knowledge before reopening a direction.'}
