"""Read-only change impact from Git, static imports and recorded research dependencies."""
from __future__ import annotations

import ast
from collections import defaultdict, deque
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

from lab_environment import ROOT, environment
import sys
sys.path.insert(0, str(ROOT / "src"))
from research.claims import load_claims, EXPORT

LIMITATIONS = ('Static module imports and recorded file associations, not theorem-level dependence, '
               'complete dynamic dependency discovery, compilation or mathematical verification. '
               'Unrecorded historical datasets cannot be certified by this report.')


def git(root: Path, *args: str) -> bytes:
    result = subprocess.run(['git', '-c', f'safe.directory={root.resolve().as_posix()}', *args],
                            cwd=root, env=environment(root), capture_output=True,
                            stdin=subprocess.DEVNULL, timeout=60)
    if result.returncode:
        raise ValueError(result.stderr.decode('utf-8', 'replace').strip())
    return result.stdout


def names(raw: bytes) -> set[str]:
    return {p.decode('utf-8') for p in raw.split(b'\0') if p}


def relative(root: Path, name: str) -> str:
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f'Path outside selected checkout: {name}')
    return path.relative_to(root.resolve()).as_posix()


def inventory(root: Path) -> set[str]:
    root = root.resolve()
    files = names(git(root, 'ls-files', '--cached', '--others', '--exclude-standard', '-z'))
    for name in files:
        if not (root / name).resolve().is_relative_to(root):
            raise ValueError(f'Path outside selected checkout: {name}')
    return files


def fingerprint(root: Path, files: set[str]) -> str:
    """Detect normal concurrent edits, additions and deletions; not an execution audit."""
    stamp = []
    for name in sorted(files):
        path = root / name
        try:
            stat = path.stat()
            stamp.append((name, stat.st_mtime_ns, stat.st_size))
        except FileNotFoundError:
            stamp.append((name, None, None))
    return hashlib.sha256(json.dumps(stamp).encode()).hexdigest()[:24]


def python_module(path: str) -> str:
    parts = Path(path).with_suffix('').parts
    if parts[0] == 'src':
        parts = parts[1:]
    if parts[-1] == '__init__':
        parts = parts[:-1]
    return '.'.join(parts)


def graph(root: Path, files: set[str], previous: dict[str, bytes]) -> tuple[dict, list[str]]:
    sources = {p for p in files | previous.keys() if p.endswith(('.py', '.lean'))
               and (p.startswith(('src/', 'tools/', 'tests/', 'formal/')) or p == 'conftest.py')}
    identities = defaultdict(set)
    for path in sources:
        if path.endswith('.py'):
            identities[python_module(path)].add(path)
            if path.startswith('tools/'):
                # Scripts run with tools/ on sys.path, including its packages.
                identities[python_module(path).removeprefix('tools.')].add(path)
        else:
            identities[path.removeprefix('formal/').removesuffix('.lean').replace('/', '.')].add(path)
    reverse = defaultdict(set)
    uncertain = []
    for path in sorted(sources):
        versions = []
        if (root / path).is_file():
            versions.append((root / path).read_bytes())
        if path in previous:
            versions.append(previous[path])
        for raw in versions:
            try:
                text = raw.decode('utf-8-sig')
            except UnicodeDecodeError:
                uncertain.append(f'Cannot decode source {path} as UTF-8')
                continue
            imports = set()
            if path.endswith('.lean'):
                imports.update(re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', text, re.M))
            else:
                try:
                    tree = ast.parse(text)
                except SyntaxError:
                    uncertain.append(f'Cannot parse Python imports in {path}')
                    continue
                module = python_module(path)
                package = module if path.endswith('/__init__.py') else module.rpartition('.')[0]
                for node in ast.walk(tree):
                    if isinstance(node, ast.Import):
                        imports.update(a.name for a in node.names)
                    elif isinstance(node, ast.ImportFrom):
                        base = node.module or ''
                        if node.level:
                            parent = package.split('.')[:len(package.split('.')) - node.level + 1]
                            base = '.'.join([*parent, *([base] if base else [])])
                        imports.add(base)
                        imports.update(base + '.' + a.name for a in node.names if a.name != '*')
            for name in imports:
                # Importing a child executes package __init__ files too.
                for end in range(1, len(name.split('.')) + 1):
                    for dependency in identities.get('.'.join(name.split('.')[:end]), ()):
                        if dependency != path:
                            reverse[dependency].add(path)
    return reverse, sorted(set(uncertain))


def closure(reverse: dict, changed: set[str]) -> set[str]:
    found = set(changed)
    pending = deque(changed)
    while pending:
        for path in reverse.get(pending.popleft(), ()):
            if path not in found:
                found.add(path)
                pending.append(path)
    return found


def old_sources(root: Path, base: str, changed: set[str]) -> dict[str, bytes]:
    tracked = names(git(root, 'ls-tree', '-r', '--name-only', '-z', base))
    paths = sorted(p for p in changed & tracked if p.endswith(('.py', '.lean')))
    result = {}
    for start in range(0, len(paths), 100):
        with zipfile.ZipFile(io.BytesIO(git(root, 'archive', '--format=zip', base, '--', *paths[start:start + 100]))) as archive:
            result.update({p: archive.read(p) for p in archive.namelist() if not p.endswith('/')})
    return result


def descriptors(rows, owner: str) -> set[str]:
    if not isinstance(rows, list) or any(not isinstance(r, dict) or not isinstance(r.get('path'), str) for r in rows):
        raise ValueError(f'Malformed file descriptors in {owner}; run lab.py check')
    return {r['path'] for r in rows}


def analyze(root: Path = ROOT, *, since: str = 'HEAD', paths: list[str] | None = None,
            test_attribution: bool = False) -> dict:
    root = root.resolve()
    base = git(root, 'rev-parse', '--verify', '--end-of-options', since + '^{commit}').decode().strip()
    files = inventory(root)
    if paths is None:
        changed = names(git(root, 'diff', '--name-only', '--no-renames', '-z', base, '--'))
        changed |= names(git(root, 'ls-files', '--others', '--exclude-standard', '-z'))
    else:
        changed = set()
        for name in paths:
            path = relative(root, name)
            if (root / path).is_dir():
                changed.update(p for p in files if path == '.' or p.startswith(path.rstrip('/') + '/'))
            else:
                changed.add(path)
    for name in changed:
        relative(root, name)
    watched = files | changed
    before = fingerprint(root, watched)
    reverse, uncertain = graph(root, files, old_sources(root, base, changed))
    affected = closure(reverse, changed)
    # Ordinary impact/full verification needs only the union, not a closure per file.
    reach = {path: closure(reverse, {path}) for path in changed} if test_attribution else {}
    uncertain += [f'Changed code reaches pytest setup: {p}' for p in sorted(affected)
                  if (p == 'conftest.py' or p.startswith('tests/'))
                  and Path(p).name in {'conftest.py', '__init__.py'}]
    items = [{'kind': 'changed_file', 'path': p, 'exists': (root / p).is_file(), 'basis': 'selected Git comparison or explicit path'}
             for p in sorted(changed)]
    items += [{'kind': 'dependent_module', 'path': p, 'basis': 'transitive static import; old and new edges included'}
              for p in sorted(affected - changed)]
    tests = {p for p in affected if p.startswith('tests/') and p.endswith('.py') and (root / p).is_file()
             and (Path(p).name.startswith('test_') or Path(p).name.endswith('_test.py'))}
    test_links = {path: tests & linked for path, linked in reach.items()}
    from research_catalog import ResearchCatalogue
    catalogue = ResearchCatalogue(root)
    claims = load_claims(root, required=False)
    for row in claims.entries:
        origin = claims.location(row['id'])
        linked = catalogue._claim_references(row, root / EXPORT) & affected
        if linked or origin['path'] in changed or EXPORT in changed:
            items.append({'kind': 'claim', 'id': row['id'], 'tag': row['tag'],
                          'claim_location': origin, 'paths': sorted(linked),
                          'basis': 'recorded association; not proof coverage'})
            cited = set()
            for reference in row.get('tests', []):
                if reference.startswith('tests/'):
                    if reference.endswith('.py') and reference in files and (root / reference).is_file():
                        cited.add(reference)
                    elif (root / reference).is_dir():
                        cited.update(p for p in files if p.startswith(reference.rstrip('/') + '/')
                                     and p.endswith('.py') and Path(p).name.startswith('test_')
                                     and (root / p).is_file())
            tests.update(cited)
            for path, reached in reach.items():
                if linked & reached or path in {origin['path'], EXPORT}:
                    test_links[path].update(cited)
    papers = set()
    for letter in 'abcde':
        manifest = f'docs/theory/paper_{letter}_' + ('build.json' if letter == 'b' else 'release.json')
        if not (root / manifest).is_file():
            continue
        release = json.loads((root / manifest).read_text(encoding='utf-8'))
        if not isinstance(release, dict):
            raise ValueError(f'Malformed release manifest: {manifest}')
        inputs = descriptors(release.get('inputs', []), manifest) | descriptors(release.get('outputs', []), manifest)
        if letter == 'b':
            inputs = {p for p in files for row in release.get('files', []) if Path(p).name == row.get('name')}
        touched = inputs & affected
        if touched or manifest in changed or any(p.startswith(f'preprints/zenodo_paper_{letter}/')
                                                 or p == f'tools/build_paper_{letter}_kit.py' for p in changed):
            papers.add(letter)
            items.append({'kind': 'paper', 'id': letter.upper(), 'manifest': manifest,
                          'paths': sorted(touched), 'basis': 'release inventory or publication-kit path; freshness not checked'})
    for name in sorted(p for p in files if p.endswith('.research.json') and (root / p).is_file()):
        data = json.loads((root / name).read_text(encoding='utf-8'))
        if not isinstance(data, dict):
            raise ValueError(f'Malformed research manifest: {name}')
        if data.get('schema') not in {'btlab-output/v1', 'btlab-output/v2'}:
            continue
        inputs = descriptors(data.get('inputs', []), name) | descriptors(data.get('source', {}).get('files', []), name)
        artifact_root = (root / name).parent / data.get('artifact_root', '.')
        outputs = {relative(root, str(artifact_root / path)) for path in descriptors(data.get('outputs', []), name)}
        touched = (inputs | outputs | {name}) & affected
        if touched:
            items.append({'kind': 'dataset', 'path': name, 'id': data.get('research_id'),
                          'paths': sorted(touched), 'basis': 'recorded source/input/output; integrity not checked'})
    items += [{'kind': 'test', 'path': p, 'basis': 'static import or explicit claim test link'} for p in sorted(tests)]
    current = inventory(root)
    if files != current or before != fingerprint(root, current | changed):
        raise ValueError('Checkout changed while computing impact; retry for a consistent snapshot')
    lean = sorted(p.removeprefix('formal/').removesuffix('.lean').replace('/', '.') for p in affected
                  if p.startswith('formal/') and p.endswith('.lean') and (root / p).is_file())
    return {'status': 'planned', 'snapshot': before, 'base_commit': base,
            'comparison': 'base commit to working tree, including staged and untracked files' if paths is None else 'explicit paths',
            'changed_files': sorted(changed), 'affected_tests': sorted(tests), 'lean_targets': lean,
            'test_links': {p: sorted(v) for p, v in sorted(test_links.items())},
            'extra_watch_paths': sorted(changed - files),
            'affected_papers': sorted(papers), 'uncertainties': uncertain,
            'items': items, 'limitations': LIMITATIONS}


def impact(root: Path = ROOT, *, since: str = 'HEAD', paths: list[str] | None = None,
           limit: int = 20, offset: int = 0, snapshot: str | None = None) -> dict:
    from research_catalog import page
    page([], limit, offset)
    result = analyze(root, since=since, paths=paths)
    if snapshot is not None and snapshot != result['snapshot']:
        raise ValueError('Impact snapshot changed; restart pagination')
    items = result.pop('items')
    result.pop('test_links')  # Internal attribution; paginated test items remain bounded.
    for row in items:
        if 'paths' in row:
            row['path_count'] = len(row['paths'])
            row['paths_truncated'] = len(row['paths']) > 12
            row['paths'] = row['paths'][:12]
    items += [{'kind': 'uncertainty', 'reason': reason} for reason in result['uncertainties']]
    # Page every potentially large collection; summary lists expose counts only.
    result['counts'] = {kind: sum(r['kind'] == kind for r in items) for kind in
                        ('changed_file', 'dependent_module', 'claim', 'dataset', 'paper', 'test', 'uncertainty')}
    for key in ('changed_files', 'affected_tests', 'lean_targets', 'uncertainties', 'extra_watch_paths'):
        values = result.pop(key)
        result[key + '_count'] = len(values)
    return result | page(items, limit, offset)
