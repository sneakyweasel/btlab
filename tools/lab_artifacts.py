"""Explicit local staging, inspection, promotion and recovery of research outputs."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import uuid

import artifact_store as store
from lab_environment import ROOT, environment
from lab_impact import git, inventory
from lab_prepare import python_inventory, runtime_python
from research.experiments.provenance import check_manifest

LIMITATIONS = ('Local cooperative workflow, not an execution sandbox or a multi-file transaction. '
              'Snapshots cover Git-visible files, explicitly watched inputs and the Python package inventory; '
              'not external services, undeclared ignored inputs or arbitrary native libraries. '
              'Manifest integrity does not establish mathematical correctness. Evidence labels are unchanged.')


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def snapshot(root: Path, selected: list[str], watched: list[str]) -> dict:
    names = inventory(root) | set(watched)
    files = {name: store.digest(store.path(root, name)) for name in sorted(names)
             if not store.owned(name, selected)}
    python = runtime_python(root)
    return {'head': git(root, 'rev-parse', 'HEAD').decode().strip(), 'files': files,
            'python': python, 'packages': python_inventory(Path(python))}


def payload(root: Path, folder: Path, state: dict, area: str) -> dict[str, str]:
    """Every promoted byte must be a sidecar or an output owned by one sidecar."""
    base = store.local(root, folder, area)
    present = store.files(base, state['targets'])
    if not present:
        raise ValueError('Producer created no selected outputs')
    # A producer may retain diagnostic logs under its scratch .build directory.
    # Reject everything else outside the selected output trees, including links.
    for name in store.files(base, [p.name for p in base.iterdir()]):
        if not store.owned(name, state['targets']) and not name.startswith('.build/'):
            raise ValueError(f'Unselected staged output: {name}')
    manifests = {name for name in present if name.endswith('.research.json')}
    covered = set()
    for name in sorted(manifests):
        file = store.local(root, folder, area + '/' + name)
        result = check_manifest(file, root, hashes=True)
        # Staging is intentionally stricter than catalogue discovery: stale sources,
        # unknown provenance and changed byte representations all block promotion.
        if result['errors'] or result['warnings']:
            raise ValueError(f'Invalid staged manifest {name}: ' + '; '.join(result['errors'] + result['warnings']))
        data = json.loads(file.read_text(encoding='utf-8'))
        if data['source']['revision'] != state['source']['head']:
            raise ValueError(f'Manifest revision differs from the staged checkout: {name}')
        if name.startswith('data/research/') and name.split('/')[2] != data['programme']:
            raise ValueError(f'Manifest programme differs from its target: {name}')
        anchor = (file.parent / data['artifact_root']).resolve()
        if not anchor.is_relative_to(base):
            raise ValueError(f'Manifest artifact root escapes staged payload: {name}')
        for output in data['outputs']:
            output_name = (anchor / output['path']).relative_to(base).as_posix()
            store.local(root, folder, area + '/' + output_name)
            if output_name not in present or output_name in manifests or output_name in covered:
                raise ValueError(f'Unselected, duplicated or recursive manifest output: {output_name}')
            if output_name.startswith('data/research/') and output_name.split('/')[2] != data['programme']:
                raise ValueError(f'Output programme differs from its manifest: {output_name}')
            covered.add(output_name)
        for entry in data['inputs'] + data['source']['files']:
            input_name = entry['path']
            store.path(root, input_name)
            if input_name not in state['source']['files'] or state['source']['files'][input_name] is None:
                raise ValueError(f'Input/source was not captured before the run; use --input for ignored files: {input_name}')
    if covered | manifests != present.keys():
        raise ValueError('Unmanifested staged outputs: ' + ', '.join(sorted(present.keys() - covered - manifests)[:10]))
    return present


def freshness(root: Path, state: dict) -> list[str]:
    reasons = []
    if snapshot(root, state['targets'], state['watched']) != state['source']:
        reasons.append('Source files, HEAD or Python environment changed since staging began')
    if store.files(root, state['targets']) != state['destination']:
        reasons.append('Canonical destination changed since staging began')
    return reasons


def stage(root: Path, targets: list[str], command: list[str], *, watched=(), timeout=1200) -> dict:
    root = root.resolve()
    selected = store.targets(root, targets)
    if (not command or command[0] != 'python' or not any('{stage}' in arg for arg in command[1:])
            or timeout <= 0):
        raise ValueError('Use an explicit python command with a {stage} output path and a positive timeout')
    watched = sorted(set(watched))
    for name in watched:
        if store.owned(name, selected) or not store.path(root, name).is_file() or name.startswith(store.DIRECTORY + '/'):
            raise ValueError('--input must name an existing checkout file outside the selected outputs and stage store')
    identifier = uuid.uuid4().hex
    folder = store.location(root, identifier)
    folder.mkdir(parents=True)
    work = store.local(root, folder, 'work')
    work.mkdir()
    argv = [runtime_python(root), *(arg.replace('{stage}', work.relative_to(root).as_posix()) for arg in command[1:])]
    state = {'schema': store.SCHEMA, 'id': identifier, 'root': root.as_posix(), 'targets': selected,
             'status': 'running', 'created_utc': now(), 'command': argv, 'watched': watched, 'files': {},
             'destination': store.files(root, selected), 'source': snapshot(root, selected, watched),
             'limitations': LIMITATIONS}
    receipt = store.local(root, folder, 'state.json')
    store.save(receipt, state)
    print('Staging ' + identifier + '; local log: ' + str(folder / 'producer.log'), file=sys.stderr, flush=True)
    try:
        if freshness(root, state):
            raise ValueError('Checkout changed while recording the starting state')
        env = environment(root)
        env['BTLAB_RUN_COMMAND'] = json.dumps(['python', *argv[1:]])
        with store.local(root, folder, 'producer.log').open('wb') as log:
            result = subprocess.run(argv, cwd=root, env=env, stdin=subprocess.DEVNULL,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        state['exit_code'] = result.returncode
        if result.returncode:
            raise ValueError(f'Producer exited with code {result.returncode}; inspect producer.log')
        candidate = payload(root, folder, state, 'work')
        for name, sha in candidate.items():
            store.copy_checked(store.local(root, folder, 'work/' + name),
                               store.local(root, folder, 'sealed/' + name), sha)
        state['files'] = candidate
        if payload(root, folder, state, 'sealed') != candidate:
            raise ValueError('Candidate changed while sealing')
        changed = freshness(root, state)
        if changed:
            raise ValueError('; '.join(changed))
        state['status'] = 'ready'
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        state.update(status='failed', error=str(exc))
    state['finished_utc'] = now()
    store.save(receipt, state)
    return summary(state)


def summary(state: dict) -> dict:
    return {key: state[key] for key in ('id', 'status', 'targets', 'created_utc', 'error') if key in state} | {
        'file_count': len(state['files']), 'receipt': store.DIRECTORY + '/' + state['id'] + '/state.json',
        'log': store.DIRECTORY + '/' + state['id'] + '/producer.log', 'limitations': LIMITATIONS}


def journal_for(root: Path, folder: Path) -> dict | None:
    file = store.local(root, folder, 'promotion.json')
    return json.loads(file.read_text(encoding='utf-8')) if file.exists() else None


def listing(root: Path, *, limit=30) -> dict:
    if not 1 <= limit <= 200:
        raise ValueError('limit must be between 1 and 200')
    root = root.resolve()
    directory = store.path(root, store.DIRECTORY)
    folders = sorted((p for p in directory.iterdir() if p.is_dir()),
                     key=lambda p: p.stat().st_mtime_ns, reverse=True) if directory.exists() else []
    items = []
    for folder in folders[:limit]:
        try:
            _, state = store.load(root, folder.name)
            item = summary(state)
            journal = journal_for(root, folder)
            if journal and journal['status'] in {'writing', 'committed'}:
                item['status'] = 'recovery_required' if journal['status'] == 'writing' else 'promoted'
            items.append(item)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            items.append({'id': folder.name, 'status': 'unreadable', 'error': str(exc)})
    return {'status': 'listed', 'stages': items, 'total': len(folders), 'truncated': len(folders) > limit,
            'freshness': 'not checked; inspect a stage before promotion'}


def inspect(root: Path, identifier: str, *, limit=30) -> dict:
    if not 1 <= limit <= 200:
        raise ValueError('limit must be between 1 and 200')
    root = root.resolve()
    folder, state = store.load(root, identifier)
    journal = journal_for(root, folder)
    result = summary(state)
    if journal:
        result['promotion'] = journal['status']
        if journal['status'] == 'committed':
            result['status'] = 'promoted'
        elif journal['status'] == 'writing':
            result['status'] = 'recovery_required'
    result['files'] = [{'path': name, 'change': 'new' if name not in state['destination'] else
                        'unchanged' if sha == state['destination'][name] else 'replaced'}
                       for name, sha in sorted(state['files'].items())][:limit]
    result['files_truncated'] = len(state['files']) > limit
    if result['status'] == 'ready':
        try:
            reasons = freshness(root, state)
            pending = store.pending(root)
            if pending:
                reasons.append('Recover pending promotion(s) first: ' + ', '.join(pending))
            if payload(root, folder, state, 'sealed') != state['files']:
                reasons.append('Sealed candidate fingerprint changed')
            result.update(promotable=not reasons, blockers=reasons)
        except (OSError, ValueError, subprocess.SubprocessError) as exc:
            result.update(promotable=False, blockers=[str(exc)])
    else:
        result['promotable'] = False
    return result


def promote(root: Path, identifier: str) -> dict:
    root = root.resolve()
    with store.lock(root):
        folder, state = store.load(root, identifier)
        old = journal_for(root, folder)
        if old and old['status'] == 'committed':
            return summary(state) | {'status': 'promoted', 'already_committed': True}
        pending = store.pending(root)
        if pending:
            raise ValueError('Recover pending promotion(s) first: ' + ', '.join(pending))
        if state['status'] != 'ready' or not state['files']:
            raise ValueError('Only a successfully sealed ready stage can be promoted')
        reasons = freshness(root, state)
        if reasons:
            raise ValueError('; '.join(reasons))
        if payload(root, folder, state, 'sealed') != state['files']:
            raise ValueError('Sealed candidate fingerprint changed')
        entries = {name: {'before': state['destination'].get(name), 'after': sha}
                   for name, sha in state['files'].items()}
        for name, record in entries.items():
            if record['before'] is not None:
                store.copy_checked(store.path(root, name), store.local(root, folder, 'backup/' + name), record['before'])
        reasons = freshness(root, state)
        if reasons:
            raise ValueError('; '.join(reasons))
        journal = {'status': 'writing', 'started_utc': now(), 'files': entries}
        journal_path = store.local(root, folder, 'promotion.json')
        store.save(journal_path, journal)
        try:
            for name in sorted(entries, key=lambda n: (n.endswith('.research.json'), n)):
                record = entries[name]
                destination = store.path(root, name)
                if store.digest(destination) != record['before']:
                    raise ValueError(f'Destination changed before replacement: {name}')
                raw = store.local(root, folder, 'sealed/' + name).read_bytes()
                if hashlib.sha256(raw).hexdigest() != record['after']:
                    raise ValueError(f'Sealed candidate changed before replacement: {name}')
                store.atomic(destination, raw)
            expected = state['destination'] | state['files']
            if store.files(root, state['targets']) != expected:
                raise ValueError('Destination changed during promotion')
            if snapshot(root, state['targets'], state['watched']) != state['source']:
                raise ValueError('Source state changed during promotion')
        except (OSError, ValueError) as exc:
            state['error'] = str(exc)
            try:
                store.restore(root, folder, state, journal)
            except (OSError, ValueError) as recovery:
                state.update(status='recovery_required', error=f'{exc}; recovery: {recovery}')
                store.save(store.local(root, folder, 'state.json'), state)
            raise ValueError(state['error']) from exc
        # The committed journal is the commit point; an interrupted state update
        # must never cause a later invocation to roll back a completed promotion.
        journal.update(status='committed', finished_utc=now())
        store.save(journal_path, journal)
        state.update(status='promoted', promoted_utc=now())
        state.pop('error', None)
        store.save(store.local(root, folder, 'state.json'), state)
        return summary(state)


def recover(root: Path, identifier: str) -> dict:
    root = root.resolve()
    with store.lock(root):
        folder, state = store.load(root, identifier)
        journal = journal_for(root, folder)
        if not journal or journal['status'] != 'writing':
            raise ValueError('No pending promotion to recover; committed promotions cannot be rolled back here')
        store.restore(root, folder, state, journal)
        return summary(state) | {'recovery': 'rolled_back'}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    overview = commands.add_parser('list', help='read recent local receipts without checking freshness')
    overview.add_argument('--limit', type=int, default=30)
    create = commands.add_parser('stage', help='run an explicit Python producer into ignored scratch space')
    create.add_argument('--target', action='append', required=True, help='checkout-relative output directory (repeatable)')
    create.add_argument('--input', action='append', default=[], help='also watch this ignored checkout input file')
    create.add_argument('--timeout', type=float, default=1200)
    create.add_argument('command', nargs=argparse.REMAINDER, help='-- python producer.py --output {stage}/data/research/...')
    for name in ('inspect', 'promote', 'recover'):
        command = commands.add_parser(name)
        command.add_argument('id')
        if name == 'inspect':
            command.add_argument('--limit', type=int, default=30)
    args = parser.parse_args(argv)
    try:
        if args.action == 'list':
            result = listing(ROOT, limit=args.limit)
        elif args.action == 'stage':
            command = args.command[1:] if args.command[:1] == ['--'] else args.command
            result = stage(ROOT, args.target, command, watched=args.input, timeout=args.timeout)
        elif args.action == 'inspect':
            result = inspect(ROOT, args.id, limit=args.limit)
        elif args.action == 'promote':
            result = promote(ROOT, args.id)
        else:
            result = recover(ROOT, args.id)
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return int(result['status'] in {'failed', 'recovery_required'} or result.get('promotable') is False
                   and result['status'] == 'ready')
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(json.dumps({'status': 'failed', 'error': str(exc)}))
        return 1
