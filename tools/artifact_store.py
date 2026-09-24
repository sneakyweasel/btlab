"""Checked artifact paths, immutable candidates and recoverable local promotion.

Promotion is atomic per file, with manifests last and a durable rollback journal.
It is not a multi-file filesystem transaction or protection against hostile writers.
"""
from __future__ import annotations

from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import tempfile

SCHEMA = 'btlab-artifact-stage/v1'
DIRECTORY = '.build/artifacts'


def relative(name: str) -> str:
    if (not isinstance(name, str) or not name or '\\' in name or ':' in name
            or any(ord(c) < 32 for c in name)
            or PurePosixPath(name).is_absolute() or '..' in PurePosixPath(name).parts
            or PurePosixPath(name).as_posix() != name or name == '.'):
        raise ValueError(f'Expected a normalized checkout-relative path: {name!r}')
    for part in PurePosixPath(name).parts:
        if (part.endswith((' ', '.')) or re.fullmatch(r'(?i:con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\..*)?', part)
                or any(c in part for c in '<>"|?*')):
            raise ValueError(f'Nonportable artifact path: {name!r}')
    return name


def path(root: Path, name: str) -> Path:
    """Reject links, including Windows junctions, before touching any managed path."""
    root = root.resolve()
    current = root
    for part in PurePosixPath(relative(name)).parts:
        current /= part
        try:
            info = current.lstat()
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(info.st_mode) or getattr(info, 'st_file_attributes', 0) & 0x400:
            raise ValueError(f'Linked artifact path: {name}')
    if not current.resolve().is_relative_to(root):
        raise ValueError('Artifact path escaped its root')
    return current


def targets(root: Path, names: list[str]) -> list[str]:
    if not names or len(names) != len(set(names)):
        raise ValueError('Supply distinct research output target directories')
    for name in names:
        parts = PurePosixPath(relative(name)).parts
        allowed = (len(parts) >= 4 and parts[:3] in {
            ('data', 'research', 'juggler'), ('data', 'research', 'collatz')}
            or len(parts) >= 3 and parts[:3] == ('docs', 'theory', 'figures'))
        if not allowed:
            raise ValueError(f'Target is not a research output directory: {name}')
        dest = path(root, name)
        if dest.exists() and not dest.is_dir():
            raise ValueError(f'Target must be a directory: {name}')
        if any(other != name and name.startswith(other + '/') for other in names):
            raise ValueError('Overlapping targets are not allowed')
    return sorted(names)


def owned(name: str, selected: list[str]) -> bool:
    return any(name.startswith(target + '/') for target in selected)


def digest(file: Path) -> str | None:
    if not file.exists():
        return None
    if not stat.S_ISREG(file.lstat().st_mode):
        raise ValueError(f'Expected a regular file: {file}')
    with file.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def files(root: Path, selected: list[str]) -> dict[str, str]:
    result = {}
    for target in selected:
        directory = path(root, target)
        if not directory.exists():
            continue
        if directory.is_file():
            result[target] = digest(directory)
            continue
        for parent, directories, names in os.walk(directory, followlinks=False):
            for name in directories + names:
                file = path(root, (Path(parent) / name).relative_to(root).as_posix())
                if file.is_file():
                    result[file.relative_to(root).as_posix()] = digest(file)
                elif not file.is_dir():
                    raise ValueError(f'Unexpected special file: {file}')
    return dict(sorted(result.items()))


def atomic(file: Path, raw: bytes) -> None:
    file.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix='.artifact-', dir=file.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, file)
    finally:
        temporary.unlink(missing_ok=True)


def save(file: Path, value: dict) -> None:
    atomic(file, (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode('utf-8'))


def location(root: Path, identifier: str) -> Path:
    if not re.fullmatch(r'[0-9a-f]{32}', identifier):
        raise ValueError('Stage ID must be 32 lowercase hexadecimal characters')
    return path(root, DIRECTORY + '/' + identifier)


def load(root: Path, identifier: str) -> tuple[Path, dict]:
    folder = location(root, identifier)
    state = json.loads(path(root, (folder / 'state.json').relative_to(root).as_posix()).read_text(encoding='utf-8'))
    if (not isinstance(state, dict) or state.get('schema') != SCHEMA or state.get('id') != identifier
            or state.get('root') != root.resolve().as_posix()):
        raise ValueError('Stage receipt does not belong to this checkout')
    targets(root, state['targets'])
    if state['status'] not in {'running', 'failed', 'ready', 'promoted', 'recovery_required'}:
        raise ValueError('Unknown artifact stage status')
    for field in ('files', 'destination'):
        hashes(state[field])
        if any(not owned(name, state['targets']) for name in state[field]):
            raise ValueError('Receipt contains an unowned target')
    return folder, state


def hashes(value: dict) -> None:
    if not isinstance(value, dict):
        raise ValueError('Expected a file fingerprint map')
    for name, sha in value.items():
        relative(name)
        if sha is not None and (not isinstance(sha, str) or not re.fullmatch(r'[0-9a-f]{64}', sha)):
            raise ValueError('Invalid file fingerprint')


def local(root: Path, folder: Path, name: str) -> Path:
    """Validate every component, including the candidate/backup directory itself."""
    relative(name)
    return path(root, folder.relative_to(root).as_posix() + '/' + name)


def copy_checked(source: Path, destination: Path, expected: str) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    if digest(destination) != expected or digest(source) != expected:
        raise ValueError(f'File changed while copying: {source.name}')


@contextmanager
def lock(root: Path):
    directory = path(root, DIRECTORY)
    directory.mkdir(parents=True, exist_ok=True)
    with path(root, DIRECTORY + '/publish.lock').open('a+b') as stream:
        if os.name == 'nt':
            import msvcrt
            if stream.tell() == 0:
                stream.write(b'\0')
                stream.flush()
            stream.seek(0)
            try:
                msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError as exc:
                raise ValueError('Another artifact promotion is running') from exc
        else:
            import fcntl
            try:
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                raise ValueError('Another artifact promotion is running') from exc
        try:
            yield
        finally:
            if os.name == 'nt':
                stream.seek(0)
                msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def pending(root: Path) -> list[str]:
    directory = path(root, DIRECTORY)
    if not directory.exists():
        return []
    result = []
    for folder in directory.iterdir():
        if re.fullmatch(r'[0-9a-f]{32}', folder.name):
            journal = path(root, DIRECTORY + '/' + folder.name + '/promotion.json')
            if journal.exists() and json.loads(journal.read_text(encoding='utf-8'))['status'] == 'writing':
                result.append(folder.name)
    return sorted(result)


def restore(root: Path, folder: Path, state: dict, journal: dict) -> None:
    """Refuse to overwrite a third party's bytes, even while recovering our own run."""
    entries = journal.get('files')
    if not isinstance(entries, dict) or not entries:
        raise ValueError('Invalid promotion journal')
    if journal.get('status') != 'writing' or set(entries) != set(state['files']):
        raise ValueError('Journal is not a pending promotion of this candidate')
    for name, record in entries.items():
        if not owned(relative(name), state['targets']):
            raise ValueError('Journal contains an unowned target')
        if record != {'before': state['destination'].get(name), 'after': state['files'][name]}:
            raise ValueError('Journal differs from the sealed candidate')
        current = digest(path(root, name))
        if current not in {record['before'], record['after']}:
            raise ValueError(f'Recovery conflict; preserve the newer destination: {name}')
        if record['before'] is not None and digest(local(root, folder, 'backup/' + name)) != record['before']:
            raise ValueError(f'Recovery backup is missing or corrupt: {name}')
    for name in sorted(entries, key=lambda n: (n.endswith('.research.json'), n)):
        record = entries[name]
        destination = path(root, name)
        current = digest(destination)
        if current == record['before']:
            continue
        if current != record['after']:
            raise ValueError(f'Destination changed during recovery: {name}')
        if record['before'] is None:
            destination.unlink()
        else:
            raw = local(root, folder, 'backup/' + name).read_bytes()
            if hashlib.sha256(raw).hexdigest() != record['before']:
                raise ValueError(f'Recovery backup changed: {name}')
            atomic(destination, raw)
    if any(digest(path(root, name)) != record['before'] for name, record in entries.items()):
        raise ValueError('Destination changed during recovery')
    journal['status'] = 'rolled_back'
    save(local(root, folder, 'promotion.json'), journal)
    state['status'] = 'ready'
    save(local(root, folder, 'state.json'), state)
