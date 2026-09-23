"""Build/check Paper A's deterministic source supplement and delivery bundle.

Run after build_paper_a.py. --archive refreshes only the source supplement,
before writing the QA record. The supplement retains repository paths and
includes the complete release input inventory, not unrelated working files.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('paper_a_builder_for_kit', Path(__file__).with_name('build_paper_a.py'))
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)
SOURCE, EDITORIAL, input_files = A.SOURCE, A.EDITORIAL, A.input_files
KIT = 'preprints/zenodo_paper_a'
SOURCE_ZIP = f'{KIT}/paper_a_source_and_verification.zip'
BUNDLE = f'{KIT}/paper_a_zenodo_package.zip'
QA = 'docs/theory/paper_a_publication_check.json'
PDF_NAME = Path(A.PDF_EXPORTS[0]).name
STAMP = datetime.fromtimestamp(int(A._SOURCE_DATE_EPOCH), timezone.utc).timetuple()[:6]
BINARY = {'.pdf', '.png', '.jpg', '.zip'}
KIT_DOCS = ['README.md', 'AFTER_ZENODO.md', 'ZENODO_FIELDS.txt']
EXTRA_SOURCE = [
    'LICENSE', A.MANIFEST, *A.OUTPUTS,
    f'{KIT}/SOURCE_README.md', f'{KIT}/ZENODO_FIELDS.txt',
    'docs/theory/figures/juggler_lean_layers.png',
    'docs/theory/figures/juggler_lean_layers.mmd',
]


def payload(path: Path) -> bytes:
    data = path.read_bytes()
    return data if path.suffix.lower() in BINARY else data.replace(b'\r\n', b'\n').replace(b'\r', b'\n')


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sums(body: dict[str, bytes]) -> bytes:
    return ''.join(f'{digest(data)}  {name}\n' for name, data in sorted(body.items())).encode('utf-8')


def source_body(root: Path) -> dict[str, bytes]:
    paths = sorted(set(input_files(root) + EXTRA_SOURCE))
    body = {p: payload(root / p) for p in paths}
    body['README.md'] = payload(root / KIT / 'SOURCE_README.md')
    return body


def write_zip(path: Path, body: dict[str, bytes]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED) as z:
        for name, data in sorted({**body, 'SHA256SUMS.txt': sums(body)}.items()):
            info = zipfile.ZipInfo(name, STAMP)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 0
            info.external_attr = 0o644 << 16
            z.writestr(info, data)


def agree(root: Path) -> None:
    record = json.loads((root / QA).read_text(encoding='utf-8'))
    meta = json.loads((root / A.METADATA).read_text(encoding='utf-8'))
    expected = {
        'version': meta['version'],
        'pdf_sha256': digest(payload(root / A.PDF)),
        'source_sha256': digest(payload(root / SOURCE)),
        'source_zip_sha256': digest(payload(root / SOURCE_ZIP)),
    }
    if any(record.get(k) != v for k, v in expected.items()):
        raise ValueError('Paper A publication check describes different files; refresh its evidence before packaging')


def bundle_body(root: Path) -> dict[str, bytes]:
    members = {
        PDF_NAME: A.PDF,
        Path(SOURCE_ZIP).name: SOURCE_ZIP,
        'paper_a_publication_check.json': QA,
        'paper_a_zenodo.json': A.METADATA,
        'PAPER_A_BUILD.md': 'docs/theory/PAPER_A_BUILD.md',
        **{n: f'{KIT}/{n}' for n in KIT_DOCS},
    }
    return {name: payload(root / path) for name, path in members.items()}


def kit_body(root: Path) -> dict[str, bytes]:
    names = [PDF_NAME, Path(SOURCE_ZIP).name, Path(BUNDLE).name,
             'paper_a_publication_check.json', 'SOURCE_README.md', *KIT_DOCS]
    return {name: (root / KIT / name).read_bytes() for name in names}


def build(root: Path, archive_only: bool = False) -> None:
    A.check(root)
    write_zip(root / SOURCE_ZIP, source_body(root))
    print(f'Built {SOURCE_ZIP}')
    if archive_only:
        return
    agree(root)
    write_zip(root / BUNDLE, bundle_body(root))
    (root / KIT / 'paper_a_publication_check.json').write_bytes(payload(root / QA))
    (root / KIT / 'SHA256SUMS.txt').write_bytes(sums(kit_body(root)))
    check(root)


def check_zip(path: Path, body: dict[str, bytes]) -> None:
    expected = {**body, 'SHA256SUMS.txt': sums(body)}
    with zipfile.ZipFile(path) as z:
        if len(z.namelist()) != len(expected) or set(z.namelist()) != set(expected):
            raise ValueError(f'Stale archive member inventory: {path.name}')
        for name, data in expected.items():
            if z.read(name) != data:
                raise ValueError(f'Stale archive member: {path.name}: {name}')


def check(root: Path) -> None:
    A.check(root)
    agree(root)
    check_zip(root / SOURCE_ZIP, source_body(root))
    check_zip(root / BUNDLE, bundle_body(root))
    if (root / KIT / 'paper_a_publication_check.json').read_bytes() != payload(root / QA):
        raise ValueError('Stale Paper A publication-check copy')
    body = kit_body(root)
    if any(b'\r' in data for name, data in body.items() if Path(name).suffix.lower() not in BINARY):
        raise ValueError('Paper A kit text must use LF line endings')
    if (root / KIT / 'SHA256SUMS.txt').read_bytes() != sums(body):
        raise ValueError('Stale Paper A kit checksums')
    print('Paper A source archive, delivery bundle, QA record and checksums agree.')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--archive', action='store_true')
    args = parser.parse_args()
    if args.check:
        check(ROOT)
    else:
        build(ROOT, archive_only=args.archive)


if __name__ == '__main__':
    main()
