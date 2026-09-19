"""Assemble the Paper B Zenodo kit: source archive, delivery bundle, checksums.

    python tools/build_paper_b_kit.py            rebuild the kit
    python tools/build_paper_b_kit.py --archive  rebuild only the source archive
    python tools/build_paper_b_kit.py --check    verify the kit against the repository

The kit used to be assembled by hand, and it showed: `sha256sum -c` on it failed
on the PDF, because `tools/build_paper_b.py --sync` refreshes the PDF alias while
nothing refreshed SHA256SUMS.txt beside it. The archives also froze whatever line
endings the packager's checkout happened to hold, so two people packaging one
commit produced two different deposits. Text members are written LF here, and
every member timestamp comes from the pinned build epoch, so the archive is a
function of the commit rather than of the machine.

Bootstrapping is why --archive exists: paper_b_release_check.json records the
source archive's digest, and the delivery bundle carries the release check. Build
the archive, write the release check against it, then build the rest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
STEM = 'juggler_parity_discrepancy_note'
KIT = 'juggler_review/zenodo_paper_b'
PDF_NAME = 'Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf'
RELEASE_CHECK = 'docs/theory/paper_b_release_check.json'
SOURCE_ARCHIVE = f'{KIT}/paper_b_source_package.zip'
BUNDLE = f'{KIT}/paper_b_zenodo_package.zip'

# Deterministic member stamps, mirroring _SOURCE_DATE_EPOCH in build_paper_b.py:
# 2026-09-19, the version this kit records.
STAMP = (2026, 9, 19, 0, 0, 0)

BINARY_SUFFIXES = {'.pdf', '.png', '.jpg', '.zip', '.bin'}

# published name -> repository path
SOURCE_MEMBERS = {
    'LICENSE-MIT.txt': 'LICENSE',
    'PAPER_B_BUILD.md': 'docs/theory/PAPER_B_BUILD.md',
    'ZENODO_README.md': 'docs/theory/ZENODO_README.md',
    'build/article.tex': 'tools/paper_b/article.tex',
    'build/layout.lua': 'tools/paper_b/layout.lua',
    'build_paper_b.py': 'tools/build_paper_b.py',
    'derive_paper_b_review.py': 'tools/derive_paper_b_review.py',
    f'{STEM}.md': f'docs/theory/{STEM}.md',
    f'{STEM}.tex': f'docs/theory/{STEM}.tex',
    'paper_b_build.json': 'docs/theory/paper_b_build.json',
    'paper_b_consolidated_validation.json': 'docs/theory/paper_b_consolidated_validation.json',
    'paper_b_proof_review.md': 'docs/theory/paper_b_proof_review.md',
    'paper_b_symbolic_review.json': 'docs/theory/paper_b_symbolic_review.json',
    'paper_b_zenodo.json': 'docs/theory/paper_b_zenodo.json',
    'paper_b_zenodo_fields.txt': 'docs/theory/paper_b_zenodo_fields.txt',
}
SOURCE_MEMBERS.update({f'validate_paper_b{s}.py': f'tools/validate_paper_b{s}.py' for s in (
    '', '_consolidated', '_d2', '_kernel_assembly', '_offset_anchor', '_ooeoe',
    '_oooee_transfer', '_repairs', '_signed_waves', '_wave_bearing')})

BUNDLE_MEMBERS = {
    PDF_NAME: f'docs/theory/{STEM}.pdf',
    'PAPER_B_BUILD.md': 'docs/theory/PAPER_B_BUILD.md',
    'ZENODO_README.md': 'docs/theory/ZENODO_README.md',
    'paper_b_proof_review.md': 'docs/theory/paper_b_proof_review.md',
    'paper_b_release_check.json': RELEASE_CHECK,
    'paper_b_source_package.zip': SOURCE_ARCHIVE,
    'paper_b_zenodo.json': 'docs/theory/paper_b_zenodo.json',
    'paper_b_zenodo_fields.txt': 'docs/theory/paper_b_zenodo_fields.txt',
}

# Kit files this tool regenerates from the repository; the rest are hand-written
# and only listed in the checksums.
KIT_GENERATED = {
    PDF_NAME: f'docs/theory/{STEM}.pdf',
    'paper_b_release_check.json': RELEASE_CHECK,
}
KIT_KEPT = ('AFTER_ZENODO.md', 'README.md', 'ZENODO_FIELDS.txt')


def payload(root: Path, rel: str) -> bytes:
    """Member bytes: text normalised to LF, binaries untouched."""
    data = (root / rel).read_bytes()
    if Path(rel).suffix.lower() in BINARY_SUFFIXES:
        return data
    return data.replace(b'\r\n', b'\n').replace(b'\r', b'\n')


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checksums(digests: dict[str, str]) -> bytes:
    """A coreutils SHA256SUMS body, sorted by name, LF throughout."""
    return b''.join(f'{d}  {n}\n'.encode() for n, d in sorted(digests.items()))


def write_zip(target: Path, body: dict[str, bytes]) -> None:
    """Write members plus their own SHA256SUMS.txt, deterministically."""
    body = dict(body)
    body['SHA256SUMS.txt'] = checksums({n: sha256(d) for n, d in body.items()})
    target.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED) as archive:
        for name in sorted(body):
            info = zipfile.ZipInfo(name, STAMP)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.create_system = 0                  # not this packager's OS
            info.external_attr = 0o644 << 16
            archive.writestr(info, body[name])


def listed_kit_files() -> dict[str, str]:
    """Everything SHA256SUMS.txt in the kit covers, which is everything but itself."""
    listed = dict(KIT_GENERATED)
    listed.update({name: f'{KIT}/{name}' for name in KIT_KEPT})
    listed['paper_b_source_package.zip'] = SOURCE_ARCHIVE
    listed['paper_b_zenodo_package.zip'] = BUNDLE
    return listed


def build(root: Path, archive_only: bool = False) -> None:
    source = {name: payload(root, rel) for name, rel in SOURCE_MEMBERS.items()}
    write_zip(root / SOURCE_ARCHIVE, source)
    print(f'{SOURCE_ARCHIVE}: {len(source) + 1} members')
    if archive_only:
        return

    agree(root)
    bundle = {name: payload(root, rel) for name, rel in BUNDLE_MEMBERS.items()}
    write_zip(root / BUNDLE, bundle)
    print(f'{BUNDLE}: {len(bundle) + 1} members')

    for name, rel in KIT_GENERATED.items():
        shutil.copyfile(root / rel, root / KIT / name)
    digests = {name: sha256((root / KIT / name).read_bytes()) for name in listed_kit_files()}
    (root / KIT / 'SHA256SUMS.txt').write_bytes(checksums(digests))
    print(f'{KIT}/SHA256SUMS.txt: {len(digests)} files')


def agree(root: Path) -> None:
    """The release check must describe the artifacts actually on disk.

    Without this the kit can be rebuilt around a record of some earlier edition,
    which is how it came to carry a source digest eleven manuscript revisions old.
    """
    record = json.loads((root / RELEASE_CHECK).read_text(encoding='utf-8'))
    pdf = root / f'docs/theory/{STEM}.pdf'
    expected = {
        'pdf_sha256': sha256(pdf.read_bytes()),
        'pdf_bytes': pdf.stat().st_size,
        'source_sha256': sha256(payload(root, f'docs/theory/{STEM}.md')),
        'tex_sha256': sha256(payload(root, f'docs/theory/{STEM}.tex')),
        'source_zip_sha256': sha256((root / SOURCE_ARCHIVE).read_bytes()),
    }
    wrong = {k: (record.get(k), v) for k, v in expected.items() if record.get(k) != v}
    if wrong:
        detail = ''.join(f'\n  {k}: records {r}, built {b}' for k, (r, b) in wrong.items())
        raise ValueError(f'{RELEASE_CHECK} describes other artifacts:{detail}')


def check(root: Path) -> None:
    agree(root)
    for target, members in ((SOURCE_ARCHIVE, SOURCE_MEMBERS), (BUNDLE, BUNDLE_MEMBERS)):
        built = {name: payload(root, rel) for name, rel in members.items()}
        stored = zipfile.ZipFile(root / target)
        if set(stored.namelist()) - {'SHA256SUMS.txt'} != set(built):
            raise ValueError(f'Stale {target}: its members are not the current kit; rebuild')
        for name, data in built.items():
            if stored.read(name) != data:
                raise ValueError(f'Stale {target}: {name} differs from the repository; rebuild')
        if stored.read('SHA256SUMS.txt') != checksums({n: sha256(d) for n, d in built.items()}):
            raise ValueError(f'Stale {target}: SHA256SUMS.txt does not match its own members')
    for name, rel in KIT_GENERATED.items():
        if (root / KIT / name).read_bytes() != (root / rel).read_bytes():
            raise ValueError(f'Stale generated copy: {KIT}/{name}; rebuild')
    digests = {name: sha256((root / KIT / name).read_bytes()) for name in listed_kit_files()}
    if (root / KIT / 'SHA256SUMS.txt').read_bytes() != checksums(digests):
        raise ValueError(f'Stale {KIT}/SHA256SUMS.txt; rebuild')
    print('Paper B kit archives, checksums, and release check agree with the repository.')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--archive', action='store_true',
                      help='build only the source archive, for release-check bootstrap')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = HERE.parent
    if args.check:
        check(root)
    else:
        build(root, archive_only=args.archive)


if __name__ == '__main__':
    main()
