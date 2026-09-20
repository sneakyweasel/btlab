"""Build the Five-Step Descent Certificates preprint PDF from Markdown using Pandoc and XeLaTeX.

Standalone package: python build_paper_b.py
Repository: python tools/build_paper_b.py
The build does not publish anything and does not certify analytic hypotheses.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


# Reproducible output.  XeLaTeX stamps a build time into the PDF's compressed metadata, so
# without this a no-op rebuild changes the bytes and therefore the sha256 in the manifest.
# The epoch is fixed to the version this guide records rather than taken from git, because a
# git-derived date lags one build behind an edit and merely relocates the churn.
_SOURCE_DATE_EPOCH = "1789862400"  # Paper B version 2026-09-20-preprint


def _pin_build_date() -> None:
    """Pin SOURCE_DATE_EPOCH unless the caller already set one."""
    os.environ.setdefault("SOURCE_DATE_EPOCH", _SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")

HERE = Path(__file__).resolve().parent
STEM = 'juggler_parity_discrepancy_note'
METADATA = 'docs/theory/paper_b_zenodo.json'
BUILD_MANIFEST = 'docs/theory/paper_b_build.json'
PDF = f'juggler_review/{STEM}.pdf'
ZENODO_DIR = 'juggler_review/zenodo_paper_b'
ZENODO_PDF = f'{ZENODO_DIR}/Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf'
ZENODO_FIELDS = f'{ZENODO_DIR}/ZENODO_FIELDS.txt'
# The PDF is written straight into juggler_review/ now, so the only export
# left is the historical name the Zenodo deposit carries. The companion site
# links the published DOI instead of serving a copy.
EXPORTS = [
    (f'docs/theory/{STEM}.md', f'juggler_review/{STEM}.md'),
    (PDF, ZENODO_PDF),
]


def repo_root() -> Path | None:
    root = HERE.parent
    if (root / METADATA).is_file():
        return root
    return None


def zenodo_fields(meta: dict) -> str:
    row = meta.get('metadata', meta)
    return (
        'GENERATED FROM docs/theory/; do not edit this export.\n'
        'Prepared metadata only; no external record has been created.\n\n'
        f"TITLE\n{row['title']}\n\nCREATOR\n{row['creators'][0]['name']}\n"
        'Affiliation: none\n\nRESOURCE TYPE\nPublication / Preprint\n\n'
        f"VERSION\n{row['version']}\n\nLICENSE\n{row['license']}\n\n"
        'PUBLICATION DATE\nUse the actual date this version is first made public.\n\n'
        'KEYWORDS\n' + '\n'.join(row['keywords']) + '\n\nDESCRIPTION (HTML)\n'
        + row['description'] + '\n\nRELATED SOFTWARE\nhttps://github.com/sneakyweasel/btlab\n'
    )


def sync(root: Path) -> None:
    for source, target in EXPORTS:
        dest = root / target
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / source, dest)
    fields = zenodo_fields(json.loads((root / METADATA).read_text(encoding='utf-8')))
    # newline='' writes the LF this string already holds. Without it Python's text
    # mode emits CRLF on Windows, and build_paper_b_kit.py checksums this file's RAW
    # bytes, so the kit's SHA256SUMS became a property of the packager's platform.
    (root / ZENODO_FIELDS).write_text(fields, encoding='utf-8', newline='')


def digest(path: Path, mode: str = 'binary') -> str:
    """Hash a build input the way Paper A and Paper C hash theirs.

    The manifest pins files git stores with LF and checks out with the platform's
    line ending, so hashing raw bytes made this gate's verdict depend on core.autocrlf:
    one and the same commit passed on a checkout that happened to hold LF and failed on
    a checkout that held CRLF.  Text inputs are hashed line-ending normalised; the PDF
    stays binary, where every byte is meant to count.
    """
    data = path.read_bytes()
    if mode == 'text':
        data = data.replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return hashlib.sha256(data).hexdigest()


def check(root: Path) -> None:
    check_exports(root)
    check_manifest(root)


def check_manifest(root: Path) -> None:
    """Verify the digests paper_b_build.json already records.

    Without this `check` compared only the EXPORTS pairs and the Zenodo fields, so
    editing the source and copying it to the mirror satisfied everything the gate
    looked at while the PDF stayed behind. Paper A and Paper C both verify their
    recorded inputs; this brings Paper B into line.
    """
    manifest = json.loads((root / BUILD_MANIFEST).read_text(encoding='utf-8'))
    # `juggler_review` joins the search because the PDF lives there now; the .tex
    # and the manifest stay in docs/theory. Names carry their extension, so the
    # two trees cannot shadow each other.
    places = (root/'docs/theory', root/'juggler_review', root/'tools/paper_b',
              root/'tools/build', root/'tools')
    for record in manifest.get('files', ()):
        built = next((d/record['name'] for d in places if (d/record['name']).is_file()), None)
        if built is None:
            raise ValueError(f'Missing Paper B build input: {record["name"]}; rebuild')
        if digest(built, record['mode']) != record['sha256']:
            raise ValueError(
                f'Stale Paper B build: {record["name"]} differs from the digest in '
                f'{BUILD_MANIFEST}; rebuild with `python tools/build_paper_b.py`')


def check_exports(root: Path) -> None:
    for source, target in EXPORTS:
        src, dest = root / source, root / target
        if not dest.is_file() or src.read_bytes() != dest.read_bytes():
            raise ValueError(f'Stale generated copy: {target}; run --sync')
    fields = (root / ZENODO_FIELDS).read_text(encoding='utf-8')
    expected = zenodo_fields(json.loads((root / METADATA).read_text(encoding='utf-8')))
    if fields != expected:
        raise ValueError('Stale Zenodo fields; run --sync')


def run(command: list[str], cwd: Path, log: Path | None = None) -> bytes:
    result = subprocess.run(command, cwd=cwd, capture_output=True)
    if log:
        log.write_bytes(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError((result.stdout + result.stderr).decode('utf-8', errors='replace')[-5000:])
    return result.stdout


def executable(name: str, supplied: str | None) -> str:
    candidate = supplied or shutil.which(name)
    if candidate:
        return candidate
    if os.name == 'nt':
        if name == 'pandoc':
            p = Path(os.environ.get('PROGRAMFILES', 'C:/Program Files'))/'Pandoc/pandoc.exe'
        else:
            p = Path(os.environ.get('LOCALAPPDATA', ''))/'Programs/MiKTeX/miktex/bin/x64/xelatex.exe'
        if p.is_file():
            return str(p)
    raise RuntimeError(f'{name} not found; install it or pass --{name}')


def main() -> None:
    _pin_build_date()
    local = HERE/f'{STEM}.md'
    default_source = local if local.exists() else HERE.parent/'docs/theory'/f'{STEM}.md'
    default_assets = HERE/'build' if (HERE/'build/article.tex').exists() else HERE/'paper_b'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=default_source)
    parser.add_argument('--assets', type=Path, default=default_assets)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--build-dir', type=Path)
    parser.add_argument('--pandoc')
    parser.add_argument('--xelatex')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--sync', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = repo_root()
    if args.sync or args.check:
        if root is None:
            raise RuntimeError('Repository Paper B metadata not found')
        if args.check:
            check(root)
            print('Paper B source, review copies, companion PDF, and Zenodo kit agree.')
        else:
            sync(root)
            check(root)
            print('Synchronized Paper B review copies and Zenodo kit.')
        return
    source, assets = args.source.resolve(), args.assets.resolve()
    output = (args.output_dir or source.parent).resolve()
    # `root` is None in an extracted source package, which is the one place
    # PAPER_B_BUILD.md tells a reviewer to run this; fall back to the output tree.
    work = (args.build_dir or (root or output)/'.build/paper_b').resolve()
    output.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    text = source.read_text(encoding='utf-8')
    if 'Five-Step Descent Certificates for the Juggler Map' not in text[:350] or 'Parity Statistics of Nested Floor Powers' not in text[:350]:
        raise RuntimeError('Expected the current Five-Step Descent Certificates manuscript')
    pandoc, xelatex = executable('pandoc',args.pandoc), executable('xelatex',args.xelatex)
    tex = work/f'{STEM}.tex'
    run([pandoc,str(source),'--from=markdown+tex_math_single_backslash+autolink_bare_uris',
         '--to=latex','--standalone','--no-highlight','--ascii',
         '--template',str(assets/'article.tex'),'--lua-filter',str(assets/'layout.lua'),
         '--output',str(tex)], work)
    for i in (1,2):
        run([xelatex,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error',tex.name],
            work,work/f'xelatex-pass-{i}.txt')
    log=(work/f'{STEM}.log').read_text(encoding='utf-8',errors='replace')
    for warning in ('Overfull', 'Missing character', 'undefined references'):
        if warning in log:
            raise RuntimeError(f'Layout check failed: {warning}; inspect {work}')
    # The .tex stays beside the manuscript it was generated from; the PDF has
    # exactly one home now, juggler_review/, so it is written there instead of
    # into docs/theory and copied out afterwards.
    shutil.copyfile(work/f'{STEM}.tex',output/f'{STEM}.tex')
    pdf_out=(root/PDF) if root is not None else output/f'{STEM}.pdf'
    pdf_out.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(work/f'{STEM}.pdf',pdf_out)
    files=[source,assets/'article.tex',assets/'layout.lua',Path(__file__).resolve(),
           output/f'{STEM}.tex',pdf_out]
    modes=['text','text','text','text','text','binary']
    records=[{'name':p.name,'mode':m,'sha256':digest(p,m)} for p,m in zip(files,modes)]
    record={'status':'built; visual review required for any changed build',
            'pandoc':run([pandoc,'--version'],work).decode(errors='replace').splitlines()[0],
            'xelatex':run([xelatex,'--version'],work).decode(errors='replace').splitlines()[0],
            'files':records}
    (output/'paper_b_build.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    if root is not None and output == (root / 'docs/theory'):
        sync(root)
    print(pdf_out)


if __name__ == '__main__':
    main()
