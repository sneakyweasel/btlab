"""Build the repaired Paper B PDF from Markdown using Pandoc and XeLaTeX.

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

HERE = Path(__file__).resolve().parent
STEM = 'juggler_parity_discrepancy_note'
METADATA = 'docs/theory/paper_b_zenodo.json'
PDF = f'docs/theory/{STEM}.pdf'
ZENODO_DIR = 'juggler_review/zenodo_paper_b'
ZENODO_PDF = f'{ZENODO_DIR}/Parity_Statistics_of_Nested_Floor_Powers.pdf'
ZENODO_FIELDS = f'{ZENODO_DIR}/ZENODO_FIELDS.txt'
EXPORTS = [
    (f'docs/theory/{STEM}.md', f'juggler_review/{STEM}.md'),
    (PDF, f'juggler_review/{STEM}.pdf'),
    (PDF, f'web/juggler-companion/public/papers/{STEM}.pdf'),
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
    (root / ZENODO_FIELDS).write_text(fields, encoding='utf-8')


def check(root: Path) -> None:
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
    work = (args.build_dir or output/'.build/paper_b').resolve()
    output.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    text = source.read_text(encoding='utf-8')
    if 'Finite-Step Descent and Conditional Extensions' not in text[:350]:
        raise RuntimeError('Expected the finite-step repair, not an earlier working draft')
    pandoc, xelatex = executable('pandoc',args.pandoc), executable('xelatex',args.xelatex)
    tex = work/f'{STEM}.tex'
    run([pandoc,str(source),'--from=markdown+tex_math_single_backslash+autolink_bare_uris',
         '--to=latex','--standalone','--no-highlight','--ascii',
         '--template',str(assets/'article.tex'),'--lua-filter',str(assets/'layout.lua'),
         '--output',str(tex)], work)
    for i in (1,2):
        run([xelatex,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error',tex.name],
            work,work/f'xelatex-{i}.log')
    log=(work/f'{STEM}.log').read_text(encoding='utf-8',errors='replace')
    for warning in ('Overfull', 'Missing character', 'undefined references'):
        if warning in log:
            raise RuntimeError(f'Layout check failed: {warning}; inspect {work}')
    for suffix in ('.pdf','.tex'):
        shutil.copyfile(work/f'{STEM}{suffix}',output/f'{STEM}{suffix}')
    files=[source,assets/'article.tex',assets/'layout.lua',Path(__file__).resolve(),
           output/f'{STEM}.tex',output/f'{STEM}.pdf']
    records=[{'name':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]
    record={'status':'built; visual review required for any changed build',
            'pandoc':run([pandoc,'--version'],work).decode(errors='replace').splitlines()[0],
            'xelatex':run([xelatex,'--version'],work).decode(errors='replace').splitlines()[0],
            'files':records}
    (output/'paper_b_build.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    if root is not None and output == (root / 'docs/theory'):
        sync(root)
    print(output/f'{STEM}.pdf')


if __name__ == '__main__':
    main()
