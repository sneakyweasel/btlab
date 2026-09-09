"""Build the conditional Paper B PDF from Markdown using Pandoc and XeLaTeX.

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
    args = parser.parse_args()
    source, assets = args.source.resolve(), args.assets.resolve()
    output = (args.output_dir or source.parent).resolve()
    work = (args.build_dir or output/'.build/paper_b').resolve()
    output.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    text = source.read_text(encoding='utf-8')
    if 'Conditional Descent Results' not in text[:350]:
        raise RuntimeError('Expected the conditional revision, not the historical working draft')
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
    print(output/f'{STEM}.pdf')


if __name__ == '__main__':
    main()
