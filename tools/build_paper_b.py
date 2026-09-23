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
_SOURCE_DATE_EPOCH = "1790121600"  # Local revision, 23 September 2026


def _pin_build_date() -> None:
    """Pin SOURCE_DATE_EPOCH unless the caller already set one."""
    os.environ.setdefault("SOURCE_DATE_EPOCH", _SOURCE_DATE_EPOCH)
    os.environ.setdefault("FORCE_SOURCE_DATE", "1")

HERE = Path(__file__).resolve().parent
STEM = 'juggler_parity_discrepancy_note'
METADATA = 'docs/theory/paper_b_zenodo.json'
BUILD_MANIFEST = 'docs/theory/paper_b_build.json'
PDF = f'preprints/{STEM}.pdf'
ZENODO_DIR = 'preprints/zenodo_paper_b'
ZENODO_PDF = f'{ZENODO_DIR}/Five_Step_Descent_Certificates_for_the_Juggler_Map.pdf'
ZENODO_FIELDS = f'{ZENODO_DIR}/ZENODO_FIELDS.txt'
# The PDF is written straight into preprints/ now, so the only export
# left is the historical name the Zenodo deposit carries. The companion site
# links the published DOI instead of serving a copy.
EXPORTS = [
    (PDF, ZENODO_PDF),
]


def repo_root() -> Path | None:
    root = HERE.parent
    if (root / METADATA).is_file():
        return root
    return None


def zenodo_fields(meta: dict) -> str:
    """Render the upload form fields from the prepared metadata.

    Three states, because two were never enough. A row naming its own `doi` describes
    a version that is deposited. A row with no `doi` but a `conceptdoi` describes a
    revision prepared on top of a record that already exists -- the state every paper
    here is normally in, and the one the old binary printed as "no external record has
    been created", underneath four published DOIs. A row with neither is a kit prepared
    before any upload. Nothing is asserted that the metadata does not carry.
    """
    row = meta.get('metadata', meta)
    doi, published = row.get('doi'), row.get('publication_date')
    concept, latest = row.get('conceptdoi'), row.get('latest_deposit') or {}
    if doi:
        standing = (f'Describes the deposit at doi:{doi}; this build does not upload '
                    f'a new version.\n\n')
    elif concept:
        standing = (
            f'Version {row["version"]} is prepared and is not deposited. The record '
            f'exists: concept doi:{concept} resolves to the latest version, which is '
            f'{latest.get("version", "unknown")} at doi:{latest.get("doi", "unknown")} '
            f'of {latest.get("publication_date", "unknown")}. A new version goes up '
            f'through the new-version operation of that record, which keeps the '
            f'concept DOI.\n\n')
    else:
        standing = 'Prepared metadata only; no external record has been created.\n\n'
    date_field = (f'PUBLICATION DATE\n{published}\n\n' if published else
                  'PUBLICATION DATE\nUse the actual date this version is first made '
                  'public.\n\n')
    who = row['creators'][0]
    orcid = (f'ORCID: {who["orcid"]} (https://orcid.org/{who["orcid"]})\n'
             if who.get('orcid') else '')
    record = f'RECORD\n{row["record_url"]}\n\n' if row.get('record_url') else ''
    related = '\n'.join(f'{r["relation"]}: {r["identifier"]}'
                        for r in row.get('related_identifiers', ()))
    return (
        'GENERATED FROM docs/theory/; do not edit this export.\n'
        + standing
        + f'TITLE\n{row["title"]}\n\nCREATOR\n{who["name"]}\n' + orcid
        + 'Affiliation: none\n\nRESOURCE TYPE\nPublication / Preprint\n\n'
        + f'VERSION\n{row["version"]}\n\nLICENSE\n{row["license"]}\n\n'
        + record + date_field
        + 'KEYWORDS\n' + '\n'.join(row['keywords']) + '\n\nDESCRIPTION (HTML)\n'
        + row['description'] + '\n\nRELATED WORKS\n' + related + '\n')

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
    # `preprints` joins the search because the PDF lives there now; the .tex
    # and the manifest stay in docs/theory. Names carry their extension, so the
    # two trees cannot shadow each other.
    places = (root/'docs/theory', root/'preprints', root/'tools/paper_b',
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
        # xelatex emits CRLF on Windows and these logs are tracked, so the
        # committed copy flipped convention on every Windows build. Written as
        # raw bytes, they never pass through the newline='' that covers the
        # other generated text.
        captured = result.stdout + result.stderr
        log.write_bytes(captured.replace(bytes([13, 10]), bytes([10]))
                        .replace(bytes([13]), bytes([10])))
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
            print('Paper B source, PDF and Zenodo exports agree.')
        else:
            sync(root)
            check(root)
            print('Synchronized Paper B PDF alias and Zenodo metadata.')
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
    # Pandoc writes this file itself, so the newline='' that keeps every other
    # generated text artifact LF never reaches it: on Windows the .tex came out CRLF
    # and the committed copy flipped convention on every Windows build. The digests
    # normalise line endings and so could not see it. Normalise the bytes instead.
    tex.write_bytes(tex.read_bytes().replace(bytes([13, 10]), bytes([10])).replace(bytes([13]), bytes([10])))
    for i in (1,2):
        run([xelatex,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error',tex.name],
            work,work/f'xelatex-pass-{i}.txt')
    log=(work/f'{STEM}.log').read_text(encoding='utf-8',errors='replace')
    for warning in ('Overfull', 'Missing character', 'undefined references'):
        if warning in log:
            raise RuntimeError(f'Layout check failed: {warning}; inspect {work}')
    # The .tex stays beside the manuscript it was generated from; the PDF has
    # exactly one home now, preprints/, so it is written there instead of
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
    (output/'paper_b_build.json').write_text(json.dumps(record,indent=2)+'\n', encoding="utf-8", newline="")
    if root is not None and output == (root / 'docs/theory'):
        sync(root)
    print(pdf_out)


if __name__ == '__main__':
    main()
