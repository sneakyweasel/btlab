from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from zipfile import ZipFile

root = Path(__file__).resolve().parents[1]
kit = root / 'juggler_review/zenodo_paper_e'
archive = kit / 'Sources_and_certificate.zip'
destination = Path(tempfile.mkdtemp(prefix='archive-qa-', dir=root / '.build/paper_e'))
with ZipFile(archive) as source:
    for entry in source.infolist():
        assert (destination / entry.filename).resolve().is_relative_to(destination.resolve())
    source.extractall(destination)
for script, arguments in [('check_paper_e.py', []), ('generate_signed_grid_certificate.py', ['--check'])]:
    environment = dict(os.environ, PYTHONPATH=str(destination / 'src'))
    subprocess.run([sys.executable, '-S', str(destination / 'tools' / script), *arguments],
                   cwd=destination, env=environment, check=True)
print('Archived sources independently reproduce the exact finite checks.')
paths = ['juggler_review/juggler_signed_collatz_note.pdf',
         'docs/theory/cochin-juggler-signed-collatz.tex',
         'docs/theory/paper_e_zenodo.json', 'docs/theory/paper_e_release.json',
         'juggler_review/zenodo_paper_e/Sources_and_certificate.zip']
hashes = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in paths}
(root / '.build/paper_e/pre-rebuild-sha256.json').write_text(json.dumps(hashes, indent=2), encoding='utf-8')
