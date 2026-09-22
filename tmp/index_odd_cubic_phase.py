"""Build the formal index using committed sources and the scoped cubic module."""
import io
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root / 'tools'))
import formalpedia as fp

snapshot = Path(tempfile.mkdtemp(prefix='odd-cubic-index-', dir=root / 'tmp')).resolve()
archive = subprocess.run(
    ['git', '-c', 'safe.directory=' + root.as_posix(), 'archive', '--format=tar', 'HEAD', 'formal'],
    cwd=root, check=True, capture_output=True).stdout
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for member in tar:
        if member.isfile():
            target = (snapshot / member.name).resolve()
            target.relative_to(snapshot)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(tar.extractfile(member).read())
for rel in ('formal/Problems/Juggler.lean', 'formal/Problems/Juggler/OddCubicPhase.lean'):
    target = snapshot / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / rel, target)
fp.ROOT = snapshot
fp.FORMAL = snapshot / 'formal'
fp.LEDGER = root / 'docs/theory/theorem_ledger.json'
index = fp.build()
(root / 'data/research/formalpedia/index.json').write_text(fp.render(index), encoding='utf-8')
print(index['totals'])
