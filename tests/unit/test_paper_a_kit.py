"""The public supplement is deterministic and rejects stale or unlisted bytes."""
import importlib.util
from pathlib import Path
import zipfile

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('paper_a_kit_test', ROOT / 'tools/build_paper_a_kit.py')
K = importlib.util.module_from_spec(spec)
spec.loader.exec_module(K)


def test_source_supplement_and_delivery_match_current_repository():
    K.check(ROOT)


def test_archive_is_reproducible_and_rejects_extra_or_stale_members(tmp_path):
    one, two = tmp_path / 'one.zip', tmp_path / 'two.zip'
    body = {'a.txt': b'public source\n', 'b.txt': b'verification\n'}
    K.write_zip(one, body)
    K.write_zip(two, dict(reversed(list(body.items()))))
    assert one.read_bytes() == two.read_bytes()
    K.check_zip(one, body)
    with pytest.raises(ValueError, match='Stale archive member'):
        K.check_zip(one, {**body, 'a.txt': b'changed\n'})
    with zipfile.ZipFile(one, 'a') as z:
        z.writestr('unlisted-private-file.txt', b'not part of the public inventory')
    with pytest.raises(ValueError, match='inventory'):
        K.check_zip(one, body)
