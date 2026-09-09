"""The Paper B Zenodo kit must stay a byte-identical export of the canonical PDF."""
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("paper_b_build", ROOT / "tools/build_paper_b.py")
B = importlib.util.module_from_spec(spec)
spec.loader.exec_module(B)


def test_current_repository_zenodo_kit_is_synchronized():
    B.check(ROOT)


def test_stale_zenodo_pdf_is_rejected(tmp_path):
    for source, target in B.EXPORTS:
        src = tmp_path / source
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_bytes(b"canonical")
        dest = tmp_path / target
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(b"canonical")
    meta = json.loads((ROOT / B.METADATA).read_text(encoding="utf-8"))
    (tmp_path / B.METADATA).parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / B.METADATA).write_text(json.dumps(meta), encoding="utf-8")
    (tmp_path / B.ZENODO_FIELDS).write_text(B.zenodo_fields(meta), encoding="utf-8")
    B.check(tmp_path)
    (tmp_path / B.ZENODO_PDF).write_bytes(b"old PDF")
    with pytest.raises(ValueError, match="Stale generated copy"):
        B.check(tmp_path)
