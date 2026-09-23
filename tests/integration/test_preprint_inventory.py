"""Preprints are a closed set of current publication artifacts, not source mirrors."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("preprints", ROOT / "tools/preprints.py")
P = importlib.util.module_from_spec(spec)
spec.loader.exec_module(P)


def test_live_preprint_inventory_and_index():
    P.check_inventory(ROOT)


@pytest.fixture
def inventory_tree(tmp_path, monkeypatch):
    expected = {"README.md", "paper.pdf", "zenodo_paper_a/README.md"}
    monkeypatch.setattr(P, "expected_files", lambda root: expected)
    monkeypatch.setattr(P, "index_text", lambda root: "current index\n")
    for name in expected:
        path = tmp_path / "preprints" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("current index\n", encoding="utf-8")
    P.check_inventory(tmp_path)
    return tmp_path


def test_unowned_scratch_file_is_rejected(inventory_tree):
    (inventory_tree / "preprints/old-manuscript.md").write_text("obsolete", encoding="utf-8")
    with pytest.raises(ValueError, match="unowned=.*old-manuscript"):
        P.check_inventory(inventory_tree)


def test_missing_publication_file_is_rejected(inventory_tree):
    (inventory_tree / "preprints/paper.pdf").unlink()
    with pytest.raises(ValueError, match="missing=.*paper.pdf"):
        P.check_inventory(inventory_tree)


def test_stale_index_is_rejected(inventory_tree):
    (inventory_tree / "preprints/README.md").write_text("old version", encoding="utf-8")
    with pytest.raises(ValueError, match="Stale preprint index"):
        P.check_inventory(inventory_tree)


def test_old_directory_is_rejected(inventory_tree):
    (inventory_tree / "juggler_review").mkdir()
    with pytest.raises(ValueError, match="Obsolete juggler_review"):
        P.check_inventory(inventory_tree)
