"""A history alias preserves, rather than bypasses, paper provenance checks."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

SPEC = importlib.util.spec_from_file_location(
    "paper_pin_history", Path(__file__).resolve().parents[2] / "tools/paper_pin.py",
)
pin = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pin)


def mapping(root, entries):
    path = root / pin.HISTORY_MAP
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"schema_version": 1, "commits": entries}), encoding="utf-8")


def test_full_and_short_aliases_and_unchanged_history(tmp_path):
    old, new = "1" * 40, "2" * 40
    mapping(tmp_path, {old: new})
    assert pin.resolve_revision(tmp_path, old) == new
    assert pin.resolve_revision(tmp_path, old[:8]) == new
    assert pin.resolve_revision(tmp_path, "3" * 40) == "3" * 40


def test_ambiguous_and_deleted_targets_fail_closed(tmp_path):
    mapping(tmp_path, {"a" * 40: "1" * 40, "a" * 39 + "b": "2" * 40})
    with pytest.raises(ValueError, match="ambiguous"):
        pin.resolve_revision(tmp_path, "a" * 8)
    mapping(tmp_path, {"a" * 40: "0" * 40})
    with pytest.raises(ValueError, match="invalid replacement"):
        pin.resolve_revision(tmp_path, "a" * 40)


def test_alias_still_checks_actual_input_bytes(tmp_path, monkeypatch):
    old, new = "1" * 40, "2" * 40
    mapping(tmp_path, {old: new})
    (tmp_path / "paper.md").write_text(
        f"Repository: https://example.invalid/repo\nCommit: {old}\n", encoding="utf-8",
    )
    (tmp_path / "data.txt").write_text("correct data\n", encoding="utf-8")
    builder = SimpleNamespace(SOURCE="paper.md", EDITORIAL=["paper.md"],
                              input_files=lambda root: ["paper.md", "data.txt"])

    def git(root, *args):
        if args[0] == "rev-parse":
            assert args[-1] == new + "^{commit}"
            return SimpleNamespace(returncode=0, stdout=new + "\n")
        assert args == ("merge-base", "--is-ancestor", new, "HEAD")
        return SimpleNamespace(returncode=0, stdout="")

    def blobs(root, commit, paths):
        assert commit == new
        assert paths == ["data.txt"]
        return {"data.txt": b"correct data\n"}

    monkeypatch.setattr(pin, "_shallow", lambda root: False)
    monkeypatch.setattr(pin, "_git", git)
    monkeypatch.setattr(pin, "_blobs", blobs)
    assert "printed pre-cleanup ID" in pin.verify(tmp_path, builder)
    (tmp_path / "data.txt").write_text("different data\n", encoding="utf-8")
    with pytest.raises(ValueError, match="differs"):
        pin.verify(tmp_path, builder)
