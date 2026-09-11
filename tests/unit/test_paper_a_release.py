"""A paper build must not silently distribute stale source or PDF copies."""
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("paper_a_build", ROOT / "tools/build_paper_a.py")
B = importlib.util.module_from_spec(spec)
spec.loader.exec_module(B)


@pytest.fixture
def release(tmp_path):
    files = B.EDITORIAL + B.BUILD_INPUTS + ["formal/lean-toolchain",
        "formal/lake-manifest.json", "formal/AxiomCheckPaperA.lean",
        "formal/AxiomCheckPaperA.expected", "formal/Problems/JugglerPaper.lean"]
    for rel in files + B.OUTPUTS:
        p = tmp_path / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("fixture\n", encoding="utf-8")
    meta = {"title": "Paper", "creators": [{"name": "Author"}], "version": "v1",
            "license": "cc-by-4.0", "keywords": [], "description": "Abstract"}
    (tmp_path / B.METADATA).write_text(json.dumps(meta), encoding="utf-8")
    manifest = {"schema": 1, "canonical_source": B.SOURCE,
        "inputs": [{"path": p, "mode": "text", "sha256": B.digest(tmp_path / p, "text")}
                   for p in B.input_files(tmp_path)],
        "outputs": [{"path": p, "mode": "binary", "sha256": B.digest(tmp_path / p)} for p in B.OUTPUTS]}
    (tmp_path / B.MANIFEST).write_text(json.dumps(manifest), encoding="utf-8")
    B.sync(tmp_path)
    return tmp_path


def test_release_and_distribution_agree(release):
    B.check(release)
    target = release / B.PDF_EXPORTS[0]
    target.write_bytes(b"old PDF")
    with pytest.raises(ValueError, match="Stale generated copy"):
        B.check(release)
    B.sync(release)
    B.check(release)


@pytest.mark.parametrize("path", [B.SOURCE, B.PDF, "formal/Problems/JugglerPaper.lean"])
def test_stale_inputs_cannot_be_synced(release, path):
    (release / path).write_bytes(b"changed")
    with pytest.raises(ValueError, match="rebuild required"):
        B.sync(release)


def test_git_line_endings_do_not_stale_a_release(release):
    p = release / B.SOURCE
    p.write_bytes(p.read_text(encoding="utf-8").replace("\n", "\r\n").encode("utf-8"))
    B.check(release)


def test_missing_output_record_is_rejected(release):
    p = release / B.MANIFEST
    data = json.loads(p.read_text())
    data['outputs'] = data['outputs'][:1]
    p.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="Incomplete"):
        B.check(release)


def test_current_repository_release_is_synchronized():
    B.check(ROOT)


def test_release_tracks_the_shared_full_import_closure(tmp_path):
    folder = tmp_path / "formal/Problems"
    folder.mkdir(parents=True)
    (folder / "JugglerPaper.lean").write_text(
        "/- import Problems.Phantom -/\n"
        "  import Problems.One Problems.Two -- Problems.Unused\n", encoding="utf-8")
    (folder / "One.lean").write_text("import Problems.Three\n", encoding="utf-8")
    for name in ("Two", "Three"):
        (folder / f"{name}.lean").write_text("-- no imports\n", encoding="utf-8")
    inputs = set(B.input_files(tmp_path))
    assert {name for name in inputs if name.startswith("formal/Problems/")} == {
        "formal/Problems/JugglerPaper.lean", "formal/Problems/One.lean",
        "formal/Problems/Two.lean", "formal/Problems/Three.lean"}
    assert "tools/trust_boundary.py" in inputs
