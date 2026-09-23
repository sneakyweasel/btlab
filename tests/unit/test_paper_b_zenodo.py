"""The Paper B Zenodo kit must stay a byte-identical export of the canonical PDF."""
import importlib.util
import json
import shutil
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
    (tmp_path / B.ZENODO_FIELDS).parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / B.ZENODO_FIELDS).write_text(B.zenodo_fields(meta), encoding="utf-8")
    B.check_exports(tmp_path)
    (tmp_path / B.ZENODO_PDF).write_bytes(b"old PDF")
    with pytest.raises(ValueError, match="Stale generated copy"):
        B.check_exports(tmp_path)


def _paper_b_tree(dest: Path) -> Path:
    """Copy the release inputs into an isolated tree before testing mutations."""
    names = [B.METADATA, B.BUILD_MANIFEST, B.ZENODO_FIELDS,
             "docs/theory/juggler_parity_discrepancy_note.md",
             "docs/theory/juggler_parity_discrepancy_note.tex",
             "tools/paper_b/article.tex", "tools/paper_b/layout.lua",
             "tools/build_paper_b.py"]
    names += [s for s, _ in B.EXPORTS] + [t for _, t in B.EXPORTS]
    for relative in dict.fromkeys(names):
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    return dest


def test_an_edited_source_is_rejected_even_when_pdf_alias_matches(tmp_path):
    """Matching PDF aliases cannot hide a manuscript change made without rebuilding."""
    tree = _paper_b_tree(tmp_path)
    source = tree / "docs/theory/juggler_parity_discrepancy_note.md"
    manifest = tree / "docs/theory/paper_b_build.json"

    recorded = {r["name"]: r for r in json.loads(manifest.read_text(encoding="utf-8"))["files"]}
    row = recorded["juggler_parity_discrepancy_note.md"]
    assert row["sha256"] == B.digest(source, row["mode"])
    B.check(tree)                                # the copy is sound to begin with

    source.write_bytes(source.read_bytes() + b'\n')
    with pytest.raises(ValueError, match="Stale Paper B build"):
        B.check(tree)


def test_the_build_script_is_itself_a_pinned_input():
    """Editing the builder invalidates the manifest, which is correct: it is an input.

    paper_b_build.json records build_paper_b.py's own digest, so a change to the
    build logic requires a rebuild rather than silently producing a PDF nobody can
    reproduce.  This caught the very patch that added the check above.
    """
    recorded = {r["name"]: r
                for r in json.loads((ROOT / "docs/theory/paper_b_build.json").read_text(encoding="utf-8"))["files"]}
    assert "build_paper_b.py" in recorded
    row = recorded["build_paper_b.py"]
    assert B.digest(ROOT / "tools/build_paper_b.py", row["mode"]) == row["sha256"]


def test_a_text_input_hashes_the_same_through_either_line_ending(tmp_path):
    """The gate must not read a checkout's line endings as an edited manuscript.

    git stores these inputs with LF and hands them to the working tree with whatever
    core.autocrlf says, so a raw-byte digest made the verdict a property of the clone
    rather than of the commit: the Paper B gate passed in the main checkout and failed
    in a worktree of the same revision, naming the manuscript as stale when not one
    character of it had changed.  The PDF stays binary, where a byte really is a byte.
    """
    body = b'line one\nline two\n'
    lf, crlf = tmp_path / "lf.md", tmp_path / "crlf.md"
    lf.write_bytes(body)
    crlf.write_bytes(body.replace(b'\n', b'\r\n'))

    assert lf.read_bytes() != crlf.read_bytes()
    assert B.digest(lf, "text") == B.digest(crlf, "text")
    assert B.digest(lf, "binary") != B.digest(crlf, "binary")
