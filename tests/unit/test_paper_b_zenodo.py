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
    """Copy just the files `B.check` reads into a throwaway root.

    The scenario below has to edit a manuscript, and it used to edit the real one
    under `docs/theory` and put it back in a `finally`.  Between that write and the
    copy to the mirror -- and again between the two restores -- the two trees
    disagree, and `tests/integration/test_review_bundle_mirrors.py` compares exactly
    those two files.  Under `-n auto` that is a race, and it fired as soon as the
    digest fix let this test past its first assertion and into the mutation.  A test
    that pins one gate should not be able to fail a different one.
    """
    names = [B.METADATA, B.BUILD_MANIFEST, B.ZENODO_FIELDS,
             "docs/theory/juggler_parity_discrepancy_note.tex",
             "tools/paper_b/article.tex", "tools/paper_b/layout.lua",
             "tools/build_paper_b.py"]
    names += [s for s, _ in B.EXPORTS] + [t for _, t in B.EXPORTS]
    for relative in dict.fromkeys(names):
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    return dest


def test_an_edited_source_is_rejected_even_when_the_mirror_is_updated_too(tmp_path):
    """The gap that let a Paper B edit ship without rebuilding the PDF.

    `check` compared the EXPORTS pairs -- which are PDF-to-PDF copies plus the .md
    mirror -- and the Zenodo fields, and printed "Paper B source, review copies,
    companion PDF, and Zenodo kit agree".  It never consulted the digests that
    paper_b_build.json already records for the source, the TeX and the PDF.

    So editing docs/theory and copying to juggler_review satisfied every comparison
    the gate made, and the published PDF stayed behind its source.  That is exactly
    how the Theorem 6.1 sharpening shipped unbuilt.  Paper A and Paper C both verify
    their recorded input digests; only Paper B did not.

    This pins the scenario the mirror check cannot see: source and mirror both moved,
    PDF untouched.
    """
    tree = _paper_b_tree(tmp_path)
    source = tree / "docs/theory/juggler_parity_discrepancy_note.md"
    mirror = tree / "juggler_review/juggler_parity_discrepancy_note.md"
    manifest = tree / "docs/theory/paper_b_build.json"

    recorded = {r["name"]: r for r in json.loads(manifest.read_text(encoding="utf-8"))["files"]}
    row = recorded["juggler_parity_discrepancy_note.md"]
    assert row["sha256"] == B.digest(source, row["mode"])
    B.check(tree)                                # the copy is sound to begin with

    source.write_bytes(source.read_bytes() + b'\n')
    shutil.copyfile(source, mirror)              # the mirror check is now satisfied
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
