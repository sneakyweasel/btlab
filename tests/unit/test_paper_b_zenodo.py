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
    B.check_exports(tmp_path)
    (tmp_path / B.ZENODO_PDF).write_bytes(b"old PDF")
    with pytest.raises(ValueError, match="Stale generated copy"):
        B.check_exports(tmp_path)


def test_an_edited_source_is_rejected_even_when_the_mirror_is_updated_too():
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
    import shutil

    source = ROOT / "docs/theory/juggler_parity_discrepancy_note.md"
    mirror = ROOT / "juggler_review/juggler_parity_discrepancy_note.md"
    manifest = ROOT / "docs/theory/paper_b_build.json"

    original = source.read_bytes()
    original_mirror = mirror.read_bytes()
    recorded = {r["name"]: r for r in json.loads(manifest.read_text(encoding="utf-8"))["files"]}
    row = recorded["juggler_parity_discrepancy_note.md"]
    assert row["sha256"] == B.digest(source, row["mode"])

    try:
        source.write_bytes(original + b"\n")
        shutil.copyfile(source, mirror)          # the mirror check is now satisfied
        with pytest.raises(ValueError, match="Stale Paper B build"):
            B.check(ROOT)
    finally:
        source.write_bytes(original)
        mirror.write_bytes(original_mirror)
    B.check(ROOT)                                # and it passes again once restored


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
