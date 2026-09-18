"""Paper B's recorded source digest must name the manuscript, not the checkout."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "docs/theory/juggler_parity_discrepancy_note.md"
RECORD = ROOT / "docs/theory/paper_b_consolidated_validation.json"
spec = importlib.util.spec_from_file_location(
    "validate_paper_b_consolidated", ROOT / "tools/validate_paper_b_consolidated.py")
V = importlib.util.module_from_spec(spec)
spec.loader.exec_module(V)


def test_a_text_input_hashes_the_same_through_either_line_ending(tmp_path):
    """The bug tools/artifact_digest.py exists to prevent, in the consolidated validator.

    source_sha256 was taken from raw bytes.  The repository has no .gitattributes and
    core.autocrlf checks the Markdown out CRLF on Windows and LF elsewhere, so the
    recorded digest named the checkout the recorder happened to have rather than the
    manuscript a reader is asked to verify.  CI, the first non-Windows machine to
    reach Paper C's printed digests, reported the identical problem on 14 September
    2026.
    """
    body = b"# Paper B\n\nOne line, then another.\n"
    lf = tmp_path / "lf.md"
    lf.write_bytes(body)
    crlf = tmp_path / "crlf.md"
    crlf.write_bytes(body.replace(b"\n", b"\r\n"))

    assert V.digest(lf, "text") == V.digest(crlf, "text")
    assert V.digest(lf, "text") == hashlib.sha256(body).hexdigest()
    assert V.digest(lf) != V.digest(crlf), "binary mode must still see the bytes"


def test_the_recorded_digest_describes_the_manuscript_beside_it():
    """A gate able to fail: the record went eleven revisions without being rerun.

    The committed value was 52520173..., which is the CRLF form of the manuscript at
    b4959ea7 (10 September 2026, the Zenodo preprint revision).  The manuscript moved
    eleven times after that -- Theorem 6.1's sharp threshold, Remark 6.2, the FD
    hypothesis -- and nothing noticed, because nothing asserted this file.
    """
    recorded = json.loads(RECORD.read_text(encoding="utf-8"))["source_sha256"]
    assert recorded == V.digest(SOURCE, "text"), (
        "docs/theory/paper_b_consolidated_validation.json describes an older "
        "manuscript; rerun `python tools/validate_paper_b_consolidated.py --output "
        "docs/theory/paper_b_consolidated_validation.json`")
