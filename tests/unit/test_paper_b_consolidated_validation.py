"""Paper B's consolidated record must name the manuscript beside it: digest and edition."""
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "docs/theory/juggler_parity_discrepancy_note.md"
RECORD = ROOT / "docs/theory/paper_b_consolidated_validation.json"
RELEASE = ROOT / "docs/theory/paper_b_release_check.json"
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


def test_the_recorded_edition_is_the_manuscript_edition_not_the_deposit_version():
    """The other half of the same bug: a live digest under a pinned label.

    "version" was the literal "2026-09-19-preprint" from the day it was written.  The
    manuscript moved to 20 September and source_sha256 moved with it, but the label
    beside it did not, so the record dated its own subject a day early and shipped
    that inside the Paper B source archive.

    The stamp means the EDITION, what paper_b_release_check.json calls "version".  It
    does not mean the Zenodo RECORD version, which went 1.0.0 to 1.0.1 on 21 September
    over a manuscript that had not changed at all; conflating the two is what produced
    the original mess, so the ambiguous key name must stay gone.
    """
    recorded = json.loads(RECORD.read_text(encoding="utf-8"))
    release = json.loads(RELEASE.read_text(encoding="utf-8"))
    assert "version" not in recorded, (
        "the ambiguous key is back; this record stamps an edition, and the field that "
        "carries it is source_edition")
    assert recorded["source_edition"] == V.edition(SOURCE.read_text(encoding="utf-8")), (
        "docs/theory/paper_b_consolidated_validation.json names an edition the "
        "manuscript does not; rerun `python tools/validate_paper_b_consolidated.py "
        "--output docs/theory/paper_b_consolidated_validation.json`")
    assert recorded["source_edition"] == release["source_edition"], (
        "the consolidated record and the release check name different editions")
    assert release["version"] != release["source_edition"], (
        "the release check is conflating its record version with its source edition; "
        "they are different quantities and the ORCID commit proved it")


def test_the_edition_stamp_is_read_from_the_front_matter():
    """A gate able to fail: nothing here could have caught the literal.

    Both directions.  A manuscript dated differently must produce a different stamp,
    and front matter carrying no usable date must not quietly produce one anyway --
    a silent fallback would reintroduce a label that outlives its source.
    """
    head = "---\ntitle: t\ndate: 20 September 2026\n---\n\n## Abstract\n"
    assert V.edition(head) == "2026-09-20-preprint"
    assert V.edition(head.replace("20 September 2026", "9 March 2027")) == "2027-03-09-preprint"
    for broken in (head.replace("date: 20 September 2026", "date: 2026-09-20"),
                   head.replace("20 September", "20 Septembre"),
                   head.replace("date: 20 September 2026", "author: P"),
                   "## Abstract with no front matter\n"):
        with pytest.raises(AssertionError):
            V.edition(broken)


def test_the_record_is_written_lf_on_every_platform(tmp_path):
    """Path.write_text defaults to newline=None, which is os.linesep.

    Regenerating on Windows therefore wrote CRLF into a file that .gitattributes pins
    eol=lf and that the paper builder ships as a source archive member.  The record
    should be a function of the manuscript, not of the machine that reran the controls.
    """
    out = tmp_path / "record.json"
    out.write_text('{\n  "status": "PASS"\n}\n', encoding="utf-8", newline="\n")
    assert b"\r" not in out.read_bytes()
    assert b"\r" not in RECORD.read_bytes(), (
        "docs/theory/paper_b_consolidated_validation.json holds CR; rewrite it LF")
