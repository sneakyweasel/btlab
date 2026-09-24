"""Paper E must reject stale proofs, changed outputs, and a corrupted supplement."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
spec = importlib.util.spec_from_file_location("paper_e_builder", ROOT / "tools/build_paper_e.py")
paper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(paper)
from check_paper_e import check as check_mathematics


@pytest.fixture
def release(tmp_path):
    paths = set(paper.input_files(ROOT) + paper.OUTPUTS + [paper.MANIFEST, paper.SOURCE_ZIP])
    paths.update(target for _, target in paper.export_pairs(ROOT))
    paths.update(f"{paper.KIT}/{name}" for name in ("ZENODO_FIELDS.txt", "SHA256SUMS.txt"))
    for name in paths:
        target = tmp_path / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
    return tmp_path


def test_current_release_and_archived_sources_agree(release):
    paper.check(release)


@pytest.mark.parametrize("module", [
    "formal/Problems/Collatz/PreimageGrid.lean",
    "formal/Problems/Juggler/PaperECompletion.lean",
    "formal/Problems/Juggler/PaperEModularReturn.lean",
    "formal/Problems/Juggler/PaperERecurrence.lean",
    "formal/Problems/Juggler/PaperECorollaries.lean",
    "formal/BTCalculus/FourierBoxCounting.lean",
    "formal/BTCalculus/HigherDerivative.lean",
    "formal/BTCalculus/FejerBox.lean",
    "formal/Problems/Juggler/OOEEffectiveModes.lean",
    "formal/Problems/Juggler/OOEEffectiveReturn.lean",
    "formal/BTCalculus/PowerBoxCounting.lean",
    "formal/BTCalculus/FourierBoxRecurrence.lean",
    "formal/BTCalculus/PowerPhaseAsymptotics.lean",
])
def test_changed_transitive_proof_requires_new_audit(release, module):
    proof = release / module
    proof.write_text(proof.read_text(encoding="utf-8") + "\n-- changed proof input\n", encoding="utf-8")
    with pytest.raises(ValueError, match="Lean proof inputs changed"):
        check_mathematics(release)
    with pytest.raises(ValueError, match="Stale or missing"):
        paper.check(release)


def test_changed_pdf_cannot_keep_a_green_release(release):
    with (release / paper.PDF).open("ab") as stream:
        stream.write(b"\nchanged")
    with pytest.raises(ValueError, match="Stale or missing"):
        paper.check(release)


def test_corrupted_source_archive_is_rejected(release):
    with (release / paper.SOURCE_ZIP).open("ab") as stream:
        stream.write(b"changed")
    with pytest.raises(ValueError, match="source-and-certificate"):
        paper.check(release)


def test_printed_grid_cannot_drift_from_formal_table(release):
    source = release / paper.SOURCE
    source.write_text(source.read_text(encoding="utf-8").replace("10000 10140 10281", "10000 10141 10281"),
                      encoding="utf-8")
    with pytest.raises(ValueError, match="printed cap table"):
        check_mathematics(release)


def test_rebuild_preserves_external_deposit_facts(tmp_path):
    path = tmp_path / paper.METADATA
    path.parent.mkdir(parents=True)
    previous = {"version": paper.VERSION, "conceptdoi": "test-concept",
                "latest_deposit": {"version": "test", "doi": "test-version"},
                "creators": [{"orcid": paper.ORCID}]}
    path.write_text(json.dumps(previous), encoding="utf-8")
    result = paper.carry_forward(tmp_path, {"creators": [{"name": "Cochin, Philippe"}]})
    assert result["conceptdoi"] == "test-concept"
    assert result["latest_deposit"] == previous["latest_deposit"]
    assert result["creators"][0]["orcid"] == paper.ORCID


def test_the_archive_is_compared_by_members_not_by_deflate_bytes(tmp_path):
    """Regression: zlib builds compress identical members differently; contents decide."""
    import io
    import zipfile

    def archive(level, members):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=level) as z:
            for name, data in members:
                info = zipfile.ZipInfo(name, (2026, 9, 22, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                z.writestr(info, data, compresslevel=level)
        return buffer.getvalue()

    members = [("a.txt", b"alpha\n" * 200), ("b.md", b"beta\n" * 50)]
    expected = archive(9, members)
    found = tmp_path / "found.zip"
    found.write_bytes(archive(1, members))
    assert found.read_bytes() != expected and paper.archive_matches(found, expected)
    found.write_bytes(archive(1, members) + b"changed")
    assert not paper.archive_matches(found, expected)
    found.write_bytes(archive(9, [("a.txt", b"alpha\n" * 200), ("b.md", b"gamma\n")]))
    assert not paper.archive_matches(found, expected)
    found.write_bytes(archive(9, members[::-1]))
    assert not paper.archive_matches(found, expected)
    found.write_bytes(b"not a zip")
    assert not paper.archive_matches(found, expected)
