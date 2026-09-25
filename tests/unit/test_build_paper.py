"""The one paper builder: every release and kit is checked the same way for every paper."""
from __future__ import annotations

import io
from pathlib import Path
import shutil
import sys
import zipfile

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import build_paper  # noqa: E402
from build_paper import Paper, letters  # noqa: E402

LETTERS = letters(ROOT)


def copy_release(letter: str, target: Path) -> Paper:
    """A throwaway copy of one paper's release and kit, so failures can be provoked safely."""
    paper = Paper(letter, ROOT)
    names = set(paper.archive_members(ROOT) + paper.kit_files() + [paper.config_path, build_paper.BUILDER])
    for name in names:
        if (ROOT / name).is_file():
            (target / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target / name)
    return Paper(letter, target)


@pytest.mark.parametrize("letter", LETTERS)
def test_release_and_kit_agree_in_a_copy(letter, tmp_path):
    copy_release(letter, tmp_path).check(tmp_path)


@pytest.mark.parametrize("letter", LETTERS)
def test_a_changed_input_stales_the_release(letter, tmp_path):
    paper = copy_release(letter, tmp_path)
    name = next(p for p in paper.input_files(tmp_path)
                if p not in paper.EDITORIAL and build_paper.mode_of(p) == "text"
                and p != paper.config_path)
    with (tmp_path / name).open("a", encoding="utf-8") as stream:
        stream.write("\n% changed input\n")
    with pytest.raises(ValueError, match="Stale or missing"):
        paper.check(tmp_path)


def test_an_edited_manuscript_stales_the_release(tmp_path):
    paper = copy_release("b", tmp_path)
    source = tmp_path / paper.SOURCE
    source.write_text(source.read_text(encoding="utf-8") + "\nOne more sentence.\n", encoding="utf-8")
    with pytest.raises(ValueError, match="Stale or missing"):
        paper.check(tmp_path)


def test_line_endings_do_not_stale_a_release(tmp_path):
    paper = copy_release("d", tmp_path)
    source = tmp_path / paper.SOURCE
    source.write_bytes(source.read_bytes().replace(b"\n", b"\r\n"))
    paper.check_release(tmp_path)


def test_a_changed_pdf_cannot_keep_a_green_release(tmp_path):
    paper = copy_release("d", tmp_path)
    with (tmp_path / paper.PDF).open("ab") as stream:
        stream.write(b"\nchanged")
    with pytest.raises(ValueError, match="Stale or missing"):
        paper.check(tmp_path)


def test_a_corrupted_or_missing_kit_file_is_rejected(tmp_path):
    paper = copy_release("d", tmp_path)
    with (tmp_path / paper.ARCHIVE).open("ab") as stream:
        stream.write(b"changed")
    with pytest.raises(ValueError, match="Stale source archive"):
        paper.check(tmp_path)
    paper.sync(tmp_path)
    (tmp_path / paper.DEPOSIT_PDF).unlink()
    with pytest.raises(ValueError, match="kit PDF"):
        paper.check(tmp_path)


def test_the_version_must_agree_everywhere(tmp_path):
    paper = copy_release("c", tmp_path)
    paper.version = "9.9.9"
    with pytest.raises(ValueError, match="version 9.9.9 differs"):
        paper.check_release(tmp_path)


@pytest.mark.parametrize("letter", LETTERS)
def test_the_archive_carries_its_release_and_a_readme(letter):
    paper = Paper(letter, ROOT)
    with zipfile.ZipFile(ROOT / paper.ARCHIVE) as z:
        names = set(z.namelist())
        readme = z.read("README.md").decode("utf-8")
    assert {paper.SOURCE, paper.PDF, paper.MANIFEST, paper.METADATA, "SHA256SUMS.txt"} <= names
    assert f"python tools/build_paper.py {letter.upper()} --check-release" in readme


def test_an_extracted_archive_passes_its_release_check(tmp_path):
    paper = Paper("d", ROOT)
    with zipfile.ZipFile(ROOT / paper.ARCHIVE) as z:
        z.extractall(tmp_path)
    Paper("d", tmp_path).check_release(tmp_path)


@pytest.mark.parametrize("letter", LETTERS)
def test_the_field_sheet_is_plain_text_and_shaped_like_the_form(letter):
    text = (ROOT / Paper(letter, ROOT).FIELDS).read_text(encoding="utf-8")
    description = text.split("DESCRIPTION (plain text)\n", 1)[1].split("\n\nRELATED WORKS", 1)[0]
    assert "<" not in description and "&" not in description.replace("& ", "")
    assert "Large language models" not in text and "AI assistance" not in text
    assert "Relation: Is supplement to\nIdentifier: https://github.com/sneakyweasel/btlab\n" \
           "Scheme: URL\nResource type: Software" in text


def test_a_prepared_version_is_not_described_as_deposited():
    paper = Paper("e", ROOT)
    meta = {"title": "T", "creators": [{"name": "Cochin, Philippe"}], "version": "2.0.0",
            "license": "cc-by-4.0", "keywords": ["k"], "description": "<p>A &gt; b.</p>",
            "doi": "10.5281/zenodo.1", "conceptdoi": "10.5281/zenodo.0",
            "latest_deposit": {"version": "1.0.0", "doi": "10.5281/zenodo.1"},
            "related_identifiers": []}
    sheet = paper.fields(meta)
    assert "Version 2.0.0 is prepared and is not deposited" in sheet
    assert "Use the actual date" in sheet and "A > b." in sheet


def test_rebuild_preserves_external_deposit_facts():
    old = {"metadata": {"conceptdoi": "c", "latest_deposit": {"version": "1"}, "doi": "d",
                        "keywords": ["stale"]}}
    new = build_paper.carry({"keywords": ["fresh"], "version": "2"}, old)
    assert new["conceptdoi"] == "c" and new["doi"] == "d" and new["latest_deposit"] == {"version": "1"}
    assert new["keywords"] == ["fresh"] and new["version"] == "2"


def test_the_archive_is_compared_by_members_not_by_deflate_bytes(tmp_path):
    """zlib builds compress identical members differently; contents decide."""
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
    assert found.read_bytes() != expected and build_paper.archive_matches(found, expected)
    for bad in (archive(1, members) + b"changed", archive(9, [members[0], ("b.md", b"gamma\n")]),
                archive(9, members[::-1]), archive(9, members + [("extra", b"x")]), b"not a zip"):
        found.write_bytes(bad)
        assert not build_paper.archive_matches(found, expected)
