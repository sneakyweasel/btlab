"""Shared Lean build cache: configuration, key handling and download safety, without network."""
from __future__ import annotations

import io
import os
from pathlib import Path
import subprocess
import sys
import tarfile

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import lean_cache  # noqa: E402

GOOD = """
[[cache.service]]
name = "btlab"
kind = "s3"
artifactEndpoint = "https://weasel-lean-cache.s3.us-east-1.amazonaws.com/lean/a0"
revisionEndpoint = "https://weasel-lean-cache.s3.us-east-1.amazonaws.com/lean/r0"
"""


def write(tmp_path: Path, text: str) -> Path:
    path = tmp_path / "lake-cache.toml"
    path.write_text(text, encoding="utf-8")
    return path


def test_committed_config_is_valid_and_public_prefix_only() -> None:
    service = lean_cache.load_service()
    assert lean_cache.public_base(service).endswith("/lean")
    assert lean_cache.region(service) == "us-east-1"
    assert lean_cache.snapshot_url(service, "abc").endswith("/lean/formalpedia/abc.tgz")


@pytest.mark.parametrize("bad", [
    GOOD.replace("/lean/a0", "/a0"),                         # outside the public prefix
    GOOD.replace("https://weasel", "http://weasel"),          # not https
    GOOD.replace("/lean/r0", "/lean/other/r0"),               # endpoints on different bases
    GOOD.replace('kind = "s3"', 'kind = "reservoir"'),
    GOOD.replace('name = "btlab"', 'name = "other"'),
    GOOD + GOOD,                                              # ambiguous: two services
])
def test_bad_configs_are_refused(tmp_path: Path, bad: str) -> None:
    with pytest.raises(ValueError):
        lean_cache.load_service(write(tmp_path, bad))


def test_region_requires_an_aws_virtual_host() -> None:
    with pytest.raises(ValueError):
        lean_cache.region({"artifactEndpoint": "https://example.r2.cloudflarestorage.com/lean/a0"})


@pytest.mark.parametrize("key", [None, "", "no-colon", "a:b:c", ":secret", "id:", " : ",
                                 "AKIA : secret", "\"AKIA:secret\"", "AKIA:sec ret", "AKIA:secret\nextra",
                                 "AK/IA:secret"])
def test_malformed_keys_are_refused(key) -> None:
    with pytest.raises(ValueError):
        lean_cache.parse_key(key)


def test_well_formed_key_splits() -> None:
    assert lean_cache.parse_key("AKIAEXAMPLE:secret/with+chars") == ("AKIAEXAMPLE", "secret/with+chars")


def test_publish_refuses_without_a_key_before_building(monkeypatch) -> None:
    monkeypatch.delenv("LAKE_CACHE_KEY", raising=False)
    monkeypatch.setattr(lean_cache.subprocess, "run", lambda *a, **k: pytest.fail("no subprocess may run"))
    with pytest.raises(ValueError, match="LAKE_CACHE_KEY"):
        lean_cache.publish()


def test_lake_env_selects_config_and_local_cache() -> None:
    env = lean_cache.lake_env({"PATH": "x"})
    assert env["LAKE_CONFIG"] == str(lean_cache.CONFIG)
    assert env["LAKE_ARTIFACT_CACHE"] == "true"
    assert env["LAKE_RESTORE_ARTIFACTS"] == "true"
    assert "LAKE_CACHE_KEY" not in env


def test_first_available_takes_the_newest_published_revision() -> None:
    published = {"c3", "c1"}
    assert lean_cache.first_available(["c4", "c3", "c2", "c1"], published.__contains__) == "c3"
    assert lean_cache.first_available(["c4", "c2"], published.__contains__) is None


def test_partial_mappings_are_refused() -> None:
    with pytest.raises(ValueError, match="partial"):
        lean_cache.check_mappings(549, 550)
    with pytest.raises(ValueError):
        lean_cache.check_mappings(10, 0)
    lean_cache.check_mappings(550, 550)
    lean_cache.check_mappings(900, 550)


def test_mapping_count_ignores_blank_lines(tmp_path: Path) -> None:
    path = tmp_path / "map.jsonl"
    path.write_text('{"a": 1}\n\n{"b": 2}\n', encoding="utf-8")
    assert lean_cache.mapping_count(path) == 2


def archive(tmp_path: Path, members: dict[str, bytes], *, link: str | None = None) -> Path:
    path = tmp_path / "snap.tgz"
    with tarfile.open(path, "w:gz") as tar:
        for name, data in members.items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
        if link:
            info = tarfile.TarInfo(link)
            info.type = tarfile.SYMTYPE
            info.linkname = "/etc/passwd"
            tar.addfile(info)
    return path


@pytest.mark.parametrize("members,link", [
    ({"../escape.txt": b"x"}, None),
    ({"/abs.txt": b"x"}, None),
    ({"ok.txt": b"x"}, "link"),
])
def test_unsafe_snapshots_are_refused_and_existing_snapshot_kept(tmp_path: Path, members, link) -> None:
    dest = tmp_path / "formalpedia"
    dest.mkdir()
    (dest / "keep.txt").write_text("previous", encoding="utf-8")
    with pytest.raises(ValueError, match="unsafe"):
        lean_cache.extract_snapshot(archive(tmp_path, members, link=link), dest)
    assert (dest / "keep.txt").read_text(encoding="utf-8") == "previous"
    assert not (tmp_path / "escape.txt").exists()


def test_safe_snapshot_replaces_the_previous_one(tmp_path: Path) -> None:
    dest = tmp_path / "formalpedia"
    dest.mkdir()
    (dest / "stale.txt").write_text("old", encoding="utf-8")
    lean_cache.extract_snapshot(archive(tmp_path, {"semantic/index.json": b"{}"}), dest)
    assert (dest / "semantic/index.json").read_bytes() == b"{}"
    assert not (dest / "stale.txt").exists()
    assert [p.name for p in tmp_path.iterdir() if p.name.startswith("snapshot-")] == []


def test_upload_failure_never_prints_the_key(monkeypatch, tmp_path: Path) -> None:
    key = "AKIAEXAMPLE:topsecret"
    failed = subprocess.CompletedProcess([], 22, stdout=f"denied for {key}", stderr="")
    monkeypatch.setattr(lean_cache.subprocess, "run", lambda *a, **k: failed)
    path = tmp_path / "f"
    path.write_text("x", encoding="utf-8")
    with pytest.raises(ValueError) as info:
        lean_cache.put_object(path, "https://example/lean/x", key, "us-east-1", "text/plain")
    assert "topsecret" not in str(info.value)
    assert "***" in str(info.value)


@pytest.mark.skipif(os.name == "nt", reason="the curl shim is a POSIX shell script for Linux CI")
def test_curl_shim_rewrites_only_the_auto_region(tmp_path: Path) -> None:
    fake = tmp_path / "fake-curl"
    fake.write_text('#!/bin/sh\nfor a do printf "%s\\n" "$a"; done\n', encoding="utf-8")
    fake.chmod(0o755)
    shim_dir = tmp_path / "shim"
    shim_dir.mkdir()
    shim = lean_cache.curl_shim(shim_dir, str(fake), "us-east-1")
    out = subprocess.run([str(shim), "-s", "--aws-sigv4", "aws:amz:auto:s3", "--user", "k:s", "a b"],
                         capture_output=True, text=True, check=True).stdout.splitlines()
    assert out == ["-s", "--aws-sigv4", "aws:amz:us-east-1:s3", "--user", "k:s", "a b"]


@pytest.mark.skipif(os.name != "nt", reason="Windows refuses to publish")
def test_curl_shim_refuses_on_windows(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="Linux"):
        lean_cache.curl_shim(tmp_path, "curl", "us-east-1")
