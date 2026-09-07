"""Offline tests for tools/prove2me.py: no network, no real key."""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("prove2me", ROOT / "tools" / "prove2me.py")
p2m = importlib.util.module_from_spec(SPEC)
sys.modules["prove2me"] = p2m
SPEC.loader.exec_module(p2m)


def test_module_names_replace_dots() -> None:
    assert p2m.theorem_module("foo.bar.baz") == "Theorems.Thm_foo_bar_baz"
    assert p2m.definition_module("Juggler.floorPower") == "Definitions.Def_Juggler_floorPower"


def test_is_uuid() -> None:
    assert p2m.is_uuid("ecc55b15-1d38-4d3d-9f47-90384687988f")
    assert not p2m.is_uuid("Juggler.tower_absorption")


def test_stub_source_is_preamble_then_statement() -> None:
    src = p2m.stub_source({
        "preamble": "import Mathlib.Data.Nat.Basic\n",
        "formal_statement": "theorem foo (n : ℕ) : n = n := by sorry",
    })
    assert src == "import Mathlib.Data.Nat.Basic\n\ntheorem foo (n : ℕ) : n = n := by sorry\n"


def test_api_key_precedence(tmp_path: Path) -> None:
    creds = tmp_path / "credentials.json"
    creds.write_text(json.dumps({"api_key": "p2m_file"}), encoding="utf-8")
    assert p2m.load_api_key({"PROVE2ME_API_KEY": "p2m_env"}, (creds,)) == "p2m_env"
    assert p2m.load_api_key({}, (creds,)) == "p2m_file"
    with pytest.raises(p2m.Prove2MeError):
        p2m.load_api_key({}, (tmp_path / "missing.json",))


def test_access_token_uses_cache_then_refreshes(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    token_file = tmp_path / "token.json"
    token_file.write_text(json.dumps({"access_token": "cached", "expires_at": 2000}), encoding="utf-8")
    calls: list[str] = []

    def refresh(key: str) -> dict:
        calls.append(key)
        return {"access_token": "fresh", "expires_at": 9000, "version": "0.9.7"}

    monkeypatch.setenv("PROVE2ME_API_KEY", "p2m_test")
    assert p2m.access_token(now=1000, token_file=token_file, refresh=refresh) == "cached"
    assert calls == []
    assert p2m.access_token(now=1990, token_file=token_file, refresh=refresh) == "fresh"
    assert calls == ["p2m_test"]
    assert json.loads(token_file.read_text(encoding="utf-8"))["expires_at"] == 9000


def test_multipart_carries_fields_and_file() -> None:
    body, ctype = p2m.encode_multipart(
        {"theorem_id": "abc", "proof_type": "prove"},
        {"file": ("solution.lean", b"theorem solution : True := trivial\n")},
    )
    boundary = ctype.split("boundary=")[1]
    assert body.count(f"--{boundary}".encode()) == 4  # 3 parts + closing
    assert b'name="theorem_id"\r\n\r\nabc' in body
    assert b'filename="solution.lean"' in body
    assert body.endswith(f"--{boundary}--\r\n".encode())


def test_repo_never_tracks_a_key() -> None:
    """The key lives outside the repository; nothing tracked may carry the p2m_ prefix."""
    import subprocess

    # A real key is `p2m_` followed by a JWT, whose header always encodes to `eyJhbGci`.
    # The pattern is assembled so this file does not match itself.
    pattern = "p2m_" + "eyJhbGci"
    out = subprocess.run(
        ["git", "grep", "-l", pattern, "--", "."],
        cwd=ROOT, capture_output=True, text=True, check=False,
    )
    assert out.stdout.strip() == "", out.stdout
