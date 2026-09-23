"""Exercise the publication boundary through real Git indexes and history."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess

import pytest

SPEC = importlib.util.spec_from_file_location(
    "check_publication", Path(__file__).resolve().parents[2] / "tools/check_publication.py",
)
publication = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(publication)


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          capture_output=True).stdout


@pytest.fixture
def repo(tmp_path):
    git(tmp_path, "init")
    git(tmp_path, "config", "user.name", "Publication test")
    git(tmp_path, "config", "user.email", "test@example.invalid")
    git(tmp_path, "config", "commit.gpgsign", "false")
    return tmp_path


def write(root, name, text="test fixture\n"):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_force_adding_ignored_private_material_is_rejected(repo):
    write(repo, ".gitignore", "literature/sources/\n*.private.json\n")
    names = ["literature/sources/a source.txt", "literature/a.private.json",
             "backup.bundle", "nested/.env.production", "nested/credentials.json"]
    for name in names:
        write(repo, name)
        git(repo, "add", "-f", "--", name)
    assert publication.violations(repo) == sorted(names)


def test_deleted_source_still_fails_history_check(repo):
    name = "literature/sources/retrieved.txt"
    write(repo, name)
    git(repo, "add", ".")
    git(repo, "commit", "-m", "Add a fixture")
    git(repo, "rm", name)
    git(repo, "commit", "-m", "Remove a fixture")
    assert publication.violations(repo) == []
    assert publication.violations(repo, "HEAD") == [name]


def test_public_citations_and_licensed_sources_remain_allowed(repo):
    for name in ("literature/paper.json", "literature/licenses/upstream-MIT.txt",
                 "formal/Problems/Collatz/Example.lean", ".env.example"):
        write(repo, name)
    git(repo, "add", ".")
    git(repo, "commit", "-m", "Public fixtures")
    assert publication.violations(repo, "HEAD") == []


def test_history_check_fails_closed_without_full_history(repo, tmp_path_factory):
    write(repo, "README.md")
    git(repo, "add", ".")
    git(repo, "commit", "-m", "Public fixture")
    clone = tmp_path_factory.mktemp("shallow") / "repo"
    subprocess.run(["git", "clone", "--depth=1", repo.as_uri(), str(clone)],
                   check=True, capture_output=True)
    with pytest.raises(RuntimeError, match="full clone"):
        publication.violations(clone, "HEAD")
