"""prove2.me client for the laboratory: search, fetch, verify, poll.

https://prove2.me is a Lean 4 theorem platform (missions, server-side kernel
verification).  Every statement it proves enters its public library,
*Formalpedia* (https://prove2.me/formalpedia), which later proofs can import.
This is not the laboratory's own ``tools/formalpedia.py``, the local index
over ``formal/``; the two share a name and nothing else.

Usage::

    python tools/prove2me.py whoami
    python tools/prove2me.py envs
    python tools/prove2me.py search <text> [--status Open|Proved|Disproved|Definition]
                                           [--tags a,b] [--limit N] [--env REV]
    python tools/prove2me.py show <theorem_id_or_name>
    python tools/prove2me.py fetch <theorem_id_or_name> [--workspace DIR]
    python tools/prove2me.py missions [--limit N]
    python tools/prove2me.py leaves <theorem_id>
    python tools/prove2me.py verify <theorem_id_or_name> <solution.lean>
                                    [--explanation FILE] [--disprove] [--wait]
    python tools/prove2me.py status <submission_id>

Credentials.  The API key (prefix ``p2m_``, valid 30 days) is read from the
environment variable ``PROVE2ME_API_KEY``, else from
``~/prove2me_workspace/credentials.json``, else ``~/.prove2me/credentials.json``
(``{"api_key": ..., "expires_at": ...}``).  It is exchanged for a one-hour
access token at ``POST /agent/refresh``; the token is cached in
``~/.prove2me/token.json``.  The key and the token go to https://prove2.me
and nowhere else.

Standard library only.
"""

from __future__ import annotations

import argparse
import json
import mimetypes
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from pathlib import Path
from typing import Any

BASE = "https://prove2.me/api/v1"
ENV_VAR = "PROVE2ME_API_KEY"
HOME = Path(os.environ.get("USERPROFILE") or Path.home())
CONFIG_DIR = HOME / ".prove2me"
TOKEN_FILE = CONFIG_DIR / "token.json"
CREDENTIAL_FILES = (
    HOME / "prove2me_workspace" / "credentials.json",
    CONFIG_DIR / "credentials.json",
)
TERMINAL = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
UUID_RE = re.compile(r"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$")


class Prove2MeError(RuntimeError):
    pass


# --------------------------------------------------------------------------- pure helpers


def is_uuid(text: str) -> bool:
    return bool(UUID_RE.match(text))


def theorem_module(theorem_name: str) -> str:
    """``Theorems.Thm_<name>`` with dots replaced by underscores."""
    return "Theorems.Thm_" + theorem_name.replace(".", "_")


def definition_module(definition_name: str) -> str:
    return "Definitions.Def_" + definition_name.replace(".", "_")


def stub_source(theorem: dict[str, Any]) -> str:
    """The local ``Thm_`` file: preamble, then the formal statement ending in ``sorry``."""
    preamble = (theorem.get("preamble") or "").strip()
    statement = (theorem.get("formal_statement") or "").strip()
    parts = [p for p in (preamble, statement) if p]
    return "\n\n".join(parts) + "\n"


def encode_multipart(fields: dict[str, str], files: dict[str, tuple[str, bytes]]) -> tuple[bytes, str]:
    """Multipart/form-data body and content type for ``POST /verify``."""
    boundary = "----prove2me-" + uuid.uuid4().hex
    lines: list[bytes] = []
    for name, value in fields.items():
        lines += [
            f"--{boundary}".encode(),
            f'Content-Disposition: form-data; name="{name}"'.encode(),
            b"",
            value.encode("utf-8"),
        ]
    for name, (filename, data) in files.items():
        ctype = mimetypes.guess_type(filename)[0] or "application/octet-stream"
        lines += [
            f"--{boundary}".encode(),
            f'Content-Disposition: form-data; name="{name}"; filename="{filename}"'.encode(),
            f"Content-Type: {ctype}".encode(),
            b"",
            data,
        ]
    lines += [f"--{boundary}--".encode(), b""]
    return b"\r\n".join(lines), f"multipart/form-data; boundary={boundary}"


# --------------------------------------------------------------------------- credentials


def load_api_key(environ: dict[str, str] | None = None, files: tuple[Path, ...] = CREDENTIAL_FILES) -> str:
    env = os.environ if environ is None else environ
    key = (env.get(ENV_VAR) or "").strip()
    if key:
        return key
    for path in files:
        if path.is_file():
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                raise Prove2MeError(f"{path} is not valid JSON: {exc}") from exc
            key = (data.get("api_key") or "").strip()
            if key:
                return key
    raise Prove2MeError(
        f"no prove2.me API key: set {ENV_VAR} (setx on Windows, then open a new shell) "
        f"or write one of {', '.join(str(p) for p in files)}"
    )


def _post_json(path: str, body: dict[str, Any]) -> dict[str, Any]:
    data = json.dumps(body).encode("utf-8")
    req = urllib.request.Request(BASE + path, data=data, method="POST")
    req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.loads(resp.read().decode("utf-8"))


def access_token(force: bool = False, now: float | None = None, token_file: Path = TOKEN_FILE,
                 refresh=None) -> str:
    """A valid access token, from the cache or by exchanging the API key."""
    now = time.time() if now is None else now
    if not force and token_file.is_file():
        try:
            cached = json.loads(token_file.read_text(encoding="utf-8"))
            if cached.get("access_token") and float(cached.get("expires_at", 0)) - 60 > now:
                return cached["access_token"]
        except (json.JSONDecodeError, ValueError):
            pass
    refresh = refresh or (lambda key: _post_json("/agent/refresh", {"api_key": key}))
    data = refresh(load_api_key())
    token = data.get("access_token")
    if not token:
        raise Prove2MeError(f"/agent/refresh returned no access_token: {data}")
    token_file.parent.mkdir(parents=True, exist_ok=True)
    token_file.write_text(
        json.dumps({"access_token": token, "expires_at": data.get("expires_at"),
                    "version": data.get("version")}),
        encoding="utf-8",
    )
    return token


# --------------------------------------------------------------------------- requests


def request(method: str, path: str, *, params: dict[str, Any] | None = None,
            json_body: dict[str, Any] | None = None,
            multipart: tuple[bytes, str] | None = None, retry: bool = True) -> Any:
    url = BASE + path
    if params:
        url += "?" + urllib.parse.urlencode({k: v for k, v in params.items() if v is not None})
    data: bytes | None = None
    headers = {"Authorization": f"Bearer {access_token()}", "Accept": "application/json"}
    if json_body is not None:
        data = json.dumps(json_body).encode("utf-8")
        headers["Content-Type"] = "application/json"
    elif multipart is not None:
        data, headers["Content-Type"] = multipart
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=120) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        if exc.code == 401 and retry:
            access_token(force=True)
            return request(method, path, params=params, json_body=json_body,
                           multipart=multipart, retry=False)
        raise Prove2MeError(f"{method} {path} -> HTTP {exc.code}: {body[:2000]}") from exc


def resolve_theorem(id_or_name: str, env: str | None = None) -> dict[str, Any]:
    if is_uuid(id_or_name):
        return request("GET", f"/theorems/{id_or_name}")
    data = request("GET", "/theorems", params={"theorem_name": id_or_name, "limit": 5, "env": env})
    items = data.get("theorems") or data.get("items") or data.get("results") or (data if isinstance(data, list) else [])
    if not items:
        raise Prove2MeError(f"no theorem named {id_or_name!r}")
    return items[0]


def _items(data: Any) -> list[dict[str, Any]]:
    if isinstance(data, list):
        return data
    for key in ("theorems", "items", "results", "missions", "environments", "open_leaves"):
        if isinstance(data.get(key), list):
            return data[key]
    return []


# --------------------------------------------------------------------------- commands


def cmd_whoami(_: argparse.Namespace) -> None:
    print(json.dumps(request("GET", "/me"), indent=1, ensure_ascii=False))


def cmd_envs(_: argparse.Namespace) -> None:
    print(json.dumps(request("GET", "/environments"), indent=1, ensure_ascii=False))


def cmd_search(args: argparse.Namespace) -> None:
    data = request("GET", "/theorems", params={
        "q": args.text, "status": args.status, "tags": args.tags,
        "limit": args.limit, "env": args.env, "sort": args.sort,
    })
    items = _items(data)
    for t in items:
        print(f"{t.get('theorem_id')}  [{t.get('status')}]  {t.get('theorem_name')}")
        title = (t.get("theorem_title") or "").strip()
        if title:
            print(f"    {title[:160]}")
    total = data.get("total") if isinstance(data, dict) else None
    print(f"-- {len(items)} shown" + (f" of {total}" if total is not None else ""))


def cmd_show(args: argparse.Namespace) -> None:
    print(json.dumps(resolve_theorem(args.theorem, args.env), indent=1, ensure_ascii=False))


def cmd_fetch(args: argparse.Namespace) -> None:
    theorem = resolve_theorem(args.theorem, args.env)
    name = theorem["theorem_name"]
    root = Path(args.workspace)
    path = root / "Theorems" / (theorem_module(name).split(".", 1)[1] + ".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(stub_source(theorem), encoding="utf-8")
    print(f"{path}  (import {theorem_module(name)}; status {theorem.get('status')}; "
          f"env {theorem.get('mathlib_rev')})")


def cmd_missions(args: argparse.Namespace) -> None:
    data = request("GET", "/missions", params={"limit": args.limit})
    for m in _items(data):
        main = m.get("main_theorem") or {}
        fields = ",".join(f.get("slug", "") for f in (m.get("fields") or []))
        print(f"{m.get('id')}  {m.get('mission_type')}  [{fields}]  {m.get('name')}")
        if main:
            goal = main.get("theorem_name") or main.get("name") or main.get("theorem_id")
            print(f"    goal: {goal} [{main.get('status')}]")


def cmd_leaves(args: argparse.Namespace) -> None:
    data = request("GET", f"/theorems/{args.theorem}/open-leaves", params={"limit": args.limit})
    for leaf in _items(data):
        print(f"{leaf.get('theorem_id')}  [{leaf.get('status')}]  closability={leaf.get('closability')}  "
              f"{leaf.get('theorem_name')}")


def cmd_verify(args: argparse.Namespace) -> None:
    theorem = resolve_theorem(args.theorem, args.env)
    source = Path(args.solution).read_bytes()
    if re.search(rb"\bsorry\b", source):
        raise Prove2MeError("solution contains `sorry`; the server would return SORRY")
    fields = {"theorem_id": theorem["theorem_id"]}
    if args.disprove:
        fields["proof_type"] = "disprove"
    if args.explanation:
        fields["explanation"] = Path(args.explanation).read_text(encoding="utf-8")
    body, ctype = encode_multipart(fields, {"file": (Path(args.solution).name, source)})
    data = request("POST", "/verify", multipart=(body, ctype))
    print(json.dumps(data, indent=1, ensure_ascii=False))
    sub = data.get("submission_id")
    if args.wait and sub:
        print(poll_status(sub))


def poll_status(submission_id: str, timeout: float = 600.0, interval: float = 5.0) -> str:
    deadline = time.time() + timeout
    while True:
        data = request("GET", "/verify", params={"submission_id": submission_id})
        status = data.get("status")
        if status in TERMINAL or time.time() > deadline:
            return json.dumps(data, indent=1, ensure_ascii=False)
        time.sleep(interval)


def cmd_status(args: argparse.Namespace) -> None:
    print(json.dumps(request("GET", "/verify", params={"submission_id": args.submission}),
                     indent=1, ensure_ascii=False))


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="command", required=True)
    sub.add_parser("whoami").set_defaults(func=cmd_whoami)
    sub.add_parser("envs").set_defaults(func=cmd_envs)
    s = sub.add_parser("search")
    s.add_argument("text")
    s.add_argument("--status", choices=["Open", "Proved", "Disproved", "Definition"])
    s.add_argument("--tags")
    s.add_argument("--limit", type=int, default=20)
    s.add_argument("--env")
    s.add_argument("--sort", choices=["newest", "votes"], default="newest")
    s.set_defaults(func=cmd_search)
    s = sub.add_parser("show")
    s.add_argument("theorem")
    s.add_argument("--env")
    s.set_defaults(func=cmd_show)
    s = sub.add_parser("fetch")
    s.add_argument("theorem")
    s.add_argument("--workspace", default=str(HOME / "prove2me_workspace"))
    s.add_argument("--env")
    s.set_defaults(func=cmd_fetch)
    s = sub.add_parser("missions")
    s.add_argument("--limit", type=int, default=20)
    s.set_defaults(func=cmd_missions)
    s = sub.add_parser("leaves")
    s.add_argument("theorem")
    s.add_argument("--limit", type=int, default=15)
    s.set_defaults(func=cmd_leaves)
    s = sub.add_parser("verify")
    s.add_argument("theorem")
    s.add_argument("solution")
    s.add_argument("--explanation")
    s.add_argument("--disprove", action="store_true")
    s.add_argument("--wait", action="store_true")
    s.add_argument("--env")
    s.set_defaults(func=cmd_verify)
    s = sub.add_parser("status")
    s.add_argument("submission")
    s.set_defaults(func=cmd_status)
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        args.func(args)
    except Prove2MeError as exc:
        print(f"prove2me: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
