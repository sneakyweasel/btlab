---
name: prove2me
description: Use the prove2.me Lean 4 theorem platform and its public library Formalpedia (https://prove2.me/formalpedia) through tools/prove2me.py. Use this when asked to search Formalpedia for an existing machine-checked theorem, to check whether a statement is already proved there before proving it locally, to fetch a platform theorem as a local Thm_ stub, to browse missions or open leaves, to submit a proof for server verification, or to publish laboratory results there. Not the laboratory's own tools/formalpedia.py, which indexes formal/ and keeps the name.
---

# prove2me

`tools/prove2me.py` is a standard-library client for https://prove2.me (API base
`https://prove2.me/api/v1`). Everything the platform proves enters *Formalpedia*, its public,
searchable library (58k theorems, 54k kernel-checked in Lean 4), and later proofs can import
those results. The laboratory's local index `tools/formalpedia.py` is a different thing with
the same name: it indexes `formal/`, never the platform.

```bash
python tools/prove2me.py whoami                      # the account behind the key
python tools/prove2me.py envs                        # pinned Lean/Mathlib environments
python tools/prove2me.py search "floor sqrt"         # Formalpedia search (q, --status, --tags)
python tools/prove2me.py show <theorem_id_or_name>   # one theorem, full JSON incl. formal_statement
python tools/prove2me.py fetch <theorem_id_or_name>  # write Theorems/Thm_<name>.lean stub in the workspace
python tools/prove2me.py missions                    # mission catalog
python tools/prove2me.py leaves <theorem_id>         # open leaves of a decomposition tree
python tools/prove2me.py verify <theorem> solution.lean --explanation notes.md --wait
python tools/prove2me.py status <submission_id>
```

## Credentials

The API key (prefix `p2m_`, valid 30 days) is read from the user environment variable
`PROVE2ME_API_KEY`, else `~/prove2me_workspace/credentials.json`, else
`~/.prove2me/credentials.json`. The client exchanges it for a one-hour access token
(`POST /agent/refresh`) cached in `~/.prove2me/token.json`. Rules that are not negotiable:

- The key and the token go to `https://prove2.me` and nowhere else.
- Nothing under the repository may contain the key: `.env`, `credentials.json` and
  `prove2me_workspace/` are gitignored, and `tests/tools/test_prove2me.py` fails if any tracked
  file carries a key-shaped string (`p2m_` followed by a JWT).
- A new shell is needed after `setx` before the variable is visible.

## Environments: the laboratory does not match the platform

| | Lean | Mathlib |
|---|---|---|
| platform default | v4.33.1 | `0df444a360eaa60ab8c11dca51a86af692955474` |
| laboratory `formal/` | v4.33.0 | `db584cd6d46c92f209a44c0f1c829460d327499d` |

Run `envs` for the authoritative list (v4.30.0 and v4.29.0-rc3 are also offered). A proof can
only import results from its own environment; a laboratory file does not compile on the
platform unchanged, and a platform theorem does not compile in `formal/` unchanged. Treat a
Formalpedia hit as a statement to re-prove or port, not as a module to import.

## Searching before proving

Search Formalpedia when a lemma is general mathematics (floor and sqrt identities, real
inequalities, Chernoff-type bounds, AM-GM forms) rather than laboratory-specific. `q` is a
substring match on title, name and description; `--status Proved` filters to machine-checked
results; `--status Definition` lists definitions. A miss is weak evidence: try the object's
name as well as the result's.

## Submitting a proof (server verification)

Three rules the server enforces on `POST /verify`:

1. The theorem is named `solution`, top level, no namespace, and its type matches the target's
   `formal_statement` exactly.
2. The target is never imported (it exists there as a `sorry` stub). Other platform theorems
   are imported as `Theorems.Thm_<name>` (dots become underscores) and definitions as
   `Definitions.Def_<name>`. A disproof may import definitions only, and negates the whole
   quantified statement.
3. The file is sorry-free; `autoImplicit` is false; use targeted imports, never
   `import Mathlib` (timeouts).

Verify locally first: the documented workspace is `$HOME/prove2me_workspace`
(`git clone https://github.com/prove2me/prove2me_workspace`, then read its `SKILL.md`;
`lake exe cache get` avoids a multi-hour Mathlib build). Verdicts: `PENDING`, `ACCEPTED`,
`SKETCH_ACCEPTED`, `CE`, `WA`, `SORRY`, `FAILED`, `ERROR`. At most 100 pending submissions.
The explanation is Markdown with KaTeX, at most 50,000 characters, opening with the statement
and the hypotheses used, then the idea, no tactic transcript.

## Publishing laboratory results

Anything public on the platform is permanent and attributed to the account. Before any
`POST /submit-problem`, `/submit-definition`, a `/verify` against a public theorem, or a
mission proposal, ask the human and say exactly what will be sent. For moving a body of
`formal/` results there, follow `https://prove2.me/references/upload_full_project.md`:
axioms must lie within `[propext, Classical.choice, Quot.sound]`, so the Juggler layer's two
`native_decide` proofs are not eligible, and the environment must be matched first.

## Reading list

`https://prove2.me/start.md`, `https://prove2.me/skill.md` (skill version 0.9.7; a token
refresh response carries the platform `version`, compare before trusting a cached copy), and
`https://prove2.me/references/{setup,prove,discover,missions,contribute,mission_solver,mission_captain,upload_full_project,lean-setup}.md`.
