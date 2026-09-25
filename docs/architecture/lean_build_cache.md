# Shared Lean build cache

A cold build of `formal/` (about 550 modules over Mathlib) takes more than half an hour
and up to 16 GB of memory. Every fresh worktree, every CI run and every cloud session
used to pay that cost. The laboratory now shares compiled modules through Lake's own
remote cache.

## How it works

| Piece | Where | Role |
|---|---|---|
| Service config | [`tools/lean/lake-cache.toml`](../../tools/lean/lake-cache.toml) | One S3 service, `btlab`, selected with `LAKE_CONFIG` |
| Bucket | `weasel-lean-cache`, `us-east-1`, prefix `lean/` | Anonymous read of `lean/*` and anonymous listing; no anonymous write. Holds the cache only |
| Writer | CI `lean` job, pushes to `main` only | `lake build -o` then `lake cache put`, key in the `LAKE_CACHE_KEY` secret |
| Reader | [`tools/lean_cache.py fetch`](../../tools/lean_cache.py) | Mathlib via `lake exe cache get`, this library via `lake cache get`, then a restoring build |
| Cloud setup | [`tools/cloud_lean_setup.sh`](../../tools/cloud_lean_setup.sh) | Pinned toolchain, Python tools, fetch |

Lake stores each compiled output under its content hash (`lean/a0/…`) and one mappings
file per Git revision (`lean/r0/…`). The scope includes the repository, toolchain and
platform, so Linux (CI, cloud) and Windows outputs never mix. `lake cache get` walks back
up to 200 first-parent commits to the nearest published revision. The formalpedia
semantic snapshot is published beside it as `lean/formalpedia/<commit>.tgz` with a
`.sha256` sidecar, so only CI runs the memory-heavy `SemanticExport`.

Three environment variables turn the cache on for a Lake process; `lean_cache.py` and
the CI job set them, and the lakefile is unchanged:

    LAKE_CONFIG=<checkout>/tools/lean/lake-cache.toml
    LAKE_ARTIFACT_CACHE=true       # read and fill Lake's local artifact cache
    LAKE_RESTORE_ARTIFACTS=true    # copy cached outputs into formal/.lake/build

## Use

    python tools/lean_cache.py status    # configuration; no network writes
    python tools/lean_cache.py fetch     # Mathlib, library, restore, snapshot

A cloud session runs `bash tools/cloud_lean_setup.sh` once. Its network allowlist must
include `weasel-lean-cache.s3.us-east-1.amazonaws.com` and Mathlib's cache host.
Local worktrees can run `fetch` too, but only receive Linux outputs if they are Linux;
on Windows the Windows scope has no publisher yet, and `--from <main>` preparation
remains the local route.

## Trust boundary

A cached artifact saves compile time. It is not proof status. Lake re-hashes every
download (a hash mismatch deletes the file) and rebuilds any module whose inputs differ.
Lake's hashes are not cryptographic, so only CI may write: the IAM user behind
`LAKE_CACHE_KEY` can put objects under `lean/` and nothing else, and agents never hold
it. Evidence still comes from the axiom audits and `formalpedia.py ledger-check
--require-compiled`, which CI runs on the same build before publishing. A publish needs
a successful build, not green gates, because a failing proof gate says nothing about
whether a compiled module matches its inputs.

## Details that matter

- **Region.** Lake 4.33 signs uploads with SigV4 region `auto`, which Cloudflare R2
  accepts and AWS rejects (`the region 'auto' is wrong; expecting 'us-east-1'`, checked
  25 September 2026). `publish` therefore puts a small `curl` wrapper first on `PATH`
  for `lake cache put` that rewrites the region. Downloads are unsigned and unaffected.
- **Listing is public on purpose.** Lake treats a missing revision as 404 and backtracks,
  but S3 answers 403 for a missing key unless the requester may list the bucket, and
  Lake stops on 403. The bucket policy therefore grants anonymous `s3:ListBucket`; a
  prefix condition would not apply to reads. Keep nothing but the cache in this bucket.
- **Partial publishes.** `publish` refuses when `lake build -o` recorded fewer mappings
  than there are build targets, and when the checkout has tracked changes.
- **Snapshot safety.** `fetch` checks the snapshot's published sha256 and extracts only
  regular files and directories with relative paths, replacing `.cache/formalpedia`
  only after every member passes.
- **Bucket owner.** The bucket, its policy and the IAM user belong to the repository
  owner's AWS account; changes to them are made by the owner, not by agents.
