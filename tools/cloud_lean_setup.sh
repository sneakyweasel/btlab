#!/usr/bin/env bash
# Setup for a cloud agent session (Linux): pinned Lean, Python tools, then the shared build.
# Paste into the cloud environment's setup script, or run from the checkout root:
#     bash tools/cloud_lean_setup.sh
# Network: needs github.com, the elan release host, Mathlib's cache host and
# weasel-lean-cache.s3.us-east-1.amazonaws.com. No secrets are used or needed.
# See docs/architecture/lean_build_cache.md.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

toolchain="$(cat formal/lean-toolchain)"
if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$toolchain"

python3 -m pip install --quiet "uv>=0.12,<0.13"
python3 tools/lab.py prepare --apply --profile python

# Mathlib from its own cache, this library from the laboratory cache (nearest published
# main commit), restored into formal/.lake/build; only changed modules compile here.
python3 tools/lean_cache.py fetch

cat <<'EOF'
Lean is ready. For later builds in this session keep the shared cache on:
  export LAKE_CONFIG="$PWD/tools/lean/lake-cache.toml" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
EOF
