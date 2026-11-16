#!/usr/bin/env bash
# One-time setup. Run from the project root:  bash scripts/bootstrap.sh
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v elan >/dev/null 2>&1; then
  echo "Installing elan (Lean toolchain manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

# 1. resolve Mathlib, 2. adopt the toolchain Mathlib requires, 3. fetch prebuilt oleans
lake update
cp .lake/packages/mathlib/lean-toolchain lean-toolchain
echo "Toolchain now: $(cat lean-toolchain)"
lake exe cache get
lake build 2>&1 | tee build.log || true

echo
echo "First build finished. Expect some Mathlib name drift on a first run."
echo "See README.md, section 'Fixing name drift'. Then run: bash scripts/check.sh"
echo "Once green, pin Mathlib: set rev in lakefile.toml to the commit in lake-manifest.json."
