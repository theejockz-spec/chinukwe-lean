#!/usr/bin/env bash
# Newer Mathlib prefers  ∑ x ∈ s, f x  over the older  ∑ x in s, f x.
# If your Mathlib rejects the old form, run this once from the project root.
set -euo pipefail
cd "$(dirname "$0")/.."
find Chinukwe Conjectures -name '*.lean' -print0 \
  | xargs -0 sed -i -E 's/(∑|∏) ([A-Za-z0-9_₀-₉'"'"']+) in /\1 \2 ∈ /g'
echo "Rewrote 'in' to '∈' in big-operator binders."
