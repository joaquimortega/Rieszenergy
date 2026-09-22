#!/usr/bin/env bash
# Reproduce the experimental Lean 4.19 comparator toolchain in a private directory.
# Network access is needed for the three upstream clones and Go modules.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
tools_dir=${1:-/tmp/bemoc-comparator-tools}
mkdir -p "$tools_dir"

if [[ -e "$tools_dir/comparator" || -e "$tools_dir/lean4export" || -e "$tools_dir/landrun" ]]; then
  echo "Tool directory already contains a checkout: $tools_dir" >&2
  exit 1
fi

git clone https://github.com/leanprover/comparator.git "$tools_dir/comparator"
git -C "$tools_dir/comparator" checkout 437574bcec4e7d76fa141e98e4a72682ab580859
git -C "$tools_dir/comparator" apply --unidiff-zero \
  "$repo_root/comparator/lean419-comparator.patch"
(cd "$tools_dir/comparator" && lake build comparator)

git clone https://github.com/leanprover/lean4export.git "$tools_dir/lean4export"
git -C "$tools_dir/lean4export" checkout aca5d120d25d9ae14436f96c0732497f11f3931e
printf 'leanprover/lean4:v4.19.0\n' > "$tools_dir/lean4export/lean-toolchain"
(cd "$tools_dir/lean4export" && lake build lean4export)

git clone https://github.com/Zouuup/landrun.git "$tools_dir/landrun"
git -C "$tools_dir/landrun" checkout 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd "$tools_dir/landrun" &&
  GOCACHE="$tools_dir/go-build-cache" GOPATH="$tools_dir/go-path" \
    go build -o landrun cmd/landrun/main.go)

printf 'COMPARATOR_BIN=%s\nCOMPARATOR_LEAN4EXPORT=%s\nCOMPARATOR_LANDRUN=%s\n' \
  "$tools_dir/comparator/.lake/build/bin/comparator" \
  "$tools_dir/lean4export/.lake/build/bin/lean4export" \
  "$tools_dir/landrun/landrun"
