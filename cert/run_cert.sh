#!/usr/bin/env bash
# Re-run both OZ-1 certificates from a fresh clone of this repo at HEAD and archive the output.
# Usage: bash targets/ozawa-entropy-variation/cert/run_cert.sh <empty-scratch-dir>
# The cert scripts are copied into the clone when they are not yet committed (their sha256 is printed
# by each script, so the archived output identifies the exact script text that ran).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../.." && pwd)"
scratch="${1:?usage: run_cert.sh <empty-scratch-dir>}"
rel="targets/ozawa-entropy-variation/cert"
commit="$(git -C "$repo" rev-parse HEAD)"
rm -rf "$scratch/clone"
git clone --quiet --no-hardlinks "$repo" "$scratch/clone"
git -C "$scratch/clone" checkout --quiet "$commit"
mkdir -p "$scratch/clone/$rel"
for f in OZ-1.py OZ-1_x.py; do
  [ -f "$scratch/clone/$rel/$f" ] || cp "$here/$f" "$scratch/clone/$rel/$f"
done
cd "$scratch/clone"
for id in OZ-1 OZ-1_x; do
  {
    echo "run_cert.sh: fresh clone of $repo at commit $commit in $scratch/clone"
    echo "run_cert.sh: invoking: python $rel/$id.py"
    start=$(date +%s.%N)
    set +e
    python "$rel/$id.py"
    rc=$?
    set -e
    end=$(date +%s.%N)
    echo "run_cert.sh: exit code $rc, wall time $(python -c "import sys;print(round(float(sys.argv[2])-float(sys.argv[1]),2))" "$start" "$end") s"
  } 2>&1 | tee "$here/$id.out"
done
