#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export PATH="${HOME}/.elan/bin:${PATH}"
if ! command -v elan >/dev/null 2>&1; then
  echo "Install elan before running setup: https://github.com/leanprover/elan" >&2
  exit 1
fi
if [[ -z "${CURL_CA_BUNDLE:-}" && -r /etc/pki/tls/certs/ca-bundle.crt ]]; then
  export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
fi
# Lake resolves the committed manifest; do not update pinned upstream revisions.
mapfile -t pla_mathlib_imports < <(python3 - <<'PY'
from pathlib import Path
import re
imports = set()
for root in ("PLAStochastic",):
    for path in Path(root).rglob("*.lean"):
        imports.update(re.findall(r"^import (Mathlib\.\S+)", path.read_text(), re.MULTILINE))
print("\n".join(sorted(imports)))
PY
)
lake exe cache get "${pla_mathlib_imports[@]}"
lake build
