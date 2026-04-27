#!/usr/bin/env bash
# Fail if any `.lean` file under `Unicode/` is not transitively imported
# from the root `Unicode.lean`. Orphan files compile in isolation but
# are NOT covered by the headline build / sorry / axiom guards, so they
# are a hiding place for unverified material.

set -euo pipefail

cd "$(dirname "$0")/.."

# Collect every Lean module name under `Unicode/` (and the root).
declare -A ALL_MODULES
while IFS= read -r path; do
  module="${path%.lean}"
  module="${module//\//.}"
  ALL_MODULES["$module"]=1
done < <(find Unicode.lean Unicode/ -name '*.lean' -type f)

# Walk the import graph from `Unicode` (the root).
declare -A REACHED
queue=("Unicode")
while [ ${#queue[@]} -gt 0 ]; do
  current="${queue[0]}"
  queue=("${queue[@]:1}")
  if [ -n "${REACHED[$current]:-}" ]; then continue; fi
  REACHED["$current"]=1
  module_path="${current//.//}.lean"
  [ -f "$module_path" ] || continue
  while IFS= read -r imp; do
    case "$imp" in
      Unicode|Unicode.*)
        if [ -z "${REACHED[$imp]:-}" ]; then
          queue+=("$imp")
        fi
        ;;
    esac
  done < <(grep -hE '^import[[:space:]]+[A-Za-z_][A-Za-z0-9_.]*' "$module_path" | awk '{print $2}')
done

orphans=()
for module in "${!ALL_MODULES[@]}"; do
  if [ -z "${REACHED[$module]:-}" ]; then
    orphans+=("$module")
  fi
done

if [ ${#orphans[@]} -gt 0 ]; then
  echo "FATAL: ${#orphans[@]} orphan file(s) — present on disk but not transitively imported from Unicode.lean:"
  printf '  %s\n' "${orphans[@]}" | sort
  exit 1
fi

echo "clean: every .lean file under Unicode/ is transitively imported from the root"
