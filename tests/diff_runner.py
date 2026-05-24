"""Cross-port differential runner — Python side.

Reads /tmp/diff_corpus.jsonl (shared with rust-port and cpp-port),
runs `homoglyph_confusable.detect` on each entry, and emits one
JSONL line to stdout in the canonical cross-port format:

    {"id":<n>,"cps":[<u32>,…],"kind":"<Clear|Hazard>","sub":"<tag|null>","target":"<str|null>"}

Any byte-level divergence from the rust-port / cpp-port output of
this same corpus is a port-drift bug.

Run:
    PYTHONPATH=src python3 tests/diff_runner.py > /tmp/python_diff.jsonl
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

# Allow running directly: add src/ to PYTHONPATH
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

from unicode_python.security import ClassificationKind  # noqa: E402
from unicode_python.security.identity import (  # noqa: E402
    homoglyph_confusable as h,
)

CORPUS_PATH = "/tmp/diff_corpus.jsonl"


def verdict_to_jsonl(input_id: int, cps: list[int]) -> str:
    v = h.detect(cps)
    if v.kind is ClassificationKind.CLEAR:
        kind = "Clear"
    elif v.kind is ClassificationKind.HAZARD:
        kind = "Hazard"
    elif v.kind is ClassificationKind.COMPOUND:
        kind = "Compound"
    else:
        kind = "Informational"

    if v.sub is None:
        sub_str = "null"
        target_str = "null"
    else:
        tag = h.sub_threat_tag(v.sub)
        sub_str = f'"{tag}"'
        if isinstance(v.sub, h.TargetMatch):
            # Same JSON-escape contract as the Rust runner — only `"` is escaped.
            escaped = v.sub.target.replace('"', '\\"')
            target_str = f'"{escaped}"'
        else:
            target_str = "null"

    cps_str = ",".join(str(cp) for cp in cps)
    return (
        f'{{"id":{input_id},"cps":[{cps_str}],"kind":"{kind}",'
        f'"sub":{sub_str},"target":{target_str}}}'
    )


def main() -> None:
    with open(CORPUS_PATH, "r", encoding="utf-8") as f:
        for line in f:
            entry = json.loads(line)
            input_id = entry["id"]
            cps = entry["cps"]
            print(verdict_to_jsonl(input_id, cps))


if __name__ == "__main__":
    main()
