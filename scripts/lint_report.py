#!/usr/bin/env python3
"""Report Mathlib's default environment linters (`#lint`) over the whole library.

Run after `lake build`. Prints the linter summary and the findings grouped by linter. Exits 0
unless `--strict` is given and some linter reports a finding, so it can run in a non-blocking CI
job and later become a blocking check.
"""

import argparse
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBE = """import BGW
import Batteries.Tactic.Lint

#lint in BGW
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--strict", action="store_true", help="exit 1 if any finding is reported")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="bgw-lint-") as temporary:
        probe = Path(temporary) / "Lint.lean"
        probe.write_text(PROBE, encoding="utf-8")
        done = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                              capture_output=True, text=True)
    output = done.stdout + done.stderr
    linter = None
    counts: Counter[str] = Counter()
    for line in output.splitlines():
        found = re.match(r"/- The `(\w+)` linter reports", line)
        if found:
            linter = found.group(1)
        elif line.startswith("#check") and linter:
            counts[linter] += 1
    summary = [line for line in output.splitlines() if "errors in" in line or "linting checks" in line]
    print(output if counts else "\n".join(summary))
    for name, count in sorted(counts.items()):
        print(f"{name}: {count}")
    if done.returncode != 0 and not counts:
        print("lint probe failed", file=sys.stderr)
        return 2
    return 1 if args.strict and counts else 0


if __name__ == "__main__":
    sys.exit(main())
