#!/usr/bin/env python3
"""Run leanprover/comparator on a trusted reference and standalone solution.

Supply a compatible comparator, lean4export, and landrun through environment
variables; see comparator/README.md. This script does not install those tools.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def required_binary(variable: str) -> str:
    value = os.environ.get(variable)
    if not value:
        raise SystemExit(f"{variable} is required; see comparator/README.md")
    result = shutil.which(value)
    if result is None:
        raise SystemExit(f"{variable} does not resolve to an executable: {value}")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--challenge-module", required=True)
    parser.add_argument("--solution-module", default="comparator.SelfContained")
    parser.add_argument("--theorem", required=True, action="append")
    parser.add_argument("--definition", action="append", default=[])
    args = parser.parse_args()

    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        raise SystemExit("This runner is documented for Lean 4.19.0; review tool compatibility")
    comparator = required_binary("COMPARATOR_BIN")
    exporter = required_binary("COMPARATOR_LEAN4EXPORT")
    landrun = required_binary("COMPARATOR_LANDRUN")
    config = {
        "challenge_module": args.challenge_module,
        "solution_module": args.solution_module,
        "theorem_names": args.theorem,
        "definition_names": args.definition,
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    }
    environment = os.environ.copy()
    environment["COMPARATOR_LEAN4EXPORT"] = exporter
    environment["COMPARATOR_LANDRUN"] = landrun
    with tempfile.TemporaryDirectory(prefix="bemoc-comparator-") as directory:
        config_path = Path(directory) / "config.json"
        config_path.write_text(json.dumps(config, indent=2) + "\n")
        print(json.dumps(config, indent=2), flush=True)
        completed = subprocess.run(
            ["lake", "env", comparator, str(config_path)],
            cwd=ROOT,
            env=environment,
            check=False,
        )
    sys.exit(completed.returncode)


if __name__ == "__main__":
    main()
