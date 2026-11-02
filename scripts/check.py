#!/usr/bin/env python3
"""Build every delivered module, exercise the public API and audit axioms/docs."""

from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def modules(package: Path, namespace: str) -> list[str]:
    """Discover source modules, including an optional namespace aggregator."""
    sources = sorted((package / namespace).rglob("*.lean"))
    aggregator = package / f"{namespace}.lean"
    if aggregator.is_file():
        sources.insert(0, aggregator)
    if not sources:
        raise RuntimeError(f"No Lean sources found for {namespace} in {package}")
    return [".".join(path.relative_to(package).with_suffix("").parts) for path in sources]


def run(*args: str) -> None:
    print("+ " + " ".join(args), flush=True)
    subprocess.run(args, cwd=ROOT, check=True)


def audit_source(names: list[str]) -> str:
    imports = "\n".join(f"import all {name}" for name in names)
    expected = ", ".join(f"`{name}" for name in names)
    return f"""/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
{imports}
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-! Generated project and vendor axiom audit, including private/generated constants. -/

open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let expected : Array Name := #[{expected}]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for modName in expected do
    unless env.header.moduleNames.contains modName do
      throwError "Missing audited module {{modName}}"
  for idx in [:env.header.moduleNames.size] do
    if expected.contains env.header.moduleNames[idx]! then
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Forbidden axiom {{ax}} in {{name}}"
        checked := checked + 1
  if checked == 0 then throwError "Audit selected no project constants"
  logInfo m!"Axiom audit passed: {{checked}} constants from {{expected.size}} modules."

#lint only docBlame in BGW
"""


def main() -> None:
    bgw = modules(ROOT, "BGW")
    vendor = modules(ROOT / "vendor/brownian-motion", "BrownianMotion")
    vendor += modules(ROOT / "vendor/kolmogorov-extension4", "KolmogorovExtension4")
    # BGW's glob covers all its sources; explicit supplier targets cover orphan modules too.
    run("lake", "build", "BGW", *(f"+{name}" for name in vendor))
    lean = (
        "lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
        "-Dlinter.style.header=true", "-Dlinter.style.native=true",
        "-Dlinter.style.maxHeartbeats=true", "-Dlinter.style.longFile=1500",
    )
    run(*lean, "BGWTest/Examples.lean")
    run(*lean, "BGWTest/Measurability.lean")
    # Generate imports from the current checkout, never from a hand-maintained manifest.
    with tempfile.TemporaryDirectory(prefix="bgw-check-") as temporary:
        audit = Path(temporary) / "Audit.lean"
        audit.write_text(audit_source(bgw + vendor), encoding="utf-8")
        run(*lean, str(audit))


if __name__ == "__main__":
    main()
