"""Run from FQFP with: lake env python tools/qhl/check_measurement.py <upstream-commit.zip>"""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile
import zipfile


REVISION = "3dfe80b893e2ab949a0428a2e18c06153b310bd0"
# Mathlib 4.35 infers the operators in these order lemmas. Only their uses in
# proofs need edits. The register lift, measurement and interpreter stay verbatim.
IMPLICIT_ARGUMENTS = {
    "Qhl.Foundations.Basic": ["LinearMap.nonneg_iff_isPositive f", "LinearMap.le_def f 1"],
    "Qhl.Foundations.Order": [
        "LinearMap.le_def f g", "LinearMap.le_def A B", "ContinuousLinearMap.nonneg_iff_isPositive _",
    ],
    "Qhl.SuperOp.LiftSO": ["LinearMap.le_def _ _"],
    "Qhl.SuperOp.Tenso": ["LinearMap.le_def A 1", "LinearMap.le_def B 1"],
}


def check(archive: zipfile.ZipFile, work: Path) -> None:
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(work), env["LEAN_PATH"]])

    def build(module: str) -> None:
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = work / relative
        olean = source.with_suffix(".olean")
        if olean.exists():
            return
        entry = f"quantum-formal-verification-{REVISION}/{relative.as_posix()}"
        code = archive.read(entry).decode("utf-8")
        for dependency in re.findall(r"^import (Qhl\.[\w.]+)$", code, re.MULTILINE):
            build(dependency)
        for call in IMPLICIT_ARGUMENTS.get(module, []):
            code = code.replace(f"({call})", call.split()[0])
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(code, encoding="utf-8")
        subprocess.run(["lean", f"--root={work}", "-o", olean, source], env=env, check=True)

    build("Qhl.Program.Spec")
    bridge = Path(__file__).with_name("MeasurementCorrespondence.lean")
    subprocess.run(["lean", bridge], env=env, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", help=f"GitHub source ZIP for Qhl commit {REVISION}")
    args = parser.parse_args()
    with zipfile.ZipFile(args.archive) as archive, tempfile.TemporaryDirectory() as directory:
        check(archive, Path(directory).resolve())
