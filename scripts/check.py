"""Run the project's build, declaration/style lint and every Lean regression."""

from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    commands = [
        ["lake", "build", "FQFP"],
        ["lake", "exe", "runLinter"],
        ["lake", "exe", "lint-style"],
        ["lake", "env", "lean", "scripts/ApiSnapshot.lean"],
        [sys.executable, "-m", "unittest", "discover", "-s", "scripts", "-p", "test_*.py"],
    ]
    for path in sorted((ROOT / "FQFPTest").rglob("*.lean")):
        commands.append(["lake", "env", "lean", path.relative_to(ROOT).as_posix()])
    for command in commands:
        print("+ " + " ".join(command), flush=True)
        result = subprocess.call(command, cwd=ROOT)
        if result:
            return result
    return 0


if __name__ == "__main__":
    sys.exit(main())
