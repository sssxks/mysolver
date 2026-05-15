#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///

"""Compare SAT harness results before and after the current local changes.

The script optionally stashes the current worktree, runs the SAT harness on the
clean tree and saves the JSON summary, restores the worktree, runs the harness
again, and finally compares the two saved summaries with the harness' built-in
`compare` subcommand.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


REPO_ROOT = Path(__file__).resolve().parent.parent
BENCHMARK_ROOT = Path("test/fixture/sat")
PRESET_ROOTS: dict[str, tuple[str, ...]] = {
    "full": (),
    "hard": ("test/fixture/sat/cases/satlib/engine_unsat_1.0",),
}


@dataclass
class StashGuard:
    """Track one temporary stash that must be restored before exit."""

    stash_ref: str | None = None
    restore_needed: bool = False

    def stash_if_needed(self) -> None:
        """Create a temporary stash when the worktree is dirty."""
        if not has_local_changes():
            print(
                "no local changes to stash; comparing two runs of the current tree",
                file=sys.stderr,
            )
            return

        print("stashing local changes", file=sys.stderr)
        run_checked(
            [
                "git",
                "stash",
                "push",
                "--include-untracked",
                "--message",
                "scripts/bench_compare_stash.py",
            ]
        )
        self.stash_ref = "stash@{0}"
        self.restore_needed = True

    def restore(self) -> None:
        """Restore the temporary stash exactly once."""
        if not self.restore_needed:
            return
        if self.stash_ref is None:
            msg = "missing stash reference for pending restore"
            raise RuntimeError(msg)

        print("restoring local changes", file=sys.stderr)
        self.restore_needed = False
        run_checked(["git", "stash", "pop", "--index", self.stash_ref])


def parse_arguments() -> tuple[argparse.Namespace, list[str]]:
    """Parse script arguments and return any extra harness flags separately."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--preset",
        choices=sorted(PRESET_ROOTS),
        default="hard",
        help="Benchmark preset passed to the SAT harness.",
    )
    return parser.parse_known_args()


def has_local_changes() -> bool:
    """Return whether the git worktree has tracked or untracked changes."""
    if subprocess.run(["git", "diff", "--quiet"], check=False, cwd=REPO_ROOT).returncode != 0:
        return True
    if (
        subprocess.run(["git", "diff", "--cached", "--quiet"], check=False, cwd=REPO_ROOT)
        .returncode
        != 0
    ):
        return True

    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        check=True,
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    return bool(untracked.stdout.strip())


def run_checked(command: list[str | Path]) -> None:
    """Run one command and raise on failure."""
    completed = subprocess.run(
        [str(part) for part in command],
        check=False,
        cwd=REPO_ROOT,
    )
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


def run_benchmark_fetch() -> None:
    """Ensure the benchmark fixtures needed by the harness are present."""
    run_checked(["./scripts/fetch_sat_benchmarks.py", "--quiet"])


def resolve_harness_roots(preset: str) -> list[str]:
    """Build the explicit harness roots for one benchmark preset."""
    roots = PRESET_ROOTS[preset]
    if not roots:
        return [str(BENCHMARK_ROOT)]
    return list(roots)


def run_harness(preset: str, harness_args: list[str], save_path: Path) -> int:
    """Run the SAT harness once and write the saved JSON summary."""
    command = [
        "cargo",
        "run",
        "-p",
        "sat-harness",
        "--release",
        "-q",
        "--",
        "run",
        *resolve_harness_roots(preset),
        *harness_args,
        "--save",
        str(save_path),
    ]
    return subprocess.run(command, check=False, cwd=REPO_ROOT).returncode


def run_compare(left: Path, right: Path) -> int:
    """Compare two saved harness summaries."""
    command = [
        "cargo",
        "run",
        "-p",
        "sat-harness",
        "--release",
        "-q",
        "--",
        "compare",
        str(left),
        str(right),
    ]
    return subprocess.run(command, check=False, cwd=REPO_ROOT).returncode


def require_saved_result(path: Path, run_label: str) -> None:
    """Fail when a harness run did not write its requested JSON result."""
    if path.is_file():
        return

    print(
        f"error: {run_label} harness run did not produce a saved result at {path}",
        file=sys.stderr,
    )
    raise SystemExit(1)


def report_nonzero_status(status: int, run_label: str) -> None:
    """Explain non-zero harness exits that still produced saved results."""
    if status == 0:
        return

    print(
        f"{run_label} harness exited with status {status}; continuing to compare saved results",
        file=sys.stderr,
    )


def main() -> int:
    """Run the clean-vs-dirty harness comparison flow."""
    arguments, harness_args = parse_arguments()
    stash = StashGuard()

    with TemporaryDirectory(prefix="bench-compare-stash.") as temp_dir_name:
        temp_dir = Path(temp_dir_name)
        clean_json = temp_dir / "clean.json"
        dirty_json = temp_dir / "dirty.json"

        try:
            run_benchmark_fetch()
            stash.stash_if_needed()

            clean_status = run_harness(arguments.preset, harness_args, clean_json)
            require_saved_result(clean_json, "clean-tree")
            report_nonzero_status(clean_status, "clean-tree")

            stash.restore()

            dirty_status = run_harness(arguments.preset, harness_args, dirty_json)
            require_saved_result(dirty_json, "dirty-tree")
            report_nonzero_status(dirty_status, "dirty-tree")

            return run_compare(clean_json, dirty_json)
        finally:
            if stash.restore_needed:
                stash.restore()


if __name__ == "__main__":
    raise SystemExit(main())
