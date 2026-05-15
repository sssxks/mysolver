#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///

"""Fetch SAT benchmark fixtures and write the expectations manifest."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import shutil
from pathlib import Path
import tarfile
from tempfile import NamedTemporaryFile
from urllib.request import urlopen


@dataclass(frozen=True)
class SuiteDownload:
    """A tarball suite downloaded from SATLIB."""

    source_label: str
    url_template: str
    suite: str
    expected: str

    @property
    def archive_name(self) -> str:
        """Return the tarball file name."""
        return f"{self.suite}.tar.gz"

    @property
    def manifest_line(self) -> str:
        """Return the manifest row for this suite."""
        return f"cases/satlib/{self.suite}/\t{self.expected}\t{self.source_label} {self.suite}"

    @property
    def url(self) -> str:
        """Return the full download URL."""
        return self.url_template.format(suite=self.suite)


@dataclass(frozen=True)
class VlsatCase:
    """A single compressed VLSAT case file."""

    case_name: str
    expected: str
    source_label: str

    @property
    def file_name(self) -> str:
        """Return the case file name."""
        return f"{self.case_name}.cnf.bz2"

    @property
    def manifest_line(self) -> str:
        """Return the manifest row for this case."""
        return f"cases/vlsat/{self.file_name}\t{self.expected}\t{self.source_label} {self.case_name}"

    @property
    def url(self) -> str:
        """Return the full download URL."""
        return f"https://cadp.inria.fr/ftp/benchmarks/vlsat/{self.file_name}"


SATLIB_RANDOM = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/{suite}.tar.gz"
SATLIB_VELEV = "https://www.cs.ubc.ca/~hoos/SATLIB/I-Velev03/{suite}.tar.gz"

RANDOM_SUITES = {
    "uf20-91": SuiteDownload("SATLIB RND3SAT", SATLIB_RANDOM, "uf20-91", "sat"),
    "uuf50-218": SuiteDownload("SATLIB RND3SAT", SATLIB_RANDOM, "uuf50-218", "unsat"),
    "uf100-430": SuiteDownload("SATLIB RND3SAT", SATLIB_RANDOM, "uf100-430", "sat"),
    "uuf100-430": SuiteDownload("SATLIB RND3SAT", SATLIB_RANDOM, "uuf100-430", "unsat"),
}
VELEV_SUITES = {
    "engine_unsat_1.0": SuiteDownload("SATLIB I-Velev03", SATLIB_VELEV, "engine_unsat_1.0", "unsat"),
    "vliw_unsat_3.0": SuiteDownload("SATLIB I-Velev03", SATLIB_VELEV, "vliw_unsat_3.0", "unsat"),
    "pipe_sat_1.0": SuiteDownload("SATLIB I-Velev03", SATLIB_VELEV, "pipe_sat_1.0", "sat"),
    "pipe_unsat_1.0": SuiteDownload("SATLIB I-Velev03", SATLIB_VELEV, "pipe_unsat_1.0", "unsat"),
}
VLSAT_CASES = {
    "vlsat1_9588_392364": VlsatCase("vlsat1_9588_392364", "sat", "CADP VLSAT-1"),
    "vlsat1_15498_838393": VlsatCase("vlsat1_15498_838393", "sat", "CADP VLSAT-1"),
}
PROFILES = {
    "smoke": {
        "random": ("uf20-91", "uuf50-218", "uf100-430"),
        "velev": ("engine_unsat_1.0",),
        "vlsat": ("vlsat1_9588_392364", "vlsat1_15498_838393"),
    },
    "core": {
        "random": ("uf20-91", "uuf50-218", "uf100-430", "uuf100-430"),
        "velev": ("engine_unsat_1.0", "vliw_unsat_3.0"),
        "vlsat": ("vlsat1_9588_392364", "vlsat1_15498_838393"),
    },
    "full": {
        "random": ("uf20-91", "uuf50-218", "uf100-430", "uuf100-430"),
        "velev": ("engine_unsat_1.0", "vliw_unsat_3.0", "pipe_sat_1.0", "pipe_unsat_1.0"),
        "vlsat": ("vlsat1_9588_392364", "vlsat1_15498_838393"),
    },
}


def parse_arguments() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true", help="Suppress cache hit notices.")
    parser.add_argument(
        "--profile",
        choices=sorted(PROFILES),
        default="smoke",
        help="Benchmark profile to download.",
    )
    parser.add_argument(
        "--dest",
        default="test/fixture/sat",
        help="Destination directory for downloaded benchmarks.",
    )
    return parser.parse_args()


def download_file(url: str, output_path: Path, *, quiet: bool) -> None:
    """Download a file unless it is already present."""
    if output_path.is_file():
        if not quiet:
            print(f"cached  {output_path}")
        return

    output_path.parent.mkdir(parents=True, exist_ok=True)
    print(f"fetch   {url}")

    temporary_path: Path | None = None
    try:
        with urlopen(url) as response, NamedTemporaryFile(
            delete=False,
            dir=output_path.parent,
            prefix=f"{output_path.name}.",
            suffix=".tmp",
        ) as temporary:
            shutil.copyfileobj(response, temporary)
            temporary_path = Path(temporary.name)

        temporary_path.replace(output_path)
    except Exception:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)
        raise


def extract_tarball(archive_path: Path, output_dir: Path, *, quiet: bool) -> None:
    """Extract a tarball unless the output directory already contains files."""
    output_dir.mkdir(parents=True, exist_ok=True)
    if any(output_dir.iterdir()):
        if not quiet:
            print(f"ready   {output_dir}")
        return

    print(f"extract {archive_path}")
    with tarfile.open(archive_path, mode="r:gz") as archive:
        archive.extractall(output_dir, filter="data")


def fetch_suite(
    suite: SuiteDownload,
    archives_dir: Path,
    cases_dir: Path,
    *,
    quiet: bool,
) -> None:
    """Download and extract one SATLIB suite."""
    archive_path = archives_dir / suite.archive_name
    output_dir = cases_dir / "satlib" / suite.suite
    download_file(suite.url, archive_path, quiet=quiet)
    extract_tarball(archive_path, output_dir, quiet=quiet)


def fetch_vlsat_case(case: VlsatCase, cases_dir: Path, *, quiet: bool) -> None:
    """Download one compressed VLSAT case file."""
    output_path = cases_dir / "vlsat" / case.file_name
    download_file(case.url, output_path, quiet=quiet)


def manifest_lines(profile: str) -> list[str]:
    """Build the expectations manifest for one profile."""
    selected = PROFILES[profile]
    lines = ["# prefix\texpected\tsource"]
    lines.extend(RANDOM_SUITES[name].manifest_line for name in selected["random"])
    lines.extend(VELEV_SUITES[name].manifest_line for name in selected["velev"])
    lines.extend(VLSAT_CASES[name].manifest_line for name in selected["vlsat"])
    return lines


def write_manifest(profile: str, manifest_path: Path) -> None:
    """Write the expectations manifest."""
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text("\n".join(manifest_lines(profile)) + "\n", encoding="utf-8")


def main() -> int:
    """Fetch the configured benchmark profile."""
    arguments = parse_arguments()
    destination = Path(arguments.dest)
    archives_dir = destination / "upstream"
    cases_dir = destination / "cases"
    manifest_path = destination / "expectations.tsv"

    selected = PROFILES[arguments.profile]
    for suite_name in selected["random"]:
        fetch_suite(RANDOM_SUITES[suite_name], archives_dir, cases_dir, quiet=arguments.quiet)
    for suite_name in selected["velev"]:
        fetch_suite(VELEV_SUITES[suite_name], archives_dir, cases_dir, quiet=arguments.quiet)
    for case_name in selected["vlsat"]:
        fetch_vlsat_case(VLSAT_CASES[case_name], cases_dir, quiet=arguments.quiet)

    write_manifest(arguments.profile, manifest_path)

    if not arguments.quiet:
        print(f"\nbenchmarks ready under {destination}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
