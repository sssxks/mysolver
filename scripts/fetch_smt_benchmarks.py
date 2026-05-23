#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.14"
# dependencies = ["zstandard>=0.23"]
# ///

"""Fetch SMT-LIB benchmarks from Zenodo and extract them."""

from __future__ import annotations

import argparse
import io
import shutil
import sys
import tarfile
from pathlib import Path
from tempfile import NamedTemporaryFile
from urllib.request import urlopen

import zstandard as zstd

ZENODO_RECORD = "15493096"
"""Zenodo record for SMT-LIB 2025 incremental benchmarks."""

LOGICS: dict[str, tuple[str, str]] = {
    "QF_UF": ("QF_UF.tar.zst", "QF_UF.tar.zst"),
}
"""Maps logic names to (file_key, archive_name)."""

DEFAULT_DEST = "test/fixture/smt"


def parse_arguments() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--logic",
        choices=sorted(LOGICS),
        default="QF_UF",
        help="SMT-LIB logic to fetch.",
    )
    parser.add_argument(
        "--dest",
        default=DEFAULT_DEST,
        help="Destination root directory for extracted benchmarks.",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress cache-hit notices.",
    )
    return parser.parse_args()


def _files_url(record_id: str) -> str:
    return f"https://zenodo.org/api/records/{record_id}/files"


def _resolve_download_url(record_id: str, file_key: str) -> str:
    """Query the Zenodo record files API and return the download URL for *file_key*."""
    api_url = _files_url(record_id)
    with urlopen(api_url) as response:
        import json

        entries = json.loads(response.read().decode())
    if isinstance(entries, dict):
        entries = entries.get("entries", [entries])
    for entry in entries:
        if entry.get("key") == file_key:
            return str(entry["links"]["content"])
    msg = f"File {file_key!r} not found in Zenodo record {record_id}"
    raise FileNotFoundError(msg)


def _download_file(url: str, output_path: Path, *, quiet: bool) -> None:
    """Download a file unless it is already cached."""
    if output_path.is_file():
        if not quiet:
            print(f"cached  {output_path}")
        return

    output_path.parent.mkdir(parents=True, exist_ok=True)
    print(f"fetch   {url}")

    tmp_path: Path | None = None
    try:
        with (
            urlopen(url) as response,
            NamedTemporaryFile(
                delete=False,
                dir=output_path.parent,
                prefix=f"{output_path.name}.",
                suffix=".tmp",
            ) as tmp,
        ):
            shutil.copyfileobj(response, tmp)
            tmp_path = Path(tmp.name)
        tmp_path.replace(output_path)
    except Exception:
        if tmp_path is not None:
            tmp_path.unlink(missing_ok=True)
        raise


def _extract_zstd_tarball(archive_path: Path, output_dir: Path, *, quiet: bool) -> None:
    """Decompress a .tar.zst archive into *output_dir*."""
    output_dir.mkdir(parents=True, exist_ok=True)
    if any(output_dir.iterdir()):
        if not quiet:
            print(f"ready   {output_dir}")
        return

    print(f"extract {archive_path}")
    dctx = zstd.ZstdDecompressor()
    with archive_path.open("rb") as raw:
        decompressed = dctx.stream_reader(raw)
        buf = io.BytesIO()
        shutil.copyfileobj(decompressed, buf)
        buf.seek(0)
        with tarfile.open(fileobj=buf, mode="r:") as archive:
            archive.extractall(output_dir, filter="data")


def _cache_hit(archive_path: Path, output_dir: Path, *, quiet: bool) -> bool:
    """Return True if both the archive and extracted cases are already cached."""
    archive_ok = archive_path.is_file()
    extracted_ok = output_dir.is_dir() and any(output_dir.iterdir())
    if archive_ok and extracted_ok:
        if not quiet:
            print(f"cached  {archive_path}")
            print(f"ready   {output_dir}")
        return True
    return False


def main() -> int:
    """Download and extract SMT-LIB benchmarks."""
    args = parse_arguments()
    file_key, archive_name = LOGICS[args.logic]
    dest = Path(args.dest)
    archives_dir = dest / "upstream"
    cases_dir = dest / "cases"

    archive_path = archives_dir / archive_name
    output_dir = cases_dir / args.logic

    if not _cache_hit(archive_path, output_dir, quiet=args.quiet):
        download_url = _resolve_download_url(ZENODO_RECORD, file_key)
        _download_file(download_url, archive_path, quiet=True)
        _extract_zstd_tarball(archive_path, output_dir, quiet=args.quiet)

    if not args.quiet:
        print(f"\nbenchmarks ready under {output_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
