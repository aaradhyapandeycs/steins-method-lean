#!/usr/bin/env python3
"""Download and verify the pinned arXiv:1109.1880v1 source without executing TeX."""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fetch_verified(url: str, expected_sha256: str, target: Path) -> None:
    if target.is_symlink():
        raise RuntimeError(f"Refusing to use symlink artifact: {target}")
    if target.is_file() and sha256_bytes(target.read_bytes()) == expected_sha256:
        return
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "SteinMethod-Lean4-ProvenanceFetcher/1.0"},
    )
    with urllib.request.urlopen(req, timeout=90) as response:
        data = response.read()
    actual = sha256_bytes(data)
    if actual != expected_sha256:
        raise RuntimeError(
            f"SHA-256 mismatch for {target.name} from {url}: "
            f"expected {expected_sha256}, got {actual}"
        )
    target.write_bytes(data)


def write_normalized_utf8_tex(raw_tex_path: Path, expected_sha256: str, out_path: Path) -> None:
    if out_path.is_symlink():
        raise RuntimeError(f"Refusing to overwrite symlink: {out_path}")
    text = raw_tex_path.read_bytes().decode("iso-8859-1")
    normalized = text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")
    actual = sha256_bytes(normalized)
    if actual != expected_sha256:
        raise RuntimeError(
            f"Normalized UTF-8 SHA-256 mismatch for {out_path.relative_to(ROOT)}: "
            f"expected {expected_sha256}, got {actual}"
        )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    if not out_path.is_file() or sha256_bytes(out_path.read_bytes()) != expected_sha256:
        out_path.write_bytes(normalized)


def main() -> None:
    provenance_path = ROOT / "source" / "provenance.json"
    metadata = json.loads(provenance_path.read_text(encoding="utf-8"))
    destination = ROOT / "source" / "upstream"
    destination.mkdir(parents=True, exist_ok=True)

    tar_name = "1109.1880v1.tar.gz"
    pdf_name = "1109.1880v1.pdf"
    fetch_verified(
        metadata["source_url"],
        metadata["artifacts"][tar_name],
        destination / tar_name,
    )
    fetch_verified(
        metadata["pdf_url"],
        metadata["artifacts"][pdf_name],
        destination / pdf_name,
    )

    extraction = destination / "tex"
    extraction.mkdir(exist_ok=True)
    expected_files: dict[str, str] = metadata["source_files"]

    for name, expected_hash in expected_files.items():
        existing = extraction / name
        if existing.is_symlink():
            raise RuntimeError(f"Refusing to overwrite symlink: {name}")
        if existing.exists() and sha256_bytes(existing.read_bytes()) != expected_hash:
            raise RuntimeError(f"Refusing to overwrite modified file: {name}")

    raw_tar = (destination / tar_name).read_bytes()
    extracted_names: set[str] = set()
    with tarfile.open(fileobj=io.BytesIO(raw_tar), mode="r:*") as archive:
        members = archive.getmembers()
        for member in members:
            resolved = (extraction / member.name).resolve()
            if not resolved.is_relative_to(extraction.resolve()) or not (
                member.isfile() or member.isdir()
            ):
                raise RuntimeError(f"Unsafe archive entry: {member.name}")
        for member in members:
            target = extraction / member.name
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                rel_name = target.relative_to(extraction).as_posix()
                extracted_names.add(rel_name)
                if not target.exists():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    stream = archive.extractfile(member)
                    if stream is None:
                        raise RuntimeError(f"Cannot read archive entry: {member.name}")
                    with stream, target.open("xb") as out_f:
                        shutil.copyfileobj(stream, out_f)

    if extracted_names != set(expected_files.keys()):
        raise RuntimeError(
            f"Archive file set {sorted(extracted_names)} != "
            f"provenance source_files {sorted(expected_files.keys())}"
        )

    for name, expected_hash in expected_files.items():
        actual_hash = sha256_bytes((extraction / name).read_bytes())
        if actual_hash != expected_hash:
            raise RuntimeError(
                f"Extracted SHA-256 mismatch for {name}: "
                f"expected {expected_hash}, got {actual_hash}"
            )

    normalized_files: dict[str, str] = metadata.get("normalized_files", {})
    utf8_rel = "docs/source/SteinIntro_utf8.tex"
    if utf8_rel in normalized_files:
        write_normalized_utf8_tex(
            extraction / "SteinIntro.tex",
            normalized_files[utf8_rel],
            ROOT / utf8_rel,
        )

    print(
        f"Verified {metadata['arxiv_id']} ({metadata['latest_version']}): "
        f"{len(expected_files)} extracted files in {destination.relative_to(ROOT)}/, "
        f"{len(metadata['artifacts'])} downloads, and "
        f"{len(normalized_files)} normalized UTF-8 file(s)."
    )


if __name__ == "__main__":
    main()
