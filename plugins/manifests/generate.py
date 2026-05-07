#!/usr/bin/env python3
"""Generate plugin build manifests from the shared manifest."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MANIFEST_DIR = Path(__file__).resolve().parent
COMMON_DIR = ROOT / "plugins/common"

VARIANTS = {
    "plugin": {
        "root": ROOT / "plugins/plugin",
        "coqproject": ROOT / "plugins/plugin/_CoqProject",
        "mlpack": ROOT / "plugins/plugin/certirocq_plugin.mlpack",
    },
    "cplugin": {
        "root": ROOT / "plugins/cplugin",
        "coqproject": ROOT / "plugins/cplugin/_CoqProject",
        "mlpack": ROOT / "plugins/cplugin/certirocq_vanilla_plugin.mlpack",
    },
}

MANIFEST = MANIFEST_DIR / "plugin-manifest"


def read_manifest() -> dict[str, list[tuple[str, str | None]]]:
    sections: dict[str, list[tuple[str, str | None]]] = {}
    section: str | None = None

    for line_number, line in enumerate(MANIFEST.read_text().splitlines(), start=1):
        if line.startswith(";"):
            continue

        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1]
            if not section:
                raise ValueError(f"{MANIFEST}:{line_number}: empty section name")
            if section in sections:
                raise ValueError(f"{MANIFEST}:{line_number}: duplicate section {section!r}")
            sections[section] = []
            continue

        if section is None:
            if line:
                raise ValueError(f"{MANIFEST}:{line_number}: content before first section")
            continue

        text, separator, suffix = line.rpartition(" :: ")
        if separator:
            if suffix not in VARIANTS:
                raise ValueError(f"{MANIFEST}:{line_number}: unknown variant {suffix!r}")
            sections[section].append((text, suffix))
        else:
            sections[section].append((line, None))

    return sections


def render_lines(
    sections: dict[str, list[tuple[str, str | None]]], section: str, variant: str
) -> list[str]:
    if section not in sections:
        raise ValueError(f"{MANIFEST}: missing section {section!r}")

    return [
        line
        for line, line_variant in sections[section]
        if line_variant is None or line_variant == variant
    ]


def discover_extraction_files(variant: str) -> list[str]:
    extraction_dir = VARIANTS[variant]["root"] / "extraction"
    if not extraction_dir.is_dir():
        raise ValueError(f"{extraction_dir}: missing extraction directory")

    files = sorted(
        path
        for path in extraction_dir.iterdir()
        if path.is_file() and path.suffix in {".ml", ".mli"}
    )
    return [f"extraction/{path.name}" for path in files]


def module_names(variant: str) -> set[str]:
    root = VARIANTS[variant]["root"]
    names = set()
    for directory, suffixes in [
        (root, {".ml", ".mlg"}),
        (root / "extraction", {".ml"}),
        (root / "static", {".ml"}),
        (COMMON_DIR, {".ml"}),
    ]:
        if not directory.is_dir():
            continue
        for path in directory.iterdir():
            if path.is_file() and path.suffix in suffixes:
                names.add(path.stem.lower())
    return names


def validate_mlpack(lines: list[str], variant: str) -> None:
    known_modules = module_names(variant)
    seen: set[str] = set()
    duplicates: list[str] = []
    stale = [
        line
        for line in lines
        if line and not line.startswith("#") and line.lower() not in known_modules
    ]
    for line in lines:
        if not line or line.startswith("#"):
            continue
        key = line.lower()
        if key in seen:
            duplicates.append(line)
        else:
            seen.add(key)
    if stale:
        names = ", ".join(stale)
        raise ValueError(f"{MANIFEST}: stale {variant} mlpack entries: {names}")
    if duplicates:
        names = ", ".join(duplicates)
        raise ValueError(f"{MANIFEST}: duplicate {variant} mlpack entries: {names}")


def render_coqproject(
    sections: dict[str, list[tuple[str, str | None]]], variant: str
) -> str:
    rendered = render_lines(sections, "coqproject", variant)
    if rendered and rendered[-1] != "":
        rendered.append("")
    rendered.append("# Extracted OCaml files.")
    rendered.extend(discover_extraction_files(variant))
    return "\n".join(rendered) + "\n"


def render_mlpack(sections: dict[str, list[tuple[str, str | None]]], variant: str) -> str:
    rendered = render_lines(sections, "mlpack", variant)
    validate_mlpack(rendered, variant)
    return "\n".join(rendered) + "\n"


def write_if_changed(path: Path, contents: str) -> None:
    if path.exists() and path.read_text() == contents:
        path.touch()
        return
    path.write_text(contents)


def generate(variants: list[str]) -> None:
    sections = read_manifest()
    for variant in variants:
        outputs = VARIANTS[variant]
        write_if_changed(outputs["coqproject"], render_coqproject(sections, variant))
        write_if_changed(outputs["mlpack"], render_mlpack(sections, variant))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Regenerate plugin _CoqProject and .mlpack files."
    )
    parser.add_argument(
        "variants",
        nargs="*",
        choices=sorted(VARIANTS),
        help="plugin variants to generate; defaults to all variants",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        generate(args.variants or sorted(VARIANTS))
    except ValueError as err:
        print(err, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
